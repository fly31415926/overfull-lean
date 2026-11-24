#!/usr/bin/env python3
"""Stage exact immutable Git blobs for ordinary browser file uploads.

This helper performs no network operation and invokes only read-only Git
commands. Known-public commits are caller-supplied, already-fetched objects;
their publication must be established by separate publication receipts.
"""
from __future__ import annotations

import argparse
from collections import defaultdict
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import stat
import subprocess
import sys
import tempfile


DEFAULT_REPO = Path('/workspace/scratch/05b9e46fe96b/overfull-lean')
DEFAULT_OBJECTS = Path('/workspace/shared/overfull-publication-objects')
MAX_FILES = 50
MAX_BYTES = 12_000_000
OID = re.compile(r'[0-9a-f]{40}\Z')


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def git_hash(kind, data):
    return hashlib.sha1(kind.encode() + b' ' + str(len(data)).encode() + b'\0' + data).hexdigest()


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def write_json(path, value):
    data = (json.dumps(value, indent=2, ensure_ascii=False) + '\n').encode()
    with path.open('xb') as stream:
        stream.write(data)
    return {'path': str(path), 'bytes': len(data), 'sha256': sha256(data)}


class Repository:
    def __init__(self, path):
        self.path = path.resolve(strict=True)
        self.env = {**os.environ, 'GIT_NO_LAZY_FETCH': '1', 'GIT_OPTIONAL_LOCKS': '0'}
        self.command = ['git', '--no-pager', '-C', str(self.path)]
        top = Path(self.git('rev-parse', '--show-toplevel').decode().strip()).resolve()
        require(top == self.path, 'Repository argument must be its exact worktree root')
        require(self.git('rev-parse', '--show-object-format').strip() == b'sha1',
                'This publication transport requires a SHA-1 Git repository')
        self.trees = {}

    def git(self, *args):
        return subprocess.check_output(self.command + list(args), env=self.env)

    def resolve(self, oid, commit_only=False):
        require(OID.fullmatch(oid), 'An exact lowercase 40-character object ID is required')
        kind = self.git('cat-file', '-t', oid).decode().strip()
        require(kind in ({'commit'} if commit_only else {'commit', 'tree'}),
                f'Expected {"commit" if commit_only else "commit or tree"}, got {kind}: {oid}')
        if kind == 'tree':
            return {'object_sha': oid, 'object_type': kind, 'tree_sha': oid}
        data = self.git('cat-file', 'commit', oid)
        require(git_hash('commit', data) == oid, f'Commit object hash mismatch: {oid}')
        first = data.split(b'\n', 1)[0]
        require(first.startswith(b'tree '), f'Commit lacks its tree header: {oid}')
        tree = first[5:].decode('ascii')
        require(OID.fullmatch(tree), f'Invalid commit tree ID: {oid}')
        return {'object_sha': oid, 'object_type': kind, 'commit_sha': oid, 'tree_sha': tree}

    def tree(self, oid):
        if oid in self.trees:
            return self.trees[oid]
        raw = self.git('ls-tree', '-r', '-t', '-z', '--full-tree', oid)
        records, names, directories = [], set(), {b'': oid}
        children = defaultdict(list)
        for item in raw.split(b'\0'):
            if not item:
                continue
            meta, path = item.split(b'\t', 1)
            mode, kind, object_id = meta.split()
            require(path and not path.startswith(b'/')
                    and all(part not in {b'', b'.', b'..'} for part in path.split(b'/')),
                    'Unexpected nonrelative Git path')
            require(path not in names, f'Duplicate Git path: {path!r}')
            names.add(path)
            object_sha = object_id.decode('ascii')
            require(OID.fullmatch(object_sha), 'Invalid tree entry object ID')
            allowed = {b'tree': {b'040000'}, b'blob': {b'100644', b'100755', b'120000'},
                       b'commit': {b'160000'}}
            require(kind in allowed and mode in allowed[kind], 'Unexpected Git entry type/mode')
            record = {'path': path.decode('utf-8'), 'mode': mode.decode('ascii'),
                      'type': kind.decode('ascii'), 'sha': object_sha}
            records.append(record)
            parent, _, basename = path.rpartition(b'/')
            children[parent].append((basename, mode, kind, object_id))
            if kind == b'tree':
                directories[path] = object_sha
        require(set(children) <= set(directories), 'Tree contains an unenumerated directory')
        # Reconstruct every tree using Git's directory-aware basename ordering.
        # Including explicit directory entries preserves even empty subtrees.
        for directory, expected in directories.items():
            ordered = sorted(children[directory], key=lambda e: e[0] + (b'/' if e[2] == b'tree' else b''))
            data = b''.join(mode.lstrip(b'0') + b' ' + name + b'\0' + bytes.fromhex(oid_.decode())
                            for name, mode, _, oid_ in ordered)
            require(git_hash('tree', data) == expected,
                    f'Reconstructed tree hash mismatch for {directory!r}')
        result = {'tree_sha': oid,
                  'entries': sorted((r for r in records if r['type'] != 'tree'), key=lambda r: r['path']),
                  'directories': sorted((r for r in records if r['type'] == 'tree'), key=lambda r: r['path'])}
        self.trees[oid] = result
        return result


def outside_repository(path, repo):
    resolved = path.resolve()
    require(resolved != repo and repo not in resolved.parents,
            f'Output must stay outside the repository worktree: {resolved}')
    return resolved


def existing_object(path, oid, size, expected_sha256):
    info = path.lstat()
    require(stat.S_ISREG(info.st_mode), f'Staged object must be a regular file: {path}')
    require(info.st_size == size, f'Existing staged object has wrong length: {path}')
    h1 = hashlib.sha1(b'blob ' + str(size).encode() + b'\0')
    h256 = hashlib.sha256()
    with path.open('rb') as source:
        for data in iter(lambda: source.read(1024 * 1024), b''):
            h1.update(data)
            h256.update(data)
    require(h1.hexdigest() == oid and h256.hexdigest() == expected_sha256,
            f'Existing staged object differs from the immutable Git blob: {path}')


def stage_blobs(repo, blob_ids, needed, objects, output, max_bytes):
    inventory, reused = {}, 0
    with (output / 'git-cat-file.stderr.log').open('xb') as error_log:
        process = subprocess.Popen(repo.command + ['cat-file', '--batch'], env=repo.env,
                                   stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=error_log)
        try:
            for oid in sorted(blob_ids):
                process.stdin.write((oid + '\n').encode('ascii'))
                process.stdin.flush()
                header = process.stdout.readline().decode('ascii').strip().split()
                require(len(header) == 3 and header[:2] == [oid, 'blob'],
                        f'Unexpected or missing cat-file blob: {header}')
                size = int(header[2])
                require(size >= 0, 'Negative blob length')
                upload = oid in needed
                require(not upload or size <= max_bytes,
                        f'Blob {oid} is {size} bytes, exceeding the exact-file batch limit {max_bytes}; '
                        'an immutable blob cannot be split for this upload method')
                h1 = hashlib.sha1(b'blob ' + str(size).encode() + b'\0')
                h256 = hashlib.sha256()
                temporary = None
                sink = None
                try:
                    if upload:
                        fd, name = tempfile.mkstemp(prefix='pending-' + oid + '-', dir=objects)
                        temporary = Path(name)
                        sink = os.fdopen(fd, 'wb')
                    remaining = size
                    while remaining:
                        data = process.stdout.read(min(remaining, 1024 * 1024))
                        require(data, f'Truncated blob body: {oid}')
                        remaining -= len(data)
                        h1.update(data)
                        h256.update(data)
                        if sink is not None:
                            sink.write(data)
                    require(process.stdout.read(1) == b'\n', f'Missing blob separator: {oid}')
                    require(h1.hexdigest() == oid, f'Git blob SHA-1 mismatch: {oid}')
                    digest = h256.hexdigest()
                    entry = {'git_blob_sha1': oid, 'bytes': size, 'sha256': digest,
                             'known_public': not upload, 'needs_upload': upload}
                    if sink is not None:
                        sink.close()
                        sink = None
                        temporary.chmod(0o644)
                        destination = objects / oid
                        try:
                            os.link(temporary, destination)
                        except FileExistsError:
                            existing_object(destination, oid, size, digest)
                            reused += 1
                        entry['local_file'] = str(destination)
                    inventory[oid] = entry
                finally:
                    if sink is not None:
                        sink.close()
                    if temporary is not None:
                        temporary.unlink(missing_ok=True)
            process.stdin.close()
            require(process.wait() == 0, 'git cat-file failed; see saved stderr')
        finally:
            if process.poll() is None:
                process.terminate()
                try:
                    process.wait(timeout=10)
                except subprocess.TimeoutExpired:
                    process.kill()
                    process.wait()
            process.stdout.close()
            if not process.stdin.closed:
                process.stdin.close()
    return inventory, reused


def prepare(args):
    repo = Repository(args.repo)
    output = outside_repository(args.output_dir, repo.path)
    objects = outside_repository(args.objects_dir, repo.path)
    require(output != objects, 'Manifest output and shared object directories must differ')
    require(1 <= args.max_files <= MAX_FILES and 1 <= args.max_bytes <= MAX_BYTES,
            'Batch limits must be positive and no larger than 50 files / 12,000,000 bytes')
    output.mkdir(parents=True, exist_ok=False)
    objects.mkdir(parents=True, exist_ok=True)
    try:
        snapshot = repo.resolve(args.snapshot)
        target = repo.tree(snapshot['tree_sha'])
        known_commits, public_blobs = [], set()
        for oid in dict.fromkeys(args.known_public_commit):
            commit = repo.resolve(oid, commit_only=True)
            public_tree = repo.tree(commit['tree_sha'])
            blobs = {e['sha'] for e in public_tree['entries'] if e['type'] == 'blob'}
            public_blobs.update(blobs)
            known_commits.append({**commit, 'unique_blob_count': len(blobs)})
        by_blob = defaultdict(list)
        for entry in target['entries']:
            if entry['type'] == 'blob':
                by_blob[entry['sha']].append(entry)
        needed = set(by_blob) - public_blobs
        inventory, reused = stage_blobs(repo, set(by_blob), needed, objects, output, args.max_bytes)
        files = []
        for oid in sorted(needed):
            files.append({**inventory[oid], 'target_paths': by_blob[oid]})
        batches, current, total = [], [], 0
        for item in files:
            if current and (len(current) == args.max_files or total + item['bytes'] > args.max_bytes):
                batches.append(current)
                current, total = [], 0
            current.append(item)
            total += item['bytes']
        if current:
            batches.append(current)
        metadata = {
            'target_tree': write_json(output / 'target-tree.json', target),
            'blob_inventory': write_json(output / 'blob-inventory.json',
                                         {'tree_sha': snapshot['tree_sha'], 'blobs': list(inventory.values())}),
            'required_uploads': write_json(output / 'required-uploads.json',
                                           {'tree_sha': snapshot['tree_sha'], 'blobs': files}),
        }
        batch_records = []
        for number, batch in enumerate(batches, 1):
            size = sum(f['bytes'] for f in batch)
            require(len(batch) <= args.max_files and size <= args.max_bytes, 'Internal batch bound failure')
            record = {'batch': number, 'tree_sha': snapshot['tree_sha'], 'file_count': len(batch),
                      'bytes': size, 'files': [{k: f[k] for k in ('git_blob_sha1', 'bytes', 'sha256', 'local_file')}
                                             for f in batch]}
            batch_file = write_json(output / f'batch-{number:04d}.json', record)
            paths_file = output / f'batch-{number:04d}.paths.txt'
            paths_data = ''.join(f['local_file'] + '\n' for f in batch).encode()
            with paths_file.open('xb') as stream:
                stream.write(paths_data)
            batch_records.append({'batch': number, 'file_count': len(batch), 'bytes': size,
                                  'manifest': batch_file, 'paths_file': str(paths_file),
                                  'paths_sha256': sha256(paths_data)})
        result = {
            'schema_version': 1, 'kind': 'immutable_git_browser_upload_preparation',
            'prepared_at_utc': datetime.now(timezone.utc).isoformat(), 'repository': str(repo.path),
            'snapshot': snapshot, 'known_public_commits': known_commits,
            'known_public_basis': 'Exact already-fetched commits supplied by the caller; no remote check performed here',
            'shared_objects_directory': str(objects), 'batch_limits': {'files': args.max_files, 'bytes': args.max_bytes},
            'target_leaf_entry_count': len(target['entries']), 'target_unique_blob_count': len(by_blob),
            'known_public_unique_blob_count': len(public_blobs),
            'target_blobs_already_public': len(set(by_blob) & public_blobs),
            'required_upload_blob_count': len(files), 'required_upload_bytes': sum(f['bytes'] for f in files),
            'required_upload_path_count': sum(len(f['target_paths']) for f in files),
            'staged_files_reused_after_hash_check': reused, 'batch_count': len(batch_records),
            'manifests': metadata, 'batches': batch_records,
            'all_target_blob_sha1_sha256_lengths_checked': True,
            'all_tree_objects_independently_reconstructed': True,
            'all_required_blobs_staged_by_exact_git_sha1': True,
            'remote_operations_performed': False, 'mutating_git_commands_used': [],
            'helper_sha256': sha256(Path(__file__).read_bytes()),
        }
        write_json(output / 'manifest.json', result)
        print(json.dumps({k: result[k] for k in ('snapshot', 'target_leaf_entry_count', 'target_unique_blob_count',
              'required_upload_blob_count', 'required_upload_bytes', 'batch_count', 'staged_files_reused_after_hash_check')}, indent=2))
        print('Manifest:', output / 'manifest.json')
        return result
    except BaseException as error:
        write_json(output / 'preparation-failure.json', {'kind': 'failed_immutable_object_preparation',
                   'observed_at_utc': datetime.now(timezone.utc).isoformat(), 'error_type': type(error).__name__,
                   'error': str(error), 'snapshot_requested': args.snapshot, 'remote_operations_performed': False})
        raise


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, default=DEFAULT_REPO)
    parser.add_argument('--snapshot', required=True, help='Exact local commit or tree SHA-1')
    parser.add_argument('--known-public-commit', action='append', required=True,
                        help='Exact already-fetched public commit SHA-1; repeat to take the union of its blobs')
    parser.add_argument('--objects-dir', type=Path, default=DEFAULT_OBJECTS)
    parser.add_argument('--output-dir', type=Path, required=True, help='Fresh manifest directory outside the repository')
    parser.add_argument('--max-files', type=int, default=MAX_FILES)
    parser.add_argument('--max-bytes', type=int, default=MAX_BYTES)
    prepare(parser.parse_args())


if __name__ == '__main__':
    main()
