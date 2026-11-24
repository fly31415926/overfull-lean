#!/usr/bin/env python3
"""Prepare bounded SHA-only GitHub create-tree requests without remote calls.

The base and target must be exact local commit or tree objects. The caller must
separately establish publication of the base and known-public commit. Every
target blob must already occur in one of those trees, regardless of its path.
Requests are sequential: check each server result against the recorded expected
tree before submitting the next request. This helper never submits a request.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile


DEFAULT_REPO = Path('/workspace/scratch/05b9e46fe96b/overfull-lean')
DEFAULT_REPOSITORY = 'fly31415926/overfull-lean'
MAX_ENTRIES = 100
MAX_JSON_BYTES = 50_000
OID = re.compile(r'[0-9a-f]{40}\Z')
ALLOWED = {'blob': {'100644', '100755', '120000'}, 'commit': {'160000'}}


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def git_hash(kind, data):
    return hashlib.sha1(kind.encode() + b' ' + str(len(data)).encode() + b'\0' + data).hexdigest()


def json_bytes(value):
    return (json.dumps(value, indent=2, ensure_ascii=False) + '\n').encode('utf-8')


def write_bytes(path, data):
    with path.open('xb') as stream:
        stream.write(data)
    return {'path': str(path), 'bytes': len(data), 'sha256': sha256(data)}


def write_json(path, value):
    return write_bytes(path, json_bytes(value))


def flat_tree_sha(entries):
    """Independently encode every directory from its exact flat leaf entries."""
    root = {}
    for path, entry in entries.items():
        parts = path.encode('utf-8').split(b'/')
        directory = root
        for part in parts[:-1]:
            child = directory.setdefault(part, {})
            require(isinstance(child, dict), f'File/directory collision at {path!r}')
            directory = child
        require(parts[-1] not in directory, f'Duplicate or colliding leaf: {path!r}')
        directory[parts[-1]] = (entry['mode'], entry['type'], entry['sha'])

    def encode(directory):
        children = []
        for name, value in directory.items():
            if isinstance(value, dict):
                children.append((name + b'/', b'40000', name, encode(value)))
            else:
                mode, _, oid = value
                children.append((name, mode.encode('ascii'), name, oid))
        data = b''.join(mode + b' ' + name + b'\0' + bytes.fromhex(oid)
                        for _, mode, name, oid in sorted(children, key=lambda row: row[0]))
        return git_hash('tree', data)

    return encode(root)


class Repository:
    def __init__(self, path):
        self.path = path.resolve(strict=True)
        self.env = {**os.environ, 'GIT_NO_LAZY_FETCH': '1', 'GIT_OPTIONAL_LOCKS': '0'}
        self.env.pop('GIT_INDEX_FILE', None)
        self.command = ['git', '--no-pager', '-c', 'core.splitIndex=false',
                        '-c', 'core.sparseCheckout=false', '-c', 'core.fsmonitor=false',
                        '-C', str(self.path)]
        top = Path(self.git('rev-parse', '--show-toplevel').decode().strip()).resolve()
        require(top == self.path, 'Repository argument must name its exact worktree root')
        require(self.git('rev-parse', '--show-object-format').strip() == b'sha1',
                'This helper requires a SHA-1 Git repository')

    def git(self, *args, data=None, env=None):
        return subprocess.check_output(self.command + list(args), input=data,
                                       env=self.env if env is None else env)

    def resolve(self, oid, commit_only=False):
        require(OID.fullmatch(oid), 'An exact lowercase 40-character object ID is required')
        kind = self.git('cat-file', '-t', oid).decode().strip()
        require(kind in ({'commit'} if commit_only else {'commit', 'tree'}),
                f'Expected {"commit" if commit_only else "commit or tree"}: {oid}')
        if kind == 'tree':
            return {'object_sha': oid, 'object_type': kind, 'tree_sha': oid}
        data = self.git('cat-file', 'commit', oid)
        require(git_hash('commit', data) == oid, f'Commit hash mismatch: {oid}')
        first = data.split(b'\n', 1)[0]
        require(first.startswith(b'tree '), f'Commit lacks its tree header: {oid}')
        tree = first[5:].decode('ascii')
        require(OID.fullmatch(tree), f'Invalid commit tree ID: {oid}')
        return {'object_sha': oid, 'object_type': kind, 'commit_sha': oid, 'tree_sha': tree}

    def flat_tree(self, tree, require_index_representation=True):
        data = self.git('cat-file', 'tree', tree)
        require(git_hash('tree', data) == tree, f'Root tree object hash mismatch: {tree}')
        entries = {}
        for item in self.git('ls-tree', '-r', '-z', '--full-tree', tree).split(b'\0'):
            if not item:
                continue
            meta, raw_path = item.split(b'\t', 1)
            mode, kind, oid = (value.decode('ascii') for value in meta.split())
            path = raw_path.decode('utf-8')
            require(path and not path.startswith('/')
                    and all(part not in {'', '.', '..'} for part in path.split('/')),
                    f'Unexpected nonrelative path: {path!r}')
            require(path not in entries, f'Duplicate tree path: {path!r}')
            require(kind in ALLOWED and mode in ALLOWED[kind] and OID.fullmatch(oid),
                    f'Unsupported tree entry: {path!r}')
            entries[path] = {'path': path, 'mode': mode, 'type': kind, 'sha': oid}
        if require_index_representation:
            require(flat_tree_sha(entries) == tree,
                    f'Tree {tree} cannot be reproduced exactly from flat index entries; '
                    'explicit empty subtrees are not supported')
        return entries

    def git_path(self, name):
        path = Path(self.git('rev-parse', '--git-path', name).decode().strip())
        return (path if path.is_absolute() else self.path / path).resolve()

    def state(self):
        index = self.git_path('index')
        return {'index_path': str(index),
                'index_bytes': index.read_bytes() if index.exists() else None,
                'head_bytes': self.git_path('HEAD').read_bytes(),
                'head_commit': self.git('rev-parse', '--verify', 'HEAD').decode().strip(),
                'refs_bytes': self.git('for-each-ref', '--format=%(refname) %(objectname) %(symref)')}


def state_record(state):
    return {'head_commit': state['head_commit'], 'head_file_sha256': sha256(state['head_bytes']),
            'index_path': state['index_path'],
            'index_bytes': None if state['index_bytes'] is None else len(state['index_bytes']),
            'index_sha256': None if state['index_bytes'] is None else sha256(state['index_bytes']),
            'all_refs_sha256': sha256(state['refs_bytes'])}


def workflow_path(path):
    return path == '.github/workflows' or path.startswith('.github/workflows/')


def request_value(repository, base, entries):
    return {'repository_full_name': repository, 'base_tree_sha': base, 'tree_elements': entries}


def batch_entries(entries, repository, max_entries, max_bytes):
    batches, pending = [], []
    for entry in entries:
        proposed = pending + [entry]
        if pending and (len(proposed) > max_entries
                        or len(json_bytes(request_value(repository, '0' * 40, proposed))) > max_bytes):
            batches.append(pending)
            pending = []
        pending.append(entry)
        require(len(json_bytes(request_value(repository, '0' * 40, pending))) <= max_bytes,
                f'One tree entry cannot fit in the JSON byte limit: {entry["path"]!r}')
    if pending:
        batches.append(pending)
    return batches


def prepare(args):
    helper_bytes = Path(__file__).read_bytes()
    repo = Repository(args.repo)
    output = args.output_dir.resolve()
    require(output != repo.path and repo.path not in output.parents,
            'All preparation outputs must be outside the repository worktree')
    require(re.fullmatch(r'[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+', args.repository_full_name),
            'Repository name must be owner/name')
    require(1 <= args.max_entries <= MAX_ENTRIES and 1 <= args.max_json_bytes <= MAX_JSON_BYTES,
            'Limits must be positive and no larger than 100 entries / 50,000 JSON bytes')
    output.mkdir(parents=True, exist_ok=False)
    initial = repo.state()
    try:
        base = repo.resolve(args.base)
        target = repo.resolve(args.target)
        known = repo.resolve(args.known_public_commit, commit_only=True)
        base_entries = repo.flat_tree(base['tree_sha'])
        target_entries = repo.flat_tree(target['tree_sha'])
        known_entries = repo.flat_tree(known['tree_sha'], require_index_representation=False)
        base_blobs = {entry['sha'] for entry in base_entries.values() if entry['type'] == 'blob'}
        known_blobs = {entry['sha'] for entry in known_entries.values() if entry['type'] == 'blob'}
        target_blobs = {entry['sha'] for entry in target_entries.values() if entry['type'] == 'blob'}
        missing = sorted(target_blobs - base_blobs - known_blobs)
        require(not missing, f'{len(missing)} target blobs are absent from the known-public/base trees: {missing}')

        removed_paths = sorted(set(base_entries) - set(target_entries))
        upsert_paths = sorted(path for path, value in target_entries.items() if base_entries.get(path) != value)
        changed_paths = sorted(set(removed_paths) | set(upsert_paths))
        forbidden = [path for path in changed_paths if workflow_path(path)]
        require(not forbidden, f'Changes under .github/workflows are forbidden: {forbidden}')
        removals = [{**base_entries[path], 'sha': None} for path in removed_paths]
        upserts = [target_entries[path].copy() for path in upsert_paths]
        phases = [('remove', batch_entries(removals, args.repository_full_name,
                                           args.max_entries, args.max_json_bytes)),
                  ('upsert', batch_entries(upserts, args.repository_full_name,
                                           args.max_entries, args.max_json_bytes))]

        metadata = {
            'base_tree': write_json(output / 'base-tree.json',
                                    {'snapshot': base, 'entries': list(base_entries.values())}),
            'target_tree': write_json(output / 'target-tree.json',
                                      {'snapshot': target, 'entries': list(target_entries.values())}),
            'known_public_tree': write_json(output / 'known-public-tree.json',
                                            {'snapshot': known, 'entries': list(known_entries.values())}),
            'blob_availability': write_json(output / 'blob-availability.json', {
                'target_unique_blob_count': len(target_blobs), 'missing': [],
                'blobs': [{'sha': oid, 'in_base_tree': oid in base_blobs,
                           'in_known_public_commit_tree': oid in known_blobs} for oid in sorted(target_blobs)]}),
        }
        current_entries = base_entries.copy()
        current_tree = base['tree_sha']
        batches = []
        with tempfile.TemporaryDirectory(prefix='private-index-', dir=output) as private_dir:
            private_index = Path(private_dir) / 'index'
            require(str(private_index) != initial['index_path'], 'Private index overlaps the worktree index')
            index_env = {**repo.env, 'GIT_INDEX_FILE': str(private_index)}
            repo.git('read-tree', base['tree_sha'], env=index_env)
            require(repo.git('write-tree', env=index_env).decode().strip() == current_tree,
                    'Private index did not reproduce the exact base tree')
            for phase, phase_batches in phases:
                for entries in phase_batches:
                    number = len(batches) + 1
                    request = request_value(args.repository_full_name, current_tree, entries)
                    encoded = json_bytes(request)
                    require(len(entries) <= args.max_entries and len(encoded) <= args.max_json_bytes,
                            'Internal request bound failure')
                    require(all(set(entry) == {'path', 'mode', 'type', 'sha'} for entry in entries),
                            'Every request entry must use only path/mode/type/sha')
                    updates = []
                    for entry in entries:
                        path = entry['path']
                        if entry['sha'] is None:
                            require(path in current_entries, f'Removal does not exist in its request base: {path}')
                            del current_entries[path]
                            mode, oid = '0', '0' * 40
                        else:
                            require(OID.fullmatch(entry['sha']), 'Non-SHA tree payload')
                            current_entries[path] = entry.copy()
                            mode, oid = entry['mode'], entry['sha']
                        updates.append((mode + ' ' + oid + '\t' + path).encode('utf-8') + b'\0')
                    expected = flat_tree_sha(current_entries)
                    repo.git('update-index', '-z', '--index-info', data=b''.join(updates), env=index_env)
                    native = repo.git('write-tree', env=index_env).decode().strip()
                    require(native == expected, f'Independent/native tree mismatch in batch {number}')
                    request_file = write_bytes(output / f'tree-{number:04d}.request.json', encoded)
                    record = {'batch': number, 'phase': phase, 'base_tree_sha': current_tree,
                              'expected_tree_sha': expected, 'entry_count': len(entries),
                              'request': request_file, 'result_leaf_entry_count': len(current_entries),
                              'independent_tree_encoding_matches_git_write_tree': True,
                              'private_index_sha256': sha256(private_index.read_bytes()),
                              'submission_rule': 'Submit only after prior result matches its expected tree; '
                                                 'require this result tree to equal expected_tree_sha'}
                    expected_file = write_json(output / f'tree-{number:04d}.expected.json', record)
                    batches.append({**record, 'expected_receipt': expected_file})
                    current_tree = expected
            require(current_entries == target_entries, 'Final flat tree entries differ from the target')
            require(current_tree == target['tree_sha'], 'Final expected tree differs from the exact target')
            require(repo.git('write-tree', env=index_env).decode().strip() == target['tree_sha'],
                    'Final native private-index tree differs from the exact target')

        final = repo.state()
        require(final == initial, 'The worktree HEAD, index, or refs changed during preparation; '
                                  'do not use these requests until concurrent changes are reviewed')
        require(Path(__file__).read_bytes() == helper_bytes, 'The running helper source changed during preparation')
        result = {
            'schema_version': 1, 'kind': 'sha_only_github_tree_request_preparation',
            'prepared_at_utc': datetime.now(timezone.utc).isoformat(),
            'repository': str(repo.path), 'repository_full_name': args.repository_full_name,
            'base': base, 'target': target, 'known_public_commit': known,
            'publication_basis': 'Caller-supplied already-fetched public commit and public base; '
                                 'this helper performs no remote check or request',
            'connector_tool': 'mcp__codex_apps__github_create_tree',
            'limits': {'entries_per_request': args.max_entries, 'json_bytes_per_request': args.max_json_bytes},
            'base_leaf_entry_count': len(base_entries), 'target_leaf_entry_count': len(target_entries),
            'removed_path_count': len(removals), 'upserted_path_count': len(upserts),
            'changed_path_count': len(changed_paths), 'changed_paths': changed_paths,
            'target_unique_blob_count': len(target_blobs),
            'all_target_blobs_in_known_public_or_base_tree': True,
            'target_blobs_absent_from_base_but_in_known_public_tree': len(target_blobs - base_blobs),
            'workflow_changes': [], 'all_entry_modes_preserved': True,
            'request_count': len(batches), 'batches': batches,
            'final_expected_tree_sha': current_tree, 'final_expected_tree_equals_exact_target': True,
            'all_intermediate_trees_independently_encoded_and_native_checked': True,
            'root_head_index_refs_unchanged': True, 'root_git_state': state_record(initial),
            'private_index_removed_after_preparation': True,
            'worktree_files_written': [], 'refs_written': [], 'remote_calls_performed': False,
            'local_git_object_note': 'git write-tree may add immutable local tree objects; '
                                     'all index changes use the external temporary index',
            'helper_sha256': sha256(helper_bytes), 'manifests': metadata,
        }
        write_json(output / 'manifest.json', result)
        print(json.dumps({key: result[key] for key in ('base', 'target', 'request_count',
                         'removed_path_count', 'upserted_path_count', 'final_expected_tree_sha',
                         'root_head_index_refs_unchanged')}, indent=2))
        print('Manifest:', output / 'manifest.json')
        return result
    except BaseException as error:
        write_json(output / 'preparation-failure.json', {
            'kind': 'failed_sha_only_tree_request_preparation',
            'observed_at_utc': datetime.now(timezone.utc).isoformat(),
            'error_type': type(error).__name__, 'error': str(error),
            'base_requested': args.base, 'target_requested': args.target,
            'remote_calls_performed': False,
            'instruction': 'Do not submit partial request files without a successful manifest.json',
        })
        raise


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, default=DEFAULT_REPO)
    parser.add_argument('--repository-full-name', default=DEFAULT_REPOSITORY)
    parser.add_argument('--base', required=True, help='Exact public base tree or commit SHA-1')
    parser.add_argument('--target', required=True, help='Exact local target tree or commit SHA-1')
    parser.add_argument('--known-public-commit', required=True,
                        help='Exact already-fetched recovery/upload commit SHA-1')
    parser.add_argument('--output-dir', type=Path, required=True, help='Fresh output directory outside the repository')
    parser.add_argument('--max-entries', type=int, default=MAX_ENTRIES)
    parser.add_argument('--max-json-bytes', type=int, default=MAX_JSON_BYTES)
    prepare(parser.parse_args())


if __name__ == '__main__':
    main()
