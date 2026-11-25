#!/usr/bin/env python3
"""Prepare exact staged Git objects for connector upload; never stage, commit or push.

All commands are offline. `prepare` creates a new snapshot directory. `read`
emits at most 8,000 characters per JSON chunk. The conventional Git object
representation includes the type/length/NUL header; GitHub create_blob instead
requires only the blob body, with encoding='base64' or 'utf-8'.
"""
from __future__ import annotations

import argparse
import base64
from collections import defaultdict
import datetime as dt
import hashlib
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
BASELINE = 'f2510d10c114bcf3d0003b5e2e4e35cb0400167d'
REPOSITORY = 'fly31415926/overfull-lean'


def git(repo: Path, *args: str) -> bytes:
    return subprocess.check_output(['git', '-C', str(repo), *args])


def object_bytes(kind: str, body: bytes) -> bytes:
    return f'{kind} {len(body)}\0'.encode('ascii') + body


def object_sha(kind: str, body: bytes) -> str:
    return hashlib.sha1(object_bytes(kind, body)).hexdigest()


def index_entries(repo: Path) -> tuple[bytes, dict]:
    raw = git(repo, 'ls-files', '--stage', '-z')
    result = {}
    for record in raw.split(b'\0'):
        if not record:
            continue
        fields, name = record.split(b'\t', 1)
        mode, sha, stage = fields.decode('ascii').split()
        if stage != '0':
            raise ValueError('The index has unresolved merge stages.')
        if mode not in ('100644', '100755', '120000'):
            raise ValueError(f'Unsupported index mode {mode}; submodule/sparse entries need review.')
        path = name.decode('utf-8', errors='strict')
        result[path] = {'path': path, 'mode': mode, 'type': 'blob', 'sha': sha}
    return raw, result


def trees_from_entries(entries: dict) -> tuple[str, dict]:
    """Compute ordinary SHA-1 Git trees, including Git's directory sort order."""
    root = {}
    for path, entry in entries.items():
        node = root
        parts = path.split('/')
        if any(p in ('', '.', '..') for p in parts):
            raise ValueError(f'Invalid Git path: {path!r}')
        for part in parts[:-1]:
            node = node.setdefault(part, {})
            if not isinstance(node, dict):
                raise ValueError(f'File/directory conflict: {path!r}')
        if parts[-1] in node:
            raise ValueError(f'Duplicate or conflicting Git path: {path!r}')
        node[parts[-1]] = (entry['mode'], entry['sha'])
    objects = {}

    def walk(node: dict, path: str) -> tuple[str, int]:
        elements, pieces, height = [], [], 0
        ordered = sorted(node, key=lambda n: n.encode('utf-8') +
                         (b'/' if isinstance(node[n], dict) else b''))
        for name in ordered:
            item = node[name]
            if isinstance(item, dict):
                child_path = f'{path}/{name}' if path else name
                sha, child_height = walk(item, child_path)
                mode, kind, raw_mode = '040000', 'tree', '40000'
                height = max(height, child_height + 1)
            else:
                mode, sha = item
                kind, raw_mode = 'blob', mode
            elements.append({'path': name, 'mode': mode, 'type': kind, 'sha': sha})
            pieces.append(raw_mode.encode('ascii') + b' ' + name.encode('utf-8') +
                          b'\0' + bytes.fromhex(sha))
        body = b''.join(pieces)
        sha = object_sha('tree', body)
        obj = objects.setdefault(sha, {'sha': sha, 'type': 'tree', 'size': len(body),
                                      'paths': [], 'height': height,
                                      'tree_elements': elements, 'body': body})
        obj['paths'].append(path)
        return sha, height

    sha, _ = walk(root, '')
    return sha, objects


def write_json(path: Path, value) -> None:
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')


def emit(value) -> None:
    print(json.dumps(value, ensure_ascii=False, separators=(',', ':')))


def load_snapshot(path: str) -> tuple[Path, dict]:
    folder = Path(path).resolve()
    return folder, json.loads((folder / 'manifest.json').read_text(encoding='utf-8'))


def prepare(args) -> None:
    repo = Path(git(HERE, 'rev-parse', '--show-toplevel').decode().strip())
    if git(repo, 'rev-parse', '--show-object-format').strip() != b'sha1':
        raise ValueError('This helper requires a SHA-1 Git repository.')
    out = Path(args.output).resolve()
    if out == HERE or not out.is_relative_to(HERE):
        raise ValueError('Snapshot output must be a new child directory of publication/.')
    if out.exists():
        raise ValueError('Snapshot output already exists; choose a new directory, never overwrite.')
    baseline = git(repo, 'rev-parse', '--verify', args.baseline + '^{commit}').decode().strip()
    baseline_tree = git(repo, 'rev-parse', baseline + '^{tree}').decode().strip()
    old, old_objects = {}, {baseline_tree}
    for record in git(repo, 'ls-tree', '-r', '-t', '-z', baseline_tree).split(b'\0'):
        if not record:
            continue
        fields, name = record.split(b'\t', 1)
        mode, kind, sha = fields.decode('ascii').split()
        old_objects.add(sha)
        if kind != 'tree':
            path = name.decode('utf-8', errors='strict')
            old[path] = {'path': path, 'mode': mode, 'type': kind, 'sha': sha}
    raw_index, entries = index_entries(repo)
    expected_tree, all_trees = trees_from_entries(entries)
    paths_by_sha = defaultdict(list)
    for path, item in entries.items():
        paths_by_sha[item['sha']].append({'path': path, 'mode': item['mode']})
    new_blobs = []
    for sha in sorted(set(paths_by_sha) - old_objects):
        body = git(repo, 'cat-file', 'blob', sha)
        if object_sha('blob', body) != sha:
            raise ValueError(f'Git blob content does not match index SHA {sha}.')
        new_blobs.append({'sha': sha, 'type': 'blob', 'size': len(body),
                          'paths': sorted(paths_by_sha[sha], key=lambda x: x['path']),
                          'body': body})
    new_trees = sorted((o for sha, o in all_trees.items() if sha not in old_objects),
                       key=lambda o: (o['height'], o['sha']))
    changes = []
    for path in sorted(set(old) | set(entries)):
        if old.get(path) == entries.get(path):
            continue
        new = entries.get(path)
        changes.append(dict(new) if new else {**old[path], 'sha': None})
    if index_entries(repo)[0] != raw_index:
        raise ValueError('The staged index changed during preparation; no snapshot was written.')
    out.mkdir()
    (out / 'objects').mkdir()
    for obj in new_blobs + new_trees:
        body = obj.pop('body')
        relative = f"objects/{obj['sha']}.{obj['type']}"
        (out / relative).write_bytes(body)
        obj.update(payload=relative, sha256=hashlib.sha256(body).hexdigest(),
                   base64_characters=4 * ((len(body) + 2) // 3),
                   conventional_git_object_base64_characters=
                   4 * ((len(object_bytes(obj['type'], body)) + 2) // 3))
    manifest = {
        'schema': 1, 'created_utc': dt.datetime.now(dt.timezone.utc).isoformat(),
        'repository_full_name': args.repository, 'local_repository': str(repo),
        'baseline_commit': baseline, 'baseline_tree': baseline_tree,
        'expected_tree': expected_tree,
        'index_entries_sha256': hashlib.sha256(raw_index).hexdigest(),
        'index_path_count': len(entries), 'changed_path_count': len(changes),
        'new_blob_count': len(new_blobs), 'new_tree_count': len(new_trees),
        'new_blob_bytes': sum(o['size'] for o in new_blobs),
        'blobs': new_blobs, 'trees': new_trees,
        'root_tree_request': 'root-tree-request.json',
        'notes': ['Snapshot is of the staged index; unstaged/untracked files are not included.',
                  'New tree objects are listed in child-before-parent dependency order.',
                  'Only blob/tree objects absent from the baseline tree are exported.',
                  'GitHub create_blob takes the body, not conventional Git object bytes.']}
    write_json(out / 'manifest.json', manifest)
    write_json(out / 'index.json', sorted(entries.values(), key=lambda x: x['path']))
    write_json(out / 'root-tree-request.json', {
        'repository_full_name': args.repository, 'base_tree_sha': baseline_tree,
        'tree_elements': changes})
    write_json(out / 'tree-requests.json', [
        {'expected_sha': obj['sha'], 'request': {'repository_full_name': args.repository,
                                               'tree_elements': obj['tree_elements']}}
        for obj in new_trees])
    emit({k: v for k, v in manifest.items() if k not in ('blobs', 'trees', 'notes')})


def read_object(args) -> None:
    folder, manifest = load_snapshot(args.snapshot)
    matches = [o for o in manifest['blobs'] + manifest['trees'] if o['sha'] == args.sha]
    if len(matches) != 1:
        raise ValueError('Object SHA is absent from the prepared snapshot.')
    obj = matches[0]
    body = (folder / obj['payload']).read_bytes()
    if object_sha(obj['type'], body) != obj['sha'] or hashlib.sha256(body).hexdigest() != obj['sha256']:
        raise ValueError('Prepared object bytes no longer match the manifest.')
    key = 'content'
    if args.encoding == 'utf-8':
        text = body.decode('utf-8', errors='strict')
    elif args.encoding == 'base64':
        text = base64.b64encode(body).decode('ascii')
    else:
        key = 'conventional_git_object_base64'
        text = base64.b64encode(object_bytes(obj['type'], body)).decode('ascii')
    if args.offset < 0 or not 1 <= args.limit <= 8000 or args.offset > len(text):
        raise ValueError('Require 0 <= offset <= total and 1 <= limit <= 8000.')
    end = min(args.offset + args.limit, len(text))
    emit({'sha': obj['sha'], 'type': obj['type'], 'byte_size': len(body),
          'encoding': args.encoding, 'offset': args.offset, 'next_offset': end,
          'total_characters': len(text), 'done': end == len(text), key: text[args.offset:end]})


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    subs = parser.add_subparsers(dest='command', required=True)
    p = subs.add_parser('prepare')
    p.add_argument('--baseline', default=BASELINE)
    p.add_argument('--repository', default=REPOSITORY)
    p.add_argument('--output', default=str(HERE / 'upload-data-proof'))
    p = subs.add_parser('read')
    p.add_argument('--snapshot', required=True)
    p.add_argument('--sha', required=True)
    p.add_argument('--encoding', choices=('utf-8', 'base64', 'conventional_git_object_base64'),
                   default='base64')
    p.add_argument('--offset', type=int, default=0)
    p.add_argument('--limit', type=int, default=4000)
    p = subs.add_parser('check-index')
    p.add_argument('--snapshot', required=True)
    p = subs.add_parser('list')
    p.add_argument('--snapshot', required=True)
    p.add_argument('--kind', choices=('blobs', 'trees'), default='blobs')
    p.add_argument('--offset', type=int, default=0)
    p.add_argument('--limit', type=int, default=20)
    args = parser.parse_args()
    if args.command == 'prepare':
        prepare(args)
    elif args.command == 'read':
        read_object(args)
    else:
        _, manifest = load_snapshot(args.snapshot)
        if args.command == 'check-index':
            raw, entries = index_entries(Path(manifest['local_repository']))
            tree, _ = trees_from_entries(entries)
            if (hashlib.sha256(raw).hexdigest() != manifest['index_entries_sha256'] or
                    tree != manifest['expected_tree']):
                raise ValueError('The index differs from the prepared snapshot.')
            emit({'index_unchanged': True, 'expected_tree': tree})
        else:
            if args.offset < 0 or not 1 <= args.limit <= 100:
                raise ValueError('Require offset >= 0 and 1 <= limit <= 100.')
            objects = manifest[args.kind]
            page = objects[args.offset:args.offset + args.limit]
            emit({'kind': args.kind, 'total': len(objects),
                  'next_offset': args.offset + len(page),
                  'objects': [{k: v for k, v in o.items() if k != 'tree_elements'} for o in page]})


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, subprocess.CalledProcessError) as error:
        print(f'Upload preparation failed: {error}', file=sys.stderr)
        raise SystemExit(1)
