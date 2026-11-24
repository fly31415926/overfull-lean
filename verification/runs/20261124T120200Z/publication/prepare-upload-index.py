#!/usr/bin/env python3
"""Check publication inclusions and compute expected hashes for every upload tree."""
import hashlib
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
from prepare import empty_directories, object_sha, tree_from_leaves

PUB = Path(__file__).resolve().parent
RUN = PUB.parent
ROOT = PUB.parents[3]
prepared = Path(sys.argv[1]).resolve()


def read(name):
    return json.loads((prepared / name).read_text())


manifest = read('manifest.json')
baseline = read('baseline-tree-inventory.json')['entries']
target = read('target-tree-inventory.json')['entries']
target_leaves = {e['path']: e for e in target if e['type'] != 'tree'}
required = {}
frozen = json.loads((RUN / 'full-01/frozen-inputs.json').read_text())
for name, digest in frozen.items():
    data = (RUN / 'full-01/input' / name).read_bytes()
    assert hashlib.sha256(data).hexdigest() == digest, name
    required[name] = data
for folder in ['development', 'setup', 'full-01']:
    for path in sorted((RUN / folder).rglob('*')):
        if path.is_file() and '__pycache__' not in path.parts:
            required[path.relative_to(ROOT).as_posix()] = path.read_bytes()
for name, data in required.items():
    assert name in target_leaves, f'Missing evidence from target tree: {name}'
    assert target_leaves[name]['sha'] == object_sha('blob', data), name

content_batches = []
for batch in manifest['content_batches']:
    payload = read(batch['file'])
    leaves = []
    for entry in payload['tree_elements']:
        digest = object_sha('blob', entry['content'].encode('utf-8'))
        assert entry['path'] == 'blob/' + digest
        leaves.append({k: v for k, v in entry.items() if k != 'content'} | {'sha': digest})
    content_batches.append(batch | {'expected_tree_sha': tree_from_leaves(leaves, set())})

state = {e['path']: e for e in baseline if e['type'] != 'tree'}
empty = empty_directories(baseline)
final_batches = []
for batch in manifest['final_tree_batches']:
    payload = read(batch['file'])
    for entry in payload['tree_elements']:
        assert entry.get('sha') is not None, 'This continuation permits no deletion'
        assert entry['type'] == 'blob', 'This continuation updates only file leaves'
        state[entry['path']] = entry
    expected = tree_from_leaves(list(state.values()), empty)
    final_batches.append(batch | {'expected_tree_sha': expected})
assert tree_from_leaves(list(state.values()), empty) == manifest['target_tree_sha']

index = {
    'schema_version': 1,
    'target_tree_sha': manifest['target_tree_sha'],
    'baseline_tree_sha': manifest['baseline_tree_sha'],
    'manifest_sha256': hashlib.sha256((prepared / 'manifest.json').read_bytes()).hexdigest(),
    'counts': manifest['counts'],
    'frozen_input_count': len(frozen),
    'required_source_and_evidence_files': len(required),
    'all_required_bytes_in_target_tree': True,
    'content_batches': content_batches,
    'chunked_blobs': [
        {k: blob[k] for k in ['sha', 'size_bytes', 'sha256', 'encoding', 'chunks']}
        for blob in manifest['new_blobs'] if 'chunks' in blob
    ],
    'final_tree_batches': final_batches,
}
(prepared / 'upload-index.json').write_text(json.dumps(index, indent=2) + '\n')
print(json.dumps({k: v for k, v in index.items()
                  if k not in ['content_batches', 'chunked_blobs', 'final_tree_batches']}, indent=2))
