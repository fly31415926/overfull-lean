#!/usr/bin/env python3
"""Validate the completed frozen run and compute exact publication upload hashes.

Usage: python3 prepare-upload-index.py /absolute/fresh-transport-directory
       [--transport-baseline-tree <explicit-40-hex-tree-SHA>]
No Git or remote writes occur. The sole output is a new upload-index.json in
that transport directory; an existing index is never overwritten.
"""
import argparse
import hashlib
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
from prepare import (BASELINE_COMMIT, DEFAULT_BASELINE_TREE, EXPECTED_FROZEN_INPUTS,
                     MAX_FINAL_TREE_ENTRIES, SHA1, empty_directories, object_sha,
                     tree_from_leaves)

PUB = Path(__file__).resolve().parent
RUN = PUB.parent
ROOT = RUN.parents[2]


def require(value, message):
    if not value:
        raise RuntimeError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('prepared', type=Path, help='Fresh external transport directory from prepare.py')
    ap.add_argument('--transport-baseline-tree', default=DEFAULT_BASELINE_TREE,
                    help='Exact transport base tree; full-verification baseline remains pinned')
    args = ap.parse_args()
    require(SHA1.fullmatch(args.transport_baseline_tree), 'Transport baseline must be a full 40-hex tree SHA')
    transport_baseline = args.transport_baseline_tree.lower()
    prepared = args.prepared.resolve(strict=True)
    destination = prepared / 'upload-index.json'
    require(not destination.exists(), 'Refusing to overwrite an existing upload index')
    require(prepared != ROOT and ROOT not in prepared.parents, 'Transport directory must be outside the repository')

    def read(name):
        return json.loads((prepared / name).read_bytes())

    manifest = read('manifest.json')
    require(manifest['baseline_tree_sha'] == transport_baseline, 'Unexpected transport baseline tree')
    if transport_baseline == DEFAULT_BASELINE_TREE:
        require(manifest['baseline_commit_reference'] == BASELINE_COMMIT, 'Unexpected proof-transfer baseline commit')
    else:
        require(manifest['baseline_commit_reference'] is None, 'Nondefault transport must not claim the continuation baseline commit')
    require(1 <= manifest['final_tree_entry_limit'] <= MAX_FINAL_TREE_ENTRIES, 'Invalid final-tree entry limit')
    baseline_inventory, target_inventory = read('baseline-tree-inventory.json'), read('target-tree-inventory.json')
    baseline, target = baseline_inventory['entries'], target_inventory['entries']
    require(baseline_inventory['tree_sha'] == manifest['baseline_tree_sha'], 'Baseline inventory header mismatch')
    require(target_inventory['tree_sha'] == manifest['target_tree_sha'], 'Target inventory header mismatch')
    target_leaves = {e['path']: e for e in target if e['type'] != 'tree'}
    require(tree_from_leaves(list(target_leaves.values()), empty_directories(target)) == manifest['target_tree_sha'],
            'Target inventory does not reconstruct its tree')
    require(tree_from_leaves([e for e in baseline if e['type'] != 'tree'], empty_directories(baseline))
            == transport_baseline, 'Transport baseline inventory does not reconstruct its tree')

    full = RUN / 'full-01'
    frozen = json.loads((full / 'frozen-inputs.json').read_bytes())
    controls = json.loads((full / 'frozen-controls.json').read_bytes())
    terminal_bytes = (full / 'terminal.json').read_bytes()
    terminal = json.loads(terminal_bytes)
    require(len(frozen) == EXPECTED_FROZEN_INPUTS and controls, 'Unexpected frozen-input inventory or empty controls')
    require(terminal_bytes == (full / 'command.json').read_bytes(), 'Command and terminal receipts differ')
    require(terminal['baseline_commit'] == BASELINE_COMMIT and terminal['baseline_tree'] == DEFAULT_BASELINE_TREE,
            'Terminal receipt has an unexpected baseline')
    require(terminal['frozen_input_count'] == len(frozen) and terminal['control_sha256'] == controls,
            'Terminal inventory differs from frozen manifests')
    require(terminal['status'] == 'passed' and terminal['exit_code'] == 0 and terminal['wrapper_exit_code'] == 0
            and terminal['preflight_passed'] is True and terminal['verifier_launched'] is True
            and terminal['inputs_unchanged'] is True and terminal['controls_unchanged'] is True
            and terminal['wrapper_errors'] == [] and terminal['missing_principal_outputs'] == [],
            'The complete frozen verifier has not passed')
    require(sha((full / 'output.log').read_bytes()) == terminal['output_sha256'], 'Full-run output log changed')
    outputs = terminal['outputs']
    output_paths = {entry['path'] for entry in outputs}
    require(len(output_paths) == len(outputs) and outputs, 'Duplicate or empty output inventory')
    scope = json.loads((RUN / 'verification-scope.json').read_bytes())
    require({'verification/results.json', 'verification/build.log', 'verification/axioms.log',
             scope['declaration_map']} <= output_paths, 'Principal verifier output is missing')
    artifacts = full / 'artifacts'
    require({p.relative_to(artifacts).as_posix() for p in artifacts.rglob('*') if p.is_file()} == output_paths,
            'Archived output inventory differs from the terminal receipt')

    required = {}
    for name, digest in frozen.items():
        data = (ROOT / name).read_bytes()
        require(sha(data) == digest and (full / 'input' / name).read_bytes() == data, 'Frozen source changed: ' + name)
        required[name] = data
    for name, digest in controls.items():
        data = (RUN / name).read_bytes()
        require(sha(data) == digest and (full / 'control' / name).read_bytes() == data, 'Frozen control changed: ' + name)
    for entry in outputs:
        data = (ROOT / entry['path']).read_bytes()
        require(sha(data) == entry['sha256'] and len(data) == entry['bytes']
                and (artifacts / entry['path']).read_bytes() == data, 'Verifier output changed: ' + entry['path'])
        required[entry['path']] = data
    for path in sorted(RUN.rglob('*')):
        if (path.is_file() and PUB not in path.parents and '__pycache__' not in path.parts
                and path != RUN / 'build.lock'):
            required[path.relative_to(ROOT).as_posix()] = path.read_bytes()
    for path in sorted(PUB.glob('*.py')):
        required[path.relative_to(ROOT).as_posix()] = path.read_bytes()
    for name, data in required.items():
        require(name in target_leaves, 'Missing source or evidence from target tree: ' + name)
        require(target_leaves[name]['type'] == 'blob' and target_leaves[name]['sha'] == object_sha('blob', data),
                'Target source/evidence byte mismatch: ' + name)

    def batch_payload(batch):
        data = (prepared / batch['file']).read_bytes()
        payload = json.loads(data)
        require(sha(data) == batch['sha256'] and len(data) == batch['size_bytes']
                and len(payload['tree_elements']) == batch['entries'], 'Batch metadata mismatch: ' + batch['file'])
        return payload

    content_batches = []
    for batch in manifest['content_batches']:
        payload = batch_payload(batch)
        leaves = []
        for entry in payload['tree_elements']:
            digest = object_sha('blob', entry['content'].encode('utf-8'))
            require(entry['path'] == 'blob/' + digest, 'Content batch path/hash mismatch')
            leaves.append({k: v for k, v in entry.items() if k != 'content'} | {'sha': digest})
        content_batches.append(batch | {'expected_tree_sha': tree_from_leaves(leaves, set())})

    state = {e['path']: e for e in baseline if e['type'] != 'tree'}
    empty = empty_directories(baseline)
    final_batches = []
    for batch in manifest['final_tree_batches']:
        payload = batch_payload(batch)
        require(1 <= batch['entries'] <= manifest['final_tree_entry_limit'], 'Oversized final-tree batch')
        for entry in payload['tree_elements']:
            require(entry.get('sha') is not None, 'This continuation permits no deletion')
            require(entry['type'] == 'blob', 'This continuation updates only file leaves')
            state[entry['path']] = entry
        expected = tree_from_leaves(list(state.values()), empty)
        final_batches.append(batch | {'expected_tree_sha': expected})
    require(tree_from_leaves(list(state.values()), empty) == manifest['target_tree_sha'], 'Final tree mismatch')

    index = {
        'schema_version': 1,
        'target_tree_sha': manifest['target_tree_sha'], 'baseline_tree_sha': transport_baseline,
        'transport_baseline_tree_sha': transport_baseline,
        'transport_baseline_commit_reference': manifest['baseline_commit_reference'],
        'continuation_baseline_commit': BASELINE_COMMIT, 'continuation_baseline_tree': DEFAULT_BASELINE_TREE,
        'manifest_sha256': sha((prepared / 'manifest.json').read_bytes()), 'counts': manifest['counts'],
        'frozen_input_count': len(frozen), 'frozen_control_count': len(controls),
        'archived_output_count': len(outputs), 'final_tree_entry_limit': manifest['final_tree_entry_limit'],
        'required_source_and_evidence_files': len(required), 'all_required_bytes_in_target_tree': True,
        'full_verifier_and_wrapper_passed': True, 'content_batches': content_batches,
        'chunked_blobs': [{k: blob[k] for k in ['sha', 'size_bytes', 'sha256', 'encoding', 'chunks']}
                          for blob in manifest['new_blobs'] if 'chunks' in blob],
        'final_tree_batches': final_batches,
    }
    destination.open('x').write(json.dumps(index, indent=2) + '\n')
    print(json.dumps({k: v for k, v in index.items()
                      if k not in ['content_batches', 'chunked_blobs', 'final_tree_batches']}, indent=2))


if __name__ == '__main__':
    main()
