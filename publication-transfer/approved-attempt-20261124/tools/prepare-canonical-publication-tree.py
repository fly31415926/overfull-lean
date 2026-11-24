#!/usr/bin/env python3
"""Prepare bounded SHA-only canonical publication trees; never submit them.

Exact base: proof db841575, tree a7e59e83. Only run/publication may change.
--entries accepts a flat entry list, one entry, or {tree_elements:[...]}.
--upload-evidence accepts {operations:[{request_path,response_path,...}]}.
Request/response paths may be absolute or relative to that evidence file;
optional request_sha256/response_sha256 are checked. Responses must be genuine
saved MCP create_blob/create_tree results (optionally wrapped in `response`).
Content-bearing tree uploads must have no base tree. This helper verifies their
returned object identity and uses the exact recorded content for its private
Git object database. It does not assert that proof P is public: confirm that
after the approved import/readback before submitting any generated request.
"""
from __future__ import annotations
import argparse, base64, hashlib, json, os, re, stat, subprocess, tempfile
from datetime import datetime, timezone
from pathlib import Path

PROOF = 'db841575ca2c427e230387c1c95fa74bedb463d6'
PROOF_TREE = 'a7e59e8303f670fab6c95348cd100acd1aaa5899'
BASELINE = '1c9404a454c99fe5c11ba8d774cb9c259f291f20'
RUN = 'verification/runs/20261124T213000Z'
PUBLICATION = RUN + '/publication/'
REPOSITORY = 'fly31415926/overfull-lean'
ORIGINAL = Path('/workspace/scratch/05b9e46fe96b/overfull-lean')
OID = re.compile(r'[0-9a-f]{40}\Z')

def need(ok, message):
    if not ok: raise RuntimeError(message)
def sha(data): return hashlib.sha256(data).hexdigest()
def gitsha(kind, data):
    return hashlib.sha1(kind.encode() + b' ' + str(len(data)).encode() + b'\0' + data).hexdigest()
def encoded(value): return (json.dumps(value, indent=2, ensure_ascii=False) + '\n').encode()
def safe_path(path):
    need(isinstance(path, str) and path and not path.startswith('/') and '\\' not in path
         and all(p not in {'', '.', '..'} for p in path.split('/')), 'Unsafe Git path')
    return path
def tree_sha(entries):
    root = {}
    for path, entry in entries.items():
        parts = safe_path(path).encode().split(b'/'); node = root
        for part in parts[:-1]:
            child = node.setdefault(part, {})
            need(isinstance(child, dict), 'File/directory collision: ' + path); node = child
        need(parts[-1] not in node, 'Duplicate/colliding path: ' + path)
        node[parts[-1]] = (entry['mode'], entry['sha'])
    def walk(node):
        children = []
        for name, value in node.items():
            if isinstance(value, dict): children.append((name + b'/', b'40000', name, walk(value)))
            else: children.append((name, value[0].encode(), name, value[1]))
        data = b''.join(mode + b' ' + name + b'\0' + bytes.fromhex(oid)
                        for _, mode, name, oid in sorted(children, key=lambda e: e[0]))
        return gitsha('tree', data)
    return walk(root)

class Git:
    def __init__(self, repo):
        self.path = repo.resolve(strict=True)
        self.env = {**os.environ, 'GIT_NO_LAZY_FETCH': '1', 'GIT_OPTIONAL_LOCKS': '0'}
        for key in ('GIT_DIR', 'GIT_COMMON_DIR', 'GIT_WORK_TREE', 'GIT_INDEX_FILE',
                    'GIT_OBJECT_DIRECTORY', 'GIT_ALTERNATE_OBJECT_DIRECTORIES'):
            self.env.pop(key, None)
        self.command = ['git', '--no-pager', '-c', 'core.splitIndex=false', '-c', 'core.sparseCheckout=false',
                        '-c', 'core.fsmonitor=false', '-C', str(self.path)]
        need(self.call('rev-parse', '--show-object-format').strip() == b'sha1', 'SHA-1 repository required')
    def call(self, *args): return subprocess.check_output(self.command + list(args), env=self.env)
    def path_for(self, name):
        p = Path(self.call('rev-parse', '--git-path', name).decode().strip())
        return (p if p.is_absolute() else self.path / p).resolve()
    def state(self):
        idx = self.path_for('index')
        return {'head': self.path_for('HEAD').read_bytes(), 'index': idx.read_bytes() if idx.exists() else None,
                'refs': self.call('for-each-ref', '--format=%(refname) %(objectname) %(symref)')}
    def commit(self, oid):
        need(OID.fullmatch(oid), 'Exact commit SHA-1 required')
        data = self.call('cat-file', 'commit', oid)
        need(gitsha('commit', data) == oid, 'Commit identity mismatch')
        headers = data.split(b'\n\n', 1)[0].splitlines()
        need(headers[0].startswith(b'tree '), 'Missing commit tree')
        return headers[0][5:].decode(), [h[7:].decode() for h in headers if h.startswith(b'parent ')]
    def flat(self, tree):
        result = {}
        for item in self.call('ls-tree', '-r', '-z', '--full-tree', tree).split(b'\0'):
            if not item: continue
            meta, path = item.split(b'\t', 1); mode, kind, oid = meta.decode().split()
            name = safe_path(path.decode())
            need(name not in result and OID.fullmatch(oid), 'Invalid tree entry')
            result[name] = {'path': name, 'mode': mode, 'type': kind, 'sha': oid}
        need(tree_sha(result) == tree, 'Flat tree does not reproduce exact Git tree')
        return result

def prepare(args):
    helper = Path(__file__).read_bytes(); repo = Git(args.repo); initial = repo.state()
    output = args.output_dir.resolve()
    for protected in (repo.path, ORIGINAL.resolve()):
        need(output != protected and protected not in output.parents, 'Output must be outside source repositories')
    output.mkdir(parents=True, exist_ok=False)
    artifacts = {}
    def capture(path):
        path = path.resolve(strict=True)
        need(stat.S_ISREG(path.lstat().st_mode), 'Evidence input must be regular')
        data = path.read_bytes()
        need(path not in artifacts or artifacts[path] == data, 'Input changed during preparation')
        artifacts[path] = data; return data
    def write(name, value):
        data = encoded(value)
        with (output / name).open('xb') as f: f.write(data)
        return {'path': str(output / name), 'bytes': len(data), 'sha256': sha(data)}
    try:
        tree, parents = repo.commit(PROOF)
        need(tree == PROOF_TREE and parents == [BASELINE], 'Exact proof/sole-baseline-parent binding failed')
        original = repo.flat(PROOF_TREE)
        def committed(path):
            e = original[path]
            need(e['type'] == 'blob' and e['mode'] in {'100644', '100755'}, 'Frozen file is not regular')
            data = repo.call('cat-file', 'blob', e['sha'])
            need(gitsha('blob', data) == e['sha'], 'Frozen manifest object mismatch')
            return data
        frozen_data = committed(RUN + '/full-01/frozen-inputs.json')
        control_data = committed(RUN + '/full-01/frozen-controls.json')
        frozen, controls = json.loads(frozen_data), json.loads(control_data)
        need(len(frozen) == 855 and len(controls) == 24, 'Unexpected frozen proof inventories')
        need(all(Path(n).name == n for n in controls), 'Unexpected control path')
        available = {e['sha'] for e in original.values() if e['type'] == 'blob'}
        known = []
        for commit in dict.fromkeys(args.known_public_commit):
            t, _ = repo.commit(commit); entries = repo.flat(t)
            ids = {e['sha'] for e in entries.values() if e['type'] == 'blob'}
            available.update(ids); known.append({'commit': commit, 'tree': t, 'unique_blobs': len(ids)})
        payloads, upload_checks = {}, []
        for evidence_path in args.upload_evidence:
            evidence = json.loads(capture(evidence_path))
            operations = evidence['operations']
            need(isinstance(operations, list), 'Upload evidence requires an operations list')
            for op in operations:
                def locate(key):
                    p = Path(op[key]); return p if p.is_absolute() else evidence_path.resolve().parent / p
                request_data, response_data = capture(locate('request_path')), capture(locate('response_path'))
                for key, data in (('request_sha256', request_data), ('response_sha256', response_data)):
                    need(key not in op or op[key] == sha(data), 'Upload evidence digest mismatch: ' + key)
                request, response = json.loads(request_data), json.loads(response_data)
                if 'response' in response: response = response['response']
                need(response.get('isError') is False and not response.get('tool_exception'), 'Upload did not succeed')
                actual = response.get('structuredContent', {}).get('sha')
                need(OID.fullmatch(actual or ''), 'Missing returned upload object SHA')
                need(request['repository_full_name'] == REPOSITORY, 'Upload belongs to another repository')
                created = {}
                if 'tree_elements' in request:
                    need(request.get('base_tree_sha') is None, 'Upload tree evidence must be a standalone temporary tree')
                    flat = {}
                    for e in request['tree_elements']:
                        path = safe_path(e['path'])
                        need(path not in flat and e['type'] == 'blob' and e['mode'] in {'100644', '100755'}, 'Invalid upload tree entry')
                        if 'content' in e:
                            need('sha' not in e and isinstance(e['content'], str), 'Ambiguous tree content')
                            data = e['content'].encode(); oid = gitsha('blob', data); created[oid] = data
                        else:
                            oid = e['sha']; need(oid in available, 'SHA-only upload references an unestablished blob')
                        flat[path] = {'path': path, 'mode': e['mode'], 'type': 'blob', 'sha': oid}
                    need(tree_sha(flat) == actual, 'Returned temporary-tree identity mismatch')
                else:
                    encoding = request.get('encoding', 'utf-8')
                    need(encoding in {'utf-8', 'base64'}, 'Unsupported blob encoding')
                    data = request['content'].encode() if encoding == 'utf-8' else base64.b64decode(request['content'], validate=True)
                    need(gitsha('blob', data) == actual, 'Returned blob identity mismatch'); created[actual] = data
                for oid, data in created.items():
                    need(oid not in payloads or payloads[oid] == data, 'Conflicting uploaded blob content')
                    payloads[oid] = data; available.add(oid)
                upload_checks.append({'request_path': str(locate('request_path')), 'request_sha256': sha(request_data),
                                      'response_path': str(locate('response_path')), 'response_sha256': sha(response_data),
                                      'returned_sha': actual, 'new_content_blob_count': len(created), 'identity_matches': True})
        requested = {}
        for path in args.entries:
            value = json.loads(capture(path))
            if isinstance(value, dict): value = [value] if 'path' in value else value['tree_elements']
            need(isinstance(value, list), 'Entry file must contain a flat list')
            for e in value:
                need(set(e) == {'path', 'mode', 'type', 'sha'}, 'Entries must be SHA-only path/mode/type/sha records')
                name = safe_path(e['path'])
                need(name.startswith(PUBLICATION), 'Change outside the publication directory: ' + name)
                need(e['type'] == 'blob' and e['mode'] in {'100644', '100755'} and OID.fullmatch(e['sha']), 'Only regular blob additions/replacements allowed')
                need(e['sha'] in available, 'Blob lacks public-tree or exact successful-upload evidence: ' + e['sha'])
                need(name not in requested or requested[name] == e, 'Conflicting entries for ' + name)
                requested[name] = e
        target = {**original, **requested}
        outside = lambda values: {n: e for n, e in values.items() if not n.startswith(PUBLICATION)}
        need(outside(target) == outside(original), 'A nonpublication path/mode/blob changed')
        for name in frozen:
            need(name in original and target[name] == original[name], 'A frozen input changed')
        for name in controls:
            path = RUN + '/' + name
            need(path in original and target[path] == original[path], 'A frozen control changed')
        nonpublication_run = {n: e for n, e in original.items() if n.startswith(RUN + '/') and not n.startswith(PUBLICATION)}
        need(all(target[n] == e for n, e in nonpublication_run.items()), 'Nonpublication run evidence changed')
        changes = [requested[n] for n in sorted(requested) if original.get(n) != requested[n]]
        batches, pending = [], []
        def request(base, entries):
            return {'repository_full_name': REPOSITORY, 'base_tree_sha': base, 'tree_elements': entries}
        for e in changes:
            if pending and (len(pending) == 100 or len(encoded(request('0' * 40, pending + [e]))) > 50000):
                batches.append(pending); pending = []
            pending.append(e)
            need(len(encoded(request('0' * 40, pending))) <= 50000, 'Single entry exceeds request bound')
        if pending: batches.append(pending)
        commands, prepared, current, previous = [], [], original.copy(), PROOF_TREE
        with tempfile.TemporaryDirectory(prefix='private-git-', dir=output) as temporary:
            private = Path(temporary); objects = private / 'objects'; objects.mkdir()
            env = {**repo.env, 'GIT_INDEX_FILE': str(private / 'index'), 'GIT_OBJECT_DIRECTORY': str(objects),
                   'GIT_ALTERNATE_OBJECT_DIRECTORIES': str(repo.path_for('objects'))}
            def native(*args, data=None):
                p = subprocess.run(repo.command + list(args), input=data, env=env, capture_output=True)
                commands.append({'argv': repo.command + list(args), 'exit_code': p.returncode,
                                 'stdin_bytes': None if data is None else len(data), 'stdin_sha256': None if data is None else sha(data),
                                 'stdout': p.stdout.decode(), 'stderr': p.stderr.decode()})
                need(p.returncode == 0, 'Native private-index operation failed; logs retained')
                return p.stdout
            native('read-tree', PROOF_TREE)
            needed = {e['sha'] for e in changes}
            for oid, data in payloads.items():
                if oid in needed: need(native('hash-object', '-w', '--stdin', data=data).decode().strip() == oid, 'Staged upload identity mismatch')
            for number, batch in enumerate(batches, 1):
                req = request(previous, batch)
                for e in batch: current[e['path']] = e
                expected = tree_sha(current)
                data = b''.join((e['mode'] + ' ' + e['sha'] + '\t' + e['path']).encode() + b'\0' for e in batch)
                native('update-index', '-z', '--index-info', data=data)
                need(native('write-tree').decode().strip() == expected, 'Native/independent expected-tree mismatch')
                receipt = write(f'tree-{number:04d}.request.json', req)
                prepared.append({'number': number, 'base_tree_sha': previous, 'expected_tree_sha': expected,
                                 'entry_count': len(batch), 'request': receipt, 'native_independent_match': True})
                previous = expected
            need(current == target and previous == tree_sha(target), 'Final canonical tree mismatch')
        need(repo.state() == initial, 'Source repository HEAD/index/refs changed during preparation')
        need(all(p.read_bytes() == data for p, data in artifacts.items()), 'An input/evidence file changed')
        need(Path(__file__).read_bytes() == helper, 'Helper changed during preparation')
        delta = write('publication-delta.json', {'entries': changes})
        native_receipt = write('native-commands.json', {'commands': commands})
        result = {'schema_version': 1, 'kind': 'canonical_publication_receipt_tree_preparation', 'status': 'prepared_not_submitted',
            'prepared_at_utc': datetime.now(timezone.utc).isoformat(), 'required_commit_parent': PROOF, 'base_tree': PROOF_TREE,
            'publication_prefix': PUBLICATION, 'known_public_commits': known, 'upload_checks': upload_checks,
            'requested_entry_count': len(requested), 'changed_entry_count': len(changes),
            'added_paths': sum(e['path'] not in original for e in changes),
            'replaced_publication_paths': [e['path'] for e in changes if e['path'] in original],
            'request_count': len(prepared), 'requests': prepared, 'final_expected_tree_sha': previous,
            'final_leaf_entry_count': len(target), 'all_deltas_confined_to_publication': True,
            'frozen_input_count': 855, 'frozen_control_count': 24, 'all_frozen_paths_modes_blob_ids_unchanged': True,
            'frozen_input_manifest_sha256': sha(frozen_data), 'frozen_control_manifest_sha256': sha(control_data),
            'nonpublication_run_file_count': len(nonpublication_run), 'all_nonpublication_run_paths_modes_blob_ids_unchanged': True,
            'all_other_nonpublication_tree_entries_unchanged': True, 'source_head_index_refs_unchanged': True,
            'source_object_store_written': False, 'network_calls_performed': False, 'commits_or_refs_created': False,
            'helper_sha256': sha(helper), 'delta': delta, 'native_receipt': native_receipt,
            'input_artifacts': [{'path': str(p), 'bytes': len(d), 'sha256': sha(d)} for p, d in artifacts.items()],
            'submission_requirements': ['Confirm exact proof P/tree is public after the approved import/readback.',
                'Submit requests sequentially and require every returned tree to equal expected_tree_sha.',
                'The canonical receipt commit must use sole parent P and the final expected tree.',
                'This helper neither creates that commit nor updates any ref.']}
        write('manifest.json', result)
        print(json.dumps({k: result[k] for k in ('status', 'required_commit_parent', 'request_count', 'changed_entry_count',
              'final_expected_tree_sha', 'frozen_input_count', 'frozen_control_count', 'nonpublication_run_file_count')}, indent=2))
        print('Manifest:', output / 'manifest.json')
        return result
    except BaseException as error:
        if 'commands' in locals() and not (output / 'native-commands.json').exists():
            write('native-commands.json', {'commands': commands})
        write('preparation-failure.json', {'status': 'failed', 'error_type': type(error).__name__, 'error': str(error),
              'network_calls_performed': False, 'instruction': 'Do not submit partial request files.'})
        raise

if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo', type=Path, required=True, help='Read-only local worktree or bare repository with fetched objects')
    p.add_argument('--entries', type=Path, action='append', required=True)
    p.add_argument('--known-public-commit', action='append', default=[])
    p.add_argument('--upload-evidence', type=Path, action='append', default=[])
    p.add_argument('--output-dir', type=Path, required=True)
    prepare(p.parse_args())
