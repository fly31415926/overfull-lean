#!/usr/bin/env python3
"""Prepare a verified incremental proof bundle and bounded ASCII archive parts.

No network calls or project worktree/index/ref mutations are performed. The
exact committed full-01 evidence must pass before a bundle can be created.
"""
from __future__ import annotations
import argparse
import base64
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time

BASELINE = '1c9404a454c99fe5c11ba8d774cb9c259f291f20'
BASELINE_TREE = '087e26b5f004af1f9423a6f2b137d805f5991f1a'
RUN = 'verification/runs/20261124T213000Z'
DEFAULT_REPO = Path('/workspace/scratch/05b9e46fe96b/overfull-lean')
PART_CHARS = 45000

def require(value, message):
    if not value:
        raise RuntimeError(message)

def digest(data):
    return hashlib.sha256(data).hexdigest()

def gitsha(kind, data):
    return hashlib.sha1(kind.encode() + b' ' + str(len(data)).encode() + b'\0' + data).hexdigest()

def encoded(value):
    return (json.dumps(value, indent=2, ensure_ascii=False) + '\n').encode()

def write_json(path, value):
    with path.open('xb') as stream:
        stream.write(encoded(value))

def metadata(path, base=None):
    data = path.read_bytes()
    return {'path': str(path if base is None else path.relative_to(base)),
            'bytes': len(data), 'sha256': digest(data)}

class Repository:
    def __init__(self, path):
        self.path = path.resolve(strict=True)
        self.env = {**os.environ, 'GIT_NO_LAZY_FETCH': '1', 'GIT_OPTIONAL_LOCKS': '0'}
        self.env.pop('GIT_INDEX_FILE', None)
        self.command = ['git', '--no-pager', '-C', str(self.path)]
        require(Path(self.git('rev-parse', '--show-toplevel').decode().strip()).resolve() == self.path,
                'Repository argument must name the exact worktree root')
        require(self.git('rev-parse', '--show-object-format').strip() == b'sha1', 'SHA-1 repository required')

    def git(self, *args):
        return subprocess.check_output(self.command + list(args), env=self.env)

    def git_path(self, name):
        value = Path(self.git('rev-parse', '--git-path', name).decode().strip())
        return (value if value.is_absolute() else self.path / value).resolve()

    def state(self):
        index = self.git_path('index')
        return {'head_commit': self.git('rev-parse', '--verify', 'HEAD').decode().strip(),
                'head_bytes': self.git_path('HEAD').read_bytes(),
                'index_bytes': index.read_bytes() if index.exists() else None,
                'refs_bytes': self.git('for-each-ref', '--format=%(refname) %(objectname) %(symref)')}

def inspect_committed_verification(repo, commit):
    require(re.fullmatch(r'[0-9a-f]{40}', commit), 'Exact lowercase commit SHA-1 required')
    raw = repo.git('cat-file', 'commit', commit)
    require(gitsha('commit', raw) == commit, 'Commit object identity mismatch')
    headers = raw.split(b'\n\n', 1)[0].splitlines()
    parents = [line[7:].decode() for line in headers if line.startswith(b'parent ')]
    require(parents == [BASELINE], 'Verified snapshot must have the sole pinned baseline parent')
    require(headers[0].startswith(b'tree '), 'Missing commit tree')
    tree = headers[0][5:].decode()
    entries = {}
    for item in repo.git('ls-tree', '-r', '-z', '--full-tree', tree).split(b'\0'):
        if item:
            meta, path = item.split(b'\t', 1)
            entries[path.decode()] = tuple(value.decode() for value in meta.split())
    reader = subprocess.Popen(repo.command + ['cat-file', '--batch'], env=repo.env,
                              stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    cache = {}
    def read(path):
        mode, kind, oid = entries[path]
        require(kind == 'blob' and mode in {'100644', '100755'}, 'Evidence must be a regular blob: ' + path)
        if oid not in cache:
            reader.stdin.write((oid + '\n').encode()); reader.stdin.flush()
            header = reader.stdout.readline().decode().strip().split()
            require(len(header) == 3 and header[:2] == [oid, 'blob'], 'Invalid batch object header')
            data = reader.stdout.read(int(header[2]))
            require(len(data) == int(header[2]) and reader.stdout.read(1) == b'\n', 'Truncated evidence blob')
            require(gitsha('blob', data) == oid, 'Evidence Git SHA mismatch')
            cache[oid] = data
        return cache[oid]
    def parsed(path):
        return json.loads(read(path))
    def record(path):
        data = read(path)
        return {'path': path, 'git_blob_sha1': entries[path][2], 'sha256': digest(data), 'bytes': len(data)}
    try:
        full = RUN + '/full-01'
        terminal_path, preservation_path = full + '/terminal.json', RUN + '/preservation.json'
        terminal, preservation = parsed(terminal_path), parsed(preservation_path)
        frozen, controls = parsed(full + '/frozen-inputs.json'), parsed(full + '/frozen-controls.json')
        require(frozen and controls, 'Empty frozen evidence inventory')
        require(terminal['command'] == ['python3', 'scripts/verify.py'] and terminal['attempt'] == 'full-01'
                and terminal['baseline_commit'] == BASELINE and terminal['baseline_tree'] == BASELINE_TREE
                and terminal['status'] == 'passed' and terminal['exit_code'] == 0
                and terminal['wrapper_exit_code'] == 0 and terminal['preflight_passed'] is True
                and terminal['verifier_launched'] is True and terminal['inputs_unchanged'] is True
                and terminal['controls_unchanged'] is True and terminal['changed_inputs'] == []
                and terminal['changed_controls'] == [] and terminal['wrapper_errors'] == []
                and terminal['missing_principal_outputs'] == [], 'Committed full-01 did not genuinely pass')
        require(read(terminal_path) == read(full + '/command.json'), 'Committed command/terminal receipts differ')
        require(digest(read(full + '/output.log')) == terminal['output_sha256'], 'Full output log digest mismatch')
        require(terminal['frozen_input_count'] == len(frozen) and terminal['control_sha256'] == controls,
                'Committed frozen inventories differ from terminal receipt')
        fixed = {'Overfull.lean', 'Audit.lean', 'lean-toolchain', 'lakefile.toml', 'lake-manifest.json',
                 'README.md', '.github/workflows/lean.yml', 'THIRD_PARTY_NOTICES.txt',
                 'CIRCULATION_NOTICE.txt', 'LICENSE_BMATCHING.txt'}
        def verifier_input(name):
            p = Path(name)
            return (name in fixed or (name.startswith('Overfull/') and p.suffix == '.lean')
                    or (len(p.parts) == 2 and p.parts[0] == 'scripts' and p.suffix == '.py')
                    or (len(p.parts) == 2 and p.parts[0] == 'docs' and p.suffix in {'.json', '.md'})
                    or (len(p.parts) == 2 and p.parts[0] == 'patches' and p.suffix == '.patch'))
        require({name for name in entries if verifier_input(name)} == set(frozen), 'Frozen input path set mismatch')
        for name, expected in frozen.items():
            require(digest(read(name)) == expected and digest(read(full + '/input/' + name)) == expected,
                    'Committed live/frozen input differs: ' + name)
        for name, expected in controls.items():
            require(Path(name).name == name, 'Unexpected nonflat control path')
            require(digest(read(RUN + '/' + name)) == expected
                    and digest(read(full + '/control/' + name)) == expected, 'Committed control differs: ' + name)
        outputs = {item['path']: item for item in terminal['outputs']}
        require(outputs and len(outputs) == len(terminal['outputs']), 'Empty or duplicate output inventory')
        scope = parsed(RUN + '/verification-scope.json')
        require({'verification/results.json', 'verification/build.log', 'verification/axioms.log',
                 scope['declaration_map']} <= set(outputs), 'Principal full-verification output missing')
        for path, item in outputs.items():
            for name in (path, full + '/artifacts/' + path):
                data = read(name)
                require(len(data) == item['bytes'] and digest(data) == item['sha256'], 'Committed output differs: ' + name)
        prefix = full + '/artifacts/'
        require({name[len(prefix):] for name in entries if name.startswith(prefix)} == set(outputs),
                'Committed output archive path set differs')
        coverage = preservation['coverage']
        require(preservation['status'] == 'passed' and preservation['full_verifier_attempt'] == 'full-01'
                and preservation['actual_full_verifier_exit'] == 0 and preservation['baseline_commit'] == BASELINE
                and preservation['baseline_tree'] == BASELINE_TREE
                and preservation['genuine_command_receipt_sha256'] == digest(read(terminal_path))
                and preservation['frozen_input_count'] == len(frozen)
                and preservation['previous_audited_declarations'] == 14627
                and preservation['previous_completed_result_mappings'] == 2777
                and preservation['previous_frozen_inputs'] == 826
                and preservation['all_previous_declarations_owners_axiom_sets_preserved'] is True
                and preservation['all_previous_completed_result_mappings_preserved'] is True
                and preservation['all_previous_source_declaration_maps_preserved'] is True
                and coverage['numbered_assertions'] == 69 and coverage['previous_complete'] == 49
                and coverage['current_complete'] == 51 and coverage['promoted_assertions'] == ['4.16', '4.17']
                and coverage['all_69_statement_identities_identical'] is True
                and coverage['all_unpromoted_records_identical'] is True
                and coverage['main_theorem_verified'] is False, 'Committed preservation/scope did not pass')
        results = parsed('verification/results.json')
        require(results['lean_build_passed'] is True and results['axiom_audit_passed'] is True
                and results['fully_verified_numbered_assertion_count'] == 51
                and results['main_theorem_verified'] is False
                and {**results['source_sha256'], **results['verification_input_sha256']} == frozen
                and results['verified_declaration_count'] == preservation['audited_declarations']
                and len(results['verified_declarations']) == preservation['audited_declarations']
                and preservation['new_audited_declarations'] == preservation['audited_declarations'] - 14627,
                'Committed verifier report differs from preservation and frozen evidence')
        counts = {'tracked_files': len(entries), 'frozen_inputs': len(frozen), 'frozen_controls': len(controls),
                  'recorded_verifier_outputs': len(outputs), 'audited_declarations': preservation['audited_declarations'],
                  'new_audited_declarations': preservation['new_audited_declarations'],
                  'completed_result_mappings': len(results['completed_results']),
                  'public_theorem_count': preservation['public_theorem_count'],
                  'complete_numbered_assertions': 51, 'numbered_assertions': 69, 'main_theorem_verified': False}
        evidence = {'terminal': record(terminal_path), 'preservation': record(preservation_path),
                    'results': record('verification/results.json'), 'full_output_log': record(full + '/output.log'),
                    'frozen_inputs': record(full + '/frozen-inputs.json'),
                    'frozen_controls': record(full + '/frozen-controls.json'), 'counts': counts,
                    'full_verifier_exit_code': 0, 'full_wrapper_exit_code': 0,
                    'all_committed_frozen_inputs_controls_outputs_checked': True,
                    'all_commit_evidence_blob_ids_checked': True, 'source': 'Exact committed Git objects'}
        return tree, evidence
    finally:
        reader.stdin.close()
        reader.stdout.close()
        require(reader.wait() == 0, 'git cat-file failed')

def prepare(args):
    helper_bytes = Path(__file__).read_bytes()
    restore_source = Path(__file__).with_name('restore-bundle.py')
    restore_bytes = restore_source.read_bytes()
    repo = Repository(args.repo)
    output = args.output_dir.resolve()
    require(output != repo.path and repo.path not in output.parents, 'Archive outputs must stay outside repository')
    output.mkdir(parents=True, exist_ok=False)
    initial = repo.state()
    commands = []
    def execute(label, argv, cwd, env):
        folder = output / label
        folder.mkdir()
        started = datetime.now(timezone.utc).isoformat()
        start = time.monotonic()
        request = {'kind': 'genuine_native_archive_command', 'argv': argv, 'cwd': str(cwd),
                   'started_at_utc': started, 'status': 'running', 'exit_code': None}
        write_json(folder / 'started.json', request)
        with (folder / 'stdout.log').open('xb') as stdout, (folder / 'stderr.log').open('xb') as stderr:
            result = subprocess.run(argv, cwd=cwd, env=env, stdout=stdout, stderr=stderr)
        terminal = {**request, 'status': 'passed' if result.returncode == 0 else 'failed',
                    'exit_code': result.returncode, 'finished_at_utc': datetime.now(timezone.utc).isoformat(),
                    'duration_seconds': time.monotonic() - start,
                    'stdout': metadata(folder / 'stdout.log', output),
                    'stderr': metadata(folder / 'stderr.log', output)}
        write_json(folder / 'terminal.json', terminal)
        commands.append(metadata(folder / 'terminal.json', output))
        require(result.returncode == 0, f'Native command failed ({label}); genuine logs retained')
        return (folder / 'stdout.log').read_bytes()
    try:
        tree, evidence = inspect_committed_verification(repo, args.commit)
        write_json(output / 'committed-verification.json', evidence)
        bundle = output / ('verified-' + args.commit + '.bundle')
        method = 'existing exact source HEAD'
        with tempfile.TemporaryDirectory(prefix='isolated-bundle-', dir=output) as temporary:
            if initial['head_commit'] == args.commit:
                bundle_command, bundle_env = repo.command, repo.env
            else:
                method = 'isolated external bare repository with its own detached HEAD'
                private = Path(temporary) / 'bundle.git'
                private_env = dict(repo.env)
                for name in ('GIT_DIR', 'GIT_WORK_TREE', 'GIT_COMMON_DIR', 'GIT_INDEX_FILE'):
                    private_env.pop(name, None)
                execute('native-isolated-init', ['git', 'init', '--quiet', '--bare', '--object-format=sha1', str(private)],
                        output, private_env)
                objects = str(repo.git_path('objects'))
                require('\n' not in objects, 'Unexpected newline in object database path')
                (private / 'objects/info/alternates').write_text(objects + '\n')
                (private / 'HEAD').write_text(args.commit + '\n')
                bundle_command, bundle_env = ['git', '--git-dir', str(private)], private_env
            execute('native-bundle-create', bundle_command + ['bundle', 'create', '--version=2', str(bundle),
                                                              'HEAD', '^' + BASELINE], output, bundle_env)
        execute('native-bundle-verify', repo.command + ['bundle', 'verify', str(bundle)], repo.path, repo.env)
        heads = execute('native-bundle-heads', repo.command + ['bundle', 'list-heads', str(bundle)], repo.path, repo.env)
        require(heads.decode().splitlines() == [args.commit + ' HEAD'], 'Bundle head differs from exact commit')
        prerequisites = []
        with bundle.open('rb') as stream:
            require(stream.readline() == b'# v2 git bundle\n', 'Unexpected bundle format')
            while True:
                line = stream.readline()
                require(line, 'Truncated bundle header')
                if line == b'\n':
                    break
                if line.startswith(b'-'):
                    prerequisites.append(line[1:41].decode())
        require(prerequisites == [BASELINE], 'Bundle must have exactly the pinned baseline prerequisite')
        bundle_digest, bundle_size, parts = hashlib.sha256(), 0, []
        with bundle.open('rb') as stream:
            while chunk := stream.read(PART_CHARS // 4 * 3):
                bundle_digest.update(chunk); bundle_size += len(chunk)
                data = base64.b64encode(chunk)
                require(len(data) <= PART_CHARS, 'Internal part size failure')
                number = len(parts) + 1
                name = f'bundle.part-{number:06d}.b64'
                with (output / name).open('xb') as part:
                    part.write(data)
                parts.append({'number': number, 'path': name, 'bytes': len(data),
                              'sha256': digest(data), 'git_blob_sha1': gitsha('blob', data)})
        require(bundle_size == bundle.stat().st_size and parts, 'Incomplete or empty bundle split')
        restore = output / 'restore-bundle.py'
        with restore.open('xb') as stream:
            stream.write(restore_bytes)
        manifest = {'schema_version': 1, 'kind': 'incremental_git_bundle_archive',
                    'prepared_at_utc': datetime.now(timezone.utc).isoformat(),
                    'commit': args.commit, 'tree': tree, 'parent': BASELINE, 'prerequisite_commit': BASELINE,
                    'bundle': {'path': bundle.name, 'format': 'git bundle v2', 'bytes': bundle_size,
                               'sha256': bundle_digest.hexdigest(), 'heads': [{'commit': args.commit, 'ref': 'HEAD'}]},
                    'part_count': len(parts), 'part_character_limit': PART_CHARS, 'parts': parts,
                    'encoded_bytes': sum(part['bytes'] for part in parts),
                    'restore_script': metadata(restore, output), 'verification': evidence,
                    'archive_method': method, 'preparation_helper_sha256': digest(helper_bytes),
                    'restore_instructions': ['Obtain a repository containing prerequisite_commit.',
                       'Place manifest.json, restore-bundle.py, and all listed parts in one directory.',
                       'Run python3 restore-bundle.py --output restored.bundle --verify-repo PATH_TO_REPOSITORY.',
                       'Inspect the exact commit/tree in this manifest before explicitly fetching from the restored bundle.'],
                    'network_calls_performed': False, 'source_worktree_files_written': [],
                    'source_refs_written': [], 'source_index_written': False,
                    'status': 'awaiting_reassembly_check'}
        validation_manifest = output / 'manifest-before-reassembly.json'
        write_json(validation_manifest, manifest)
        with tempfile.TemporaryDirectory(prefix='roundtrip-', dir=output) as check_dir:
            reconstructed = Path(check_dir) / 'reassembled.bundle'
            raw = execute('native-reassembly-verify', [sys.executable, str(restore), '--manifest', str(validation_manifest),
                          '--output', str(reconstructed), '--verify-repo', str(repo.path)], output, repo.env)
            result = json.loads(raw)
            require(result['status'] == 'passed' and result['git_bundle_verified'] is True
                    and result['sha256'] == bundle_digest.hexdigest() and result['bytes'] == bundle_size,
                    'Round-trip verification differs from exact bundle')
            with bundle.open('rb') as original, reconstructed.open('rb') as rebuilt:
                while left := original.read(1024 * 1024):
                    require(left == rebuilt.read(len(left)), 'Round-trip bundle bytes differ')
                require(rebuilt.read(1) == b'', 'Round-trip bundle has extra bytes')
        require(repo.state() == initial, 'Project HEAD/index/refs changed during archive preparation')
        require(Path(__file__).read_bytes() == helper_bytes and restore_source.read_bytes() == restore_bytes,
                'Archive helper source changed during preparation')
        manifest.update({'status': 'prepared_and_verified', 'git_bundle_verification_passed': True,
                         'all_parts_reassembled_and_exact_bundle_bytes_compared': True,
                         'reassembled_bundle_git_verification_passed': True,
                         'project_head_index_refs_unchanged': True,
                         'source_head_commit': initial['head_commit'],
                         'source_index_sha256': None if initial['index_bytes'] is None else digest(initial['index_bytes']),
                         'source_refs_sha256': digest(initial['refs_bytes']),
                         'reassembly_input_manifest': metadata(validation_manifest, output),
                         'native_command_receipts': commands})
        write_json(output / 'manifest.json', manifest)
        print(json.dumps({'status': manifest['status'], 'commit': args.commit, 'tree': tree,
                          'bundle_bytes': bundle_size, 'bundle_sha256': bundle_digest.hexdigest(),
                          'part_count': len(parts), 'maximum_part_characters': max(part['bytes'] for part in parts),
                          'encoded_bytes': manifest['encoded_bytes'], 'manifest': str(output / 'manifest.json'),
                          'manifest_sha256': digest((output / 'manifest.json').read_bytes()),
                          'verification_counts': evidence['counts']}, indent=2))
        return manifest
    except BaseException as error:
        write_json(output / 'preparation-failure.json', {'status': 'failed', 'commit': args.commit,
                    'error_type': type(error).__name__, 'error': str(error),
                    'recorded_at_utc': datetime.now(timezone.utc).isoformat(),
                    'network_calls_performed': False, 'instruction': 'Do not publish as a verified archive.'})
        raise

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, default=DEFAULT_REPO)
    parser.add_argument('--commit', required=True)
    parser.add_argument('--output-dir', type=Path, required=True)
    prepare(parser.parse_args())
