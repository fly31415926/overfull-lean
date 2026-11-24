#!/usr/bin/env python3
"""Check baseline preservation, immutable evidence, and the actual full kernel audit."""
from datetime import datetime, timezone
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import subprocess
import sys

RUN = Path(__file__).resolve().parent
ROOT = RUN.parents[2]
BASELINE = '1c9404a454c99fe5c11ba8d774cb9c259f291f20'
TREE = '087e26b5f004af1f9423a6f2b137d805f5991f1a'
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
EDITABLE_INPUTS = {'Overfull.lean', 'README.md', 'docs/continuation-handoff.md',
                   'scripts/verify.py', 'docs/next-verification-target.md',
                   'docs/coverage.json', 'docs/manuscript-source.json'}
LIVE_OUTPUTS = {'verification/results.json', 'verification/build.log', 'verification/axioms.log',
                'verification/lean-version.log', 'verification/vizing-source.log'}
REQUIRED_CONTROLS = {'check-preservation.py', 'run-verifier.py', 'record-command.py',
                     'verification-scope.json', 'verifier-additions.json', 'root-added-imports.json',
                     'development-index.json', 'independent-verification-review.md',
                     'environment.json', 'authorization.md', 'baseline-remote-refs.json',
                     'recovered-verifier-provenance.json', 'recovery-provenance.json',
                     'recovered-evidence-index.json', 'environment-dependencies.json',
                     'source-statement-recovery.json'}


def require(value, message):
    if not value:
        raise RuntimeError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def load(path):
    return json.loads(path.read_text())


def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT)


@lru_cache(None)
def old(path):
    return git('show', f'{BASELINE}:{path}')


def scope():
    return load(RUN / 'verification-scope.json')


def principal_outputs():
    return {'verification/results.json', 'verification/build.log', 'verification/axioms.log',
            scope()['declaration_map']}


def current_inputs():
    paths = [ROOT / 'Overfull.lean', ROOT / 'Audit.lean', *(ROOT / 'Overfull').rglob('*.lean'),
             ROOT / 'lean-toolchain', ROOT / 'lakefile.toml', ROOT / 'lake-manifest.json',
             ROOT / 'README.md', ROOT / '.github/workflows/lean.yml',
             *(ROOT / 'scripts').glob('*.py'), *(ROOT / 'docs').glob('*.json'),
             *(ROOT / 'docs').glob('*.md'), *(ROOT / 'patches').glob('*.patch'),
             ROOT / 'THIRD_PARTY_NOTICES.txt', ROOT / 'CIRCULATION_NOTICE.txt',
             ROOT / 'LICENSE_BMATCHING.txt']
    return {p.relative_to(ROOT).as_posix(): p.read_bytes() for p in sorted(paths)}


def current_controls():
    paths = {RUN / name for name in REQUIRED_CONTROLS}
    paths.update(RUN.glob('*.py'))
    paths.update(RUN.glob('independent-*.md'))
    paths.update(RUN.glob('verifier-*.patch'))
    return {p.name: p.read_bytes() for p in sorted(paths)}


def check_verifier():
    expected = old('scripts/verify.py').decode()
    edits = load(RUN / 'verifier-additions.json')
    exact_promotions = {
        ('COMPLETED_NUMBERED_ASSERTION_COUNT = 49\n',
         'COMPLETED_NUMBERED_ASSERTION_COUNT = 51\n'),
        ('    for number in ("2.24", "4.4", "4.5", "4.16", "6.1", "6.2", "6.3"):\n',
         '    for number in ("2.24", "4.4", "4.5", "6.1", "6.2", "6.3"):\n'),
    }
    require(len(edits) == 7, 'Unexpected verifier registration count')
    observed_promotions = set()
    for edit in edits:
        if edit['kind'] == 'exact_coverage_promotion':
            pair = (edit['old'], edit['new'])
            require(pair in exact_promotions, 'Unreviewed nonadditive verifier change')
            observed_promotions.add(pair)
        else:
            require(edit['kind'] == 'additive' and edit['old'] in edit['new']
                    and len(edit['new']) > len(edit['old']), 'Verifier edit is not additive')
        require(expected.count(edit['old']) == 1, 'Ambiguous verifier edit anchor')
        expected = expected.replace(edit['old'], edit['new'], 1)
    require(observed_promotions == exact_promotions, 'Exact two coverage promotions missing')
    require((ROOT / 'scripts/verify.py').read_text() == expected,
            'Verifier changed beyond the exact recorded modifications')
    require((ROOT / 'Audit.lean').read_bytes() == old('Audit.lean'), 'The stock kernel audit changed')
    return {'exact_recorded_edit_count': len(edits), 'stock_kernel_audit_byte_identical': True}


def check_coverage():
    previous, current = json.loads(old('docs/coverage.json')), load(ROOT / 'docs/coverage.json')
    before = {a['number']: a for a in previous['numbered_assertions']}
    after = {a['number']: a for a in current['numbered_assertions']}
    require(list(before) == list(after) and len(after) == 69, 'Numbered assertion inventory changed')
    promoted = scope()['promoted_assertions']
    require(promoted == {
        '4.16': ['Overfull.frequent_pattern_result_one_factorization'],
        '4.17': ['Overfull.regular_core_one_factorization']},
        'Only the exact full 4.16 and 4.17 endpoints may be promoted')
    identity = ['number', 'kind', 'labels', 'section', 'statement_source_lines', 'statement_sha256',
                'imported_statement']
    for number in before:
        require(all(before[number][key] == after[number][key] for key in identity),
                'Numbered statement identity changed: ' + number)
        if number in promoted:
            require(before[number]['full_assertion_verified'] is False
                    and after[number]['full_assertion_verified'] is True
                    and after[number]['lean_theorems'] == promoted[number],
                    'Promotion does not match exact declared theorem(s): ' + number)
        else:
            require(before[number] == after[number], 'Unrelated assertion changed: ' + number)
    old_complete = {n for n, a in before.items() if a['full_assertion_verified']}
    new_complete = {n for n, a in after.items() if a['full_assertion_verified']}
    require(len(old_complete) == 49 and new_complete == old_complete | set(promoted),
            'Coverage exceeds the declared exact closure')
    require(current['fully_verified_numbered_assertion_count'] == len(new_complete)
            and current['main_theorem_verified'] is False, 'Unexpected complete coverage or main-theorem claim')
    old_catalog = previous['checked_component_catalog']
    require(current['checked_component_catalog'][:len(old_catalog)] == old_catalog,
            'A previous checked component changed')
    allowed = {'scope', 'checked_component_catalog', 'numbered_assertions', 'fully_verified_numbered_assertion_count'}
    require({k: v for k, v in previous.items() if k not in allowed}
            == {k: v for k, v in current.items() if k not in allowed}, 'Other coverage metadata changed')
    previous_source = json.loads(old('docs/manuscript-source.json'))
    source = load(ROOT / 'docs/manuscript-source.json')
    require(source['fully_verified_numbered_assertions'] == len(new_complete), 'Manuscript count is wrong')
    old_additional = previous_source['additional_complete_results']
    require(source['additional_complete_results'][:len(old_additional)] == old_additional,
            'A previous manuscript completed-result entry changed')
    extra = source['additional_complete_results'][len(old_additional):]
    allowed_names = {n for names in promoted.values() for n in names}
    require(len(extra) == len(allowed_names) and {x['lean_name'] for x in extra} == allowed_names,
            'Manuscript extra results differ from exact promoted declarations')
    allowed_source = {'fully_verified_numbered_assertions', 'additional_complete_results'}
    require({k: v for k, v in source.items() if k not in allowed_source}
            == {k: v for k, v in previous_source.items() if k not in allowed_source},
            'Pinned manuscript metadata or historical evidence changed')
    return {'numbered_assertions': 69, 'previous_complete': 49, 'current_complete': len(new_complete),
            'promoted_assertions': list(promoted), 'all_69_statement_identities_identical': True,
            'all_unpromoted_records_identical': True, 'main_theorem_verified': False}


def check_development():
    recorded = load(RUN / 'development-index.json')
    files = {p.relative_to(RUN).as_posix(): p for p in (RUN / 'development').rglob('*') if p.is_file()}
    require(recorded['schema_version'] == 1 and recorded['file_count'] == len(files)
            and set(recorded['files']) == set(files), 'Development evidence inventory changed')
    for name, path in files.items():
        data, entry = path.read_bytes(), recorded['files'][name]
        require(len(data) == entry['bytes'] and sha(data) == entry['sha256'], 'Development bytes changed: ' + name)
    attempts = []
    recorder_clarifications = []
    for path in sorted((RUN / 'development').glob('*/command.json')):
        command = load(path)
        snapshot_sha = sha((path.parent / 'recorder.py').read_bytes())
        if snapshot_sha != command['recorder_sha256']:
            # Two interrupted commands queued while the inherited recorder was
            # edited. Their raw receipts remain unchanged; the narrowly pinned
            # metadata discrepancy does not certify either interrupted build.
            require(path.parent.name in {'four-grouping-even-01', 'twoodd-cuts-01'}
                    and command['status'] == 'running' and command['exit_code'] is None,
                    'Unexplained focused recorder mismatch')
            clarification = load(path.parent / 'recorder-hash-clarification.json')
            require(snapshot_sha == 'e0587e43ec60b79f85ae2a55b167dace5fa707c186fd321632312d8f97dffbea'
                    and command['recorder_sha256'] == '53ccba193876da2fb99ff694b7221f12d5e20057762cba0f2f9ef5715a5b62ab'
                    and clarification['kind'] == 'documented_recorder_hash_race'
                    and clarification['executed_source_snapshot_sha256'] == snapshot_sha
                    and clarification['recorded_hash_of_later_live_file'] == command['recorder_sha256']
                    and clarification['original_command_receipt_sha256'] == sha(path.read_bytes())
                    and clarification['snapshot_captured_before_waiting_for_build_lock'] is True,
                    'Recorder hash clarification differs from the actual preserved evidence')
            recorder_clarifications.append(path.parent.name)
        require((path.parent / 'output.log').is_file(), 'Focused output disappeared')
        interrupted = command['exit_code'] is None and command['status'] == 'running'
        if interrupted:
            interruption = load(path.parent / 'interruption.json')
            require(interruption['status'] == 'interrupted'
                    and interruption['child_exit_code'] is None
                    and interruption['observed_tool_exit_code'] == 130
                    and interruption['observed_tool_result']['exit_code'] == 130
                    and interruption['original_command_receipt_preserved'] is True,
                    'Interrupted attempt lacks a genuine observed tool result')
        else:
            require(type(command['exit_code']) is int and command['status'] in {'passed', 'failed'},
                    'Unfinished focused attempt cannot be included in final freeze')
            require((command['status'] == 'passed') == (command['exit_code'] == 0), 'Invalid focused pass/fail status')
            require(sha((path.parent / 'output.log').read_bytes()) == command['output_sha256'],
                    'Focused output no longer matches execution receipt')
        for source, digest in command['source_sha256'].items():
            require(sha((path.parent / 'source' / source).read_bytes()) == digest, 'Focused source snapshot changed')
        entry = {'attempt': path.parent.name, 'command': command['command'],
                 'exit_code': command['exit_code'], 'status': 'interrupted' if interrupted else command['status'],
                 'changed_inputs': command.get('inputs_changed_during_command')}
        if interrupted:
            entry['observed_tool_exit_code'] = interruption['observed_tool_exit_code']
        attempts.append(entry)
    counts = {status: sum(a['status'] == status for a in attempts) for status in {'passed', 'failed', 'interrupted'}}
    require(recorded['attempt_count'] == len(attempts) and recorded['attempts'] == attempts
            and recorded['status_counts'] == counts, 'Development summary changed')
    return {'attempt_count': len(attempts), 'file_count': len(files), 'status_counts': counts,
            'attempts_with_recorded_input_changes': [a['attempt'] for a in attempts if a['changed_inputs']],
            'attempts_with_unknown_input_change_status': [a['attempt'] for a in attempts if a['changed_inputs'] is None],
            'exact_inventory_hashes_and_sizes_preserved': True,
            'interrupted_attempts_with_documented_recorder_identity_metadata_race': recorder_clarifications}


def check_recovered_evidence():
    inventory = load(RUN / 'recovered-evidence-index.json')
    actual = {p.relative_to(RUN).as_posix(): p
              for p in (RUN / 'recovered-evidence').rglob('*') if p.is_file()}
    require(inventory['file_count'] == len(actual)
            and set(inventory['files']) == set(actual), 'Recovered evidence inventory changed')
    for name, path in actual.items():
        data = path.read_bytes()
        require(inventory['files'][name] == {'bytes': len(data), 'sha256': sha(data)},
                'Recovered evidence bytes changed: ' + name)
    recovered = load(RUN / 'recovered-evidence/recovery-index.json')
    require(len(recovered['blobs']) == inventory['exact_recovered_blob_count'] == 11,
            'Recovered blob inventory changed')
    for entry in recovered['blobs']:
        data = (RUN / 'recovered-evidence' / entry['git_blob_sha1']).read_bytes()
        blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        require(blob == entry['git_blob_sha1'] and sha(data) == entry['sha256']
                and len(data) == entry['bytes'], 'Recovered Git object bytes changed')
    return {'file_count': len(actual), 'exact_blob_count': len(recovered['blobs']),
            'all_recovered_evidence_unchanged': True,
            'historical_partial_evidence_does_not_substitute_for_new_full_run': True}


def check_statement_evidence():
    record = load(RUN / 'source-statement-recovery.json')
    actual = {p.relative_to(RUN).as_posix(): p
              for p in (RUN / 'source-evidence').rglob('*') if p.is_file()}
    require(record['file_count'] == len(actual) and set(record['files']) == set(actual),
            'Scoped statement evidence inventory changed')
    for name, path in actual.items():
        data = path.read_bytes()
        require(record['files'][name] == {'bytes': len(data), 'sha256': sha(data)},
                'Scoped statement evidence bytes changed: ' + name)
    expected = {
        'notation': 'a29824dbdf5c5f75796927e0766fe709596e4a6b7e66d53369500b005f325c2e',
        '4.13': '557d62e4c4ab7c00ac7cc29fa403d80601a2b9851e7c7eb62cdeb4caa1d40c3b',
        '4.16': '1ba102e379594ab72de4ba73cf41c88d9fbdadf1c132e2943b48da04e8c2cc1c',
        '4.17': 'b271893680e87b1c06c35172a138050dbf84009964eb618dce53c53ba595e322',
    }
    first = load(RUN / 'source-evidence/source-excerpt-read.json')['structuredContent']['results']
    second = load(RUN / 'source-evidence/source-assertion-read.json')['structuredContent']['results']
    rows = {'notation': first[0], '4.13': first[1], '4.16': second[0], '4.17': second[1]}
    require(len(record['blocks']) == 4 and {b['number'] for b in record['blocks']} == set(expected),
            'Scoped statement block list changed')
    for block in record['blocks']:
        number = block['number']
        row = rows[number]
        raw, pinned = (RUN / block['raw_path']).read_bytes(), (RUN / block['pinned_path']).read_bytes()
        require(raw == row['content'][0].encode() and sha(raw) == block['raw_sha256'],
                'Statement block is not exact source read content')
        for key in ['library_file_id', 'file_id', 'version_id', 'modified_at']:
            require(block[key] == row[key], 'Scoped source provenance metadata differs')
        require(block['current_source_lines'] == [row['start_line'], row['end_line']],
                'Scoped source line metadata differs')
        if number == 'notation':
            transformed = raw + b'\n'
        elif number in {'4.16', '4.17'}:
            require(raw.count(b'$1$-factorization') == 1, 'Ambiguous statement normalization')
            transformed = raw.replace(b'$1$-factorization', b'one-factorization', 1)
        else:
            transformed = raw
        require(pinned == transformed and sha(pinned) == expected[number] == block['pinned_sha256'],
                'Scoped statement hash or exact normalization differs')
    require(record['whole_manuscript_recovered'] is False
            and record['whole_manuscript_identity_claimed'] is False, 'Unwarranted whole-manuscript claim')
    return {'numbered_blocks': ['4.13', '4.16', '4.17'], 'standing_notation_preserved': True,
            'exact_pinned_numbered_block_hashes': {n: expected[n] for n in ['4.13', '4.16', '4.17']},
            'normalizations_explicit_and_checked': True, 'whole_manuscript_identity_claimed': False}


def preflight(inputs=None):
    inputs = current_inputs() if inputs is None else inputs
    require(git('rev-parse', 'HEAD').decode().strip() == BASELINE, 'Unexpected baseline HEAD')
    require(git('rev-parse', BASELINE + '^{tree}').decode().strip() == TREE, 'Unexpected baseline tree')
    previous = json.loads(old('verification/results.json'))
    require(previous['verified_declaration_count'] == 14627 and len(previous['completed_results']) == 2777,
            'Baseline audit counts differ')
    hashes = {**previous['source_sha256'], **previous['verification_input_sha256']}
    require(len(hashes) == 826, 'Baseline frozen-input count differs')
    for path, digest in hashes.items():
        require(path in inputs, 'A previous frozen input disappeared: ' + path)
        if path not in EDITABLE_INPUTS:
            require(sha(inputs[path]) == digest, 'A previous immutable input changed: ' + path)
    changes = set(git('diff', '--name-only', BASELINE, '--').decode().splitlines())
    prior_paths = set(git('ls-tree', '-r', '--name-only', BASELINE).decode().splitlines())
    changed_previous = changes & prior_paths
    require(changed_previous <= EDITABLE_INPUTS | LIVE_OUTPUTS,
            'Unreviewed prior tracked files changed: ' + str(sorted(changed_previous - EDITABLE_INPUTS - LIVE_OUTPUTS)))
    verifier = check_verifier()
    coverage = check_coverage()
    manifest = load(ROOT / scope()['source_manifest'])
    require(manifest['numbered_assertions_completed'] == 2
            and manifest['main_theorem_verified'] is False, 'Continuation scope changed')
    new_sources = {path for path in inputs if path.endswith('.lean') and path not in hashes}
    require(new_sources == {m['path'] for m in manifest['modules']}, 'New source manifest incomplete')
    for module in manifest['modules']:
        require(sha(inputs[module['path']]) == module['sha256'], 'New source hash mismatch: ' + module['path'])
    imports = load(RUN / 'root-added-imports.json')
    original = old('Overfull.lean').decode()
    split = original.index('\n/-!')
    expected = original[:split] + ''.join(imports) + original[split:]
    require((ROOT / 'Overfull.lean').read_text() == expected, 'Root changed beyond recorded additive imports')
    for line in imports:
        require(line.startswith('import ') and line.endswith('\n')
                and line[7:].strip() in {m['module'] for m in manifest['modules']}, 'Unmapped root import')
    development = check_development()
    recovered = check_recovered_evidence()
    statements = check_statement_evidence()
    return {'baseline_commit': BASELINE, 'baseline_tree': TREE, 'previous_audited_declarations': 14627,
            'previous_completed_result_mappings': 2777, 'previous_frozen_inputs': len(hashes),
            'coverage': coverage, 'all_previous_mathematical_sources_and_audit_unchanged': True,
            'verifier_changes_exactly_recorded': verifier, 'new_module_count': len(new_sources),
            'development_evidence': development, 'recovered_evidence': recovered,
            'statement_evidence': statements}


def index(declarations):
    result = {d['name']: (d['module'], frozenset(d['axioms'])) for d in declarations}
    require(len(result) == len(declarations), 'Duplicate audited declaration name')
    return result


def check_execution_receipt(folder, receipt, frozen, inputs):
    require(receipt['command'] == ['python3', 'scripts/verify.py'] and receipt['cwd'] == str(ROOT)
            and receipt['attempt'] == folder.name and receipt['baseline_commit'] == BASELINE
            and receipt['baseline_tree'] == TREE and receipt['verifier_launched'] is True
            and receipt['exit_code'] == 0 and receipt['preflight_passed'] is True
            and receipt['wrapper_exit_code'] == 0 and receipt['wrapper_errors'] == []
            and receipt['missing_principal_outputs'] == [] and receipt['status'] == 'passed'
            and receipt['inputs_unchanged'] is True and receipt['controls_unchanged'] is True,
            'Full verifier did not pass genuinely on unchanged inputs and controls')
    require((folder / 'command.json').read_bytes() == (folder / 'terminal.json').read_bytes(),
            'Terminal and command receipts differ')
    require(sha((folder / 'output.log').read_bytes()) == receipt['output_sha256'], 'Full raw output changed')
    require(receipt['frozen_input_count'] == len(frozen)
            and {p: sha(data) for p, data in inputs.items()} == frozen, 'Inputs changed after full verification')
    for path, digest in frozen.items():
        require(sha((folder / 'input' / path).read_bytes()) == digest, 'Frozen source snapshot changed: ' + path)
    controls = current_controls()
    recorded_controls = receipt['control_sha256']
    require(REQUIRED_CONTROLS <= set(recorded_controls)
            and {name: sha(data) for name, data in controls.items()} == recorded_controls,
            'Control inventory or live control bytes changed')
    require(load(folder / 'frozen-controls.json') == recorded_controls, 'Frozen controls differ from receipt')
    for name, digest in recorded_controls.items():
        require(Path(name).name == name, 'Control is not a flat run-relative name')
        require(sha((folder / 'control' / name).read_bytes()) == digest, 'Frozen control changed: ' + name)
    outputs = {entry['path']: entry for entry in receipt['outputs']}
    require(len(outputs) == len(receipt['outputs']), 'Duplicate output path')
    require(principal_outputs() <= set(outputs), 'Missing principal output')
    for path, entry in outputs.items():
        relative = Path(path)
        require(len(relative.parts) == 2 and relative.parts[0] == 'verification'
                and relative.suffix in {'.json', '.log'}, 'Unexpected verifier output path')
        live, archived = (ROOT / path).read_bytes(), (folder / 'artifacts' / path).read_bytes()
        require(len(live) == len(archived) == entry['bytes'] and sha(live) == sha(archived) == entry['sha256'],
                'Live and archived output differ from genuine command: ' + path)
    return {'principal_outputs_present': True, 'all_recorded_live_outputs_match_archive': True,
            'raw_command_output_unchanged': True, 'terminal_receipt_identical': True,
            'all_verification_controls_preserved': True, 'control_count': len(recorded_controls),
            'recorded_output_count': len(outputs)}


def main():
    attempt = sys.argv[1] if len(sys.argv) == 2 else 'full-01'
    inputs = current_inputs()
    result = preflight(inputs)
    folder = RUN / attempt
    receipt = load(folder / 'command.json')
    frozen = load(folder / 'frozen-inputs.json')
    execution = check_execution_receipt(folder, receipt, frozen, inputs)
    current = load(ROOT / 'verification/results.json')
    previous = json.loads(old('verification/results.json'))
    require(current['lean_build_passed'] and current['axiom_audit_passed'], 'Complete verification failed')
    require({**current['source_sha256'], **current['verification_input_sha256']} == frozen,
            'Actual frozen inputs and verifier report inputs differ')
    old_declarations, new_declarations = index(previous['verified_declarations']), index(current['verified_declarations'])
    require(all(new_declarations.get(n) == value for n, value in old_declarations.items()),
            'A prior declaration, module owner, or axiom set changed/disappeared')
    require(all(axioms <= ALLOWED_AXIOMS for _, axioms in new_declarations.values()), 'Forbidden axiom found')
    require(all(current['completed_results'].get(k) == v for k, v in previous['completed_results'].items()),
            'A prior completed-result mapping changed')
    for key, value in previous.items():
        if key.endswith('_declaration_map'):
            require(current[key] == value, 'Prior complete source/declaration map changed: ' + key)
            require(sha((ROOT / value['path']).read_bytes()) == value['sha256'], 'Prior declaration-map bytes changed')
    expected_complete = 49 + len(scope()['promoted_assertions'])
    require(current['fully_verified_numbered_assertion_count'] == expected_complete
            and not current['main_theorem_verified'], 'Full verifier coverage differs from reviewed scope')
    manifest = load(ROOT / scope()['source_manifest'])
    modules = {m['module'] for m in manifest['modules']}
    mapped = load(ROOT / scope()['declaration_map'])
    require(index(mapped['proof_declaration_map']) == {n: d for n, d in new_declarations.items() if d[0] in modules},
            'New map omits private or generated audited proofs')
    result.update({'status': 'passed', 'checked_at_utc': datetime.now(timezone.utc).isoformat(),
                   'full_verifier_attempt': attempt, 'actual_full_verifier_exit': receipt['exit_code'],
                   'audited_declarations': len(new_declarations),
                   'new_audited_declarations': len(new_declarations) - len(old_declarations),
                   'public_theorem_count': manifest['public_theorem_count'], 'frozen_input_count': len(frozen),
                   'allowed_axioms': sorted(ALLOWED_AXIOMS),
                   'all_previous_declarations_owners_axiom_sets_preserved': True,
                   'all_previous_completed_result_mappings_preserved': True,
                   'all_previous_source_declaration_maps_preserved': True,
                   'execution_evidence': execution,
                   'genuine_command_receipt_sha256': sha((folder / 'command.json').read_bytes())})
    (RUN / 'preservation.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
