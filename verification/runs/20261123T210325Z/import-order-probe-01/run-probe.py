#!/usr/bin/env python3
"""Observe the five generated-declaration owners with the old import prefix.

This scratch probe imports the actual compiled modules. It neither changes
the repository nor traverses axioms. The full frozen verifier remains required.
"""
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path('/workspace/scratch/96ddfd820f7d/overfull-next')
RUN = Path(__file__).resolve().parent
PARENT = 'b7be9966640e932ef7bbd030d3dae42f7bcb4638'
RUNTIME = Path('/workspace/scratch/5d2e6f7b5492/lean-runtime/lean-4.24.0-linux/bin')
NAMES = [
    'Overfull.BipartiteMatchingCompletion.uncoveredLeftOutside.eq_1',
    'Overfull.BipartiteMatchingCompletion.uncoveredRightOutside.eq_1',
    'Overfull.IsRobustExpander.congr_simp',
    'Overfull.MatchingProbability.graphCutEdges.eq_1',
    'Overfull.internalEdges.eq_1',
]


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def sha(data):
    return hashlib.sha256(data).hexdigest()


old_root = subprocess.check_output(['git', 'show', PARENT + ':Overfull.lean'], cwd=ROOT)
previous = json.loads(subprocess.check_output(['git', 'show', PARENT + ':verification/results.json'], cwd=ROOT))
expected = {item['name']: item['module'] for item in previous['verified_declarations'] if item['name'] in NAMES}
assert set(expected) == set(NAMES)
new_imports_path = ROOT / 'verification/runs/20261123T210325Z/root-added-imports.json'
new_imports = json.loads(new_imports_path.read_text())
assert len(new_imports) == 5
before_comment, separator, old_comment = old_root.partition(b'/-!')
assert separator and before_comment.count(b'import ') == len(re.findall(rb'^import ', before_comment, re.M))
new_root = before_comment + ''.join(new_imports).encode() + separator + old_comment
quoted_names = ',\n    '.join('`' + name for name in NAMES)
probe = new_root.decode() + '\n' + '''
open Lean Elab Command

elab "#probe_generated_declaration_owners" : command => do
  let env \u2190 getEnv
  let names : Array Name := #[
    ''' + quoted_names + ''']
  for name in names do
    let some idx := env.getModuleIdxFor? name |
      throwError "No imported module for {name}"
    let moduleName := env.header.moduleNames[idx.toNat]!
    let record := Json.mkObj [
      ("name", toJson name.toString),
      ("module", toJson moduleName.toString)]
    logInfo ("OWNERSHIP_PROBE " ++ record.compress)
  logInfo "OWNERSHIP_PROBE_COMPLETE 5"

#probe_generated_declaration_owners
'''
source = RUN / 'OldPrefixThenPalette.lean'
assert not (RUN / 'command.json').exists(), 'Never overwrite a recorded probe attempt'
source.write_text(probe)
(RUN / 'proposed-Overfull.lean').write_bytes(new_root)
write_json(RUN / 'expected.json', expected)
cmd = [str(RUNTIME / 'lake'), 'env', 'lean', '-DwarningAsError=true', str(source)]
started = datetime.now(timezone.utc)
record = {
    'command': cmd, 'cwd': str(ROOT), 'started_at_utc': started.isoformat(),
    'status': 'running', 'exit_code': None,
    'parent_verified_commit': PARENT,
    'scope': 'Module attribution only; no axiom traversal or complete verification.',
    'source_sha256': {str(source): sha(source.read_bytes())},
    'parent_root_sha256': sha(old_root), 'proposed_root_sha256': sha(new_root),
    'root_added_imports_sha256': sha(new_imports_path.read_bytes()),
}
write_json(RUN / 'command.json', record)
env = os.environ.copy()
env['PATH'] = str(RUNTIME) + ':' + env['PATH']
with (RUN / 'output.log').open('wb') as output:
    result = subprocess.run(cmd, cwd=ROOT, env=env, stdout=output, stderr=subprocess.STDOUT)
finished = datetime.now(timezone.utc)
record.update({'status': 'passed' if result.returncode == 0 else 'failed',
               'exit_code': result.returncode, 'finished_at_utc': finished.isoformat(),
               'elapsed_seconds': (finished - started).total_seconds(),
               'output_sha256': sha((RUN / 'output.log').read_bytes())})
write_json(RUN / 'command.json', record)
text = (RUN / 'output.log').read_text()
records = [json.loads(line) for line in re.findall(r'^OWNERSHIP_PROBE ([^\n]+)$', text, re.M)]
actual = {entry['name']: entry['module'] for entry in records}
matches = (result.returncode == 0 and len(records) == len(actual) == len(NAMES)
           and actual == expected and text.count('OWNERSHIP_PROBE_COMPLETE 5') == 1)
comparison = {'status': 'passed' if matches else 'failed', 'parent_verified_commit': PARENT,
              'expected': expected, 'observed': actual, 'all_five_module_owners_match_parent': matches,
              'compiler_exit_code': result.returncode, 'command_metadata_sha256': sha((RUN / 'command.json').read_bytes()),
              'scope': 'Targeted module-attribution observation. A fresh strict full verifier is still required.'}
write_json(RUN / 'comparison.json', comparison)
print(text, end='')
print(json.dumps(comparison, indent=2))
sys.exit(0 if matches else 1)
