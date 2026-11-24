#!/usr/bin/env python3
"""Install reviewed additive source inventory and current integration documentation."""
import json
from pathlib import Path
import re
import shutil
import subprocess

RUN = Path(__file__).resolve().parent
ROOT = RUN.parents[2]
BASELINE = 'd2e7b1274d280ef6567cb2b562ec6e94eec2dda0'
DRAFT = RUN / 'docs-draft'


def previous(path):
    return subprocess.check_output(['git', 'show', BASELINE + ':' + path], cwd=ROOT)


def main():
    if subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT).decode().strip() != BASELINE:
        raise SystemExit('Candidate must be installed on the exact verified baseline')
    imports = json.loads((DRAFT / 'candidate-root-added-imports.json').read_text())
    old_root = previous('Overfull.lean')
    prefix = re.match(rb'(?:import [^\n]+\n|\n)*import [^\n]+\n', old_root)
    if prefix is None or not old_root[prefix.end():].startswith(b'\n/-!'):
        raise SystemExit('Unexpected baseline root import layout')
    (ROOT / 'Overfull.lean').write_bytes(old_root[:prefix.end()] +
        ''.join(imports).encode() + old_root[prefix.end():])
    (RUN / 'root-added-imports.json').write_text(json.dumps(imports, indent=2) + '\n')
    for name in ('native-integration-semantic-review.md', 'native-integration-verification.md'):
        shutil.copyfile(DRAFT / name, ROOT / 'docs' / name)
    shutil.copyfile(DRAFT / 'continuation-handoff.md', ROOT / 'docs/continuation-handoff.md')
    readme = previous('README.md').decode()
    first, rest = readme.split('\n', 1)
    (ROOT / 'README.md').write_text(first + '\n\n' +
        (DRAFT / 'readme-latest-section.md').read_text() + rest)
    coverage = json.loads(previous('docs/coverage.json'))
    coverage['scope'] = json.loads((DRAFT / 'coverage-scope.json').read_text())['scope']
    (ROOT / 'docs/coverage.json').write_text(json.dumps(coverage, indent=2) + '\n')
    subprocess.run(['python3', 'scripts/update_native_integration_manifest.py'], cwd=ROOT, check=True)
    actual = json.loads((ROOT / 'docs/native-integration-source.json').read_text())
    if actual != json.loads((DRAFT / 'native-integration-source.json').read_text()):
        raise SystemExit('Installed actual source manifest differs from reviewed draft inventory')
    subprocess.run(['git', 'diff', '--check'], cwd=ROOT, check=True)
    print(json.dumps({'root_added_imports': len(imports), 'new_modules': actual['module_count'],
        'public_theorem_proofs': actual['public_theorem_count'],
        'numbered_assertions_complete': 47, 'numbered_assertions_total': 69,
        'full_verifier_started_by_this_script': False}, indent=2))


if __name__ == '__main__':
    main()
