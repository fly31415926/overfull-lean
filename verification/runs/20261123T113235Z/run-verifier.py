#!/usr/bin/env python3
"""Run the unchanged full verification gates and record genuine status and frozen inputs."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[3]
RUN = Path(__file__).resolve().parent

def hashes():
    paths = [ROOT / 'Overfull.lean', ROOT / 'Audit.lean',
        *(ROOT / 'Overfull').rglob('*.lean'),
        ROOT / 'lean-toolchain', ROOT / 'lakefile.toml', ROOT / 'lake-manifest.json',
        ROOT / 'README.md', ROOT / '.github/workflows/lean.yml',
        *(ROOT / 'scripts').glob('*.py'), *(ROOT / 'docs').glob('*.json'),
        *(ROOT / 'docs').glob('*.md'), *(ROOT / 'patches').glob('*.patch'),
        ROOT / 'THIRD_PARTY_NOTICES.txt', ROOT / 'CIRCULATION_NOTICE.txt',
        ROOT / 'LICENSE_BMATCHING.txt']
    return {p.relative_to(ROOT).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(paths)}

before = hashes()
(RUN / 'frozen-candidate-inputs.json').write_text(json.dumps(before, indent=2) + '\n')
started = datetime.now(timezone.utc)
record = {'command': ['python3', 'scripts/verify.py'],
    'started_at_utc': started.isoformat(), 'status': 'running',
    'exit_code': None, 'candidate_input_hash_count': len(before)}
(RUN / 'verification-command.json').write_text(json.dumps(record, indent=2) + '\n')
print('Starting complete strict build and stock audit at', started.isoformat(), flush=True)
with (RUN / 'verification-console.log').open('wb') as log:
    result = subprocess.run(record['command'], cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
finished = datetime.now(timezone.utc)
unchanged = hashes() == before
record.update({'completed_at_utc': finished.isoformat(),
    'elapsed_seconds': round((finished - started).total_seconds(), 3),
    'exit_code': result.returncode, 'all_frozen_inputs_unchanged': unchanged,
    'status': 'passed' if result.returncode == 0 and unchanged else 'failed'})
(RUN / 'verification-command.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record, indent=2), flush=True)
sys.exit(result.returncode if result.returncode else (0 if unchanged else 1))
