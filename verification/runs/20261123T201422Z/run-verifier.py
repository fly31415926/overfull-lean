#!/usr/bin/env python3
"""Run all stock verification gates against exact frozen current inputs.

Each attempt has its own immutable directory. Top-level run records point
to the latest attempt, while prior attempts retain their real logs/status.
"""
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[3]
RUN = Path(__file__).resolve().parent


def hashes():
    paths = [ROOT/'Overfull.lean', ROOT/'Audit.lean',
             *(ROOT/'Overfull').rglob('*.lean'),
             ROOT/'lean-toolchain', ROOT/'lakefile.toml', ROOT/'lake-manifest.json',
             ROOT/'README.md', ROOT/'.github/workflows/lean.yml',
             *(ROOT/'scripts').glob('*.py'), *(ROOT/'docs').glob('*.json'),
             *(ROOT/'docs').glob('*.md'), *(ROOT/'patches').glob('*.patch'),
             ROOT/'THIRD_PARTY_NOTICES.txt', ROOT/'CIRCULATION_NOTICE.txt',
             ROOT/'LICENSE_BMATCHING.txt']
    return {p.relative_to(ROOT).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(paths)}


phase = sys.argv[1] if len(sys.argv) == 2 else 'full-01'
if not phase.startswith('full-') or not phase.replace('-', '').isalnum():
    raise SystemExit('Use a simple full-NN attempt name')
folder = RUN/phase
folder.mkdir(exist_ok=False)
before = hashes()
frozen = json.dumps(before, indent=2)+'\n'
(folder/'frozen-candidate-inputs.json').write_text(frozen)
(RUN/'frozen-candidate-inputs.json').write_text(frozen)
snapshots = {}
for path in sorted((ROOT/'Overfull/NativeReserve').glob('*.lean')):
    shutil.copyfile(path, folder/path.name)
    snapshots[path.relative_to(ROOT).as_posix()] = hashlib.sha256(path.read_bytes()).hexdigest()
started = datetime.now(timezone.utc)
record = {'command': ['python3', 'scripts/verify.py'], 'cwd': str(ROOT),
          'started_at_utc': started.isoformat(), 'status': 'running', 'exit_code': None,
          'attempt': phase, 'candidate_input_hash_count': len(before),
          'source_sha256': snapshots}
for path in [folder/'command.json', RUN/'verification-command.json']:
    path.write_text(json.dumps(record, indent=2)+'\n')
env = os.environ.copy()
env['PATH'] = '/workspace/scratch/5d2e6f7b5492/lean-runtime/lean-4.24.0-linux/bin:'+env['PATH']
print('Starting full strict build and unchanged audit', phase, started.isoformat(), flush=True)
with (folder/'output.log').open('wb') as log:
    result = subprocess.run(record['command'], cwd=ROOT, env=env,
                            stdout=log, stderr=subprocess.STDOUT)
finished = datetime.now(timezone.utc)
unchanged = hashes() == before
record.update({'finished_at_utc': finished.isoformat(),
               'completed_at_utc': finished.isoformat(),
               'elapsed_seconds': (finished-started).total_seconds(),
               'exit_code': result.returncode, 'all_frozen_inputs_unchanged': unchanged,
               'status': 'passed' if result.returncode == 0 and unchanged else 'failed'})
for path in [folder/'command.json', RUN/'verification-command.json']:
    path.write_text(json.dumps(record, indent=2)+'\n')
shutil.copyfile(folder/'output.log', RUN/'verification-console.log')
print(json.dumps({k:v for k,v in record.items() if k != 'source_sha256'}, indent=2), flush=True)
sys.exit(result.returncode if result.returncode else (0 if unchanged else 1))
