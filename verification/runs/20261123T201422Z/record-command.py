"""Record an actual command, its exit status, and available source snapshots."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import os
import subprocess
import sys

RUN = Path(__file__).resolve().parent
ROOT = RUN.parents[2]
name, *command = sys.argv[1:]
folder = RUN / name
folder.mkdir(parents=True, exist_ok=False)
env = os.environ.copy()
env['PATH'] = '/workspace/scratch/5d2e6f7b5492/lean-runtime/lean-4.24.0-linux/bin:' + env['PATH']
snapshots = {}
for path in sorted((ROOT / 'Overfull/NativeReserve').glob('*.lean')):
    data = path.read_bytes()
    (folder / path.name).write_bytes(data)
    snapshots[path.relative_to(ROOT).as_posix()] = hashlib.sha256(data).hexdigest()
start = datetime.now(timezone.utc)
record = {'command': command, 'cwd': str(ROOT), 'started_at_utc': start.isoformat(),
          'source_sha256': snapshots, 'status': 'running', 'exit_code': None}
(folder / 'command.json').write_text(json.dumps(record, indent=2) + '\n')
print('Starting', name, command, flush=True)
with (folder / 'output.log').open('wb') as log:
    proc = subprocess.run(command, cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT)
end = datetime.now(timezone.utc)
record.update({'finished_at_utc': end.isoformat(), 'elapsed_seconds': (end-start).total_seconds(),
               'exit_code': proc.returncode, 'status': 'passed' if proc.returncode == 0 else 'failed'})
(folder / 'command.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps({k:v for k,v in record.items() if k != 'source_sha256'}, indent=2), flush=True)
print((folder / 'output.log').read_text(errors='replace')[-8000:], flush=True)
sys.exit(proc.returncode)
