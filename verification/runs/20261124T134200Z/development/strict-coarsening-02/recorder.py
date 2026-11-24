#!/usr/bin/env python3
"""Record genuine focused commands and exact source snapshots without overwriting attempts."""
from datetime import datetime, timezone
import fcntl
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time

RUN = Path(__file__).resolve().parent
ROOT = RUN.parents[2]
BASELINE = '3991bb7eee091a329046073e0366daa84a603e5d'
name, *command = sys.argv[1:]
if not command or '/' in name or name in {'.', '..'}:
    raise SystemExit('usage: record-command.py UNIQUE-ATTEMPT COMMAND ...')
folder = RUN / 'development' / name
folder.mkdir(parents=True, exist_ok=False)
(folder / 'recorder.py').write_bytes(Path(__file__).read_bytes())
env = os.environ.copy()
env['PATH'] = '/workspace/scratch/77adbfc63087/toolchain/lean-4.24.0-linux/bin:' + env['PATH']
baseline_paths = set(subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', BASELINE], cwd=ROOT, text=True).splitlines())
with (RUN / 'build.lock').open('a') as lock:
    fcntl.flock(lock, fcntl.LOCK_EX)
    snapshots, dependencies = {}, {}
    for path in sorted((ROOT / 'Overfull').rglob('*.lean')):
        data = path.read_bytes()
        rel = path.relative_to(ROOT).as_posix()
        dependencies[rel] = hashlib.sha256(data).hexdigest()
        if rel not in baseline_paths:
            target = folder / 'source' / rel
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
            snapshots[rel] = dependencies[rel]
    for rel in ['Overfull.lean', 'Audit.lean', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain']:
        path = ROOT / rel
        dependencies[rel] = hashlib.sha256(path.read_bytes()).hexdigest()
    start, tick = datetime.now(timezone.utc), time.monotonic()
    record = {'command': command, 'cwd': str(ROOT), 'started_at_utc': start.isoformat(),
              'source_sha256': snapshots, 'input_sha256': dependencies,
              'status': 'running', 'exit_code': None,
              'baseline_verified_local_commit': BASELINE,
              'recorder_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    receipt = folder / 'command.json'
    receipt.write_text(json.dumps(record, indent=2) + '\n')
    print('Starting', name, command, flush=True)
    interrupted = False
    with (folder / 'output.log').open('wb') as log:
        proc = subprocess.Popen(command, cwd=ROOT, env=env, stdout=log,
                                stderr=subprocess.STDOUT, start_new_session=True)
        try:
            proc.wait()
        except KeyboardInterrupt:
            interrupted = True
            if proc.poll() is None:
                os.killpg(proc.pid, signal.SIGTERM)
                try:
                    proc.wait(timeout=10)
                except subprocess.TimeoutExpired:
                    os.killpg(proc.pid, signal.SIGKILL)
                    proc.wait()
    changed = [rel for rel, digest in dependencies.items()
               if not (ROOT / rel).is_file() or hashlib.sha256((ROOT / rel).read_bytes()).hexdigest() != digest]
    record.update({'finished_at_utc': datetime.now(timezone.utc).isoformat(),
                   'elapsed_seconds': time.monotonic() - tick,
                   'exit_code': proc.returncode, 'status': 'passed' if proc.returncode == 0 else 'failed',
                   'wrapper_interrupted': interrupted,
                   'inputs_changed_during_command': changed,
                   'output_sha256': hashlib.sha256((folder / 'output.log').read_bytes()).hexdigest()})
    receipt.write_text(json.dumps(record, indent=2) + '\n')
    print(json.dumps({k: v for k, v in record.items() if k not in ('source_sha256', 'input_sha256')}, indent=2), flush=True)
    print((folder / 'output.log').read_text(errors='replace')[-12000:], flush=True)
    raise SystemExit(proc.returncode)
