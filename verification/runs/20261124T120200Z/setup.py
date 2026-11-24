#!/usr/bin/env python3
"""Restore pinned dependencies, preserving genuine command output and status."""
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

RUN = Path(__file__).resolve().parent
ROOT = RUN.parents[2]
RUNTIME = Path('/workspace/scratch/77adbfc63087/toolchain/lean-4.24.0-linux/bin')
SETUP = RUN / 'setup'
SETUP.mkdir(exist_ok=True)
ENV = os.environ.copy()
ENV['PATH'] = str(RUNTIME) + ':' + ENV['PATH']


def execute(name, command, cwd=ROOT):
    folder = SETUP / name
    folder.mkdir(exist_ok=False)
    started = datetime.now(timezone.utc).isoformat()
    tick = time.monotonic()
    receipt = {'command': command, 'cwd': str(cwd), 'started_at_utc': started,
               'status': 'running', 'exit_code': None}
    (folder / 'command.json').write_text(json.dumps(receipt, indent=2) + '\n')
    with (folder / 'output.log').open('wb') as log:
        result = subprocess.run(command, cwd=cwd, env=ENV, stdout=log, stderr=subprocess.STDOUT)
    receipt.update({'finished_at_utc': datetime.now(timezone.utc).isoformat(),
                    'elapsed_seconds': time.monotonic() - tick,
                    'exit_code': result.returncode,
                    'status': 'passed' if result.returncode == 0 else 'failed',
                    'output_sha256': hashlib.sha256((folder / 'output.log').read_bytes()).hexdigest()})
    (folder / 'command.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(name, receipt['status'], receipt['elapsed_seconds'], flush=True)
    if result.returncode:
        print((folder / 'output.log').read_text(errors='replace')[-8000:], flush=True)
    return result.returncode


def restore(dep):
    path = ROOT / '.lake/packages' / dep['name']
    path.mkdir(parents=True, exist_ok=False)
    commands = [['git', 'init', '-q', str(path)],
                ['git', '-C', str(path), 'remote', 'add', 'origin', dep['url']],
                ['git', '-C', str(path), 'fetch', '--depth', '1', 'origin', dep['rev']],
                ['git', '-C', str(path), 'checkout', '--detach', 'FETCH_HEAD']]
    for i, command in enumerate(commands):
        if execute(dep['name'] + '-' + str(i), command):
            return False
    actual = subprocess.check_output(['git', '-C', str(path), 'rev-parse', 'HEAD'], text=True).strip()
    clean = subprocess.run(['git', '-C', str(path), 'diff', '--quiet', 'HEAD', '--']).returncode == 0
    result = {'name': dep['name'], 'expected_revision': dep['rev'], 'actual_revision': actual,
              'tracked_sources_clean': clean, 'status': 'passed' if actual == dep['rev'] and clean else 'failed'}
    (SETUP / (dep['name'] + '-revision.json')).write_text(json.dumps(result, indent=2) + '\n')
    return result['status'] == 'passed'


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else 'dependencies'
    if mode == 'dependencies':
        manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
        with ThreadPoolExecutor(max_workers=4) as pool:
            results = list(pool.map(restore, [p for p in manifest['packages'] if p['type'] == 'git']))
        if not all(results):
            return 1
        return execute('vizing', ['python3', 'scripts/setup_vizing.py'])
    if mode == 'cache':
        if execute('lean-version', ['lean', '--version']):
            return 1
        return execute('mathlib-cache', ['lake', 'exe', 'cache', 'get'])
    raise SystemExit('Unknown setup stage')


if __name__ == '__main__':
    raise SystemExit(main())
