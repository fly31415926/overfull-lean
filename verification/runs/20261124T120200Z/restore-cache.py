#!/usr/bin/env python3
"""Retry only required cache roots at a reduced request rate, then unpack under the build lock."""
import fcntl
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
RUN = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('run_setup', RUN / 'setup.py')
setup = importlib.util.module_from_spec(spec)
spec.loader.exec_module(setup)
tools = RUN / 'setup' / 'rate-limited-tools'
tools.mkdir(exist_ok=True)
wrapper = tools / 'curl'
wrapper.write_text('#!/bin/sh\nexec /usr/bin/curl --parallel-max 2 --rate 5/s "$@"\n')
wrapper.chmod(0o755)
setup.ENV['PATH'] = str(tools) + ':' + setup.ENV['PATH']
roots = json.loads((RUN / 'setup' / 'mathlib-cache-roots.json').read_text())
result = setup.execute('mathlib-required-cache', ['lake', 'exe', 'cache', 'get-', *roots])
if result:
    raise SystemExit(result)
with (RUN / 'build.lock').open('a') as lock:
    fcntl.flock(lock, fcntl.LOCK_EX)
    raise SystemExit(setup.execute('mathlib-cache-unpack', ['lake', 'exe', 'cache', 'unpack']))
