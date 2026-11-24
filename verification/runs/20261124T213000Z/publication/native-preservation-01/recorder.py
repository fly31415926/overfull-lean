#!/usr/bin/env python3
"""Append genuine publication-stage command evidence without changing frozen controls."""
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import time
import traceback

PUB = Path(__file__).resolve().parent
ROOT = PUB.parents[3]
SOURCE = Path(__file__).read_bytes()
if len(sys.argv) < 3 or not re.fullmatch(r"native-[A-Za-z0-9_-]+", sys.argv[1]):
    raise SystemExit("usage: record-command.py native-UNIQUE COMMAND [ARG ...]")
name, command = sys.argv[1], sys.argv[2:]
folder = PUB / name
folder.mkdir(exist_ok=False)
(folder / "recorder.py").write_bytes(SOURCE)
env = os.environ.copy()
env["GIT_TERMINAL_PROMPT"] = "0"
record = {"schema_version": 1, "kind": "genuine_native_publication_command",
          "attempt": name, "command": command, "cwd": str(ROOT),
          "environment_overrides": {"GIT_TERMINAL_PROMPT": "0"},
          "recorder_sha256": hashlib.sha256(SOURCE).hexdigest(),
          "started_at_utc": datetime.now(timezone.utc).isoformat(),
          "status": "running", "process_started": False, "exit_code": None,
          "received_signals": [], "process_group_signals": [], "wrapper_errors": []}
tick = time.monotonic()
proc = None


def write_record(path):
    path.write_text(json.dumps(record, indent=2) + "\n")


def signal_received(signum, _frame):
    record["received_signals"].append(signum)
    raise KeyboardInterrupt(f"received signal {signum}")


def stop_child():
    if proc is None or proc.poll() is not None:
        return
    for signum in [signal.SIGTERM, signal.SIGKILL]:
        try:
            os.killpg(proc.pid, signum)
            record["process_group_signals"].append(int(signum))
        except ProcessLookupError:
            pass
        try:
            proc.wait(timeout=10)
            return
        except subprocess.TimeoutExpired:
            pass
    raise RuntimeError("Child process group did not terminate")


signal.signal(signal.SIGINT, signal_received)
signal.signal(signal.SIGTERM, signal_received)
write_record(folder / "command.json")
print("Starting", name, command, flush=True)
with (folder / "output.log").open("wb") as log:
    try:
        proc = subprocess.Popen(command, cwd=ROOT, env=env, stdout=log,
                                stderr=subprocess.STDOUT, start_new_session=True)
        record.update(process_started=True, pid=proc.pid)
        write_record(folder / "command.json")
        proc.wait()
    except BaseException:
        record["wrapper_errors"].append(traceback.format_exc())
        try:
            stop_child()
        except BaseException:
            record["wrapper_errors"].append(traceback.format_exc())
data = (folder / "output.log").read_bytes()
actual_exit = proc.returncode if proc is not None else None
passed = record["process_started"] and actual_exit == 0 and not record["wrapper_errors"]
wrapper_exit = 0 if passed else (actual_exit if actual_exit and actual_exit > 0 else 1)
record.update(finished_at_utc=datetime.now(timezone.utc).isoformat(),
              elapsed_seconds=time.monotonic() - tick, exit_code=actual_exit,
              wrapper_exit_code=wrapper_exit, status="passed" if passed else "failed",
              output_sha256=hashlib.sha256(data).hexdigest(), output_bytes=len(data))
write_record(folder / "command.json")
write_record(folder / "terminal.json")
print(json.dumps(record, indent=2), flush=True)
print(data.decode(errors="replace")[-4000:], flush=True)
raise SystemExit(wrapper_exit)
