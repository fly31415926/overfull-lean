"""Observe one actual complete-verifier process and retain genuine heartbeats."""
from pathlib import Path
from datetime import datetime, timezone
import json
import subprocess
import sys
import time

RUN = Path(__file__).resolve().parent
ROOT = RUN.parents[2]
ATTEMPT = "full-01"
STARTED = datetime.now(timezone.utc)
command = [sys.executable, "-u", str(RUN / "run-verifier.py"), ATTEMPT]
proc = subprocess.Popen(command, cwd=ROOT)


def observe(status, code=None):
    data = {
        "observed_at_utc": datetime.now(timezone.utc).isoformat(),
        "supervisor_started_at_utc": STARTED.isoformat(),
        "command": command, "cwd": str(ROOT), "attempt": ATTEMPT,
        "process_status": status, "observed_return_code": code,
    }
    receipt = RUN / ATTEMPT / "command.json"
    if receipt.is_file():
        current = json.loads(receipt.read_text())
        data.update({k: current.get(k) for k in [
            "started_at_utc", "status", "exit_code", "candidate_input_hash_count",
            "finished_at_utc", "all_frozen_inputs_unchanged",
        ]})
    build = ROOT / "verification/build.log"
    if build.is_file() and build.stat().st_mtime >= STARTED.timestamp():
        tail = build.read_text(errors="replace").splitlines()[-1:]
        data["fresh_strict_build_final_line"] = tail[0] if tail else ""
    (RUN / "execution-heartbeat.json").write_text(json.dumps(data, indent=2) + "\n")
    with (RUN / "execution-heartbeat.log").open("a") as log:
        log.write(json.dumps(data) + "\n")
    print(json.dumps(data), flush=True)
    return data


last = 0.0
while True:
    code = proc.poll()
    if code is not None:
        terminal = observe("completed", code)
        terminal["actual_terminal_exit_code"] = code
        terminal["terminal_observed_at_utc"] = datetime.now(timezone.utc).isoformat()
        (RUN / "execution-terminal.json").write_text(json.dumps(terminal, indent=2) + "\n")
        break
    if time.monotonic() - last >= 30:
        observe("running")
        last = time.monotonic()
    time.sleep(1)
sys.exit(code)
