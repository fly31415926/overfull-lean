#!/usr/bin/env python3
"""Record the real frozen-runner preflight without invoking Lean or freezing.

This checks candidate identity and exact promotion prerequisites only. A later
attached complete verifier and axiom audit remain necessary.
"""
from datetime import datetime, timezone
import fcntl
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time

RUN = Path(__file__).resolve().parent
ROOT = RUN.parents[2]


def main():
    attempt = sys.argv[1] if len(sys.argv) == 2 else "candidate-preflight-01"
    if len(sys.argv) > 2 or not attempt.startswith("candidate-preflight-") or "/" in attempt:
        raise SystemExit("Usage: check-candidate.py [candidate-preflight-NN]")
    folder = RUN / attempt
    folder.mkdir(exist_ok=False)
    code = (
        "import importlib.util,json,sys;sys.dont_write_bytecode=True;"
        f"p={str(RUN / 'run-verifier.py')!r};"
        "s=importlib.util.spec_from_file_location('terminal_full_runner',p);"
        "m=importlib.util.module_from_spec(s);s.loader.exec_module(m);"
        "r=m.baseline_preflight(m.current_inputs());print(json.dumps(r,indent=2))"
    )
    command = ["python3", "-c", code]
    with (RUN / "build.lock").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        started, tick = datetime.now(timezone.utc), time.monotonic()
        with (folder / "output.log").open("wb") as log:
            result = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
        finished = datetime.now(timezone.utc)
        record = {"command": command, "cwd": str(ROOT), "started_at_utc": started.isoformat(),
                  "finished_at_utc": finished.isoformat(), "elapsed_seconds": time.monotonic() - tick,
                  "exit_code": result.returncode, "status": "passed" if result.returncode == 0 else "failed",
                  "kind": "candidate_identity_and_exact_promotion_preflight_only",
                  "lean_build_or_axiom_audit_executed": False,
                  "output_sha256": hashlib.sha256((folder / "output.log").read_bytes()).hexdigest(),
                  "runner_sha256": hashlib.sha256((RUN / "run-verifier.py").read_bytes()).hexdigest(),
                  "checker_sha256": hashlib.sha256((RUN / "record-final.py").read_bytes()).hexdigest()}
        (folder / "command.json").write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps({k: v for k, v in record.items() if k != "command"}, indent=2))
    if result.returncode:
        print((folder / "output.log").read_text(errors="replace"))
    sys.exit(result.returncode)


if __name__ == "__main__":
    main()
