#!/usr/bin/env python3
"""Await one actual verifier process, retaining its output and observed exit.

Thirty-second heartbeats are observations, never substitutes for completion.
Every supervisor invocation has a fresh directory, including preflight failures.
"""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import time

sys.dont_write_bytecode = True
RUN = Path(__file__).resolve().parent
ROOT = RUN.parents[2]


def main() -> None:
    attempt = sys.argv[1] if len(sys.argv) == 2 else "full-01"
    if len(sys.argv) > 2 or re.fullmatch(r"full-[A-Za-z0-9-]+", attempt) is None:
        raise SystemExit("Usage: supervise-verifier.py [full-NN]")
    folder = RUN / "supervision" / attempt
    folder.mkdir(parents=True, exist_ok=False)
    started = datetime.now(timezone.utc)
    command = [sys.executable, "-u", str(RUN / "run-verifier.py"), attempt]
    log_path = folder / "runner-output.log"
    printed_bytes = 0
    with log_path.open("wb") as runner_log:
        proc = subprocess.Popen(command, cwd=ROOT, stdout=runner_log, stderr=subprocess.STDOUT)

        def observe(status, code=None):
            nonlocal printed_bytes
            output = log_path.read_bytes()
            if len(output) > printed_bytes:
                print(output[printed_bytes:].decode(errors="replace"), end="", flush=True)
                printed_bytes = len(output)
            data = {"observed_at_utc": datetime.now(timezone.utc).isoformat(),
                    "supervisor_started_at_utc": started.isoformat(), "command": command,
                    "cwd": str(ROOT), "attempt": attempt, "process_status": status,
                    "observed_return_code": code, "observed_child_pid": proc.pid,
                    "supervisor_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                    "runner_output_path": log_path.relative_to(ROOT).as_posix(),
                    "runner_output_bytes": len(output)}
            receipt = RUN / attempt / "command.json"
            if receipt.is_file():
                try:
                    current = json.loads(receipt.read_text())
                except json.JSONDecodeError:
                    data["command_receipt_observation"] = "writer update in progress"
                else:
                    data.update({key: current.get(key) for key in [
                        "started_at_utc", "status", "exit_code", "candidate_input_hash_count",
                        "finished_at_utc", "all_frozen_inputs_unchanged",
                        "all_control_files_unchanged"]})
            stages = {}
            for name in ["vizing-source.log", "lean-version.log", "build.log", "axioms.log"]:
                path = ROOT / "verification" / name
                if path.is_file() and path.stat().st_mtime >= started.timestamp():
                    stages[name] = {"bytes": path.stat().st_size,
                                    "observed_final_line": path.read_text(errors="replace").splitlines()[-1:]}
            data["fresh_stage_log_observations"] = stages
            console = RUN / attempt / "output.log"
            if console.is_file():
                data["verifier_console_bytes"] = console.stat().st_size
            encoded = json.dumps(data, indent=2) + "\n"
            for path in [folder / "heartbeat.json", RUN / "execution-heartbeat.json"]:
                path.write_text(encoded)
            for path in [folder / "heartbeat.log", RUN / "execution-heartbeat.log"]:
                with path.open("a") as stream:
                    stream.write(json.dumps(data) + "\n")
            print(json.dumps(data), flush=True)
            return data

        last = 0.0
        while True:
            code = proc.poll()
            if code is not None:
                terminal = observe("completed", code)
                terminal.update({"actual_terminal_exit_code": code,
                                 "terminal_observed_at_utc": datetime.now(timezone.utc).isoformat(),
                                 "runner_output_sha256": hashlib.sha256(log_path.read_bytes()).hexdigest()})
                encoded = json.dumps(terminal, indent=2) + "\n"
                for path in [folder / "terminal.json", RUN / "execution-terminal.json"]:
                    path.write_text(encoded)
                break
            if time.monotonic() - last >= 30:
                observe("running")
                last = time.monotonic()
            time.sleep(1)
    sys.exit(code)


if __name__ == "__main__":
    main()
