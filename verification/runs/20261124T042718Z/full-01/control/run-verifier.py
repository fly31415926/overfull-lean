#!/usr/bin/env python3
"""Freeze all verifier inputs, run the actual verifier, and retain genuine outputs."""
from datetime import datetime, timezone
import fcntl
import importlib.util
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time
import traceback

sys.dont_write_bytecode = True
RUN = Path(__file__).resolve().parent
ROOT = RUN.parents[2]
spec = importlib.util.spec_from_file_location("preservation", RUN / "check-preservation.py")
checks = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checks)


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def stop_process(proc):
    """Stop this command's process group without leaving a detached Lean build."""
    if proc is None or proc.poll() is not None:
        return
    try:
        os.killpg(proc.pid, signal.SIGTERM)
    except ProcessLookupError:
        pass
    try:
        proc.wait(timeout=10)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        proc.wait(timeout=10)


def main():
    attempt = sys.argv[1] if len(sys.argv) == 2 else "full-01"
    if not attempt.startswith("full-") or "/" in attempt:
        raise SystemExit("Expected a unique full-NN attempt name")
    with (RUN / "build.lock").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        folder = RUN / attempt
        folder.mkdir(exist_ok=False)
        started = datetime.now(timezone.utc)
        tick = time.monotonic()
        receipt = {"command": ["python3", "scripts/verify.py"], "cwd": str(ROOT),
                   "attempt": attempt, "started_at_utc": started.isoformat(),
                   "baseline_commit": checks.BASELINE, "baseline_tree": checks.TREE,
                   "frozen_input_count": 0, "control_sha256": {},
                   "verifier_launched": False, "preflight_passed": False,
                   "status": "running", "exit_code": None}
        # Create evidence before preflight so a rejected or interrupted attempt is
        # retained honestly. A command not launched never receives a made-up exit.
        (folder / "output.log").write_bytes(b"")
        write(folder / "command.json", receipt)
        frozen, controls, errors = {}, {}, []
        proc, started_ns, after, after_controls = None, None, None, None
        stage = "freeze"
        try:
            inputs = checks.current_inputs()
            control_data = checks.current_controls()
            frozen = {p: checks.sha(data) for p, data in inputs.items()}
            controls = {name: checks.sha(data) for name, data in control_data.items()}
            receipt.update({"frozen_input_count": len(frozen), "control_sha256": controls})
            write(folder / "frozen-inputs.json", frozen)
            write(folder / "frozen-controls.json", controls)
            for name, data in inputs.items():
                target = folder / "input" / name
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(data)
            for name, data in control_data.items():
                target = folder / "control" / name
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(data)
            stage = "preflight"
            write(folder / "baseline-preflight.json", checks.preflight(inputs))
            receipt["preflight_passed"] = True
            env = os.environ.copy()
            env["PATH"] = "/workspace/scratch/5d2e6f7b5492/lean-runtime/lean-4.24.0-linux/bin:" + env["PATH"]
            print(f"Starting complete verifier {attempt}, {len(frozen)} fully snapshotted inputs", flush=True)
            stage = "verifier"
            with (folder / "output.log").open("wb") as log:
                started_ns = time.time_ns()
                receipt["verifier_started_at_utc"] = datetime.now(timezone.utc).isoformat()
                proc = subprocess.Popen(receipt["command"], cwd=ROOT, env=env,
                                        stdout=log, stderr=subprocess.STDOUT,
                                        start_new_session=True)
                receipt["verifier_launched"] = True
                write(folder / "command.json", receipt)
                proc.wait()
        except BaseException:
            errors.append({"stage": stage, "traceback": traceback.format_exc()})
            try:
                stop_process(proc)
            except BaseException:
                errors.append({"stage": "terminate verifier", "traceback": traceback.format_exc()})

        # Final evidence collection is best-effort on a failed attempt. Any
        # collection exception makes the wrapper fail, even if the child exited 0.
        try:
            after = {p: checks.sha(data) for p, data in checks.current_inputs().items()}
        except BaseException:
            errors.append({"stage": "compare inputs", "traceback": traceback.format_exc()})
        try:
            after_controls = {name: checks.sha(data) for name, data in checks.current_controls().items()}
        except BaseException:
            errors.append({"stage": "compare controls", "traceback": traceback.format_exc()})
        outputs = []
        if receipt["verifier_launched"]:
            try:
                for path in sorted((ROOT / "verification").iterdir()):
                    if not path.is_file() or path.stat().st_mtime_ns < started_ns:
                        continue
                    if path.suffix not in {".json", ".log"}:
                        continue
                    relative = path.relative_to(ROOT).as_posix()
                    data = path.read_bytes()
                    target = folder / "artifacts" / relative
                    target.parent.mkdir(parents=True, exist_ok=True)
                    target.write_bytes(data)
                    outputs.append({"path": relative, "sha256": checks.sha(data), "bytes": len(data)})
            except BaseException:
                errors.append({"stage": "archive outputs", "traceback": traceback.format_exc()})
        unchanged = after is not None and frozen == after
        controls_unchanged = after_controls is not None and controls == after_controls
        missing = sorted(checks.PRINCIPAL_OUTPUTS - {entry["path"] for entry in outputs})
        actual_exit = proc.returncode if proc is not None else None
        passed = (receipt["verifier_launched"] and receipt["preflight_passed"]
                  and actual_exit == 0 and not errors and unchanged and controls_unchanged and not missing)
        receipt.update({"finished_at_utc": datetime.now(timezone.utc).isoformat(),
                        "elapsed_seconds": time.monotonic() - tick, "exit_code": actual_exit,
                        "inputs_unchanged": unchanged, "controls_unchanged": controls_unchanged,
                        "changed_inputs": None if after is None else sorted(
                            p for p in frozen.keys() | after.keys() if frozen.get(p) != after.get(p)),
                        "changed_controls": None if after_controls is None else sorted(
                            p for p in controls.keys() | after_controls.keys()
                            if controls.get(p) != after_controls.get(p)),
                        "outputs": outputs, "missing_principal_outputs": missing,
                        "wrapper_errors": errors,
                        "output_sha256": checks.sha((folder / "output.log").read_bytes()),
                        "status": "passed" if passed else "failed"})
        if errors:
            (folder / "wrapper-errors.log").write_text("\n".join(
                f"Stage: {error['stage']}\n{error['traceback']}" for error in errors))
            receipt["wrapper_errors_sha256"] = checks.sha((folder / "wrapper-errors.log").read_bytes())
        receipt["wrapper_exit_code"] = 0 if passed else (actual_exit if actual_exit and actual_exit > 0 else 1)
        write(folder / "command.json", receipt)
        write(folder / "terminal.json", receipt)
        print(json.dumps({k: v for k, v in receipt.items() if k != "outputs"}, indent=2), flush=True)
        print((folder / "output.log").read_text(errors="replace")[-5000:], flush=True)
        sys.exit(receipt["wrapper_exit_code"])


if __name__ == "__main__":
    main()
