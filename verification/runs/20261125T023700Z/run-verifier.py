#!/usr/bin/env python3
"""Freeze all inputs, execute the genuine full verifier, and check preservation."""
from datetime import datetime, timezone
import gzip
import hashlib
import importlib.util
import io
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tarfile
import time
import traceback

sys.dont_write_bytecode = True
RUN = Path(__file__).resolve().parent
ROOT = RUN.parents[2]
CHECKER = RUN / "check-preservation.py"
spec = importlib.util.spec_from_file_location("preservation", CHECKER)
checks = importlib.util.module_from_spec(spec)
exec(compile(CHECKER.read_bytes(), str(CHECKER), "exec"), checks.__dict__)


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def archive(path, files):
    with path.open("wb") as raw, gzip.GzipFile(fileobj=raw, mode="wb", mtime=0, filename="") as gz:
        with tarfile.open(fileobj=gz, mode="w|") as tar:
            for name, data in sorted(files.items()):
                info = tarfile.TarInfo(name)
                info.size, info.mode, info.mtime = len(data), 0o644, 0
                tar.addfile(info, io.BytesIO(data))


def main():
    label = sys.argv[1] if len(sys.argv) == 2 else "full-01"
    if not label.startswith("full-") or "/" in label:
        raise SystemExit("Expected a unique full-NN attempt label")
    folder = RUN / label
    folder.mkdir(exist_ok=False)
    tick = time.monotonic()
    receipt = {"command": ["python3", "scripts/verify.py"], "cwd": str(ROOT),
               "started_at_utc": datetime.now(timezone.utc).isoformat(),
               "baseline_commit": checks.BASELINE, "baseline_tree": checks.TREE,
               "verifier_launched": False, "exit_code": None, "status": "running"}
    write(folder / "command.json", receipt)
    (folder / "output.log").write_bytes(b"")
    frozen, controls, outputs, errors = {}, {}, {}, []
    process, started_ns, preserved = None, None, None
    try:
        inputs = checks.current_inputs()
        control_bytes = checks.current_controls()
        frozen = {p: checks.sha(data) for p, data in inputs.items()}
        controls = {p: checks.sha(data) for p, data in control_bytes.items()}
        write(folder / "frozen-inputs.json", frozen)
        write(folder / "frozen-controls.json", controls)
        archive(folder / "frozen-inputs.tar.gz", inputs)
        archive(folder / "frozen-controls.tar.gz", control_bytes)
        write(folder / "preflight.json", checks.preflight(inputs))
        env = os.environ.copy()
        env["PATH"] = "/home/agent/.elan/bin:" + env["PATH"]
        env["LEAN_NUM_THREADS"] = "2"
        with (folder / "output.log").open("wb") as log:
            started_ns = time.time_ns()
            process = subprocess.Popen(receipt["command"], cwd=ROOT, env=env,
                                       stdout=log, stderr=subprocess.STDOUT, start_new_session=True)
            receipt["verifier_launched"] = True
            write(folder / "command.json", receipt)
            print(f"Running full verifier on {len(frozen)} frozen inputs", flush=True)
            process.wait()
        if process.returncode == 0:
            preserved = checks.final_checks()
            write(folder / "preservation.json", preserved)
    except BaseException:
        errors.append(traceback.format_exc())
        if process is not None and process.poll() is None:
            try:
                os.killpg(process.pid, signal.SIGTERM)
                process.wait(timeout=10)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait(timeout=10)
    after = {p: checks.sha(data) for p, data in checks.current_inputs().items()}
    after_controls = {p: checks.sha(data) for p, data in checks.current_controls().items()}
    if started_ns is not None:
        for path in sorted((ROOT / "verification").iterdir()):
            if path.is_file() and path.suffix in {".json", ".log"} and path.stat().st_mtime_ns >= started_ns:
                outputs[path.relative_to(ROOT).as_posix()] = path.read_bytes()
    archive(folder / "outputs.tar.gz", outputs)
    output_hashes = {p: checks.sha(data) for p, data in outputs.items()}
    write(folder / "outputs.json", output_hashes)
    required = {"verification/results.json", "verification/build.log", "verification/axioms.log", checks.NEW_MAP}
    missing = sorted(required - outputs.keys())
    passed = (process is not None and process.returncode == 0 and not errors
              and frozen == after and controls == after_controls and preserved is not None and not missing)
    receipt.update({"finished_at_utc": datetime.now(timezone.utc).isoformat(),
                    "elapsed_seconds": time.monotonic() - tick,
                    "exit_code": process.returncode if process is not None else None,
                    "status": "passed" if passed else "failed",
                    "frozen_input_count": len(frozen), "frozen_control_count": len(controls),
                    "output_count": len(outputs), "missing_required_outputs": missing,
                    "inputs_unchanged": frozen == after, "controls_unchanged": controls == after_controls,
                    "changed_inputs": sorted(p for p in frozen.keys() | after.keys() if frozen.get(p) != after.get(p)),
                    "changed_controls": sorted(p for p in controls.keys() | after_controls.keys()
                                               if controls.get(p) != after_controls.get(p)),
                    "output_sha256": checks.sha((folder / "output.log").read_bytes()),
                    "archives": {p.name: checks.sha(p.read_bytes()) for p in folder.glob("*.tar.gz")},
                    "wrapper_errors": errors, "preservation": preserved})
    write(folder / "command.json", receipt)
    write(folder / "terminal.json", receipt)
    print(json.dumps(receipt, indent=2), flush=True)
    print((folder / "output.log").read_text(errors="replace")[-5000:], flush=True)
    raise SystemExit(0 if passed else 1)


if __name__ == "__main__":
    main()
