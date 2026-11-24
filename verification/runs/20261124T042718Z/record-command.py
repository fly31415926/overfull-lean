"""Record a genuine focused command with source identity and immutable attempts."""
from pathlib import Path
from datetime import datetime, timezone
import fcntl
import hashlib
import json
import os
import subprocess
import sys
import time

RUN = Path(__file__).resolve().parent
ROOT = RUN.parents[2]
name, *command = sys.argv[1:]
if not command:
    raise SystemExit("usage: record-command.py ATTEMPT COMMAND ...")
folder = RUN / "development" / name
folder.mkdir(parents=True, exist_ok=False)
env = os.environ.copy()
env["PATH"] = "/workspace/scratch/5d2e6f7b5492/lean-runtime/lean-4.24.0-linux/bin:" + env["PATH"]
with (RUN / "build.lock").open("a") as lock:
    fcntl.flock(lock, fcntl.LOCK_EX)
    snapshots = {}
    dependencies = {}
    for path in sorted((ROOT / "Overfull").rglob("*.lean")):
        data = path.read_bytes()
        rel = path.relative_to(ROOT).as_posix()
        dependencies[rel] = hashlib.sha256(data).hexdigest()
        if rel.startswith(("Overfull/ThreeCoreReduction/", "Overfull/AuxiliarySimple/", "Overfull/TerminalFourOdd/", "Overfull/CompatibleCircuits/FourAdmissible")):
            target = folder / "source" / rel
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
            snapshots[rel] = dependencies[rel]
    for rel in ["Overfull.lean", "Audit.lean", "lakefile.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain"]:
        path = ROOT / rel
        if path.exists():
            dependencies[rel] = hashlib.sha256(path.read_bytes()).hexdigest()
    start = datetime.now(timezone.utc)
    tick = time.monotonic()
    record = {
        "command": command, "cwd": str(ROOT), "started_at_utc": start.isoformat(),
        "source_sha256": snapshots, "input_sha256": dependencies,
        "status": "running", "exit_code": None,
        "baseline_verified_local_commit": "14978e4dec2bce94f63953df7b1bdd54f61c3e6c",
        "recorder_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    receipt = folder / "command.json"
    receipt.write_text(json.dumps(record, indent=2) + "\n")
    print("Starting", name, command, flush=True)
    with (folder / "output.log").open("wb") as log:
        proc = subprocess.run(command, cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT)
    end = datetime.now(timezone.utc)
    changed = [rel for rel, digest in dependencies.items()
               if not (ROOT / rel).is_file()
               or hashlib.sha256((ROOT / rel).read_bytes()).hexdigest() != digest]
    record.update({
        "finished_at_utc": end.isoformat(), "elapsed_seconds": time.monotonic() - tick,
        "exit_code": proc.returncode, "status": "passed" if proc.returncode == 0 else "failed",
        "inputs_changed_during_command": changed,
    })
    receipt.write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps({k: v for k, v in record.items()
                     if k not in ("source_sha256", "input_sha256")}, indent=2), flush=True)
    print((folder / "output.log").read_text(errors="replace")[-12000:], flush=True)
    sys.exit(proc.returncode)
