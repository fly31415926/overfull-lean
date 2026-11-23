#!/usr/bin/env python3
"""Preserve an actual strict targeted check of the recreated constructor."""
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

RUN = Path(__file__).resolve().parent
ROOT = RUN.parents[2]
SOURCE = ROOT / "Overfull/AssignedParts/Basic.lean"
tag = sys.argv[1]
snapshot = RUN / f"{tag}-source.lean.txt"
if snapshot.exists():
    raise SystemExit("Refusing to overwrite an earlier source snapshot")
snapshot.write_bytes(SOURCE.read_bytes())
digest = hashlib.sha256(snapshot.read_bytes()).hexdigest()
command = ["lake", "build", "--wfail", "Overfull.AssignedParts.Basic"]
env = dict(os.environ)
env["PATH"] = str(ROOT.parent / "lean-runtime/lean-4.24.0-linux/bin") + ":" + env["PATH"]
started = datetime.now(timezone.utc)
with (RUN / f"{tag}.log").open("wb") as log:
    result = subprocess.run(command, cwd=ROOT, env=env,
                            stdout=log, stderr=subprocess.STDOUT)
finished = datetime.now(timezone.utc)
record = {
    "command": command,
    "cwd": str(ROOT),
    "started_at_utc": started.isoformat(),
    "finished_at_utc": finished.isoformat(),
    "elapsed_seconds": round((finished - started).total_seconds(), 3),
    "exit_code": result.returncode,
    "source_path": str(SOURCE.relative_to(ROOT)),
    "source_sha256": digest,
    "source_snapshot": snapshot.name,
    "source_unchanged_during_check": hashlib.sha256(SOURCE.read_bytes()).hexdigest() == digest,
    "log": f"{tag}.log",
}
(RUN / f"{tag}.json").write_text(json.dumps(record, indent=2) + "\n")
print(json.dumps(record, indent=2))
print((RUN / f"{tag}.log").read_text()[-18000:])
raise SystemExit(result.returncode if result.returncode else
                 (0 if record["source_unchanged_during_check"] else 1))
