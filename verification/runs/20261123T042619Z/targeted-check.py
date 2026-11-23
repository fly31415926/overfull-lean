#!/usr/bin/env python3
"""Preserve an actual strict module check and the exact source it checked."""

from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time


run = Path(__file__).resolve().parent
root = run.parents[2]
tag, module = sys.argv[1:]
source = root / (module.replace(".", "/") + ".lean")
snapshot = run / (tag + ".lean")
if snapshot.exists():
    raise SystemExit("Refusing to overwrite an earlier source snapshot")
data = source.read_bytes()
snapshot.write_bytes(data)
command = ["lake", "build", "--wfail", module]
started = datetime.now(timezone.utc).isoformat()
tick = time.monotonic()
with (run / (tag + ".log")).open("w") as output:
    result = subprocess.run(command, cwd=root, stdout=output, stderr=subprocess.STDOUT)
record = {
    "command": command,
    "started_at_utc": started,
    "completed_at_utc": datetime.now(timezone.utc).isoformat(),
    "elapsed_seconds": round(time.monotonic() - tick, 3),
    "exit_code": result.returncode,
    "source_sha256": hashlib.sha256(data).hexdigest(),
    "source_unchanged_during_check": source.read_bytes() == data,
    "source_snapshot": snapshot.name,
    "log": tag + ".log",
}
(run / (tag + ".json")).write_text(json.dumps(record, indent=2) + "\n")
print(json.dumps(record))
print((run / (tag + ".log")).read_text()[-16000:])
raise SystemExit(result.returncode or (0 if record["source_unchanged_during_check"] else 1))
