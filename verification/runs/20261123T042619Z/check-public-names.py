#!/usr/bin/env python3
"""Resolve each mapped public proof name using the freshly compiled imports."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess
import time

RUN = Path(__file__).resolve().parent
ROOT = RUN.parents[2]
manifests = [ROOT / "docs" / (name + "-source.json")
             for name in ("joining-circuit", "assigned-part")]
before = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
          for p in manifests}
names = [n for p in manifests
         for n in json.loads(p.read_text())["required_proof_declarations"]]
assert len(names) == len(set(names))
source = RUN / "public-name-check.lean"
source.write_text("import Overfull.AssignedParts.JoiningConstruction\n\n" +
                  "\n".join("#check " + n for n in sorted(names)) + "\n")
source_bytes = source.read_bytes()
command = ["lake", "env", "lean", str(source.relative_to(ROOT))]
started = datetime.now(timezone.utc).isoformat()
tick = time.monotonic()
with (RUN / "public-name-check.log").open("wb") as output:
    process = subprocess.run(command, cwd=ROOT, stdout=output, stderr=subprocess.STDOUT)
unchanged = source.read_bytes() == source_bytes and all(
    hashlib.sha256((ROOT / p).read_bytes()).hexdigest() == sha
    for p, sha in before.items())
record = {
    "command": command,
    "started_at_utc": started,
    "completed_at_utc": datetime.now(timezone.utc).isoformat(),
    "elapsed_seconds": round(time.monotonic() - tick, 3),
    "exit_code": process.returncode,
    "mapped_public_name_count": len(names),
    "manifest_sha256": before,
    "source_sha256": hashlib.sha256(source_bytes).hexdigest(),
    "source_snapshot": source.name,
    "source_unchanged_during_check": unchanged,
    "log": "public-name-check.log",
}
(RUN / "public-name-check.json").write_text(json.dumps(record, indent=2) + "\n")
print(json.dumps(record, indent=2))
raise SystemExit(process.returncode or (0 if unchanged else 1))
