#!/usr/bin/env python3
"""Record genuine focused compiler output and the exact target source bytes."""
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

RUN = Path(__file__).resolve().parent
ROOT = RUN.parents[2]


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    label, *command = sys.argv[1:]
    if not label or "/" in label or not command:
        raise SystemExit("Expected a unique label followed by a command")
    folder = RUN / "focused" / label
    folder.mkdir(parents=True, exist_ok=False)
    sources = {}
    for arg in command:
        path = ROOT / arg
        if arg.endswith(".lean") and path.is_file():
            relative = path.relative_to(ROOT).as_posix()
            data = path.read_bytes()
            sources[relative] = sha(data)
            target = folder / "source" / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
    recorder = Path(__file__).read_bytes()
    (folder / "recorder.py").write_bytes(recorder)
    receipt = {"command": command, "cwd": str(ROOT),
               "started_at_utc": datetime.now(timezone.utc).isoformat(),
               "source_sha256": sources, "recorder_sha256": sha(recorder),
               "status": "running", "exit_code": None}
    metadata = folder / "command.json"
    metadata.write_text(json.dumps(receipt, indent=2) + "\n")
    env = os.environ.copy()
    env["PATH"] = "/home/agent/.elan/bin:" + env["PATH"]
    env["LEAN_NUM_THREADS"] = "2"
    env["MATHLIB_NO_CACHE_ON_UPDATE"] = "1"
    tick = time.monotonic()
    with (folder / "output.log").open("wb") as log:
        process = subprocess.run(command, cwd=ROOT, env=env,
                                 stdout=log, stderr=subprocess.STDOUT)
    changed = [p for p, digest in sources.items()
               if sha((ROOT / p).read_bytes()) != digest]
    passed = process.returncode == 0 and not changed
    receipt.update({"finished_at_utc": datetime.now(timezone.utc).isoformat(),
                    "elapsed_seconds": time.monotonic() - tick,
                    "exit_code": process.returncode,
                    "status": "passed" if passed else "failed",
                    "changed_sources": changed,
                    "output_sha256": sha((folder / "output.log").read_bytes())})
    metadata.write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, indent=2), flush=True)
    print((folder / "output.log").read_text(errors="replace")[-12000:], flush=True)
    raise SystemExit(0 if passed else (process.returncode or 1))


if __name__ == "__main__":
    main()
