#!/usr/bin/env python3
"""Record an actual supplementary checker invocation without self-changing evidence.

The child's temporary output is outside the run until the checker finishes.
Failed attempts are retained verbatim. Success aliases are created only from
the actual successful invocation and are supplementary evidence after its freeze.
"""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time

RUN = Path(__file__).resolve().parent
ROOT = RUN.parents[2]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    attempt = sys.argv[1] if len(sys.argv) == 2 else "preservation-check-01"
    if len(sys.argv) > 2 or re.fullmatch(r"preservation-check-[A-Za-z0-9-]+", attempt) is None:
        raise SystemExit("Usage: record-preservation.py [preservation-check-NN]")
    folder = RUN / attempt
    if folder.exists():
        raise SystemExit("Refusing to overwrite an actual supplementary attempt")
    source = (RUN / "record-final.py").read_bytes()
    command = ["python3", str(RUN / "record-final.py")]
    started, tick = datetime.now(timezone.utc), time.monotonic()
    with tempfile.TemporaryDirectory(prefix=RUN.name + "-preservation-", dir=ROOT.parent) as temp:
        output = Path(temp) / "output.log"
        with output.open("wb") as log:
            result = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
        finished = datetime.now(timezone.utc)
        folder.mkdir()
        (folder / "output.log").write_bytes(output.read_bytes())
    (folder / "record-final.py").write_bytes(source)
    unchanged = source == (RUN / "record-final.py").read_bytes()
    status = "passed" if result.returncode == 0 and unchanged else "failed"
    record = {"command": command, "cwd": str(ROOT), "started_at_utc": started.isoformat(),
              "finished_at_utc": finished.isoformat(), "elapsed_seconds": time.monotonic() - tick,
              "status": status, "exit_code": result.returncode,
              "all_frozen_inputs_unchanged": unchanged,
              "checker_sha256": hashlib.sha256(source).hexdigest(),
              "output_sha256": sha(folder / "output.log"),
              "evidence_written_after_checker_completed": True}
    if status == "passed":
        record["preservation_report_sha256"] = sha(RUN / "preservation.json")
    (folder / "command.json").write_text(json.dumps(record, indent=2) + "\n")
    if status == "passed":
        (RUN / "record-final-output.log").write_bytes((folder / "output.log").read_bytes())
        (RUN / "record-final-command.json").write_text(json.dumps(record, indent=2) + "\n")
        paths = [folder / name for name in ["command.json", "output.log", "record-final.py"]]
        paths += [RUN / "record-final-command.json", RUN / "record-final-output.log"]
        (RUN / "supplementary-evidence-after-freeze.json").write_text(json.dumps({
            "recorded_at_utc": datetime.now(timezone.utc).isoformat(),
            "kind": "actual_checker_command_and_output_recorded_after_successful_evidence_freeze",
            "preservation_report_sha256": record["preservation_report_sha256"],
            "files": {path.relative_to(ROOT).as_posix(): sha(path) for path in paths},
        }, indent=2) + "\n")
    print((folder / "output.log").read_text(errors="replace"), end="", flush=True)
    print(json.dumps(record, indent=2), flush=True)
    sys.exit(result.returncode if result.returncode else (0 if unchanged else 1))


if __name__ == "__main__":
    main()
