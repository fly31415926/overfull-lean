#!/usr/bin/env python3
"""Index and check actual retained attempts; never reconstruct compiler output."""
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
RUN = HERE.parent
ROOT = RUN.parents[2]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    attempts = []
    counts = Counter()
    for path in sorted((RUN / "focused").glob("*/command.json")):
        data = json.loads(path.read_text())
        folder = path.parent
        assert data["status"] in {"passed", "failed"}, path
        assert (data["status"] == "passed") == (
            data["exit_code"] == 0 and not data["changed_sources"]), path
        assert sha(folder / "output.log") == data["output_sha256"], path
        assert sha(folder / "recorder.py") == data["recorder_sha256"], path
        snapshots = []
        for source, expected in sorted(data["source_sha256"].items()):
            saved = folder / "source" / source
            assert saved.is_file() and sha(saved) == expected, saved
            snapshots.append({"source_path": source,
                              "saved_snapshot": saved.relative_to(ROOT).as_posix(),
                              "sha256": expected})
        actual = {p.relative_to(folder / "source").as_posix()
                  for p in (folder / "source").rglob("*.lean")}
        assert actual == set(data["source_sha256"]), path
        counts[data["status"]] += 1
        attempts.append({"attempt": folder.name, "status": data["status"],
                         "exit_code": data["exit_code"], "command": data["command"],
                         "elapsed_seconds": data["elapsed_seconds"],
                         "changed_sources": data["changed_sources"],
                         "receipt_path": path.relative_to(ROOT).as_posix(),
                         "receipt_sha256": sha(path),
                         "output_sha256": data["output_sha256"],
                         "recorder_sha256": data["recorder_sha256"],
                         "source_snapshots": snapshots})
    result = {"schema_version": 1, "indexed_at_utc": datetime.now(timezone.utc).isoformat(),
              "scope": "Checks and indexes retained execution receipts, logs, recorders and saved source bytes; does not rerun Lean or replace full verification.",
              "total_attempts": len(attempts), "status_counts": dict(counts),
              "all_outputs_and_recorders_match_recorded_hashes": True,
              "all_saved_sources_match_recorded_hashes": True,
              "source_snapshot_count": sum(len(a["source_snapshots"]) for a in attempts),
              "attempts": attempts}
    target = HERE / "focused-evidence-index.json"
    assert not target.exists(), "Never overwrite a prior evidence index"
    target.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"path": target.relative_to(ROOT).as_posix(), "sha256": sha(target),
                      "attempts": len(attempts), "status_counts": dict(counts)}, indent=2))


if __name__ == "__main__":
    main()
