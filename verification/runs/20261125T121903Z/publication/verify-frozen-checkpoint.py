#!/usr/bin/env python3
"""Read-only verification of genuine full-run files and their frozen archives."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import sys
import tarfile

HERE = Path(__file__).resolve().parent
RUN = HERE.parent
ROOT = RUN.parents[2]


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    label = sys.argv[1] if len(sys.argv) == 2 else "full-01"
    assert label.startswith("full-") and "/" not in label
    folder = RUN / label
    terminal = json.loads((folder / "terminal.json").read_text())
    assert terminal["status"] == "passed" and terminal["exit_code"] == 0
    assert terminal["inputs_unchanged"] and terminal["controls_unchanged"]
    assert terminal["preservation"]["status"] == "passed"
    assert (folder / "command.json").read_bytes() == (folder / "terminal.json").read_bytes()
    assert digest((folder / "output.log").read_bytes()) == terminal["output_sha256"]
    checks = {}
    for basename, base in [("frozen-inputs", ROOT), ("frozen-controls", RUN), ("outputs", ROOT)]:
        expected = json.loads((folder / (basename + ".json")).read_text())
        for relative, sha in expected.items():
            current = (base / relative).resolve(strict=True)
            assert current.is_relative_to(base), relative
            assert digest(current.read_bytes()) == sha, relative
        archive = folder / (basename + ".tar.gz")
        assert digest(archive.read_bytes()) == terminal["archives"][archive.name]
        contents = {}
        with tarfile.open(archive, "r:gz") as tar:
            for member in tar:
                assert member.isfile() and member.name not in contents, member.name
                with tar.extractfile(member) as stream:
                    contents[member.name] = digest(stream.read())
        assert contents == expected, basename
        checks[basename] = {"count": len(expected), "current_bytes_match": True,
                            "archive_bytes_match": True,
                            "archive_sha256": terminal["archives"][archive.name]}
    result = {"checked_at_utc": datetime.now(timezone.utc).isoformat(), "status": "passed",
              "full_attempt": label, "baseline_commit": terminal["baseline_commit"],
              "baseline_tree": terminal["baseline_tree"], "checks": checks,
              "preservation": terminal["preservation"],
              "terminal_sha256": digest((folder / "terminal.json").read_bytes()),
              "scope": "Read-only hash and archive verification of the recorded full execution; not a new Lean build or audit."}
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
