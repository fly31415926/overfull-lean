#!/usr/bin/env python3
"""Validate the completed local run and write a receipt; never publish or stage."""
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
RUN = HERE.parent
ROOT = RUN.parents[2]


def load(path):
    return json.loads(path.read_text())


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def verify_index(index_path, base):
    index = load(index_path)
    require(len(index["files"]) == index["file_count"], "Incorrect evidence count")
    for relative, item in index["files"].items():
        path = base / relative
        require(path.stat().st_size == item["bytes"] and digest(path) == item["sha256"],
                "Evidence changed: " + str(path))
    return index["file_count"]


def main():
    target = HERE / "local-verification-gate.json"
    require(not target.exists(), "Receipt already exists; do not overwrite it")
    full = RUN / "full-02"
    terminal = load(full / "terminal.json")
    require(terminal["status"] == "passed" and terminal["exit_code"] == 0,
            "The full verifier has not passed")
    require(terminal["inputs_unchanged"] and terminal["controls_unchanged"]
            and not terminal["missing_required_outputs"] and not terminal["wrapper_errors"],
            "The full run did not preserve its frozen inputs or complete its outputs")
    checker = RUN / "check-preservation.py"
    spec = importlib.util.spec_from_file_location("preservation", checker)
    checks = importlib.util.module_from_spec(spec)
    exec(compile(checker.read_bytes(), str(checker), "exec"), checks.__dict__)
    inputs = {p: checks.sha(data) for p, data in checks.current_inputs().items()}
    controls = {p: checks.sha(data) for p, data in checks.current_controls().items()}
    require(inputs == load(full / "frozen-inputs.json"), "Verified inputs changed after run")
    require(controls == load(full / "frozen-controls.json"), "Frozen controls changed after run")
    for relative, expected in load(full / "outputs.json").items():
        require(digest(ROOT / relative) == expected, "Actual verifier output changed: " + relative)
    attempts = []
    for folder in sorted(RUN.glob("full-*")):
        receipt = load(folder / "terminal.json")
        require(digest(folder / "output.log") == receipt["output_sha256"],
                "Saved full output changed: " + folder.name)
        for name, expected in receipt["archives"].items():
            require(digest(folder / name) == expected, "Saved archive changed: " + folder.name + "/" + name)
        attempts.append({"attempt": folder.name, "status": receipt["status"],
                         "exit_code": receipt["exit_code"], "terminal_sha256": digest(folder / "terminal.json")})
    setup_count = verify_index(RUN / "environment-setup-index.json", RUN / "environment-setup")
    development_count = verify_index(RUN / "development-index.json", RUN)
    preserved = checks.final_checks()
    require(preserved == load(full / "preservation.json"), "Preservation result changed after run")
    receipt = {
        "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "status": "passed", "baseline_commit": checks.BASELINE,
        "verified_input_count": len(inputs), "frozen_control_count": len(controls),
        "all_frozen_inputs_controls_and_outputs_unchanged": True,
        "setup_evidence_files": setup_count, "development_evidence_files": development_count,
        "full_attempts": attempts, "preservation": preserved,
        "publication_status": "blocked_by_automatic_approval_review",
        "successful_remote_blob_uploads": 0, "remote_commits_created": 0,
        "remote_branch_updates_attempted": 0,
        "publication_rejection_receipts": ["blocked-upload.json", "reassessed-upload.json"],
    }
    target.write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
