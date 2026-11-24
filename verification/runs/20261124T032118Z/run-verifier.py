#!/usr/bin/env python3
"""Run the strict verifier with preserved gates against fully snapshotted input.

Invoke only after the source, documentation, manifest, root-import record and
development archive are stable. Every invocation gets a new full-NN directory.
This wrapper never edits mathematical sources, documentation, or verifier gates.
"""
from __future__ import annotations

from datetime import datetime, timezone
import fcntl
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

sys.dont_write_bytecode = True

ROOT = Path(__file__).resolve().parents[3]
RUN = Path(__file__).resolve().parent
BASELINE = "0cf1c68c4daaeec9b879a03f1871eb64a0fa9640"
BASELINE_TREE = "5d031253d02d0d0878422f8fbc367f04b812450c"
SOURCE_DIRS = ("Terminal",)
RUNTIME = "/workspace/scratch/5d2e6f7b5492/lean-runtime/lean-4.24.0-linux/bin"
STAGE_LOGS = ("vizing-source.log", "lean-version.log", "build.log", "axioms.log")
CONTROL_FILES = ("record-command.py", "run-verifier.py", "supervise-verifier.py", "record-final.py",
                 "run.json", "verifier-additions.json", "root-added-imports.json",
                 "coverage-extension-plan.json", "development-archive.json")


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def write_json(path: Path, data) -> None:
    path.write_text(json.dumps(data, indent=2) + "\n")


def require(ok: bool, message: str) -> None:
    if not ok:
        raise SystemExit(message)


def git(*args: str) -> bytes:
    return subprocess.check_output(["git", *args], cwd=ROOT)


def current_inputs() -> dict[str, bytes]:
    paths = [ROOT / "Overfull.lean", ROOT / "Audit.lean",
             *(ROOT / "Overfull").rglob("*.lean"),
             ROOT / "lean-toolchain", ROOT / "lakefile.toml", ROOT / "lake-manifest.json",
             ROOT / "README.md", ROOT / ".github/workflows/lean.yml",
             *(ROOT / "scripts").glob("*.py"), *(ROOT / "docs").glob("*.json"),
             *(ROOT / "docs").glob("*.md"), *(ROOT / "patches").glob("*.patch"),
             ROOT / "THIRD_PARTY_NOTICES.txt", ROOT / "CIRCULATION_NOTICE.txt",
             ROOT / "LICENSE_BMATCHING.txt"]
    return {p.relative_to(ROOT).as_posix(): p.read_bytes() for p in sorted(paths)}


def baseline_preflight(inputs: dict[str, bytes]) -> dict:
    require(git("rev-parse", "HEAD").decode().strip() == BASELINE,
            "Current HEAD is not the exact verified local baseline")
    require(git("rev-parse", BASELINE + "^{tree}").decode().strip() == BASELINE_TREE,
            "Verified baseline tree differs")
    paths = {p.decode() for p in git("ls-tree", "-rz", "--name-only", BASELINE).split(b"\0") if p}
    require(len(paths) == 5478, "Verified baseline does not contain exactly 5478 files")
    previous = json.loads(git("show", BASELINE + ":verification/results.json"))
    original = {**previous["source_sha256"], **previous["verification_input_sha256"]}
    require(len(previous["source_sha256"]) == 609 and len(original) == 716
            and previous["verified_declaration_count"] == 13366
            and len(previous["completed_results"]) == 2272,
            "Actual committed baseline verification counts disagree")
    frozen_path = "verification/runs/20261124T021500Z/frozen-candidate-inputs.json"
    require(json.loads(git("show", BASELINE + ":" + frozen_path)) == original,
            "Baseline frozen candidate differs from its committed result")
    editable = {"Overfull.lean", "README.md", "docs/continuation-handoff.md",
                "scripts/verify.py", "docs/coverage.json"}
    for path, expected in original.items():
        require(digest(git("show", BASELINE + ":" + path)) == expected,
                "Baseline frozen hash differs from committed bytes: " + path)
        require(path in inputs, "A prior frozen input disappeared: " + path)
        if path not in editable:
            require(digest(inputs[path]) == expected,
                    "An immutable preceding frozen input changed: " + path)
    spec = importlib.util.spec_from_file_location("terminal_preservation_checker", RUN / "record-final.py")
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    checker.check_verifier_extension()
    checker.check_coverage_preservation()
    source = json.loads((ROOT / "docs/three-core-terminal-source.json").read_text())
    modules = {item["module"] for item in source["modules"]}
    checker.check_root_imports(modules)
    additions = {path for path in inputs if path.startswith(tuple(
        "Overfull/" + name + "/" for name in SOURCE_DIRS)) and path.endswith(".lean")}
    require(additions == {item["path"] for item in source["modules"]},
            "New source inventory differs from the three-core-terminal manifest")
    for item in source["modules"]:
        require(digest(inputs[item["path"]]) == item["sha256"]
                and checker.source_public_proofs(ROOT / item["path"]) == item["public_proof_declarations"],
                "New source hash/public theorem inventory differs: " + item["path"])
    archive, records = checker.check_development_archive()
    require(all(item["status"] not in {"incomplete", "interrupted"} for item in records),
            "An active/incomplete focused command must be resolved or explicitly archived before this freeze")
    return {"checked_at_utc": datetime.now(timezone.utc).isoformat(),
            "baseline_commit": BASELINE, "baseline_tree": BASELINE_TREE,
            "baseline_tracked_file_count": len(paths), "baseline_frozen_input_count": len(original),
            "baseline_frozen_input_sha256": original,
            "baseline_audited_declaration_count": previous["verified_declaration_count"],
            "baseline_completed_result_mapping_count": len(previous["completed_results"]),
            "unchanged_prior_frozen_input_count": len(original.keys() - editable),
            "exact_reviewed_verifier_and_root_edits_checked": True,
            "all_69_assertion_records_and_48_completed_records_preserved": True,
            "manuscript_source_byte_identical": True,
            "numbered_assertions_completed_in_this_run": 0,
            "new_module_count": len(modules), "public_theorem_count": source["public_theorem_count"],
            "development_archive_sha256": archive["sha256"]}


def retain_outputs(folder: Path, started_ns: int) -> dict:
    retained = {}
    for path in sorted((ROOT / "verification").glob("*")):
        if not path.is_file() or path.name not in (*STAGE_LOGS, "results.json") and not path.name.endswith("declarations.json"):
            continue
        if path.stat().st_mtime_ns < started_ns:
            continue
        relative = path.relative_to(ROOT).as_posix()
        target = folder / "artifacts" / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        data = path.read_bytes()
        target.write_bytes(data)
        retained[relative] = {"snapshot": target.relative_to(ROOT).as_posix(),
                              "sha256": digest(data), "bytes": len(data)}
    audit = folder / "artifacts/verification/axioms.log"
    if audit.is_file():
        data = audit.read_bytes()
        segment_dir = folder / "raw-audit-segments"
        segment_dir.mkdir()
        segments = []
        for offset in range(0, len(data), 1048576):
            chunk = data[offset:offset + 1048576]
            part = segment_dir / f"part-{len(segments):04d}.log"
            part.write_bytes(chunk)
            segments.append({"path": part.relative_to(ROOT).as_posix(), "offset": offset,
                             "bytes": len(chunk), "sha256": digest(chunk)})
        write_json(segment_dir / "manifest.json", {
            "kind": "exact_contiguous_raw_audit_bytes", "source": audit.relative_to(ROOT).as_posix(),
            "source_sha256": digest(data), "bytes": len(data), "segments": segments})
    return retained


def main() -> None:
    phase = sys.argv[1] if len(sys.argv) == 2 else "full-01"
    require(len(sys.argv) <= 2 and re.fullmatch(r"full-[A-Za-z0-9-]+", phase) is not None,
            "Usage: run-verifier.py [full-NN]")
    with (RUN / "build.lock").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        inputs = current_inputs()
        preflight = baseline_preflight(inputs)
        controls = {name: (RUN / name).read_bytes() for name in CONTROL_FILES}
        control_hashes = {name: digest(data) for name, data in controls.items()}
        folder = RUN / phase
        folder.mkdir(exist_ok=False)
        before = {path: digest(data) for path, data in inputs.items()}
        write_json(folder / "baseline-preservation-preflight.json", preflight)
        for name, data in controls.items():
            target = folder / "control" / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
        for target in (folder / "frozen-candidate-inputs.json", RUN / "frozen-candidate-inputs.json"):
            write_json(target, before)
        snapshots = {}
        for path, data in inputs.items():
            target = folder / "input" / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
            if path.startswith(tuple("Overfull/" + name + "/" for name in SOURCE_DIRS)):
                target = folder / "source" / path
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(data)
                snapshots[path] = before[path]
        started = datetime.now(timezone.utc)
        started_ns, tick = time.time_ns(), time.monotonic()
        record = {"schema_version": 2, "command": ["python3", "scripts/verify.py"], "cwd": str(ROOT),
                  "started_at_utc": started.isoformat(), "status": "running", "exit_code": None,
                  "attempt": phase, "candidate_input_hash_count": len(before),
                  "source_sha256": snapshots, "input_sha256": before,
                  "all_frozen_inputs_snapshotted": True,
                  "control_sha256": control_hashes, "all_control_files_snapshotted": True,
                  "baseline_local_verified_commit": BASELINE, "baseline_local_verified_tree": BASELINE_TREE,
                  "runner_sha256": digest(Path(__file__).read_bytes()),
                  "verifier_sha256": before["scripts/verify.py"]}
        def save():
            for target in (folder / "command.json", RUN / "verification-command.json"):
                write_json(target, record)
        save()
        env = os.environ.copy()
        env["PATH"] = RUNTIME + ":" + env["PATH"]
        print("Starting complete strict verifier and unchanged full audit", phase, started.isoformat(), flush=True)
        with (folder / "output.log").open("wb") as log:
            proc = subprocess.Popen(record["command"], cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT)
            record["observed_child_pid"] = proc.pid
            save()
            try:
                code = proc.wait()
            except BaseException as error:
                record.update({"status": "incomplete", "exit_code": None,
                               "observed_child_return_code_at_interruption": proc.poll(),
                               "interruption_observed_at_utc": datetime.now(timezone.utc).isoformat(),
                               "interruption_reason": type(error).__name__ + ": " + str(error)})
                save()
                raise
        finished = datetime.now(timezone.utc)
        after = {path: digest(data) for path, data in current_inputs().items()}
        changed = sorted(path for path in before.keys() | after.keys() if before.get(path) != after.get(path))
        changed_controls = sorted(name for name, expected in control_hashes.items()
                                  if not (RUN / name).is_file() or digest((RUN / name).read_bytes()) != expected)
        retained = retain_outputs(folder, started_ns)
        record.update({"finished_at_utc": finished.isoformat(), "completed_at_utc": finished.isoformat(),
                       "elapsed_seconds": time.monotonic() - tick, "exit_code": code,
                       "all_frozen_inputs_unchanged": not changed, "inputs_changed_during_command": changed,
                       "all_control_files_unchanged": not changed_controls,
                       "control_files_changed_during_command": changed_controls,
                       "status": "passed" if code == 0 and not changed and not changed_controls else "failed",
                       "output_sha256": digest((folder / "output.log").read_bytes()),
                       "retained_current_outputs": retained})
        save()
        shutil.copyfile(folder / "output.log", RUN / "verification-console.log")
        print(json.dumps({k: v for k, v in record.items() if k not in
                         {"source_sha256", "input_sha256", "retained_current_outputs"}}, indent=2), flush=True)
        sys.exit(code if code else (0 if not changed and not changed_controls else 1))


if __name__ == "__main__":
    main()
