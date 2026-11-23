#!/usr/bin/env python3
"""Check the frozen residual-palette audit and preservation of its actual parent.

Usage: python3 verification/runs/20261123T210325Z/record-final.py NATIVE_VERIFIED_SHA

Run only after the latest complete verifier passes and the actual preceding
native-reserve verification commit is available locally. This supplementary
checker neither builds proofs nor replaces scripts/verify.py or Audit.lean.
It writes no success report until its consistency and preservation checks pass.
Capture stdout outside this run directory until the command has finished.
"""
from __future__ import annotations

from datetime import datetime, timezone
from functools import lru_cache
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys


RUN = Path(__file__).resolve().parent
ROOT = RUN.parents[2]
VERIFIED_BASELINE = "98c6b228a997fead863d05041f12799c93fac18b"
SOURCE_CHECKPOINT = "964027f1a74cd68149033dc74f87846cabdf2eae"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
NEW_MODULE_COUNT = 12
NEW_PUBLIC_PROOF_COUNT = 75
EDITED_PREVIOUS_INPUTS = {"README.md", "docs/continuation-handoff.md", "scripts/verify.py"}
NEW_INPUTS = {
    "docs/residual-palette-source.json", "docs/residual-palette-semantic-review.md",
    "docs/residual-palette-verification.md", "scripts/update_residual_palette_manifest.py",
}
LIVE_OUTPUTS = {
    "verification/results.json", "verification/build.log", "verification/axioms.log",
    "verification/lean-version.log", "verification/vizing-source.log",
}
REPORT_OUTPUTS = {"preservation.json", "final-report.md", "record-final-output.log"}
ADDED_IMPORTS = [
    "import Overfull.ResidualPalette.UniformJoining\n",
    "import Overfull.ResidualPalette.PaletteBudget\n",
    "import Overfull.ResidualPalette.JoiningGrouping\n",
    "import Overfull.ResidualPalette.NativeProtectedPalette\n",
    "import Overfull.ResidualPalette.ProtectedBudget\n",
]
VERIFIER_EDITS = [
    {
        "old": '                          ("native_reserve", "native-reserve-source.json")):\n',
        "new": '                          ("native_reserve", "native-reserve-source.json"),\n'
               '                          ("residual_palette", "residual-palette-source.json")):\n',
    },
    {
        "old": '    # Every first-party mathematical file must be included in the library build.\n',
        "new": '    if extension_maps["residual_palette"][0]["numbered_assertions_completed"] != 0:\n'
               '        raise SystemExit("The residual-palette continuation completes no numbered manuscript assertion.")\n\n'
               '    # Every first-party mathematical file must be included in the library build.\n',
    },
    {
        "old": '                    "native_reserve": "native-reserve"}[key]\n',
        "new": '                    "native_reserve": "native-reserve",\n'
               '                    "residual_palette": "residual-palette"}[key]\n',
    },
    {
        "old": '        "native_reserve_declaration_map": extension_evidence["native_reserve"],\n',
        "new": '        "native_reserve_declaration_map": extension_evidence["native_reserve"],\n'
               '        "residual_palette_declaration_map": extension_evidence["residual_palette"],\n',
    },
]

# These are bytes actually inspected while this checker was being prepared.
# They pin completed failures/observations, not any still-running attempt.
OBSERVED_EVIDENCE = {
    "full-01/command.json": "f2c21d3cba0648841962c56c2cdb7c0887efe3aa46b1803e417cff95464960b8",
    "full-01/output.log": "3a905ab4c42eb4041a9bab5a3d7e6e34b77005b1d2135f08fd0f164a35a57f15",
    "full-01/frozen-candidate-inputs.json": "cd8c17c5de8f9784face697188dc4caa0a47df4d6906ded12ae32b1e20ac4f49",
    "full-02/command.json": "acf0b1eb53a765c114a04f1cea14f0afa6d3bf5e581bc137f3603437561a18c9",
    "full-02/output.log": "eff99ea4eff40dc22d22919925815f0f6d6c7e8019ccf2587233b5388b05008d",
    "full-02/frozen-candidate-inputs.json": "2c51d2cb1add2663a7432fa8eee025521ff3a8ff595ccacb90d940ee64c7a729",
    "initial-integration-build.log": "5cd43883e571dcb0f2f99ce1f12e300e3234b621b327e045101d092808d5335a",
    "initial-integration-tool-result.json": "70e1c959d89c4e1dd919f49d5490857c25a184befb0c94f4f3d8d49fe164fae5",
    "initial-integration-observation.json": "c1f3479317f760ed50f5ec69e61c1d750d3285b7b25212fce06e731b0458ad45",
    "manifest-01/update_residual_palette_manifest.py": "10ae21b1da715245ec55fdcd5548b5230361207ed0f111193270c53b131a6c42",
    "manifest-01/observation.json": "4fad630cb8d0d0fc663492e1002ff6bafd2338698c25bbc879d92c4c6195f394",
    "setup-observations.md": "bc997c6852c69846a1bb02034668a5baa8f954c47eaf1fd970bf91914691df70",
    "development-archive.json": "c3b6e08543355da220864fbdf2d2da81b7a4b5c97cf26dc15bf7f771c98abc29",
}


def require(ok: bool, message: str) -> None:
    if not ok:
        raise SystemExit(message)


def load(path: Path):
    return json.loads(path.read_text(encoding="utf-8"))


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha(path: Path) -> str:
    return digest(path.read_bytes())


def rel(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def local(path: str) -> Path:
    parsed = PurePosixPath(path)
    require(isinstance(path, str) and bool(parsed.parts) and not parsed.is_absolute()
            and ".." not in parsed.parts and str(parsed) == path,
            f"Noncanonical repository-relative evidence path: {path!r}")
    return ROOT / path


def timestamp(value: str) -> datetime:
    parsed = datetime.fromisoformat(value)
    require(parsed.tzinfo is not None, f"Evidence timestamp has no time zone: {value}")
    return parsed


def git(*args: str) -> bytes:
    return subprocess.check_output(["git", *args], cwd=ROOT)


@lru_cache(maxsize=None)
def old_bytes(commit: str, path: str) -> bytes:
    local(path)
    return git("show", f"{commit}:{path}")


def tracked_paths(commit: str) -> set[str]:
    return {item.decode("utf-8") for item in git("ls-tree", "-rz", "--name-only", commit).split(b"\0") if item}


def declaration_index(items: list[dict], label: str) -> dict:
    require(isinstance(items, list), f"Malformed declaration inventory: {label}")
    indexed = {}
    for item in items:
        name, module, axioms = item["name"], item["module"], item["axioms"]
        require(isinstance(name, str) and isinstance(module, str)
                and isinstance(axioms, list) and all(isinstance(x, str) for x in axioms)
                and len(axioms) == len(set(axioms)) and name not in indexed,
                f"Malformed or duplicate declaration in {label}: {name}")
        indexed[name] = (module, frozenset(axioms))
    return indexed


def current_paths() -> tuple[set[str], set[str]]:
    sources = {"Overfull.lean", "Audit.lean"} | {
        rel(path) for path in (ROOT / "Overfull").rglob("*.lean")
    }
    inputs = {rel(path) for path in [
        ROOT / "lean-toolchain", ROOT / "lakefile.toml", ROOT / "lake-manifest.json",
        ROOT / "README.md", ROOT / ".github/workflows/lean.yml",
        *(ROOT / "scripts").glob("*.py"), *(ROOT / "docs").glob("*.json"),
        *(ROOT / "docs").glob("*.md"), *(ROOT / "patches").glob("*.patch"),
        ROOT / "THIRD_PARTY_NOTICES.txt", ROOT / "CIRCULATION_NOTICE.txt",
        ROOT / "LICENSE_BMATCHING.txt",
    ]}
    return sources, inputs


def source_public_proofs(path: Path) -> list[dict]:
    """Recompute the explicit theorem/lemma manifest without writing sources.

    This lexical inventory is supplemental. The unchanged Lean audit is the
    authority for the full proof inventory, including private/generated proofs.
    """
    source = path.read_text(encoding="utf-8")
    out, index, depth, quoted = [], 0, 0, False
    while index < len(source):
        if depth:
            if source.startswith("/-", index):
                depth += 1
                out.extend("  ")
                index += 2
            elif source.startswith("-/", index):
                depth -= 1
                out.extend("  ")
                index += 2
            else:
                out.append("\n" if source[index] == "\n" else " ")
                index += 1
        elif quoted:
            char = source[index]
            out.append(char)
            index += 1
            if char == "\\" and index < len(source):
                out.append(source[index])
                index += 1
            elif char == '"':
                quoted = False
        elif source.startswith("/-", index):
            depth = 1
            out.extend("  ")
            index += 2
        elif source.startswith("--", index):
            while index < len(source) and source[index] != "\n":
                out.append(" ")
                index += 1
        else:
            char = source[index]
            out.append(char)
            index += 1
            if char == '"':
                quoted = True
    require(depth == 0 and not quoted, f"Unterminated comment/string in {rel(path)}")
    namespaces, scopes, declarations = [], [], []
    for number, line in enumerate("".join(out).splitlines(), 1):
        if match := re.match(r"^namespace\s+(\S+)\s*$", line):
            namespaces.append(match[1])
            scopes.append(("namespace", match[1]))
        elif match := re.match(r"^section(?:\s+(\S+))?\s*$", line):
            scopes.append(("section", match[1]))
        elif match := re.match(r"^end(?:\s+(\S+))?\s*$", line):
            require(bool(scopes) and scopes[-1][1] == match[1],
                    f"Unmatched lexical scope at {rel(path)}:{number}")
            kind, _ = scopes.pop()
            if kind == "namespace":
                namespaces.pop()
        elif match := re.match(r"^(?:@\[[^]]+\]\s+)?(?:theorem|lemma)\s+([^\s(:{]+)", line):
            declarations.append({"name": ".".join([*namespaces, match[1]]), "source_line": number})
    require(not namespaces and not scopes, f"Unclosed lexical scope in {rel(path)}")
    return declarations


def check_verifier_extension(parent: str) -> list[dict]:
    edits = load(RUN / "verifier-additions.json")
    require(edits == VERIFIER_EDITS and len(edits) == 4,
            "Verifier edit manifest differs from the four reviewed additive extensions")
    expected = old_bytes(parent, "scripts/verify.py")
    for edit in edits:
        old, new = edit["old"].encode(), edit["new"].encode()
        require(expected.count(old) == 1, "Ambiguous or missing additive verifier edit")
        expected = expected.replace(old, new, 1)
    require((ROOT / "scripts/verify.py").read_bytes() == expected,
            "Verifier differs beyond the four reviewed additive manifest/mapping edits")
    return edits


def check_new_mapping(current: dict, audited: dict) -> dict:
    source_path = ROOT / "docs/residual-palette-source.json"
    map_path = ROOT / "verification/residual-palette-declarations.json"
    source, mapping = load(source_path), load(map_path)
    require(source["baseline_commit"] == VERIFIED_BASELINE
            and source["native_reserve_source_checkpoint"] == SOURCE_CHECKPOINT
            and source["kind"] == "supporting_continuation"
            and source["numbered_assertions_completed"] == 0
            and source["main_theorem_verified"] is False,
            "Residual-palette source manifest changes its historical baseline or mathematical scope")
    modules = {item["module"]: item for item in source["modules"]}
    require(len(modules) == len(source["modules"]) == source["module_count"] == NEW_MODULE_COUNT,
            "Residual-palette module inventory has duplicates or an unexpected count")
    public = {}
    for module, item in modules.items():
        path = local(item["path"])
        require(module.startswith("Overfull.ResidualPalette.")
                and item["path"] == module.replace(".", "/") + ".lean"
                and sha(path) == item["sha256"], f"New source path/hash mismatch: {module}")
        require(source_public_proofs(path) == item["public_proof_declarations"],
                f"Explicit public proof names or source lines differ from the source: {module}")
        names = [entry["name"] for entry in item["public_proof_declarations"]]
        require(len(names) == len(set(names)) == item["public_theorem_count"],
                f"Public-proof inventory mismatch: {module}")
        for name in names:
            require(name not in public and name in audited and audited[name][0] == module,
                    f"New public proof missing, duplicated or audited elsewhere: {name}")
            public[name] = module
    require(set(public) == set(source["required_proof_declarations"])
            and len(public) == len(source["required_proof_declarations"])
            == source["public_theorem_count"] == NEW_PUBLIC_PROOF_COUNT,
            "Residual-palette required-public-proof map is incomplete")
    expected = {name: value for name, value in audited.items() if value[0] in modules}
    actual = declaration_index(mapping["proof_declaration_map"], "residual-palette declaration map")
    require(actual == expected and {entry[0] for entry in actual.values()} == set(modules),
            "Complete new declaration map differs from the actual full audit")
    for item in mapping["proof_declaration_map"]:
        module = modules[item["module"]]
        require(item["source_path"] == module["path"] and item["source_sha256"] == module["sha256"],
                f"New audited declaration has stale source binding: {item['name']}")
    summary = current["residual_palette_declaration_map"]
    require(summary["path"] == rel(map_path) and summary["sha256"] == sha(map_path),
            "New result summary has a stale declaration-map path/hash")
    for key, value in [("module_count", len(modules)), ("public_theorem_count", len(public)),
                       ("verified_declaration_count", len(actual)), ("numbered_assertions_completed", 0)]:
        require(summary[key] == mapping[key] == value, f"New result/map count mismatch: {key}")
    require(mapping["kind"] == source["kind"]
            and mapping["includes_private_and_generated_proofs"] is True
            and mapping["manuscript_number"] is None and mapping["statement_sha256"] is None,
            "New declaration map omits support proofs or claims a complete numbered assertion")
    return {"source_manifest_path": rel(source_path), "source_manifest_sha256": sha(source_path),
            "declaration_map_path": rel(map_path), "declaration_map_sha256": sha(map_path),
            "modules": modules, "public_names": sorted(public),
            "all_audited_names": sorted(actual), "module_count": len(modules),
            "public_theorem_count": len(public), "audited_declaration_count": len(actual),
            "scope": source["scope"], "review_path": source["review"], "proof_map_path": source["proof_map"]}


def command_record(path: Path, data: dict, log_path: Path) -> dict:
    require(isinstance(data.get("command"), list) and bool(data["command"])
            and all(isinstance(part, str) for part in data["command"]),
            f"Malformed actual command record: {rel(path)}")
    require(log_path.is_file(), f"Missing actual command output: {rel(log_path)}")
    code = data.get("exit_code")
    if code is None:
        status = "incomplete"
        require(data.get("status") in {None, "running", "incomplete"},
                f"Unfinished command claims completion: {rel(path)}")
    else:
        require(type(code) is int, f"Invalid command exit code: {rel(path)}")
        if data.get("status") == "interrupted":
            require(code == 130 and (data.get("reason") or data.get("interruption_reason")),
                    f"Interrupted command lacks its observed reason/status: {rel(path)}")
            status = "interrupted"
        else:
            status = "passed" if code == 0 and data.get("all_frozen_inputs_unchanged") is not False else "failed"
            require(data.get("status", status) == status,
                    f"Command status and exit/frozen-input result disagree: {rel(path)}")
        finish = next((data[key] for key in ["finished_at_utc", "completed_at_utc", "ended_at_utc",
                                            "interruption_observed_at_utc"] if data.get(key)), None)
        if data.get("started_at_utc"):
            require(finish is not None and timestamp(data["started_at_utc"]) <= timestamp(finish),
                    f"Command lacks an ordered observed completion timestamp: {rel(path)}")
    recorded_sources = data.get("source_sha256", {})
    snapshots = {}
    if isinstance(recorded_sources, dict):
        require(len({Path(source).name for source in recorded_sources}) == len(recorded_sources),
                f"Ambiguous source snapshot basenames: {rel(path)}")
        snapshots = {path.parent / Path(source).name: expected for source, expected in recorded_sources.items()}
    elif isinstance(recorded_sources, str):
        source_args = [part for part in data["command"] if part.endswith(".lean")]
        require(bool(source_args), f"Source hash lacks its actual Lean input: {rel(path)}")
        snapshots = {path.parent / Path(source_args[-1]).name: recorded_sources}
    else:
        require(False, f"Malformed source-hash record: {rel(path)}")
    for snapshot, expected in snapshots.items():
        require(snapshot.is_file() and sha(snapshot) == expected,
                f"Recorded source snapshot differs: {rel(snapshot)}")
    if "final_source_sha256" in data:
        require(data["final_source_sha256"] == recorded_sources,
                f"Source changed during the recorded targeted check: {rel(path)}")
    if "output_sha256" in data:
        require(data["output_sha256"] == sha(log_path), f"Recorded output hash differs: {rel(log_path)}")
    return {"metadata_path": rel(path), "metadata_sha256": sha(path),
            "command": data["command"], "status": status, "exit_code": code,
            "log_path": rel(log_path), "log_sha256": sha(log_path),
            "source_snapshot_count": len(snapshots),
            "dependency_hash_records_retained": len(data.get("dependency_source_sha256", {}))}


def full_attempts() -> tuple[list[dict], dict]:
    paths = sorted(RUN.glob("full-*/command.json"))
    require(bool(paths), "No recorded complete-verifier attempts exist")
    records, ordered = [], []
    for path in paths:
        data = load(path)
        require(re.fullmatch(r"full-[A-Za-z0-9-]+", path.parent.name) is not None
                and data.get("attempt") == path.parent.name
                and data.get("command") == ["python3", "scripts/verify.py"]
                and data.get("cwd") == str(ROOT), f"Wrong complete-verifier provenance: {rel(path)}")
        frozen = load(path.parent / "frozen-candidate-inputs.json")
        require(isinstance(frozen, dict) and data["candidate_input_hash_count"] == len(frozen)
                and all(frozen.get(source) == expected for source, expected in data["source_sha256"].items()),
                f"Verifier attempt snapshots differ from its own frozen inputs: {rel(path)}")
        records.append(command_record(path, data, path.parent / "output.log"))
        ordered.append((timestamp(data["started_at_utc"]), path.parent.name, data))
    require(len({start for start, _, _ in ordered}) == len(ordered), "Ambiguous latest verification attempt")
    _, latest_name, latest = max(ordered, key=lambda item: item[0])
    require(latest["status"] == "passed" and latest["exit_code"] == 0
            and latest.get("all_frozen_inputs_unchanged") is True,
            f"Latest full verifier {latest_name} has not passed with unchanged inputs")
    for alias, original in [("verification-command.json", "command.json"),
                            ("frozen-candidate-inputs.json", "frozen-candidate-inputs.json"),
                            ("verification-console.log", "output.log")]:
        require((RUN / alias).read_bytes() == (RUN / latest_name / original).read_bytes(),
                f"Latest verification alias differs from its actual attempt: {alias}")
    return records, latest


def check_development_archive() -> tuple[dict, list[dict]]:
    archive_path = RUN / "development-archive.json"
    archive = load(archive_path)
    require(archive["kind"] == "byte_identical_genuine_development_evidence"
            and archive["file_count"] == len(archive["files"]), "Malformed development archive inventory")
    indexed = {}
    prefix = rel(RUN / "development") + "/"
    for item in archive["files"]:
        path = item["path"]
        require(path.startswith(prefix) and path not in indexed
                and isinstance(item["copied_from"], str) and Path(item["copied_from"]).is_absolute()
                and sha(local(path)) == item["sha256"], f"Development archive path/hash differs: {path}")
        indexed[path] = item["sha256"]
    require(set(indexed) == {rel(path) for path in (RUN / "development").rglob("*") if path.is_file()},
            "Development archive contains unlisted files or has missing files")
    records = []
    for path in sorted((RUN / "development").rglob("*.json")):
        data = load(path)
        if isinstance(data, dict) and isinstance(data.get("command"), list):
            log = path.parent / "output.log" if path.name == "command.json" else path.with_suffix(".log")
            records.append(command_record(path, data, log))
    aggregate_path = RUN / "development/joining-degree-work/targeted-checks.json"
    aggregate = load(aggregate_path)
    ids = set()
    for entry in aggregate["records"]:
        require(entry["id"] not in ids, "Duplicate archived targeted-command identifier")
        ids.add(entry["id"])
        log_path = aggregate_path.parent / entry["log"]
        require(sha(log_path) == entry["log_sha256"], f"Targeted-command log changed: {entry['id']}")
        if "metadata" in entry:
            metadata_path = aggregate_path.parent / entry["metadata"]
            metadata = load(metadata_path)
            require(sha(metadata_path) == entry["metadata_sha256"]
                    and metadata["exit_code"] == entry["exit_code"] and metadata["status"] == entry["status"],
                    f"Targeted-command summary differs from actual metadata: {entry['id']}")
            for name, expected in entry["source_snapshots"].items():
                require(sha(metadata_path.parent / name) == expected,
                        f"Targeted-command source snapshot changed: {entry['id']}/{name}")
        else:
            require(type(entry["exit_code"]) is int and entry["status"] ==
                    ("passed" if entry["exit_code"] == 0 else "failed"),
                    f"Manual targeted-command status differs: {entry['id']}")
            snapshot = aggregate_path.parent / entry["source_snapshot"]
            require(sha(snapshot) == entry["source_sha256"],
                    f"Manual targeted-command source snapshot changed: {entry['id']}")
            records.append({"metadata_path": rel(aggregate_path), "metadata_sha256": sha(aggregate_path),
                            "metadata_record_id": entry["id"], "command": entry["command"],
                            "status": entry["status"], "exit_code": entry["exit_code"],
                            "log_path": rel(log_path), "log_sha256": sha(log_path),
                            "source_snapshot_count": 1, "timing_note": entry["timing"]})
    return {"path": rel(archive_path), "sha256": sha(archive_path), "file_count": len(indexed),
            "all_recorded_byte_hashes_match": True, "files": indexed}, records


def check_observations() -> dict:
    for path, expected in OBSERVED_EVIDENCE.items():
        require(sha(RUN / path) == expected, f"Previously inspected failure or observation changed: {path}")
    for name in ["full-01", "full-02"]:
        record = load(RUN / name / "command.json")
        require(record["status"] == "failed" and record["exit_code"] == 1,
                f"Actual earlier integration failure no longer retained: {name}")
    observation = load(RUN / "initial-integration-observation.json")
    raw = load(RUN / "initial-integration-tool-result.json")
    output = (RUN / observation["output_log"]).read_text(encoding="utf-8")
    require(raw["output"] == output and raw["exit_code"] == observation["exit_code"] == 0
            and observation["kind"] == "actual_tool_output_observation"
            and observation["status"] == "passed",
            "Initial integration observation differs from its genuine raw tool result")
    require(all(sha(local(path)) == expected for path, expected in observation["observed_source_sha256"].items()),
            "An initially integrated new proof source changed before the final check")
    manifest_failure = load(RUN / "manifest-01/observation.json")
    require(manifest_failure["exit_code"] == 1
            and manifest_failure["source_sha256"] == sha(RUN / "manifest-01/update_residual_palette_manifest.py"),
            "Initial manifest-scanner failure lost its exact failed script")
    return {"pinned_observation_sha256": OBSERVED_EVIDENCE,
            "initial_integration": observation, "manifest_scanner_failure": manifest_failure,
            "setup_observation_path": rel(RUN / "setup-observations.md"),
            "timing_note": "No unrecorded start or finish times have been inferred for observations."}


def main() -> None:
    require(len(sys.argv) == 2 and re.fullmatch(r"[0-9a-f]{40}", sys.argv[1]) is not None,
            "Usage: record-final.py ACTUAL_PRECEDING_NATIVE_VERIFIED_40_CHARACTER_COMMIT_SHA")
    parent = sys.argv[1]
    require(git("rev-parse", f"{parent}^{{commit}}").decode().strip() == parent,
            "The supplied native-verified parent is not an available exact commit")
    require(subprocess.run(["git", "merge-base", "--is-ancestor", VERIFIED_BASELINE, parent],
                           cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE).returncode == 0,
            "The supplied native-verified parent does not descend from the recorded verified baseline")
    full_records, command = full_attempts()
    run = load(RUN / "run.json")
    require(run["run_id"] == RUN.name and run["verified_baseline_commit"] == VERIFIED_BASELINE
            and run["native_reserve_source_checkpoint"] == SOURCE_CHECKPOINT
            and run["repository"] == "fly31415926/overfull-lean",
            "Run metadata identifies a different continuation or historical source base")
    require(timestamp(run["started_at_utc"]) <= timestamp(command["started_at_utc"])
            <= timestamp(command["completed_at_utc"]), "Latest verifier timestamps do not belong to this run")

    previous = json.loads(old_bytes(parent, "verification/results.json"))
    current = load(ROOT / "verification/results.json")
    for label, result in [("preceding native-verified commit", previous), ("fresh result", current)]:
        require(result["lean_build_passed"] is True and result["axiom_audit_passed"] is True
                and result["status"] == "partial_formalization" and result["main_theorem_verified"] is False,
                f"Invalid verification status or main-theorem scope in {label}")
        require(set(result["allowed_logical_axioms"]) == ALLOWED_AXIOMS
                and result["declaration_count_includes_generated_support_lemmas"] is True,
                f"Changed logical axiom allowance or support-proof scope in {label}")
    require("native_reserve_declaration_map" in previous and "residual_palette_declaration_map" not in previous,
            "Argument is not the preceding native-reserve verified result (a source checkpoint is insufficient)")
    require(current["toolchain"] == previous["toolchain"] == "leanprover/lean4:v4.24.0"
            and current["mathlib_revision"] == previous["mathlib_revision"] == "f897ebcf72cd16f89ab4577d0c826cd14afaafc7"
            and current["dependency_source_revisions"] == previous["dependency_source_revisions"],
            "Pinned Lean/mathlib/dependency sources changed")
    before = declaration_index(previous["verified_declarations"], "preceding native-verified result")
    after = declaration_index(current["verified_declarations"], "fresh complete result")
    require(len(before) == previous["verified_declaration_count"] and len(before) > 12055,
            "Preceding result does not include the completed native-reserve audit")
    require(len(after) == current["verified_declaration_count"]
            and all(after.get(name) == value for name, value in before.items()),
            "A previous audited declaration name, source module or axiom set changed")
    require(all(axioms <= ALLOWED_AXIOMS for _, axioms in after.values()),
            "Fresh declaration audit contains an unapproved axiom")
    require(all(current["completed_results"].get(name) == value
                for name, value in previous["completed_results"].items()),
            "A previous completed-result declaration mapping changed")

    parent_paths = tracked_paths(parent)
    parent_sources = {path for path in parent_paths if path in {"Audit.lean", "Overfull.lean"}
                      or path.startswith("Overfull/") and path.endswith(".lean")}
    require(set(previous["source_sha256"]) == parent_sources,
            "Preceding verified commit has an incomplete authoritative source inventory")
    for path in sorted(parent_sources):
        original = old_bytes(parent, path)
        require(digest(original) == previous["source_sha256"][path],
                f"Preceding source hash disagrees with its actual committed bytes: {path}")
        if path != "Overfull.lean":
            require(local(path).read_bytes() == original, f"Prior nonroot proof source changed: {path}")
    require(load(RUN / "root-added-imports.json") == ADDED_IMPORTS, "Reviewed root import list changed")
    root_bytes = (ROOT / "Overfull.lean").read_bytes()
    for added in ADDED_IMPORTS:
        encoded = added.encode()
        require(root_bytes.count(encoded) == 1, "New root import is missing or duplicated")
        root_bytes = root_bytes.replace(encoded, b"", 1)
    require(root_bytes == old_bytes(parent, "Overfull.lean"), "Proof root differs beyond its five additive imports")
    verifier_edits = check_verifier_extension(parent)

    sources, inputs = current_paths()
    require(set(current["source_sha256"]) == sources and set(current["verification_input_sha256"]) == inputs
            and sources.isdisjoint(inputs), "Fresh source/input inventory is incomplete or stale")
    previous_inputs = set(previous["verification_input_sha256"])
    require(previous_inputs <= inputs and inputs - previous_inputs == NEW_INPUTS
            and EDITED_PREVIOUS_INPUTS <= previous_inputs,
            "Verification input inventory differs beyond the four new continuation input files")
    for path in sorted(previous_inputs):
        original = old_bytes(parent, path)
        require(digest(original) == previous["verification_input_sha256"][path],
                f"Preceding verification-input hash differs from its committed bytes: {path}")
        if path not in EDITED_PREVIOUS_INPUTS:
            require(local(path).read_bytes() == original,
                    f"A prior source/provenance manifest or other unchanged verification input changed: {path}")
    actual_hashes = {path: sha(local(path)) for path in sorted(sources | inputs)}
    recorded_hashes = {**current["source_sha256"], **current["verification_input_sha256"]}
    frozen = load(RUN / "frozen-candidate-inputs.json")
    require(actual_hashes == recorded_hashes == frozen
            and command["candidate_input_hash_count"] == len(frozen),
            "Current bytes, complete verifier results and frozen input hashes disagree")

    old_coverage = json.loads(old_bytes(parent, "docs/coverage.json"))
    coverage = load(ROOT / "docs/coverage.json")
    require((ROOT / "docs/coverage.json").read_bytes() == old_bytes(parent, "docs/coverage.json"),
            "The prior coverage file is not byte-identical")
    assertions = coverage["numbered_assertions"]
    require(assertions == old_coverage["numbered_assertions"]
            and len(assertions) == coverage["numbered_assertion_count"] == 69,
            "One of the 69 complete numbered-assertion records changed")
    complete = [item for item in assertions if item["full_assertion_verified"]]
    require(len(complete) == 47 and coverage["main_theorem_verified"] is False
            and current["fully_verified_numbered_assertion_count"] == previous["fully_verified_numbered_assertion_count"] == 47
            and current["fully_verified_numbered_assertions"] == previous["fully_verified_numbered_assertions"]
            == [item["number"] for item in complete], "Preserved 47/69 assertion scope changed")

    old_maps = {}
    for key, summary in previous.items():
        if key.endswith("_declaration_map"):
            path = summary["path"]
            require(local(path).read_bytes() == old_bytes(parent, path)
                    and current.get(key) == summary and sha(local(path)) == summary["sha256"],
                    f"Prior declaration map or metadata changed: {path}")
            old_maps[key] = {"path": path, "sha256": summary["sha256"], "metadata": summary}
    native = check_new_mapping(current, after)
    require(parent_sources <= sources and sources - parent_sources == {item["path"] for item in native["modules"].values()},
            "New proof-source inventory differs from the residual-palette manifest")
    new_names = sorted(set(after) - set(before))
    require(set(new_names) == set(native["all_audited_names"])
            and set(native["public_names"]).isdisjoint(before),
            "Added audit declarations are not exactly the new modules' complete proof map")
    previous_imports, current_imports = set(previous["imported_project_modules"]), set(current["imported_project_modules"])
    require(len(current_imports) == len(current["imported_project_modules"])
            and current_imports == previous_imports | set(native["modules"])
            and previous_imports.isdisjoint(native["modules"]),
            "Checked root module inventory differs from the old modules plus exactly the new modules")

    audit_path = ROOT / "verification/axioms.log"
    audit_text = audit_path.read_text(encoding="utf-8")
    audit_records = [json.loads(line) for line in re.findall(r"^VERIFIED_DECLARATION ([^\n]+)$", audit_text, re.MULTILINE)]
    require(declaration_index(audit_records, "actual complete axiom log") == after
            and re.findall(r"^OVERFULL_AXIOM_AUDIT_OK (\d+)$", audit_text, re.MULTILINE) == [str(len(after))],
            "Actual complete axiom log disagrees with the fresh result declarations")
    for marker, key in [("IMPORTED_PROJECT_MODULE", "imported_project_modules"),
                        ("IMPORTED_EXTERNAL_MODULE", "audited_external_modules")]:
        actual = re.findall(rf"^{marker} (\S+)$", audit_text, re.MULTILINE)
        require(len(actual) == len(set(actual)) and sorted(actual) == sorted(current[key]),
                f"Actual full audit module list differs from results: {marker}")
    require(set(previous["audited_external_modules"]) <= set(current["audited_external_modules"]),
            "Previously audited external modules disappeared from the checked root")
    build_text = (ROOT / "verification/build.log").read_text(encoding="utf-8")
    build_counts = re.findall(r"^Build completed successfully \((\d+) jobs\)\.$", build_text, re.MULTILINE)
    require(len(build_counts) == 1, "Actual fresh strict build lacks one final success marker")
    jobs = int(build_counts[0])
    log_names = ["vizing-source.log", "lean-version.log", "build.log", "axioms.log"]
    expected_console = b"".join((ROOT / "verification" / name).read_bytes() for name in log_names)
    expected_console += f"Checked {len(after)} project declarations; full manuscript status: unverified.\n".encode()
    require((RUN / "verification-console.log").read_bytes() == expected_console,
            "Latest complete-verifier console is not the exact concatenation of its actual stage logs and final result")
    require((ROOT / "verification/lean-version.log").read_text().strip() == current["lean_version"],
            "Fresh observed Lean version differs from results")

    historical_paths = sorted(path for path in parent_paths
                              if path.startswith(("verification/", "recovery/")) and path not in LIVE_OUTPUTS)
    for path in historical_paths:
        require(local(path).read_bytes() == old_bytes(parent, path), f"Historical verification/recovery evidence changed: {path}")
    observations = check_observations()
    archive, development_records = check_development_archive()
    records = full_records + development_records
    statuses = {status: [item for item in records if item["status"] == status]
                for status in ["passed", "failed", "incomplete", "interrupted"]}

    # Capture all checked evidence before copying or writing any final report.
    evidence_paths = {rel(path) for path in RUN.rglob("*") if path.is_file()
                      and path.name not in REPORT_OUTPUTS and "final" not in path.relative_to(RUN).parts
                      and "__pycache__" not in path.parts and path.suffix != ".pyc"}
    evidence_paths |= sources | inputs | set(historical_paths) | LIVE_OUTPUTS
    evidence_paths |= {native["declaration_map_path"], *(item["path"] for item in old_maps.values())}
    evidence_hashes = {path: sha(local(path)) for path in sorted(evidence_paths)}
    copy_origins = [ROOT / "verification" / name for name in [*log_names, "results.json"]]
    copy_origins += [local(summary["path"]) for key, summary in current.items() if key.endswith("_declaration_map")]
    copy_origins += [RUN / name for name in ["verification-command.json", "verification-console.log", "frozen-candidate-inputs.json"]]
    copy_origins.append(local(native["source_manifest_path"]))
    require(len({path.name for path in copy_origins}) == len(copy_origins), "Ambiguous final evidence copy basenames")
    final_dir = RUN / "final"
    if final_dir.exists():
        require(all(path.is_file() and path.name in {origin.name for origin in copy_origins}
                    for path in final_dir.iterdir()), "Final directory contains unrecognized prior evidence")
        for origin in copy_origins:
            destination = final_dir / origin.name
            require(not destination.exists() or destination.read_bytes() == origin.read_bytes(),
                    f"Refusing to replace different existing final evidence: {destination.name}")
    final_dir.mkdir(exist_ok=True)
    copied = {}
    for origin in copy_origins:
        destination = final_dir / origin.name
        destination.write_bytes(origin.read_bytes())
        require(sha(destination) == evidence_hashes[rel(origin)], f"Fresh evidence copy changed: {origin.name}")
        copied[rel(destination)] = {"copied_from": rel(origin), "sha256": sha(destination)}
    require(all(sha(local(path)) == expected for path, expected in evidence_hashes.items()),
            "A checked source, result, command or historical evidence file changed during preservation checking")
    # Detect a newer attempt even if the alias writer has not yet updated its files.
    require({rel(path) for path in RUN.glob("full-*/command.json")} == {item["metadata_path"] for item in full_records},
            "A new full verifier attempt started during preservation checking")

    now = datetime.now(timezone.utc)
    record = {
        "schema_version": 1, "status": "verification_and_preservation_passed", "run_id": RUN.name,
        "run_started_at_utc": run["started_at_utc"], "recorded_at_utc": now.isoformat(),
        "verified_baseline_commit": VERIFIED_BASELINE,
        "native_reserve_source_checkpoint": SOURCE_CHECKPOINT,
        "actual_preceding_native_verified_commit": parent,
        "checked_worktree_head": git("rev-parse", "HEAD").decode().strip(),
        "comparison_commit_note": "Preservation is checked against the actual preceding native-verified commit argument. The source manifest retains the earlier verified baseline and source-only checkpoint as historical provenance.",
        "verification_command": command, "latest_complete_verifier_attempt": command["attempt"],
        "strict_build_jobs": jobs, "verified_declaration_count": len(after),
        "previous_verified_declarations_preserved": len(before),
        "new_verified_declaration_count": len(new_names), "new_verified_declarations": new_names,
        "all_prior_declaration_names_modules_and_axiom_sets_preserved": True,
        "previous_completed_result_mappings_preserved": len(previous["completed_results"]),
        "byte_identical_previous_nonroot_lean_source_count": len(parent_sources) - 1,
        "all_previous_nonroot_lean_sources_byte_identical": True,
        "root_added_imports_only": [line.strip() for line in ADDED_IMPORTS],
        "stock_audit_byte_identical": True,
        "verifier_previous_gates_byte_preserved_after_four_declared_extensions": True,
        "verifier_exact_additive_edits": verifier_edits, "previous_declaration_maps_byte_identical": old_maps,
        "byte_identical_previous_verification_input_count": len(previous_inputs - EDITED_PREVIOUS_INPUTS),
        "all_previous_source_and_provenance_manifests_byte_identical": True,
        "explicitly_edited_previous_verification_inputs": sorted(EDITED_PREVIOUS_INPUTS),
        "new_verification_input_paths": sorted(NEW_INPUTS),
        "coverage_file_byte_identical": True,
        "all_69_original_numbered_assertion_records_and_statement_hashes_preserved": True,
        "all_47_completed_assertion_records_preserved": True,
        "fully_verified_numbered_assertion_count": 47, "remaining_numbered_assertion_count": 22,
        "numbered_assertions_completed_in_this_run": 0, "main_theorem_verified": False,
        "source_hash_count": len(sources), "verification_input_hash_count": len(inputs),
        "frozen_input_count": len(frozen), "all_source_and_input_hashes_match_frozen_candidate": True,
        "source_public_proof_inventory_recomputed": True, "raw_audit_and_result_declarations_agree": True,
        "console_is_exact_actual_stage_log_concatenation": True,
        "imported_project_module_count": len(current_imports), "allowed_logical_axioms": current["allowed_logical_axioms"],
        "residual_palette": native, "preserved_historical_evidence_paths": historical_paths,
        "development_archive": archive, "retained_observations": observations,
        "retained_command_count": len(records), "successful_command_count": len(statuses["passed"]),
        "failed_command_count": len(statuses["failed"]), "incomplete_command_count": len(statuses["incomplete"]),
        "interrupted_command_count": len(statuses["interrupted"]), "command_evidence": records,
        "command_count_note": "Counts include distinct archived command records, not duplicate aggregate references. Metadata observations and unrecorded-time raw outputs remain separately identified.",
        "copied_fresh_outputs": copied,
        "evidence_sha256": {**evidence_hashes, **{path: item["sha256"] for path, item in copied.items()}},
        "next_target": {"path": "docs/continuation-handoff.md", "sha256": sha(ROOT / "docs/continuation-handoff.md"),
                        "status": "internal_exceptional_and_robust_completion_unproved"},
        "publication": {"repository": run["repository"], "target_branches": run["target_branches"],
                        "status": "pending_verified_branch_updates",
                        "note": "This report precedes publication of this continuation and makes no claim that its verified-branch updates succeeded."},
    }
    module_rows = "\n".join(f"| `{name}` | {item['public_theorem_count']} |"
                            for name, item in native["modules"].items())
    attempt_rows = "\n".join(f"| `{Path(item['metadata_path']).parent.name}` | {item['status']} | {item['exit_code']} | `{item['log_path']}` |"
                             for item in full_records)
    report = f"""# Native residual joining palettes: verification and preservation

**The exact frozen candidate passed the complete strict Lean verifier and the unchanged full axiom audit.**
The successful latest attempt is `{command['attempt']}` in run `{RUN.name}`.
This supplementary preservation report was recorded at `{now.isoformat()}`;
it does not replace the compiler or axiom audit.

## Exact comparison and provenance

| Reference | Commit |
| --- | --- |
| Actual preceding native-reserve verified commit, used for preservation | `{parent}` |
| Earlier verified baseline retained in the source manifest | `{VERIFIED_BASELINE}` |
| Earlier native-reserve source-only checkpoint retained in the source manifest | `{SOURCE_CHECKPOINT}` |

The earlier source checkpoint and the actual preceding verified commit have
different roles. Every preservation comparison uses the actual preceding
verified commit supplied to this checker. The frozen source manifest keeps
its historical baseline and source-checkpoint fields unchanged.

## Mathematical scope

{native['scope']}

The uniform parameter theorem chooses the surviving robustness `θ>0`, with
`θ≤σ`, before the requested surplus error `δ`. The actual residual joining
degree bounds use the original representative's assignment, preserve actual
parallel copies, and give the natural degree bound needed by the palette
construction. The prior completion theorem and all prior proof sources are
retained byte-for-byte.

The joining classes are actual matchings that are disjoint and cover all
joining copies exactly once. Their certificates retain per-class cut parity,
at most `3L` copies and `6L` support vertices per class, and at most `D`
classes meeting each vertex. The odd assigned-part case selects `⌊r/2⌋`
distinct surviving original reserve crossings. The composed protected-palette
theorem makes each selected crossing an entire singleton joining class under
its explicit margin `6D+⌊r/2⌋<h` and capacity
`nD≤2L(h-6D-⌊r/2⌋)`. Separate quantitative budget proofs supply positive
capacity and small whole-class footprints under their stated bounds.

These singleton joining classes are not yet complete reserved boundary color
classes. Internal exceptional incidences, the equal-free-palette construction
for an exceptional pair with arbitrary parallel copies, old-core uncovered
parity after that internal extension, robust perfect-matching completions,
and final factorization/reconstruction remain open. The full two-core
Corollary 4.6, full five-exception statement and main theorem remain incomplete.
**No numbered assertion is added: coverage remains 47/69, with 22 incomplete.**

| New module | Mapped public theorem proofs |
| --- | ---: |
{module_rows}

The {native['module_count']} new modules contain {native['public_theorem_count']}
mapped public theorem proofs and {native['audited_declaration_count']} audited
proof declarations including private and generated support. The full audit,
source manifest and declaration map agree on all of them.

## Observed verification and preservation

| Check | Observed result |
| --- | --- |
| Latest complete verifier | Exit 0; all frozen inputs unchanged |
| Strict `lake build --wfail` | {jobs:,} jobs passed |
| Unchanged full `Audit.lean` | {len(after):,} declarations passed |
| Prior declarations, modules and axiom sets | All {len(before):,} preserved |
| Newly audited declarations | {len(new_names):,} |
| Prior nonroot Lean proof sources | {len(parent_sources)-1} byte-identical |
| Previous declaration maps and metadata | All {len(old_maps)} unchanged |
| Previous source/provenance manifests and other preserved inputs | {len(previous_inputs - EDITED_PREVIOUS_INPUTS)} byte-identical |
| Previous completed-result mappings | All {len(previous['completed_results']):,} retained |
| Numbered assertion records | All 69 unchanged; all 47 completed records retained |
| Frozen sources and verification inputs | {len(frozen)} exact SHA256 matches |
| Archived development files | All {archive['file_count']} exact SHA256 matches |
| Historical verification/recovery paths | All {len(historical_paths)} byte-identical |

The stock audit is unchanged. The verifier differs only by the four recorded
additive residual-palette manifest and mapping edits; the proof root differs
only by five declared imports. Lean remains 4.24.0 and mathlib remains
`f897ebcf72cd16f89ab4577d0c826cd14afaafc7`. Logical axioms remain limited
to `propext`, `Classical.choice`, and `Quot.sound`.
All previous verification inputs are byte-identical except the explicitly
updated README, continuation handoff and verifier; the latter is restricted
to its exact four additive edits. All prior source/provenance manifest JSON
files and earlier proof maps remain unchanged.

The actual raw axiom records and imported-module lists agree with the fresh
results. The latest console is exactly the concatenation of the four actual
stage logs and the final verifier summary. The `final/` directory contains
byte-for-byte copies of those logs, all latest declaration maps, results,
the frozen inputs, latest command/console and new source manifest. No earlier
verification output was replayed as a current result.

## Retained failures and development evidence

| Complete-verifier attempt | Recorded status | Exit code | Actual output |
| --- | --- | ---: | --- |
{attempt_rows}

`full-01` genuinely failed because the source manifest had not been generated.
The initial manifest scanner confused a named Lean section with a namespace;
its exact failed script and observed error remain archived. `full-02`
genuinely failed because new root imports followed a non-import command.
Both attempts retain their original command metadata, frozen inputs, source
snapshots and failure logs; their inspected hashes are pinned by this checker.
The setup-path failure and successful targeted initial integration observation
also remain intact. The latter preserves its raw tool output without inventing
an unrecorded start time.

There are {len(records)} distinct retained command records: {len(statuses['passed'])}
successful, {len(statuses['failed'])} failed, {len(statuses['interrupted'])} interrupted,
and {len(statuses['incomplete'])} incomplete. Development commands establish
only their recorded targeted results; the latest full attempt supplies the
complete verification claim. Source snapshots and recorded output hashes
were checked. Recorded dependency hashes are retained as provenance; no
missing dependency snapshots or missing timing metadata are reconstructed.

## Publication and remaining work

Publication of this continuation to the authorized verified branches is
pending. This report makes no claim that those branch updates succeeded.
Publish the exact checked sources and genuine evidence, preserve concurrent
work, and record the actual resulting commit/tree identifiers after readback.

The continuation handoff identifies the next internal exceptional completion
and robust completion obligations. The protected joining palette is a proved
intermediate result under its explicit hypotheses, not a final factorization.
"""
    (RUN / "preservation.json").write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
    (RUN / "final-report.md").write_text(report, encoding="utf-8")
    print(json.dumps({key: record[key] for key in [
        "status", "actual_preceding_native_verified_commit", "latest_complete_verifier_attempt",
        "strict_build_jobs", "verified_declaration_count", "previous_verified_declarations_preserved",
        "new_verified_declaration_count", "source_hash_count", "verification_input_hash_count",
        "failed_command_count", "fully_verified_numbered_assertion_count", "main_theorem_verified",
    ]}, indent=2))


if __name__ == "__main__":
    main()
