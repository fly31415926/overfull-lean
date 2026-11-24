#!/usr/bin/env python3
"""Validate weighted-palette verification and exact baseline preservation.

Run after the latest complete verifier has passed:
    python3 verification/runs/20261123T230808Z/record-final.py

This supplementary checker does not run Lean, rebuild proofs, modify the
verifier, or replace the unchanged Audit.lean. All success outputs are
written only after the consistency and preservation gates below pass.
Capture this command's output outside the run folder until it finishes.
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
BASELINE = "c28cec49522e1537452ee9fdc3b2baf3ca1cc3b2"
BASELINE_TREE = "6a9e73eee4e944b104ff98630b04655e8bfb959d"
BASELINE_FILE_COUNT = 2355
BASELINE_DECLARATION_COUNT = 12738
BASELINE_COMPLETED_MAPPING_COUNT = 1938
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
EDITED_PREVIOUS_INPUTS = {
    "README.md", "docs/continuation-handoff.md", "scripts/verify.py", "docs/coverage.json",
}
NEW_INPUTS = {
    "docs/weighted-palette-source.json", "docs/weighted-palette-semantic-review.md",
    "docs/weighted-palette-verification.md", "scripts/update_weighted_palette_manifest.py",
}
LIVE_OUTPUTS = {
    "verification/results.json", "verification/build.log", "verification/axioms.log",
    "verification/lean-version.log", "verification/vizing-source.log",
}
REPORT_OUTPUTS = {"preservation.json", "final-report.md", "record-final-output.log"}
VERIFIER_EDITS = [{'old': '                          ("exceptional_palette", "exceptional-palette-source.json")):\n',
  'new': '                          ("exceptional_palette", "exceptional-palette-source.json"),\n'
         '                          ("weighted_palette", "weighted-palette-source.json")):\n'},
 {'old': '    # Every first-party mathematical file must be included in the library build.\n',
  'new': '    if extension_maps["weighted_palette"][0]["numbered_assertions_completed"] != 0:\n'
         '        raise SystemExit("The weighted-palette continuation completes no numbered manuscript '
         'assertion.")\n'
         '\n'
         '    # Every first-party mathematical file must be included in the library build.\n'},
 {'old': '                    "exceptional_palette": "exceptional-palette"}[key]\n',
  'new': '                    "exceptional_palette": "exceptional-palette",\n'
         '                    "weighted_palette": "weighted-palette"}[key]\n'},
 {'old': '        "exceptional_palette_declaration_map": extension_evidence["exceptional_palette"],\n',
  'new': '        "exceptional_palette_declaration_map": extension_evidence["exceptional_palette"],\n'
         '        "weighted_palette_declaration_map": extension_evidence["weighted_palette"],\n'}]


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


def check_verifier_extension() -> list[dict]:
    """Require the exact four reviewed additive substitutions, without skips."""
    expected = old_bytes(BASELINE, "scripts/verify.py")
    for edit in VERIFIER_EDITS:
        old, new = edit["old"].encode(), edit["new"].encode()
        require(expected.count(old) == 1, "Ambiguous or missing reviewed verifier insertion")
        expected = expected.replace(old, new, 1)
    require((ROOT / "scripts/verify.py").read_bytes() == expected,
            "Verifier differs beyond the four exact additive weighted-palette extensions")
    manifest = RUN / "verifier-additions.json"
    if manifest.exists():
        require(load(manifest) == VERIFIER_EDITS, "Verifier-additions record differs from reviewed edits")
    return VERIFIER_EDITS


def check_root_imports(modules: set[str]) -> list[str]:
    additions = load(RUN / "root-added-imports.json")
    require(isinstance(additions, list) and bool(additions)
            and len(additions) == len(set(additions)), "Malformed or duplicate root-added-import list")
    for line in additions:
        require(isinstance(line, str) and re.fullmatch(
            r"import Overfull\.WeightedPalette\.[A-Za-z0-9_]+\n", line) is not None
            and line[len("import "):].strip() in modules,
            f"Root addition is not an exact import of a new mapped module: {line!r}")
    original = old_bytes(BASELINE, "Overfull.lean")
    prefix = re.match(rb"(?:import [^\n]+\n|\n)*import [^\n]+\n", original)
    require(prefix is not None and original[prefix.end():].startswith(b"\n/-!"),
            "Baseline root has an unexpected import-prefix/documentation layout")
    expected = original[:prefix.end()] + "".join(additions).encode() + original[prefix.end():]
    require((ROOT / "Overfull.lean").read_bytes() == expected,
            "Root differs beyond a contiguous import block after the complete old prefix")
    return additions


def check_new_mapping(current: dict, audited: dict) -> dict:
    source_path = ROOT / "docs/weighted-palette-source.json"
    map_path = ROOT / "verification/weighted-palette-declarations.json"
    source, mapping = load(source_path), load(map_path)
    require(source["baseline_commit"] == BASELINE and source["baseline_tree"] == BASELINE_TREE
            and source["baseline_publication_status"] == "published"
            and source["kind"] == "supporting_continuation"
            and source["numbered_assertions_completed"] == 0
            and source["main_theorem_verified"] is False,
            "Weighted-palette manifest has wrong baseline, publication status or mathematical scope")
    require(source["review"] == "docs/weighted-palette-semantic-review.md"
            and source["proof_map"] == "docs/weighted-palette-verification.md"
            and isinstance(source["scope"], str) and bool(source["scope"]),
            "Weighted-palette source/review mapping is incomplete")
    modules = {item["module"]: item for item in source["modules"]}
    require(0 < len(modules) == len(source["modules"]) == source["module_count"],
            "New module inventory is empty, duplicated or has a wrong count")
    public = {}
    for module, item in modules.items():
        path = local(item["path"])
        require(re.fullmatch(r"Overfull\.WeightedPalette\.[A-Za-z0-9_]+", module) is not None
                and item["path"] == module.replace(".", "/") + ".lean"
                and sha(path) == item["sha256"], f"New source path/hash mismatch: {module}")
        require(source_public_proofs(path) == item["public_proof_declarations"],
                f"New public proof names or source lines differ from the actual source: {module}")
        names = [entry["name"] for entry in item["public_proof_declarations"]]
        require(len(names) == len(set(names)) == item["public_theorem_count"],
                f"New public theorem count disagrees: {module}")
        for name in names:
            require(name not in public and name in audited and audited[name][0] == module,
                    f"New public proof missing, duplicated or audited in a different module: {name}")
            public[name] = module
    require(set(public) == set(source["required_proof_declarations"])
            and len(public) == len(source["required_proof_declarations"]) == source["public_theorem_count"],
            "New required-public-proof inventory is incomplete")
    expected = {name: value for name, value in audited.items() if value[0] in modules}
    actual = declaration_index(mapping["proof_declaration_map"], "weighted-palette declaration map")
    require(actual == expected and {entry[0] for entry in actual.values()} == set(modules),
            "New complete declaration map differs from the actual full audit")
    for item in mapping["proof_declaration_map"]:
        module = modules[item["module"]]
        require(item["source_path"] == module["path"] and item["source_sha256"] == module["sha256"],
                f"New audited declaration is not bound to the current checked source: {item['name']}")
    summary = current["weighted_palette_declaration_map"]
    require(summary["path"] == rel(map_path) and summary["sha256"] == sha(map_path),
            "Current result points to a stale new declaration map")
    for key, value in [("module_count", len(modules)), ("public_theorem_count", len(public)),
                       ("verified_declaration_count", len(actual)), ("numbered_assertions_completed", 0)]:
        require(summary[key] == mapping[key] == value, f"New result/map count mismatch: {key}")
    require(mapping["kind"] == source["kind"]
            and mapping["includes_private_and_generated_proofs"] is True
            and mapping["manuscript_number"] is None and mapping["statement_sha256"] is None,
            "New declaration map omits supporting proofs or claims a complete numbered assertion")
    return {"source_manifest_path": rel(source_path), "source_manifest_sha256": sha(source_path),
            "declaration_map_path": rel(map_path), "declaration_map_sha256": sha(map_path),
            "modules": modules, "public_names": sorted(public),
            "all_audited_names": sorted(actual), "module_count": len(modules),
            "public_theorem_count": len(public), "audited_declaration_count": len(actual),
            "scope": source["scope"], "review_path": source["review"], "proof_map_path": source["proof_map"]}


def command_record(path: Path, data: dict) -> dict:
    """Read genuine diagnostics without inventing missing execution metadata."""
    require(isinstance(data.get("command"), list) and bool(data["command"])
            and all(isinstance(part, str) for part in data["command"]),
            f"Malformed actual command record: {rel(path)}")
    if (path.parent / "output.log").is_file():
        logs = [path.parent / "output.log"]
    else:
        logs = [path.parent / name for name in ["stdout.log", "stderr.log"]
                if (path.parent / name).is_file()]
    require(bool(logs), f"Missing exact command output: {rel(path)}")
    code = data.get("exit_code")
    if code is None:
        status = "incomplete"
        require(data.get("status") in {None, "running", "incomplete"},
                f"Unfinished diagnostic claims completion: {rel(path)}")
    else:
        require(type(code) is int, f"Nonintegral command exit code: {rel(path)}")
        if data.get("status") == "interrupted":
            require(code == 130 and (data.get("reason") or data.get("interruption_reason")),
                    f"Interrupted command lacks an actual reason/status: {rel(path)}")
            status = "interrupted"
        else:
            status = "passed" if code == 0 and data.get("all_frozen_inputs_unchanged") is not False else "failed"
            require(data.get("status", status) == status,
                    f"Command status disagrees with exit/frozen-input result: {rel(path)}")
    start = next((data[key] for key in ["started_at_utc", "started_at"] if data.get(key)), None)
    finish = next((data[key] for key in ["finished_at_utc", "completed_at_utc", "ended_at_utc",
                                        "finished_at", "interruption_observed_at_utc"] if data.get(key)), None)
    if start is not None:
        timestamp(start)
        if code is not None:
            require(finish is not None and timestamp(start) <= timestamp(finish),
                    f"Completed command lacks ordered completion timestamps: {rel(path)}")
    snapshots = {}
    recorded_sources = data.get("source_sha256")
    if isinstance(recorded_sources, dict):
        require(len({Path(source).name for source in recorded_sources}) == len(recorded_sources),
                f"Ambiguous recorded source snapshot basenames: {rel(path)}")
        for source, expected in recorded_sources.items():
            local(source)
            nested = path.parent / "source" / source
            snapshot = nested if nested.is_file() else path.parent / Path(source).name
            require(snapshot.is_file() and sha(snapshot) == expected,
                    f"Recorded source snapshot differs: {rel(snapshot)}")
            snapshots[rel(snapshot)] = expected
    elif isinstance(recorded_sources, str):
        source_args = [part for part in data["command"] if part.endswith(".lean")]
        require(bool(source_args), f"A source hash has no actual Lean source argument: {rel(path)}")
        snapshot = path.parent / Path(source_args[-1]).name
        require(snapshot.is_file() and sha(snapshot) == recorded_sources,
                f"Recorded source snapshot differs: {rel(snapshot)}")
        snapshots[rel(snapshot)] = recorded_sources
    else:
        require(recorded_sources is None, f"Malformed source-hash field: {rel(path)}")
        for argument in data["command"]:
            if argument.endswith(".lean"):
                snapshot = path.parent / Path(argument).name
                require(snapshot.is_file(), f"Actual Lean diagnostic lacks its retained source: {rel(path)}")
                snapshots[rel(snapshot)] = sha(snapshot)
    if "final_source_sha256" in data:
        require(data["final_source_sha256"] == recorded_sources,
                f"Source changed during the recorded targeted check: {rel(path)}")
    if "output_sha256" in data:
        require(len(logs) == 1 and data["output_sha256"] == sha(logs[0]),
                f"Recorded output hash differs: {rel(path)}")
    return {"metadata_path": rel(path), "metadata_sha256": sha(path),
            "command": data["command"], "status": status, "exit_code": code,
            "logs": [{"path": rel(log), "sha256": sha(log)} for log in logs],
            "source_snapshots": snapshots, "source_hashes_in_original_command": recorded_sources is not None,
            "dependency_hash_records_retained": len(data.get("input_sha256", data.get("dependency_source_sha256", {}))),
            "timing_recorded": start is not None,
            "provenance_note": "Missing original metadata is not reconstructed; archived snapshot and log hashes describe the retained bytes."}


def full_attempts() -> tuple[list[dict], dict]:
    paths = sorted(RUN.glob("full-*/command.json"))
    require(bool(paths), "No complete-verifier command records exist")
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
                f"Verifier source snapshots differ from their own frozen candidate: {rel(path)}")
        records.append(command_record(path, data))
        ordered.append((timestamp(data["started_at_utc"]), path.parent.name, data))
    require(len({start for start, _, _ in ordered}) == len(ordered), "Ambiguous latest verifier start")
    _, latest_name, latest = max(ordered, key=lambda item: item[0])
    require(latest["status"] == "passed" and latest["exit_code"] == 0
            and latest.get("all_frozen_inputs_unchanged") is True,
            f"Latest complete verifier {latest_name} has not passed with unchanged frozen inputs")
    for alias, original in [("verification-command.json", "command.json"),
                            ("frozen-candidate-inputs.json", "frozen-candidate-inputs.json"),
                            ("verification-console.log", "output.log")]:
        require((RUN / alias).read_bytes() == (RUN / latest_name / original).read_bytes(),
                f"Latest verifier alias differs from the actual latest attempt: {alias}")
    return records, latest


def check_development_archive() -> tuple[dict, list[dict]]:
    archive_path = RUN / "development-archive.json"
    archive = load(archive_path)
    require(archive["kind"] == "genuine_development_evidence"
            and archive["file_count"] == len(archive["files"]), "Malformed development archive inventory")
    indexed = {}
    prefix = rel(RUN / "development") + "/"
    for item in archive["files"]:
        path = item["path"]
        require(path.startswith(prefix) and path not in indexed
                and isinstance(item["recorded_at_path"], str) and Path(item["recorded_at_path"]).is_absolute()
                and sha(local(path)) == item["sha256"], f"Archived development path/hash differs: {path}")
        # Recheck the original bytes when that scratch source still exists.
        original = Path(item["recorded_at_path"])
        if original.is_file():
            require(sha(original) == item["sha256"], f"Archive differs from its still-available source: {path}")
        indexed[path] = item["sha256"]
    require(set(indexed) == {rel(path) for path in (RUN / "development").rglob("*") if path.is_file()},
            "Development archive has unlisted or missing files")
    records = []
    for path in sorted((RUN / "development").rglob("*.json")):
        data = load(path)
        if isinstance(data, dict) and isinstance(data.get("command"), list):
            require(path.name == "command.json", f"Unrecognized command metadata layout: {rel(path)}")
            records.append(command_record(path, data))
    return {"path": rel(archive_path), "sha256": sha(archive_path), "file_count": len(indexed),
            "all_recorded_byte_hashes_match": True, "files": indexed}, records


def main() -> None:
    require(len(sys.argv) == 1 or len(sys.argv) == 2 and sys.argv[1] == BASELINE,
            "Usage: record-final.py [c28cec49522e1537452ee9fdc3b2baf3ca1cc3b2]")
    require(git("rev-parse", f"{BASELINE}^{{commit}}").decode().strip() == BASELINE
            and git("rev-parse", f"{BASELINE}^{{tree}}").decode().strip() == BASELINE_TREE,
            "The pinned preceding verified commit/tree is unavailable or changed")
    full_records, command = full_attempts()
    run = load(RUN / "run.json")
    require(run["run_id"] == RUN.name
            and run["baseline_local_verified_commit"] == BASELINE
            and run["baseline_local_verified_tree"] == BASELINE_TREE,
            "Run metadata identifies a different continuation or verified baseline")
    require(timestamp(run["started_at_utc"]) <= timestamp(command["started_at_utc"])
            <= timestamp(command["completed_at_utc"]), "Latest verifier timestamps do not belong to this run")

    previous = json.loads(old_bytes(BASELINE, "verification/results.json"))
    current = load(ROOT / "verification/results.json")
    for label, result in [("preceding verified commit", previous), ("fresh result", current)]:
        require(result["lean_build_passed"] is True and result["axiom_audit_passed"] is True
                and result["status"] == "partial_formalization" and result["main_theorem_verified"] is False,
                f"Invalid verification status or main-theorem scope in {label}")
        require(set(result["allowed_logical_axioms"]) == ALLOWED_AXIOMS
                and result["declaration_count_includes_generated_support_lemmas"] is True,
                f"Changed logical axiom allowance or support-proof scope in {label}")
    require("exceptional_palette_declaration_map" in previous and "weighted_palette_declaration_map" not in previous,
            "Pinned baseline is not the preceding exceptional-palette verified result")
    require(current["toolchain"] == previous["toolchain"] == "leanprover/lean4:v4.24.0"
            and current["mathlib_revision"] == previous["mathlib_revision"] == "f897ebcf72cd16f89ab4577d0c826cd14afaafc7"
            and current["dependency_source_revisions"] == previous["dependency_source_revisions"],
            "Pinned Lean, mathlib or dependency-source revisions changed")
    for key in ["full_sharpness_proposition_verified", "density_corollary_verified", "vizing_source",
                "matching_polytope_source", "circulation_source", "checkpoint_reconstruction"]:
        require(current[key] == previous[key], f"A preceding verified scope/provenance field changed: {key}")
    before = declaration_index(previous["verified_declarations"], "preceding verified result")
    after = declaration_index(current["verified_declarations"], "fresh complete result")
    require(len(before) == previous["verified_declaration_count"] == BASELINE_DECLARATION_COUNT
            and len(previous["completed_results"]) == BASELINE_COMPLETED_MAPPING_COUNT,
            "Pinned preceding verification counts disagree with the actual committed result")
    require(len(after) == current["verified_declaration_count"]
            and all(after.get(name) == value for name, value in before.items()),
            "A previous audited declaration name, module or axiom set changed")
    require(all(axioms <= ALLOWED_AXIOMS for _, axioms in after.values()),
            "Fresh audited declaration depends on an unapproved axiom")
    require(all(current["completed_results"].get(name) == value
                for name, value in previous["completed_results"].items()),
            "A previous completed-result declaration mapping changed")

    baseline_paths = tracked_paths(BASELINE)
    require(len(baseline_paths) == BASELINE_FILE_COUNT, "Pinned baseline file inventory count changed")
    baseline_sources = {path for path in baseline_paths if path in {"Audit.lean", "Overfull.lean"}
                        or path.startswith("Overfull/") and path.endswith(".lean")}
    require(set(previous["source_sha256"]) == baseline_sources,
            "Preceding verified source inventory omits committed mathematical sources")
    for path in sorted(baseline_sources):
        original = old_bytes(BASELINE, path)
        require(digest(original) == previous["source_sha256"][path],
                f"Baseline source hash differs from its committed bytes: {path}")
        if path != "Overfull.lean":
            require(local(path).read_bytes() == original, f"Prior nonroot mathematical source changed: {path}")
    verifier_edits = check_verifier_extension()

    sources, inputs = current_paths()
    require(set(current["source_sha256"]) == sources and set(current["verification_input_sha256"]) == inputs
            and sources.isdisjoint(inputs), "Fresh verification source/input inventory is incomplete or stale")
    previous_inputs = set(previous["verification_input_sha256"])
    require(previous_inputs <= inputs and inputs - previous_inputs == NEW_INPUTS
            and EDITED_PREVIOUS_INPUTS <= previous_inputs,
            "Input inventory differs beyond the four new weighted-palette input files")
    for path in sorted(previous_inputs):
        original = old_bytes(BASELINE, path)
        require(digest(original) == previous["verification_input_sha256"][path],
                f"Baseline verification-input hash differs from committed bytes: {path}")
        if path not in EDITED_PREVIOUS_INPUTS:
            require(local(path).read_bytes() == original,
                    f"Prior source/provenance manifest or other unchanged verification input changed: {path}")
    actual_hashes = {path: sha(local(path)) for path in sorted(sources | inputs)}
    recorded_hashes = {**current["source_sha256"], **current["verification_input_sha256"]}
    frozen = load(RUN / "frozen-candidate-inputs.json")
    require(actual_hashes == recorded_hashes == frozen
            and command["candidate_input_hash_count"] == len(frozen),
            "Current bytes, actual full-verifier results and frozen hashes disagree")

    old_coverage = json.loads(old_bytes(BASELINE, "docs/coverage.json"))
    coverage = load(ROOT / "docs/coverage.json")
    require(isinstance(coverage.get("scope"), str) and bool(coverage["scope"])
            and {k: v for k, v in coverage.items() if k != "scope"}
            == {k: v for k, v in old_coverage.items() if k != "scope"},
            "Coverage changed beyond the single permitted top-level scope string")
    assertions = coverage["numbered_assertions"]
    require(assertions == old_coverage["numbered_assertions"]
            and len(assertions) == coverage["numbered_assertion_count"] == 69,
            "One of the 69 original assertion records or statement hashes changed")
    complete = [item for item in assertions if item["full_assertion_verified"]]
    require(len(complete) == 47 and coverage["main_theorem_verified"] is False
            and current["fully_verified_numbered_assertion_count"] == previous["fully_verified_numbered_assertion_count"] == 47
            and current["fully_verified_numbered_assertions"] == previous["fully_verified_numbered_assertions"]
            == [item["number"] for item in complete], "Preserved 47/69 complete-assertion scope changed")
    scope_change = {"path": "docs/coverage.json", "old_scope": old_coverage["scope"],
                    "new_scope": coverage["scope"], "scope_changed": old_coverage["scope"] != coverage["scope"],
                    "all_other_parsed_fields_identical": True,
                    "baseline_sha256": digest(old_bytes(BASELINE, "docs/coverage.json")),
                    "current_sha256": sha(ROOT / "docs/coverage.json")}

    old_maps = {}
    for key, summary in previous.items():
        if key.endswith("_declaration_map"):
            path = summary["path"]
            require(local(path).read_bytes() == old_bytes(BASELINE, path)
                    and current.get(key) == summary and sha(local(path)) == summary["sha256"],
                    f"Prior declaration map or summary metadata changed: {path}")
            old_maps[key] = {"path": path, "sha256": summary["sha256"], "metadata": summary}
    extension = check_new_mapping(current, after)
    require(baseline_sources <= sources
            and sources - baseline_sources == {item["path"] for item in extension["modules"].values()},
            "New mathematical-source inventory differs from the weighted-palette manifest")
    additions = check_root_imports(set(extension["modules"]))
    new_names = sorted(set(after) - set(before))
    require(set(new_names) == set(extension["all_audited_names"])
            and set(extension["public_names"]).isdisjoint(before),
            "New audit declarations are not exactly the complete new-module proof inventory")
    expected_completed = dict(previous["completed_results"])
    expected_completed.update({f"weighted_palette_closure_{i}": name
                               for i, name in enumerate(extension["public_names"], 1)})
    require(current["completed_results"] == expected_completed,
            "Completed-result mappings differ beyond the exact new public theorem mapping")
    previous_imports = set(previous["imported_project_modules"])
    current_imports = set(current["imported_project_modules"])
    require(len(current_imports) == len(current["imported_project_modules"])
            and current_imports == previous_imports | set(extension["modules"])
            and previous_imports.isdisjoint(extension["modules"]),
            "Actual imported mathematical-module inventory differs from old modules plus exactly the new ones")

    audit_text = (ROOT / "verification/axioms.log").read_text(encoding="utf-8")
    audit_records = [json.loads(line) for line in re.findall(r"^VERIFIED_DECLARATION ([^\n]+)$", audit_text, re.MULTILINE)]
    require(declaration_index(audit_records, "actual complete axiom log") == after
            and re.findall(r"^OVERFULL_AXIOM_AUDIT_OK (\d+)$", audit_text, re.MULTILINE) == [str(len(after))],
            "Actual complete axiom log disagrees with current verified declarations")
    for marker, key in [("IMPORTED_PROJECT_MODULE", "imported_project_modules"),
                        ("IMPORTED_EXTERNAL_MODULE", "audited_external_modules")]:
        actual = re.findall(rf"^{marker} (\S+)$", audit_text, re.MULTILINE)
        require(len(actual) == len(set(actual)) and sorted(actual) == sorted(current[key]),
                f"Actual full audit module list differs from current results: {marker}")
    require(current["audited_external_modules"] == previous["audited_external_modules"],
            "Previously audited external-module inventory changed")
    build_text = (ROOT / "verification/build.log").read_text(encoding="utf-8")
    build_counts = re.findall(r"^Build completed successfully \((\d+) jobs\)\.$", build_text, re.MULTILINE)
    require(len(build_counts) == 1, "Actual fresh strict build lacks one final success marker")
    jobs = int(build_counts[0])
    log_names = ["vizing-source.log", "lean-version.log", "build.log", "axioms.log"]
    expected_console = b"".join((ROOT / "verification" / name).read_bytes() for name in log_names)
    expected_console += f"Checked {len(after)} project declarations; full manuscript status: unverified.\n".encode()
    require((RUN / "verification-console.log").read_bytes() == expected_console,
            "Latest full-verifier console is not the exact concatenation of its actual stage logs and final summary")
    require((ROOT / "verification/lean-version.log").read_text().strip() == current["lean_version"],
            "Actual observed Lean version differs from the current result")

    # Every baseline file is immutable except these explicitly reviewed current files.
    permitted_changed = EDITED_PREVIOUS_INPUTS | LIVE_OUTPUTS | {"Overfull.lean"}
    preserved_paths = sorted(baseline_paths - permitted_changed)
    for path in preserved_paths:
        require(local(path).read_bytes() == old_bytes(BASELINE, path),
                f"A preceding source, documentation, mapping or historical artifact changed: {path}")
    historical_paths = [path for path in preserved_paths if path.startswith(("verification/", "recovery/"))]
    archive, development_records = check_development_archive()
    supplementary_records = []
    for path in sorted(RUN.glob("preservation-check-*/command.json")):
        data = load(path)
        require(data.get("cwd") == str(ROOT), f"Wrong supplementary-check working directory: {rel(path)}")
        supplementary_records.append(command_record(path, data))
    records = full_records + development_records + supplementary_records
    require(len({item["metadata_path"] for item in records}) == len(records),
            "A diagnostic command is counted more than once")
    statuses = {status: [item for item in records if item["status"] == status]
                for status in ["passed", "failed", "incomplete", "interrupted"]}

    # Freeze all checked evidence before writing any successful report.
    evidence_paths = {rel(path) for path in RUN.rglob("*") if path.is_file()
                      and path.name not in REPORT_OUTPUTS and "final" not in path.relative_to(RUN).parts
                      and "__pycache__" not in path.parts and path.suffix != ".pyc"}
    evidence_paths |= sources | inputs | set(preserved_paths) | LIVE_OUTPUTS
    evidence_paths.add(extension["declaration_map_path"])
    evidence_hashes = {path: sha(local(path)) for path in sorted(evidence_paths)}
    copy_origins = [ROOT / "verification" / name for name in [*log_names, "results.json"]]
    copy_origins += [local(summary["path"]) for key, summary in current.items() if key.endswith("_declaration_map")]
    copy_origins += [RUN / name for name in ["verification-command.json", "verification-console.log", "frozen-candidate-inputs.json"]]
    copy_origins.append(local(extension["source_manifest_path"]))
    require(len({path.name for path in copy_origins}) == len(copy_origins), "Ambiguous final-copy evidence basenames")
    final_dir = RUN / "final"
    if final_dir.exists():
        require(all(path.is_file() and path.name in {origin.name for origin in copy_origins}
                    for path in final_dir.iterdir()), "Final directory contains unrecognized evidence")
        for origin in copy_origins:
            destination = final_dir / origin.name
            require(not destination.exists() or destination.read_bytes() == origin.read_bytes(),
                    f"Refusing to overwrite different existing final evidence: {destination.name}")
    final_dir.mkdir(exist_ok=True)
    copied = {}
    for origin in copy_origins:
        destination = final_dir / origin.name
        destination.write_bytes(origin.read_bytes())
        require(sha(destination) == evidence_hashes[rel(origin)], f"Fresh evidence copy differs: {origin.name}")
        copied[rel(destination)] = {"copied_from": rel(origin), "sha256": sha(destination)}
    require(all(sha(local(path)) == expected for path, expected in evidence_hashes.items()),
            "A checked source, result, command, log or historical artifact changed during this check")
    require({rel(path) for path in RUN.glob("full-*/command.json")} == {item["metadata_path"] for item in full_records},
            "A new complete-verifier attempt started during preservation checking")

    now = datetime.now(timezone.utc)
    record = {
        "schema_version": 1, "status": "verification_and_preservation_passed", "run_id": RUN.name,
        "run_started_at_utc": run["started_at_utc"], "recorded_at_utc": now.isoformat(),
        "actual_preceding_verified_commit": BASELINE, "actual_preceding_verified_tree": BASELINE_TREE,
        "checked_worktree_head": git("rev-parse", "HEAD").decode().strip(),
        "baseline_tracked_file_count": len(baseline_paths),
        "verification_command": command, "latest_complete_verifier_attempt": command["attempt"],
        "strict_build_jobs": jobs, "verified_declaration_count": len(after),
        "previous_verified_declarations_preserved": len(before),
        "new_verified_declaration_count": len(new_names), "new_verified_declarations": new_names,
        "all_prior_declaration_names_modules_and_axiom_sets_preserved": True,
        "previous_completed_result_mappings_preserved": len(previous["completed_results"]),
        "new_completed_result_mappings": len(extension["public_names"]),
        "byte_identical_previous_nonroot_lean_source_count": len(baseline_sources) - 1,
        "all_previous_nonroot_lean_sources_byte_identical": True,
        "stock_audit_byte_identical": True,
        "root_added_imports_only": additions,
        "root_original_complete_import_prefix_preserved": True,
        "verifier_previous_gates_byte_preserved_after_four_declared_extensions": True,
        "verifier_exact_additive_edits": verifier_edits,
        "previous_declaration_maps_byte_identical": old_maps,
        "byte_identical_previous_verification_input_count": len(previous_inputs - EDITED_PREVIOUS_INPUTS),
        "all_previous_source_and_provenance_manifests_byte_identical": True,
        "explicitly_reviewed_mutable_previous_inputs": sorted(EDITED_PREVIOUS_INPUTS),
        "new_verification_input_paths": sorted(NEW_INPUTS),
        "coverage_scope_only_correction": scope_change,
        "all_69_original_numbered_assertion_records_and_statement_hashes_preserved": True,
        "all_47_completed_assertion_records_preserved": True,
        "fully_verified_numbered_assertion_count": 47, "remaining_numbered_assertion_count": 22,
        "numbered_assertions_completed_in_this_run": 0, "main_theorem_verified": False,
        "source_hash_count": len(sources), "verification_input_hash_count": len(inputs),
        "frozen_input_count": len(frozen), "all_source_and_input_hashes_match_frozen_candidate": True,
        "source_public_proof_inventory_recomputed": True, "raw_audit_and_result_declarations_agree": True,
        "console_is_exact_actual_stage_log_concatenation": True,
        "imported_project_module_count": len(current_imports), "allowed_logical_axioms": current["allowed_logical_axioms"],
        "weighted_palette": extension,
        "byte_identical_previous_file_count": len(preserved_paths),
        "byte_identical_previous_paths": preserved_paths,
        "preserved_historical_evidence_paths": historical_paths,
        "development_archive": archive,
        "retained_command_count": len(records), "successful_command_count": len(statuses["passed"]),
        "failed_command_count": len(statuses["failed"]), "incomplete_command_count": len(statuses["incomplete"]),
        "interrupted_command_count": len(statuses["interrupted"]), "command_evidence": records,
        "command_count_note": "Distinct recorded full-verifier, archived development and supplementary-preservation commands; no absent command metadata or missing timings are reconstructed.",
        "copied_fresh_outputs": copied,
        "evidence_sha256": {**evidence_hashes, **{path: item["sha256"] for path, item in copied.items()}},
        "next_target": {"path": "docs/continuation-handoff.md", "sha256": sha(ROOT / "docs/continuation-handoff.md"),
                        "status": "general_exceptional_to_core_incidence_and_final_robust_factorization_unproved"},
        "publication": {"repository": "fly31415926/overfull-lean",
                        "target_branches": ["main", "verified-bipartite-continuation-2026-11-21"],
                        "baseline_status": "published_and_independently_read_back",
                        "baseline_public_commit": BASELINE,
                        "status": "local_continuation_after_published_baseline",
                        "note": "Both public branches were verified at the baseline; this report does not claim the new continuation was published."},
    }
    module_rows = "\n".join(f"| `{name}` | {item['public_theorem_count']} |"
                            for name, item in extension["modules"].items())
    attempt_rows = "\n".join(f"| `{Path(item['metadata_path']).parent.name}` | {item['status']} | {item['exit_code']} |"
                             for item in full_records)
    report = f"""# Weighted palette continuation: verification and preservation

**The exact frozen candidate passed the complete strict verifier and the unchanged full axiom audit.**
The latest successful attempt is `{command['attempt']}` in run `{RUN.name}`.
This supplementary report was recorded at `{now.isoformat()}`. It checks
consistency and preservation; it does not replace the Lean build or audit.

## Exact baseline and mathematical scope

The preceding verified public commit is `{BASELINE}`, with tree
`{BASELINE_TREE}` and {len(baseline_paths):,} files. Both public branches were
independently read back at this commit before this continuation began.
It exactly reproduces local checkpoint `89678bc`; its parent exactly
reproduces `1b5663a`. This report concerns the new local continuation.

{extension['scope']}

No numbered assertion is promoted: **47 of 69 remain complete; 22 remain
incomplete. The main theorem and full two-core Corollary 4.6 remain unproved.**

| New module | Mapped public theorem proofs |
| --- | ---: |
{module_rows}

The {extension['module_count']} new modules contain {extension['public_theorem_count']}
mapped public theorem proofs and {extension['audited_declaration_count']} audited
declarations including private and generated support. The exact sources,
lexically recomputed public inventory, declaration map and full audit agree.

## Observed verification and preservation

| Check | Observed result |
| --- | --- |
| Latest complete verifier | Exit 0; frozen inputs unchanged |
| Strict `lake build --wfail` | {jobs:,} jobs passed |
| Unchanged full `Audit.lean` | {len(after):,} declarations passed |
| Prior declaration names, modules and axiom sets | All {len(before):,} preserved |
| Newly audited declarations | {len(new_names):,} |
| Prior nonroot mathematical sources, including audit | {len(baseline_sources)-1} byte-identical |
| Prior completed-result mappings | All {len(previous['completed_results']):,} retained |
| Prior declaration maps and metadata | All {len(old_maps)} unchanged |
| Prior verification inputs outside the four allowed edited files | {len(previous_inputs - EDITED_PREVIOUS_INPUTS)} byte-identical |
| Baseline files outside the explicit current-file allowance | {len(preserved_paths):,} byte-identical |
| Historical verification/recovery paths | {len(historical_paths):,} byte-identical |
| Original numbered assertion records and statement hashes | All 69 unchanged |
| Frozen source/input hashes | {len(frozen)} exact matches |
| Archived development files | {archive['file_count']} exact matches |

Lean remains 4.24.0 and mathlib remains
`f897ebcf72cd16f89ab4577d0c826cd14afaafc7`. The only permitted logical axioms
are `propext`, `Classical.choice` and `Quot.sound`.

The proof root retains the complete original import prefix and adds only
the recorded contiguous new imports before the original documentation.
The verifier differs by exactly four additive weighted-palette source-map
and declaration-map edits, recorded in `preservation.json`. Every preceding
gate and the full stock `Audit.lean` are unchanged.

The coverage inventory may correct only its top-level `scope` prose.
The checker compares every other parsed JSON field exactly, including all
69 assertion records. Both old and current scope strings and byte hashes
are retained in `preservation.json`; it does not falsely claim that the
entire coverage file remains byte-identical when that prose changes.

The actual raw axiom records and imported-module lists agree with current
results. The latest console is exactly the concatenation of the actual
four stage logs and final verifier summary. The `final/` directory contains
byte-identical copies of the current logs, results, declaration maps, frozen
inputs, command/console and new source manifest. Historical verification
logs have not been replayed as current verification.

## Retained actual diagnostics

| Full-verifier attempt | Recorded status | Exit code |
| --- | --- | ---: |
{attempt_rows}

The run retains {len(records)} distinct recorded commands: {len(statuses['passed'])}
passed, {len(statuses['failed'])} failed, {len(statuses['incomplete'])} incomplete and
{len(statuses['interrupted'])} interrupted. Individual records, exact outputs
and available source snapshots are listed in `preservation.json`. Source
hashes or timings absent from an original command record are identified as
absent; the checker does not invent them. A targeted compiler pass establishes
only its own result; the latest complete verifier establishes the full audit.

## Publication and remaining work

The authorized preceding checkpoints have been published, and both branch
heads, exact trees and complete file inventories were independently read back.
The retained baseline receipts record that successful publication. The new
weighted continuation is verified locally by this run; this report does not
claim a later public branch promotion.

General exceptional-to-core incidence coloring, the resulting old-core
completion conditions, final robust matching completion and factorization
remain distinct obligations as detailed in the continuation handoff.
"""
    (RUN / "preservation.json").write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
    (RUN / "final-report.md").write_text(report, encoding="utf-8")
    print(json.dumps({key: record[key] for key in ["status", "latest_complete_verifier_attempt",
          "strict_build_jobs", "verified_declaration_count", "previous_verified_declarations_preserved",
          "new_verified_declaration_count", "previous_completed_result_mappings_preserved",
          "frozen_input_count", "fully_verified_numbered_assertion_count", "main_theorem_verified"]}, indent=2))


if __name__ == "__main__":
    main()


