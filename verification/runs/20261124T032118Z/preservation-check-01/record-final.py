#!/usr/bin/env python3
"""Check the actual three-core audit and preserve every preceding proof and assertion.

This supplementary checker never runs Lean and never substitutes for Audit.lean.
Success is written only after actual full-verifier completion and all byte checks.
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
sys.dont_write_bytecode = True
RUN = Path(__file__).resolve().parent
ROOT = RUN.parents[2]
BASELINE = "0cf1c68c4daaeec9b879a03f1871eb64a0fa9640"
BASELINE_TREE = "5d031253d02d0d0878422f8fbc367f04b812450c"
BASELINE_FILE_COUNT = 5478
BASELINE_DECLARATION_COUNT = 13366
BASELINE_COMPLETED_MAPPING_COUNT = 2272
BASELINE_FROZEN_INPUT_COUNT = 716
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
EDITED_PREVIOUS_INPUTS = {"README.md", "docs/continuation-handoff.md", "scripts/verify.py", "docs/coverage.json"}
NEW_INPUTS = {"docs/three-core-terminal-source.json", "docs/three-core-terminal-semantic-review.md",
              "docs/three-core-terminal-verification.md", "scripts/update_three_core_terminal_manifest.py"}
LIVE_OUTPUTS = {"verification/results.json", "verification/build.log", "verification/axioms.log",
                "verification/lean-version.log", "verification/vizing-source.log"}
REPORT_OUTPUTS = {"preservation.json", "final-report.md", "record-final-output.log"}
VERIFIER_EDITS = [{'new': '                          ("native_terminal", "native-terminal-source.json"),\n'
         '                          ("three_core_terminal", "three-core-terminal-source.json")):\n',
  'old': '                          ("native_terminal", "native-terminal-source.json")):\n'},
 {'new': '    three_core_source, _, three_core_public = extension_maps["three_core_terminal"]\n'
         '    if (three_core_source["kind"] != "supporting_continuation"\n'
         '            or three_core_source["numbered_assertions_completed"] != 0\n'
         '            or three_core_source["manuscript_number"] != "4.16"\n'
         '            or three_core_source["manuscript_label"] != "three:prop:terminal"\n'
         '            or three_core_source["statement_sha256"] != '
         '"1ba102e379594ab72de4ba73cf41c88d9fbdadf1c132e2943b48da04e8c2cc1c"\n'
         '            or three_core_source["verified_subcase"] != "exactly_three_core_parts"\n'
         '            or three_core_source["public_theorems"] != [\n'
         '                "Overfull.three_core_terminal_factorization",\n'
         '                "Overfull.three_core_terminal_one_factorization"]\n'
         '            or not set(three_core_source["public_theorems"]) <= '
         'set(three_core_public)):\n'
         '        raise SystemExit("The three-core continuation must identify only its exact '
         'terminal subcase.")\n'
         '\n'
         '    # Every first-party mathematical file must be included in the library build.\n',
  'old': '    # Every first-party mathematical file must be included in the library build.\n'},
 {'new': '                    "native_terminal": "native-terminal",\n'
         '                    "three_core_terminal": "three-core-terminal"}[key]\n',
  'old': '                    "native_terminal": "native-terminal"}[key]\n'},
 {'new': '        "native_terminal_declaration_map": extension_evidence["native_terminal"],\n'
         '        "three_core_terminal_declaration_map": '
         'extension_evidence["three_core_terminal"],\n',
  'old': '        "native_terminal_declaration_map": extension_evidence["native_terminal"],\n'}]

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
    """Require exactly four additive registrations; every preceding verifier guard remains."""
    expected = old_bytes(BASELINE, "scripts/verify.py")
    for edit in VERIFIER_EDITS:
        old, new = edit["old"].encode(), edit["new"].encode()
        require(expected.count(old) == 1, "Ambiguous or missing reviewed verifier insertion")
        expected = expected.replace(old, new, 1)
    require((ROOT / "scripts/verify.py").read_bytes() == expected,
            "Verifier differs beyond the four exact additive three-core registrations")
    manifest = RUN / "verifier-additions.json"
    if manifest.exists():
        require(load(manifest) == VERIFIER_EDITS, "Verifier-additions record differs from reviewed edits")
    return VERIFIER_EDITS


def check_coverage_preservation() -> dict:
    """Allow one supporting component and scope text, preserving all 69 records."""
    previous_bytes = old_bytes(BASELINE, "docs/coverage.json")
    previous = json.loads(previous_bytes)
    current = load(ROOT / "docs/coverage.json")
    source = load(ROOT / "docs/three-core-terminal-source.json")
    public = ["Overfull.three_core_terminal_factorization",
              "Overfull.three_core_terminal_one_factorization"]
    statement_hash = "1ba102e379594ab72de4ba73cf41c88d9fbdadf1c132e2943b48da04e8c2cc1c"
    allowed_top = {"scope", "checked_component_catalog"}
    require({key: value for key, value in current.items() if key not in allowed_top}
            == {key: value for key, value in previous.items() if key not in allowed_top},
            "Coverage changed beyond supporting-component and top-level scope additions")
    before, after = previous["numbered_assertions"], current["numbered_assertions"]
    require(before == after and len(after) == current["numbered_assertion_count"] == 69,
            "One of the 69 original numbered assertion records or its ordering changed")
    completed = [item["number"] for item in after if item["full_assertion_verified"]]
    require(len(completed) == previous["fully_verified_numbered_assertion_count"]
            == current["fully_verified_numbered_assertion_count"] == 48
            and current["main_theorem_verified"] is False
            and isinstance(current["scope"], str) and bool(current["scope"]),
            "Supporting continuation changed completed coverage or main-theorem status")
    assertion = next(item for item in after if item["number"] == "4.16")
    require(assertion["statement_sha256"] == source["statement_sha256"] == statement_hash
            and assertion["labels"] == ["three:prop:terminal"]
            and assertion["full_assertion_verified"] is False
            and source["manuscript_number"] == "4.16"
            and source["verified_subcase"] == "exactly_three_core_parts"
            and source["kind"] == "supporting_continuation"
            and source["numbered_assertions_completed"] == 0
            and source["public_theorems"] == public,
            "Three-core subcase was confused with completion of full Proposition 4.16")
    old_catalog, new_catalog = previous["checked_component_catalog"], current["checked_component_catalog"]
    require(len(new_catalog) == len(old_catalog) + 1 and new_catalog[:-1] == old_catalog,
            "Prior checked components changed or more than one component was appended")
    component = new_catalog[-1]
    require(set(component) == {"id", "kind", "description", "lean_declarations",
                               "scope_limit", "manuscript_locations"}
            and component["id"] == "three_core_terminal"
            and component["kind"] == "graph_theoretic_result"
            and component["description"] == source["scope"]
            and component["lean_declarations"] == public
            and component["manuscript_locations"] == ["three:prop:terminal"]
            and isinstance(component["scope_limit"], str) and bool(component["scope_limit"]),
            "Appended component differs from the exact source-linked three-core theorem pair")
    plan = load(RUN / "coverage-extension-plan.json")
    require(plan["kind"] == "supporting_subcase_only"
            and plan["numbered_assertions_completed"] == 0
            and plan["new_component"] == component
            and plan["old_scope"] == previous["scope"]
            and plan["new_scope"] == current["scope"]
            and plan["all_69_assertion_records_identical"] is True,
            "Coverage differs from its exact reviewed supporting-extension plan")
    manuscript_bytes = old_bytes(BASELINE, "docs/manuscript-source.json")
    require((ROOT / "docs/manuscript-source.json").read_bytes() == manuscript_bytes,
            "The historical manuscript-source manifest must remain byte-identical")
    return {"all_69_assertion_records_identical": True,
            "all_69_statement_identities_and_hashes_identical": True,
            "all_48_completed_assertion_records_identical": True,
            "completed_assertions": completed, "old_completed_count": 48, "new_completed_count": 48,
            "numbered_assertions_completed_in_this_run": 0,
            "full_proposition_4_16_remains_unverified": True,
            "source_statement_sha256": statement_hash,
            "all_previous_component_catalog_entries_identical": True,
            "appended_component": component, "old_scope": previous["scope"], "new_scope": current["scope"],
            "coverage_baseline_sha256": digest(previous_bytes),
            "coverage_current_sha256": sha(ROOT / "docs/coverage.json"),
            "manuscript_source_byte_identical": True,
            "manuscript_source_sha256": digest(manuscript_bytes)}


def check_root_imports(modules: set[str]) -> list[str]:
    additions = load(RUN / "root-added-imports.json")
    require(isinstance(additions, list) and bool(additions)
            and len(additions) == len(set(additions)), "Malformed or duplicate root-added-import list")
    for line in additions:
        require(isinstance(line, str) and re.fullmatch(
            r"import Overfull\.Terminal\.[A-Za-z0-9_]+\n", line) is not None
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
    source_path = ROOT / "docs/three-core-terminal-source.json"
    map_path = ROOT / "verification/three-core-terminal-declarations.json"
    source, mapping = load(source_path), load(map_path)
    require(source["baseline_commit"] == BASELINE and source["baseline_tree"] == BASELINE_TREE
            and source["baseline_publication_status"] == "published_exact_tree_and_both_refs_verified"
            and source["kind"] == "supporting_continuation"
            and source["numbered_assertions_completed"] == 0
            and source["manuscript_number"] == "4.16"
            and source["verified_subcase"] == "exactly_three_core_parts"
            and source["manuscript_label"] == "three:prop:terminal"
            and source["statement_sha256"] == "1ba102e379594ab72de4ba73cf41c88d9fbdadf1c132e2943b48da04e8c2cc1c"
            and source["public_theorems"] == ["Overfull.three_core_terminal_factorization",
                                             "Overfull.three_core_terminal_one_factorization"]
            and source["main_theorem_verified"] is False,
            "Three-core-terminal manifest has wrong baseline, publication status or mathematical scope")
    require(source["review"] == "docs/three-core-terminal-semantic-review.md"
            and source["proof_map"] == "docs/three-core-terminal-verification.md"
            and isinstance(source["scope"], str) and bool(source["scope"]),
            "Three-core-terminal source/review mapping is incomplete")
    modules = {item["module"]: item for item in source["modules"]}
    require(0 < len(modules) == len(source["modules"]) == source["module_count"],
            "New module inventory is empty, duplicated or has a wrong count")
    public = {}
    for module, item in modules.items():
        path = local(item["path"])
        require(re.fullmatch(r"Overfull\.Terminal\.[A-Za-z0-9_]+", module) is not None
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
    actual = declaration_index(mapping["proof_declaration_map"], "three-core-terminal declaration map")
    require(actual == expected and {entry[0] for entry in actual.values()} == set(modules),
            "New complete declaration map differs from the actual full audit")
    for item in mapping["proof_declaration_map"]:
        module = modules[item["module"]]
        require(item["source_path"] == module["path"] and item["source_sha256"] == module["sha256"],
                f"New audited declaration is not bound to the current checked source: {item['name']}")
    summary = current["three_core_terminal_declaration_map"]
    require(summary["path"] == rel(map_path) and summary["sha256"] == sha(map_path),
            "Current result points to a stale new declaration map")
    for key, value in [("module_count", len(modules)), ("public_theorem_count", len(public)),
                       ("verified_declaration_count", len(actual)), ("numbered_assertions_completed", 0)]:
        require(summary[key] == mapping[key] == value, f"New result/map count mismatch: {key}")
    require(mapping["kind"] == source["kind"]
            and mapping["includes_private_and_generated_proofs"] is True
            and mapping["manuscript_number"] == source["manuscript_number"]
            and mapping["statement_sha256"] == source["statement_sha256"],
            "New declaration map omits support proofs or the exact source-linked subcase identity")
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
            status = "passed" if (code == 0
                and data.get("all_frozen_inputs_unchanged") is not False
                and data.get("all_control_files_unchanged") is not False) else "failed"
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
        legacy_sources = [source for source in recorded_sources
                          if not (path.parent / "source" / source).is_file()]
        require(len({Path(source).name for source in legacy_sources}) == len(legacy_sources),
                f"Ambiguous legacy source snapshot basenames: {rel(path)}")
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
    changed_inputs = data.get("inputs_changed_during_command")
    if changed_inputs is not None:
        require(isinstance(changed_inputs, list)
                and all(isinstance(item, str) for item in changed_inputs)
                and len(changed_inputs) == len(set(changed_inputs)),
                f"Malformed recorded concurrent input changes: {rel(path)}")
        for item in changed_inputs:
            local(item)
    return {"metadata_path": rel(path), "metadata_sha256": sha(path),
            "command": data["command"], "status": status, "exit_code": code,
            "logs": [{"path": rel(log), "sha256": sha(log)} for log in logs],
            "source_snapshots": snapshots, "source_hashes_in_original_command": recorded_sources is not None,
            "dependency_hash_records_retained": len(data.get("input_sha256", data.get("dependency_source_sha256", {}))),
            "timing_recorded": start is not None,
            "inputs_changed_during_command": changed_inputs,
            "provenance_note": "Missing original metadata is not reconstructed; archived snapshot and log hashes describe the retained bytes."}


def full_attempt_paths() -> list[Path]:
    """Enumerate every current-run full attempt, including genuine failures."""
    return sorted(RUN.glob("full-*/command.json"))


def check_full_snapshots(path: Path, data: dict, frozen: dict) -> None:
    """Validate all retained current-run input bytes and genuine output copies."""
    require(data.get("schema_version") == 2
            and data.get("input_sha256") == frozen
            and data.get("all_frozen_inputs_snapshotted") is True
            and data.get("baseline_local_verified_commit") == BASELINE
            and data.get("baseline_local_verified_tree") == BASELINE_TREE,
            f"Current full attempt lacks complete frozen-input provenance: {rel(path)}")
    inputs = path.parent / "input"
    require({p.relative_to(inputs).as_posix() for p in inputs.rglob("*") if p.is_file()} == set(frozen),
            f"Full frozen-input snapshots have extra or missing files: {rel(path)}")
    for source, expected in frozen.items():
        local(source)
        require(sha(inputs / source) == expected,
                f"Full frozen-input snapshot changed: {source}")
    expected_sources = {source: expected for source, expected in frozen.items()
                        if source.startswith(("Overfull/Terminal/",)) and source.endswith(".lean")}
    require(data["source_sha256"] == expected_sources,
            f"Full new-source snapshot inventory is incomplete: {rel(path)}")
    controls = data.get("control_sha256")
    required_controls = {"record-command.py", "run-verifier.py", "supervise-verifier.py", "record-final.py",
                         "run.json", "verifier-additions.json", "root-added-imports.json",
                         "coverage-extension-plan.json", "development-archive.json"}
    require(isinstance(controls, dict) and set(controls) == required_controls
            and data.get("all_control_files_snapshotted") is True
            and controls["run-verifier.py"] == data["runner_sha256"],
            f"Full attempt lacks immutable verification-control snapshots: {rel(path)}")
    control_dir = path.parent / "control"
    require({p.name for p in control_dir.iterdir() if p.is_file()} == required_controls,
            f"Control snapshot inventory differs: {rel(path)}")
    for name, expected in controls.items():
        require(sha(control_dir / name) == expected,
                f"Verification-control snapshot changed: {rel(path)} / {name}")
    preflight = load(path.parent / "baseline-preservation-preflight.json")
    previous = json.loads(old_bytes(BASELINE, "verification/results.json"))
    original = {**previous["source_sha256"], **previous["verification_input_sha256"]}
    require(preflight["baseline_commit"] == BASELINE and preflight["baseline_tree"] == BASELINE_TREE
            and preflight["baseline_frozen_input_sha256"] == original
            and preflight["baseline_frozen_input_count"] == len(original) == BASELINE_FROZEN_INPUT_COUNT
            and preflight["baseline_audited_declaration_count"] == BASELINE_DECLARATION_COUNT
            and preflight["baseline_completed_result_mapping_count"] == BASELINE_COMPLETED_MAPPING_COUNT,
            f"Full-attempt baseline preflight disagrees with committed evidence: {rel(path)}")
    retained = data.get("retained_current_outputs", {})
    for original_path, item in retained.items():
        source_path = local(original_path)
        expected = path.parent / "artifacts" / original_path
        require(source_path.parent == ROOT / "verification"
                and (source_path.name in {"vizing-source.log", "lean-version.log", "build.log",
                                          "axioms.log", "results.json"}
                     or source_path.name.endswith("declarations.json"))
                and item["snapshot"] == rel(expected) and expected.is_file()
                and sha(expected) == item["sha256"] and expected.stat().st_size == item["bytes"],
                f"Full-attempt genuine output snapshot changed: {original_path}")
    artifacts = path.parent / "artifacts"
    require({rel(p) for p in artifacts.rglob("*") if p.is_file()}
            == {item["snapshot"] for item in retained.values()},
            f"Full-attempt output snapshot inventory is incomplete: {rel(path)}")
    if "verification/axioms.log" in retained:
        segment_dir = path.parent / "raw-audit-segments"
        manifest = load(segment_dir / "manifest.json")
        audit = local(retained["verification/axioms.log"]["snapshot"]).read_bytes()
        require(manifest["kind"] == "exact_contiguous_raw_audit_bytes"
                and manifest["source"] == retained["verification/axioms.log"]["snapshot"]
                and manifest["source_sha256"] == digest(audit) and manifest["bytes"] == len(audit),
                f"Raw audit segment source identity disagrees: {rel(path)}")
        offset, chunks, segment_paths = 0, [], set()
        for number, item in enumerate(manifest["segments"]):
            segment = segment_dir / f"part-{number:04d}.log"
            chunk = segment.read_bytes()
            require(item["path"] == rel(segment) and item["offset"] == offset
                    and item["bytes"] == len(chunk) and item["sha256"] == digest(chunk),
                    f"Raw audit segment bytes/position changed: {rel(segment)}")
            offset += len(chunk)
            chunks.append(chunk)
            segment_paths.add(segment.name)
        require(b"".join(chunks) == audit
                and {p.name for p in segment_dir.iterdir()} == segment_paths | {"manifest.json"},
                f"Raw audit segments do not reconstruct the exact complete raw log: {rel(path)}")


def full_attempts() -> tuple[list[dict], dict]:
    paths = full_attempt_paths()
    require(bool(paths), "No complete-verifier command records exist")
    records, ordered = [], []
    for path in paths:
        data = load(path)
        expected_cwd = str(ROOT)
        require(re.fullmatch(r"full-[A-Za-z0-9-]+", path.parent.name) is not None
                and data.get("attempt") == path.parent.name
                and data.get("command") == ["python3", "scripts/verify.py"]
                and data.get("cwd") == expected_cwd, f"Wrong complete-verifier provenance: {rel(path)}")
        frozen = load(path.parent / "frozen-candidate-inputs.json")
        require(isinstance(frozen, dict) and data["candidate_input_hash_count"] == len(frozen)
                and all(frozen.get(source) == expected for source, expected in data["source_sha256"].items()),
                f"Verifier source snapshots differ from their own frozen candidate: {rel(path)}")
        record = command_record(path, data)
        check_full_snapshots(path, data, frozen)
        record["cwd"] = data["cwd"]
        records.append(record)
        ordered.append((timestamp(data["started_at_utc"]), path.parent.name, data))
    require(bool(ordered), "No current-run complete-verifier attempt exists")
    require(len({start for start, _, _ in ordered}) == len(ordered), "Ambiguous latest verifier start")
    _, latest_name, latest = max(ordered, key=lambda item: item[0])
    require(latest["status"] == "passed" and latest["exit_code"] == 0
            and latest.get("all_frozen_inputs_unchanged") is True
            and latest.get("all_control_files_unchanged") is True,
            f"Latest complete verifier {latest_name} has not passed with unchanged frozen inputs")
    for alias, original in [("verification-command.json", "command.json"),
                            ("frozen-candidate-inputs.json", "frozen-candidate-inputs.json"),
                            ("verification-console.log", "output.log")]:
        require((RUN / alias).read_bytes() == (RUN / latest_name / original).read_bytes(),
                f"Latest verifier alias differs from the actual latest attempt: {alias}")
    require(all(sha(RUN / name) == expected for name, expected in latest["control_sha256"].items()),
            "A verification-control file changed after the latest successful frozen run")
    retained = latest["retained_current_outputs"]
    require({"verification/" + name for name in ["vizing-source.log", "lean-version.log", "build.log",
                                                "axioms.log", "results.json"]} <= retained.keys(),
            "Latest successful verifier did not retain all of its actual complete stage outputs")
    for original, item in retained.items():
        require(local(original).read_bytes() == local(item["snapshot"]).read_bytes(),
                f"Latest full-attempt output no longer equals its live alias: {original}")
    return records, latest


def check_supervision(latest: dict) -> list[dict]:
    """Require the actual attached runner exit; preserve earlier supervisor failures."""
    reports = []
    folders = sorted(path for path in (RUN / "supervision").glob("full-*") if path.is_dir())
    require(bool(folders), "No attached verifier supervision receipts exist")
    for folder in folders:
        history_path = folder / "heartbeat.log"
        history = [json.loads(line) for line in history_path.read_text().splitlines()]
        require(bool(history), f"Empty supervisor observation history: {rel(folder)}")
        previous_time = None
        for item in history:
            observed = timestamp(item["observed_at_utc"])
            require(item["attempt"] == folder.name and item["cwd"] == str(ROOT)
                    and item["command"][1:] == ["-u", str(RUN / "run-verifier.py"), folder.name]
                    and Path(item["command"][0]).name.startswith("python")
                    and item["process_status"] in {"running", "completed"}
                    and (previous_time is None or previous_time <= observed)
                    and timestamp(item["supervisor_started_at_utc"]) <= observed,
                    f"Malformed or unordered attached observation: {rel(folder)}")
            previous_time = observed
        require(load(folder / "heartbeat.json") == history[-1]
                and all(item["process_status"] == "running" for item in history[:-1]),
                f"Supervisor history changed or continued after completion: {rel(folder)}")
        require(len({item["observed_child_pid"] for item in history}) == 1,
                f"Supervisor changed its observed child: {rel(folder)}")
        terminal_path = folder / "terminal.json"
        output_path = folder / "runner-output.log"
        require(output_path.is_file(), f"Missing actual runner output: {rel(folder)}")
        record = {"attempt": folder.name, "history_path": rel(history_path),
                  "history_sha256": sha(history_path), "observation_count": len(history),
                  "runner_output_path": rel(output_path), "runner_output_sha256": sha(output_path),
                  "completed": terminal_path.is_file()}
        if terminal_path.is_file():
            terminal = load(terminal_path)
            added = {"actual_terminal_exit_code", "terminal_observed_at_utc", "runner_output_sha256"}
            require({key: value for key, value in terminal.items() if key not in added} == history[-1]
                    and terminal["process_status"] == "completed"
                    and type(terminal["actual_terminal_exit_code"]) is int
                    and terminal["actual_terminal_exit_code"] == terminal["observed_return_code"]
                    and timestamp(terminal["observed_at_utc"]) <= timestamp(terminal["terminal_observed_at_utc"])
                    and terminal["runner_output_path"] == rel(output_path)
                    and terminal["runner_output_bytes"] == output_path.stat().st_size
                    and terminal["runner_output_sha256"] == sha(output_path),
                    f"Terminal supervision differs from observed process/output: {rel(folder)}")
            record.update({"terminal_path": rel(terminal_path), "terminal_sha256": sha(terminal_path),
                           "actual_terminal_exit_code": terminal["actual_terminal_exit_code"]})
        else:
            require(history[-1]["process_status"] == "running",
                    f"Lost terminal receipt after a completed observation: {rel(folder)}")
        full_path = RUN / folder.name / "command.json"
        record["complete_verifier_command_started"] = full_path.is_file()
        if folder.name == latest["attempt"]:
            require(terminal_path.is_file(), "Latest full verifier lacks an observed supervisor exit")
            terminal = load(terminal_path)
            require(terminal["actual_terminal_exit_code"] == latest["exit_code"] == 0
                    and terminal["status"] == latest["status"] == "passed"
                    and terminal["all_frozen_inputs_unchanged"] is True
                    and terminal["all_control_files_unchanged"] is True
                    and terminal["supervisor_sha256"] == latest["control_sha256"]["supervise-verifier.py"]
                    and timestamp(terminal["supervisor_started_at_utc"]) <= timestamp(latest["started_at_utc"])
                    and timestamp(latest["finished_at_utc"]) <= timestamp(terminal["terminal_observed_at_utc"]),
                    "Latest full result lacks matching observed attached process completion")
            require((RUN / "execution-terminal.json").read_bytes() == terminal_path.read_bytes()
                    and (RUN / "execution-heartbeat.json").read_bytes() == (folder / "heartbeat.json").read_bytes(),
                    "Latest supervisor aliases disagree with the actual terminal observation")
        reports.append(record)
    require(any(item["attempt"] == latest["attempt"] for item in reports),
            "No supervisor belongs to the latest complete verifier")
    return reports


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
            "Usage: record-final.py [0cf1c68c4daaeec9b879a03f1871eb64a0fa9640]")
    require(git("rev-parse", f"{BASELINE}^{{commit}}").decode().strip() == BASELINE
            and git("rev-parse", f"{BASELINE}^{{tree}}").decode().strip() == BASELINE_TREE,
            "The pinned preceding verified commit/tree is unavailable or changed")
    full_records, command = full_attempts()
    supervision = check_supervision(command)
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
    require("native_terminal_declaration_map" in previous and "three_core_terminal_declaration_map" not in previous,
            "Pinned baseline is not the preceding complete-Corollary-4.6 verified result")
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
    baseline_frozen = {**previous["source_sha256"], **previous["verification_input_sha256"]}
    require(len(baseline_frozen) == BASELINE_FROZEN_INPUT_COUNT
            and json.loads(old_bytes(BASELINE,
                "verification/runs/20261124T021500Z/frozen-candidate-inputs.json")) == baseline_frozen,
            "The preceding 716 frozen source/input hashes differ from the baseline result")
    require(previous_inputs <= inputs and inputs - previous_inputs == NEW_INPUTS
            and EDITED_PREVIOUS_INPUTS <= previous_inputs,
            "Input inventory differs beyond the four new three-core-terminal input files")
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

    coverage_preservation = check_coverage_preservation()
    old_coverage = json.loads(old_bytes(BASELINE, "docs/coverage.json"))
    coverage = load(ROOT / "docs/coverage.json")
    complete = [item for item in coverage["numbered_assertions"] if item["full_assertion_verified"]]
    old_complete = [item for item in old_coverage["numbered_assertions"] if item["full_assertion_verified"]]
    require(complete == old_complete and len(complete) == 48
            and current["fully_verified_numbered_assertion_count"]
                == previous["fully_verified_numbered_assertion_count"] == 48
            and current["fully_verified_numbered_assertions"]
                == previous["fully_verified_numbered_assertions"] == [item["number"] for item in complete],
            "The exact 48 completed assertion records or their result mappings changed")

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
            "New mathematical-source inventory differs from the three-core-terminal manifest")
    additions = check_root_imports(set(extension["modules"]))
    new_names = sorted(set(after) - set(before))
    require(set(new_names) == set(extension["all_audited_names"])
            and set(extension["public_names"]).isdisjoint(before),
            "New audit declarations are not exactly the complete new-module proof inventory")
    expected_completed = dict(previous["completed_results"])
    expected_completed.update({f"three_core_terminal_closure_{i}": name
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
    require({rel(path) for path in full_attempt_paths()} == {item["metadata_path"] for item in full_records},
            "A new complete-verifier attempt started during preservation checking")

    now = datetime.now(timezone.utc)
    record = {
        "schema_version": 1, "status": "verification_and_preservation_passed", "run_id": RUN.name,
        "run_started_at_utc": run["started_at_utc"], "recorded_at_utc": now.isoformat(),
        "actual_preceding_verified_commit": BASELINE, "actual_preceding_verified_tree": BASELINE_TREE,
        "checked_worktree_head": git("rev-parse", "HEAD").decode().strip(),
        "baseline_tracked_file_count": len(baseline_paths),
        "baseline_frozen_input_count": len(baseline_frozen),
        "all_baseline_frozen_inputs_checked_against_committed_bytes": True,
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
        "verifier_changes_exactly_four_reviewed_additive_substitutions": True,
        "all_previous_verifier_guards_preserved": True,
        "verifier_exact_additive_edits": verifier_edits,
        "previous_declaration_maps_byte_identical": old_maps,
        "byte_identical_previous_verification_input_count": len(previous_inputs - EDITED_PREVIOUS_INPUTS),
        "all_previous_proof_source_manifests_byte_identical": True,
        "manuscript_source_byte_identical": True,
        "explicitly_reviewed_mutable_previous_inputs": sorted(EDITED_PREVIOUS_INPUTS),
        "new_verification_input_paths": sorted(NEW_INPUTS),
        "coverage_preservation": coverage_preservation,
        "all_69_original_statement_identities_and_hashes_preserved": True,
        "all_69_numbered_assertion_records_preserved": True,
        "all_48_completed_assertion_records_preserved": True,
        "fully_verified_numbered_assertion_count": 48, "remaining_numbered_assertion_count": 21,
        "numbered_assertions_completed_in_this_run": 0, "main_theorem_verified": False,
        "source_hash_count": len(sources), "verification_input_hash_count": len(inputs),
        "frozen_input_count": len(frozen), "all_source_and_input_hashes_match_frozen_candidate": True,
        "source_public_proof_inventory_recomputed": True, "raw_audit_and_result_declarations_agree": True,
        "console_is_exact_actual_stage_log_concatenation": True,
        "all_full_attempt_frozen_inputs_snapshotted": True,
        "latest_verifier_controls_snapshotted_and_byte_identical": True,
        "latest_attached_supervisor_observed_exit_zero": True,
        "supervision_evidence": supervision,
        "raw_audit_segments_reconstruct_complete_actual_audit": True,
        "imported_project_module_count": len(current_imports), "allowed_logical_axioms": current["allowed_logical_axioms"],
        "three_core_terminal": extension,
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
                        "status": "remaining_native_factorization_obligations_recorded_in_handoff"},
        "publication": {"repository": "fly31415926/overfull-lean",
                        "target_branches": ["main", "verified-bipartite-continuation-2026-11-21"],
                        "baseline_status_at_input_freeze": "published_exact_tree_and_both_refs_verified",
                        "baseline_local_verified_commit": BASELINE,
                        "baseline_public_commit": run["baseline_public_commit"],
                        "observed_public_main_at_input_freeze": run["observed_public_main"],
                        "observed_public_continuation_at_input_freeze": run["observed_public_continuation"],
                        "status": "local_continuation_after_published_verified_baseline",
                        "note": "Local verification and public branch promotion are distinct; separate receipts establish exact public tree identity and branch readback."},
    }
    module_rows = "\n".join(f"| `{name}` | {item['public_theorem_count']} |"
                            for name, item in extension["modules"].items())
    attempt_rows = "\n".join(f"| `{Path(item['metadata_path']).parent.name}` | {item['status']} | {item['exit_code']} |"
                             for item in full_records)
    report = f"""# Three-core terminal continuation: verification and preservation

**The exact frozen candidate passed the complete strict verifier and the unchanged full axiom audit.**
The latest full attempt is `{command['attempt']}` in run `{RUN.name}`. Its
attached supervisor observed the actual runner exit zero. This supplementary
report was recorded at `{now.isoformat()}` and checks consistency and
preservation; it does not replace the Lean build or the full audit.

## Exact baseline and mathematical scope

The preceding published verified commit is `{BASELINE}`, tree
`{BASELINE_TREE}`, with {len(baseline_paths):,} files. Its committed result
contains {len(before):,} audited declarations and {len(previous['completed_results']):,}
completed-result mappings. All their names, modules, axiom sets and mappings
are preserved. The baseline public heads recorded at run creation were
`{run['observed_public_main']}` for `main` and
`{run['observed_public_continuation']}` for the continuation branch.

{extension['scope']}

**Numbered coverage remains 48 of 69, with 21 assertions incomplete. All 69
original assertion records, including all 48 completed records, are unchanged.
This run proves the exactly-three-core subcase; full Proposition 4.16, its
four-core cases, and the main theorem remain unverified.**

| New module | Mapped public theorem proofs |
| --- | ---: |
{module_rows}

The {extension['module_count']} new modules contain {extension['public_theorem_count']}
mapped public theorem proofs and {extension['audited_declaration_count']} audited
declarations including private and generated support. The source hashes,
recomputed public inventory, declaration map and full audit agree.

## Observed verification and preservation

| Check | Observed result |
| --- | --- |
| Latest complete verifier | Actual exit 0; frozen sources and controls unchanged |
| Attached supervisor | Actual child exit 0 observed and retained |
| Strict `lake build --wfail` | {jobs:,} jobs passed |
| Unchanged full `Audit.lean` | {len(after):,} declarations passed |
| Prior declaration names, modules and axiom sets | All {len(before):,} preserved |
| Newly audited declarations | {len(new_names):,} |
| Prior nonroot mathematical sources, including audit | {len(baseline_sources)-1} byte-identical |
| Prior completed-result mappings | All {len(previous['completed_results']):,} retained |
| Prior declaration maps and metadata | All {len(old_maps)} unchanged |
| Prior verification inputs outside the four allowed edited files | {len(previous_inputs - EDITED_PREVIOUS_INPUTS)} byte-identical |
| Baseline files outside the explicit current-file allowance | {len(preserved_paths):,} byte-identical |
| Historical verification/recovery files | {len(historical_paths):,} byte-identical |
| Original numbered assertion records | All 69 unchanged |
| Completed numbered assertion records | All 48 unchanged |
| `docs/manuscript-source.json` | Byte-identical |
| Frozen source/input hashes | {len(frozen)} exact matches |
| Archived development files | {archive['file_count']} exact matches |

Lean remains 4.24.0 and mathlib remains
`f897ebcf72cd16f89ab4577d0c826cd14afaafc7`. The only permitted logical axioms
are `propext`, `Classical.choice` and `Quot.sound`.

The proof root retains its complete original import prefix and adds only
the recorded contiguous new imports before the original documentation.
The verifier differs by exactly four reviewed additive substitutions:
new source/declaration registrations and an explicit scope gate for the
source-linked three-core subcase. Every preceding verifier guard and every
byte of the full stock `Audit.lean` remain unchanged.

Coverage permits only top-level scope prose and one appended
`three_core_terminal` supporting component. All earlier component catalog
entries and every numbered assertion record are identical. The original
Proposition 4.16 statement hash remains pinned, its full-assertion flag stays
false, and the manuscript-source manifest is byte-identical.

The actual raw axiom records and imported-module lists agree with current
results. The latest console equals the exact concatenation of its four
actual stage logs and final summary. The `final/` directory retains exact
copies of the current logs, results, declaration maps, frozen-input manifest,
command, console and new source manifest. Every full attempt also retains
all input bytes, control-script bytes, its actual outputs and exact contiguous
raw audit segments. Earlier failures remain genuine failed records.

## Retained actual diagnostics

| Full-verifier attempt | Recorded status | Exit code |
| --- | --- | ---: |
{attempt_rows}

The run retains {len(records)} distinct full-verifier, development and
supplementary command records: {len(statuses['passed'])} passed,
{len(statuses['failed'])} failed, {len(statuses['incomplete'])} incomplete and
{len(statuses['interrupted'])} interrupted. Supervisor observations and runner
outputs are additionally retained for {len(supervision)} attached invocations,
including any preflight failures. Missing original timings or source metadata
are identified as missing and are never reconstructed. Concurrent edits in
focused development are reported by their original receipts; only the final
frozen full verifier establishes the complete candidate result.

## Publication and remaining work

This report establishes local verification and exact preservation. Any later
publication has separate exact-tree and branch-readback receipts; it is not
inferred from a local result or an unreferenced upload. The remaining four-core
terminal obligations and their precise scope are recorded in
`docs/continuation-handoff.md` and the source-linked semantic review.
No numbered assertion is promoted in this run.
"""
    (RUN / "preservation.json").write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
    (RUN / "final-report.md").write_text(report, encoding="utf-8")
    print(json.dumps({key: record[key] for key in ["status", "latest_complete_verifier_attempt",
          "strict_build_jobs", "verified_declaration_count", "previous_verified_declarations_preserved",
          "new_verified_declaration_count", "previous_completed_result_mappings_preserved",
          "frozen_input_count", "fully_verified_numbered_assertion_count",
          "numbered_assertions_completed_in_this_run", "main_theorem_verified"]}, indent=2))


if __name__ == "__main__":
    main()
