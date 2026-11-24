#!/usr/bin/env python3
"""Validate exact baseline preservation and the genuine complete audit result."""
from datetime import datetime, timezone
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import subprocess
import sys

RUN = Path(__file__).resolve().parent
ROOT = RUN.parents[2]
BASELINE = "14978e4dec2bce94f63953df7b1bdd54f61c3e6c"
TREE = "c16767d2e47032ac8e28fd6f18a2bfe4b0ea4767"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
EDITABLE_INPUTS = {"Overfull.lean", "README.md", "docs/continuation-handoff.md",
                   "docs/coverage.json", "docs/manuscript-source.json", "scripts/verify.py"}
LIVE_OUTPUTS = {"verification/results.json", "verification/build.log", "verification/axioms.log",
                "verification/lean-version.log", "verification/vizing-source.log"}
PRINCIPAL_OUTPUTS = {
    "verification/results.json", "verification/build.log", "verification/axioms.log",
    "verification/global-factorization-declarations.json",
}
REQUIRED_CONTROLS = {
    "check-preservation.py", "run-verifier.py", "record-command.py",
    "verifier-additions.json", "root-added-imports.json", "development-index.json",
    "source-statement-3.1.tex", "source-statement-3.1.json",
    "independent-single-core-review.md", "independent-four-regular-review.md",
    "independent-verification-review.md",
}


def require(value, message):
    if not value:
        raise RuntimeError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def load(path):
    return json.loads(path.read_text())


def git(*args):
    return subprocess.check_output(["git", *args], cwd=ROOT)


@lru_cache(None)
def old(path):
    return git("show", f"{BASELINE}:{path}")


def current_inputs():
    paths = [ROOT / "Overfull.lean", ROOT / "Audit.lean", *(ROOT / "Overfull").rglob("*.lean"),
             ROOT / "lean-toolchain", ROOT / "lakefile.toml", ROOT / "lake-manifest.json",
             ROOT / "README.md", ROOT / ".github/workflows/lean.yml",
             *(ROOT / "scripts").glob("*.py"), *(ROOT / "docs").glob("*.json"),
             *(ROOT / "docs").glob("*.md"), *(ROOT / "patches").glob("*.patch"),
             ROOT / "THIRD_PARTY_NOTICES.txt", ROOT / "CIRCULATION_NOTICE.txt",
             ROOT / "LICENSE_BMATCHING.txt"]
    return {p.relative_to(ROOT).as_posix(): p.read_bytes() for p in sorted(paths)}


def current_controls():
    """Freeze the code, exact edit permissions, pinned statement, and reviews."""
    paths = {RUN / name for name in REQUIRED_CONTROLS}
    paths.update(RUN.glob("*.py"))
    paths.update(RUN.glob("independent-*.md"))
    paths.update(RUN.glob("verifier-*.patch"))
    return {p.name: p.read_bytes() for p in sorted(paths)}


def check_verifier():
    expected = old("scripts/verify.py").decode()
    edits = load(RUN / "verifier-additions.json")
    require(len(edits) == 5, "Expected the reviewed count update and four additive registrations")
    for edit in edits:
        require(expected.count(edit["old"]) == 1, "Ambiguous verifier edit anchor")
        expected = expected.replace(edit["old"], edit["new"], 1)
    require((ROOT / "scripts/verify.py").read_text() == expected,
            "Verifier changed beyond the five reviewed modifications")
    require((ROOT / "Audit.lean").read_bytes() == old("Audit.lean"), "The stock kernel audit changed")


def check_coverage():
    previous, current = json.loads(old("docs/coverage.json")), load(ROOT / "docs/coverage.json")
    before = {a["number"]: a for a in previous["numbered_assertions"]}
    after = {a["number"]: a for a in current["numbered_assertions"]}
    require(list(before) == list(after) and len(after) == 69, "Numbered assertion inventory changed")
    require(all(before[n] == after[n] for n in before if n != "3.1"), "An unrelated assertion changed")
    identity = ["number", "kind", "labels", "section", "statement_source_lines", "statement_sha256",
                "imported_statement"]
    require(all(before["3.1"][k] == after["3.1"][k] for k in identity), "Lemma 3.1 identity changed")
    require(after["3.1"]["statement_sha256"] == "e367990020005abeac5226b4f90e96728cafec20b584b7db4d442fda779af0fe"
            and after["3.1"]["full_assertion_verified"] is True
            and after["3.1"]["lean_theorems"] == ["Overfull.single_core_coloring"],
            "Coverage does not identify the exact complete single-core lemma")
    old_complete = {n for n, a in before.items() if a["full_assertion_verified"]}
    new_complete = {n for n, a in after.items() if a["full_assertion_verified"]}
    require(len(old_complete) == 48 and new_complete == old_complete | {"3.1"}
            and current["fully_verified_numbered_assertion_count"] == 49
            and current["main_theorem_verified"] is False, "Coverage exceeds the proved closure")
    old_catalog = previous["checked_component_catalog"]
    require(current["checked_component_catalog"][:len(old_catalog)] == old_catalog,
            "A previous checked component changed")
    allowed = {"scope", "checked_component_catalog", "numbered_assertions",
               "fully_verified_numbered_assertion_count"}
    require({k: v for k, v in previous.items() if k not in allowed}
            == {k: v for k, v in current.items() if k not in allowed}, "Other coverage metadata changed")
    previous_source = json.loads(old("docs/manuscript-source.json"))
    source = load(ROOT / "docs/manuscript-source.json")
    require(source["fully_verified_numbered_assertions"] == 49, "Manuscript completed count is wrong")
    old_additional = previous_source["additional_complete_results"]
    require(source["additional_complete_results"][:len(old_additional)] == old_additional
            and len(source["additional_complete_results"]) == len(old_additional) + 1
            and source["additional_complete_results"][-1]["lean_name"] == "Overfull.single_core_coloring",
            "Manuscript result inventory changed beyond the single-core closure")
    allowed_source = {"fully_verified_numbered_assertions", "additional_complete_results"}
    require({k: v for k, v in source.items() if k not in allowed_source}
            == {k: v for k, v in previous_source.items() if k not in allowed_source},
            "Pinned manuscript metadata or historical evidence changed")
    return {"numbered_assertions": 69, "previous_complete": 48, "current_complete": 49,
            "only_promoted_assertion": "3.1", "all_other_68_records_identical": True,
            "all_69_statement_identities_identical": True, "main_theorem_verified": False}


def check_development():
    """Check the exact inventory of genuine successful and failed focused runs."""
    recorded = load(RUN / "development-index.json")
    files = {p.relative_to(RUN).as_posix(): p for p in (RUN / "development").rglob("*") if p.is_file()}
    require(recorded["schema_version"] == 1 and recorded["file_count"] == len(files)
            and set(recorded["files"]) == set(files), "Development evidence inventory changed")
    for name, path in files.items():
        data, entry = path.read_bytes(), recorded["files"][name]
        require(len(data) == entry["bytes"] and sha(data) == entry["sha256"],
                "Development evidence bytes changed: " + name)
    attempts = []
    for path in sorted((RUN / "development").glob("*/command.json")):
        command = load(path)
        require(type(command["exit_code"]) is int and command["status"] in {"passed", "failed"},
                "An unfinished focused attempt cannot be included in the final freeze")
        require(command["status"] != "passed" or command["exit_code"] == 0,
                "A focused attempt was marked passed despite a nonzero actual exit")
        require((path.parent / "output.log").is_file(), "Missing genuine focused command output")
        for source, digest in command["source_sha256"].items():
            require(sha((path.parent / "source" / source).read_bytes()) == digest,
                    "Changed focused-command source snapshot")
        attempts.append({"attempt": path.parent.name, "command": command["command"],
                         "exit_code": command["exit_code"], "status": command["status"],
                         "changed_inputs": command["inputs_changed_during_command"]})
    counts = {status: sum(a["status"] == status for a in attempts) for status in {"passed", "failed"}}
    require(recorded["attempt_count"] == len(attempts) and recorded["attempts"] == attempts
            and recorded["status_counts"] == counts, "Development attempt summary changed")
    return {"attempt_count": len(attempts), "file_count": len(files), "status_counts": counts,
            "attempts_with_recorded_input_changes": [a["attempt"] for a in attempts if a["changed_inputs"]],
            "exact_inventory_hashes_and_sizes_preserved": True}


def preflight(inputs=None):
    inputs = current_inputs() if inputs is None else inputs
    require(git("rev-parse", "HEAD").decode().strip() == BASELINE, "Unexpected baseline HEAD")
    require(git("rev-parse", BASELINE + "^{tree}").decode().strip() == TREE, "Unexpected baseline tree")
    previous = json.loads(old("verification/results.json"))
    require(previous["verified_declaration_count"] == 13675
            and len(previous["completed_results"]) == 2396, "Baseline verification counts differ")
    hashes = {**previous["source_sha256"], **previous["verification_input_sha256"]}
    require(len(hashes) == 741, "Baseline frozen-input count differs")
    for path, digest in hashes.items():
        require(path in inputs, f"A previous frozen input disappeared: {path}")
        if path not in EDITABLE_INPUTS:
            require(sha(inputs[path]) == digest, f"A previous immutable input changed: {path}")
    changes = set(git("diff", "--name-only", BASELINE, "--").decode().splitlines())
    require(changes <= EDITABLE_INPUTS | LIVE_OUTPUTS,
            "Unreviewed previous tracked files changed: " + str(sorted(changes - EDITABLE_INPUTS - LIVE_OUTPUTS)))
    check_verifier()
    coverage = check_coverage()
    manifest = load(ROOT / "docs/global-factorization-source.json")
    new_sources = {path for path in inputs if path.endswith(".lean") and path not in hashes}
    require(new_sources == {m["path"] for m in manifest["modules"]}, "New source manifest is incomplete")
    for module in manifest["modules"]:
        require(sha(inputs[module["path"]]) == module["sha256"], "New source hash mismatch")
    imports = load(RUN / "root-added-imports.json")
    original = old("Overfull.lean").decode()
    split = original.index("\n/-!")
    expected = original[:split] + "".join(imports) + original[split:]
    require((ROOT / "Overfull.lean").read_text() == expected, "Root changed beyond recorded added imports")
    for line in imports:
        require(line.startswith("import ") and line.endswith("\n")
                and line[7:].strip() in {m["module"] for m in manifest["modules"]}, "Unmapped root import")
    development = check_development()
    return {"baseline_commit": BASELINE, "baseline_tree": TREE,
            "previous_audited_declarations": 13675, "previous_completed_result_mappings": 2396,
            "previous_frozen_inputs": len(hashes), "coverage": coverage,
            "all_previous_mathematical_sources_and_audit_unchanged": True,
            "verifier_changes_exactly_reviewed": True, "new_module_count": len(new_sources),
            "development_evidence": development}


def index(declarations):
    result = {d["name"]: (d["module"], frozenset(d["axioms"])) for d in declarations}
    require(len(result) == len(declarations), "Duplicate audited declaration name")
    return result


def check_execution_receipt(folder, receipt, frozen, inputs):
    """Bind the live report and raw audit to the one actual recorded execution."""
    require(receipt["command"] == ["python3", "scripts/verify.py"]
            and receipt["cwd"] == str(ROOT) and receipt["attempt"] == folder.name
            and receipt["baseline_commit"] == BASELINE and receipt["baseline_tree"] == TREE
            and receipt["verifier_launched"] is True and receipt["exit_code"] == 0
            and receipt["preflight_passed"] is True and receipt["wrapper_exit_code"] == 0
            and receipt["wrapper_errors"] == [] and receipt["missing_principal_outputs"] == []
            and receipt["status"] == "passed" and receipt["inputs_unchanged"] is True
            and receipt["controls_unchanged"] is True,
            "The genuine full verifier did not pass on unchanged inputs and controls")
    require((folder / "command.json").read_bytes() == (folder / "terminal.json").read_bytes(),
            "The terminal receipt differs from the command receipt")
    require(sha((folder / "output.log").read_bytes()) == receipt["output_sha256"],
            "The recorded full command output changed")
    require(receipt["frozen_input_count"] == len(frozen)
            and {p: sha(data) for p, data in inputs.items()} == frozen,
            "Inputs changed after full verification")
    for path, digest in frozen.items():
        require(sha((folder / "input" / path).read_bytes()) == digest,
                "Frozen input snapshot changed: " + path)
    controls = current_controls()
    recorded_controls = receipt["control_sha256"]
    require(REQUIRED_CONTROLS <= set(recorded_controls)
            and {name: sha(data) for name, data in controls.items()} == recorded_controls,
            "Verification control inventory or live control bytes changed")
    require(load(folder / "frozen-controls.json") == recorded_controls,
            "The frozen control inventory differs from the command receipt")
    for name, digest in recorded_controls.items():
        require(Path(name).name == name, "A control name is not a flat run-relative path")
        require(sha((folder / "control" / name).read_bytes()) == digest,
                "Frozen verification control changed: " + name)
    outputs = {entry["path"]: entry for entry in receipt["outputs"]}
    require(len(outputs) == len(receipt["outputs"]), "Duplicate full-verifier output path")
    require(PRINCIPAL_OUTPUTS <= set(outputs),
            "The full-verifier receipt omits a principal output")
    for path, entry in outputs.items():
        relative = Path(path)
        require(len(relative.parts) == 2 and relative.parts[0] == "verification"
                and relative.suffix in {".json", ".log"}, "Unexpected verifier output path")
        live = (ROOT / path).read_bytes()
        archived = (folder / "artifacts" / path).read_bytes()
        require(len(live) == len(archived) == entry["bytes"]
                and sha(live) == sha(archived) == entry["sha256"],
                "Live and archived output differ from the actual command: " + path)
    return {"principal_outputs_present": True, "all_recorded_live_outputs_match_archive": True,
            "raw_command_output_unchanged": True, "terminal_receipt_identical": True,
            "all_verification_controls_preserved": True, "control_count": len(recorded_controls),
            "recorded_output_count": len(outputs)}


def main():
    attempt = sys.argv[1] if len(sys.argv) == 2 else "full-01"
    inputs = current_inputs()
    result = preflight(inputs)
    folder = RUN / attempt
    receipt = load(folder / "command.json")
    frozen = load(folder / "frozen-inputs.json")
    execution = check_execution_receipt(folder, receipt, frozen, inputs)
    current = load(ROOT / "verification/results.json")
    previous = json.loads(old("verification/results.json"))
    require(current["lean_build_passed"] and current["axiom_audit_passed"], "Complete verification failed")
    require({**current["source_sha256"], **current["verification_input_sha256"]} == frozen,
            "Full-verifier result does not identify the actual frozen inputs")
    old_declarations, new_declarations = index(previous["verified_declarations"]), index(current["verified_declarations"])
    require(all(new_declarations.get(n) == value for n, value in old_declarations.items()),
            "A prior declaration, module owner or axiom set changed/disappeared")
    require(all(axioms <= ALLOWED_AXIOMS for _, axioms in new_declarations.values()), "Forbidden axiom found")
    require(all(current["completed_results"].get(k) == v for k, v in previous["completed_results"].items()),
            "A previous completed-result mapping changed")
    for k, v in previous.items():
        if k.endswith("_declaration_map"):
            require(current[k] == v, "A previous complete source/declaration map changed: " + k)
            require(sha((ROOT / v["path"]).read_bytes()) == v["sha256"], "A prior declaration map changed bytes")
    require(current["fully_verified_numbered_assertion_count"] == 49 and not current["main_theorem_verified"],
            "Full-verifier coverage does not match the reviewed scope")
    manifest = load(ROOT / "docs/global-factorization-source.json")
    modules = {m["module"] for m in manifest["modules"]}
    mapped = load(ROOT / "verification/global-factorization-declarations.json")
    require(index(mapped["proof_declaration_map"]) == {n: d for n, d in new_declarations.items() if d[0] in modules},
            "The new map does not include every private and generated audited proof")
    result.update({"status": "passed", "checked_at_utc": datetime.now(timezone.utc).isoformat(),
                   "full_verifier_attempt": attempt, "actual_full_verifier_exit": receipt["exit_code"],
                   "audited_declarations": len(new_declarations),
                   "new_audited_declarations": len(new_declarations) - len(old_declarations),
                   "public_theorem_count": manifest["public_theorem_count"],
                   "frozen_input_count": len(frozen), "allowed_axioms": sorted(ALLOWED_AXIOMS),
                   "all_previous_declarations_owners_axiom_sets_preserved": True,
                   "all_previous_completed_result_mappings_preserved": True,
                   "all_previous_source_declaration_maps_preserved": True,
                   "execution_evidence": execution,
                   "genuine_command_receipt_sha256": sha((folder / "command.json").read_bytes())})
    (RUN / "preservation.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
