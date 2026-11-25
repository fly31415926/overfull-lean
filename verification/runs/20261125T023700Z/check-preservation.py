#!/usr/bin/env python3
"""Check immutable baseline mathematics and the actual new kernel audit."""
from functools import lru_cache
import hashlib
import json
import re
from pathlib import Path
import subprocess

RUN = Path(__file__).resolve().parent
ROOT = RUN.parents[2]
BASELINE = "5679471018d5d087d942c592c72fca3d24e7ea32"
TREE = "918663f3827a27a29312835f7b2218d850326a0d"
NEW_MAP = "verification/two-pair-native-declarations.json"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def require(value, message):
    if not value:
        raise RuntimeError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def load(path):
    return json.loads(path.read_text())


@lru_cache(None)
def old(path):
    return subprocess.check_output(["git", "show", f"{BASELINE}:{path}"], cwd=ROOT)


def current_inputs():
    paths = [ROOT / "Overfull.lean", ROOT / "Audit.lean", *(ROOT / "Overfull").rglob("*.lean"),
             ROOT / "lean-toolchain", ROOT / "lakefile.toml", ROOT / "lake-manifest.json",
             ROOT / "README.md", ROOT / ".github/workflows/lean.yml",
             *(ROOT / "scripts").glob("*.py"), *(ROOT / "docs").glob("*.json"),
             *(ROOT / "docs").glob("*.md"), *(ROOT / "patches").glob("*.patch"),
             ROOT / "THIRD_PARTY_NOTICES.txt", ROOT / "CIRCULATION_NOTICE.txt",
             ROOT / "LICENSE_BMATCHING.txt"]
    return {p.relative_to(ROOT).as_posix(): p.read_bytes() for p in sorted(set(paths))}


def current_controls():
    paths = [p for p in RUN.iterdir() if p.is_file() and p.suffix in {".py", ".md", ".json", ".tex"}]
    return {p.name: p.read_bytes() for p in sorted(paths)}


def preflight(inputs):
    observed_tree = subprocess.check_output(
        ["git", "rev-parse", f"{BASELINE}^{{tree}}"], cwd=ROOT).decode().strip()
    require(observed_tree == TREE, "Baseline tree does not match its pinned identity")
    previous = json.loads(old("verification/results.json"))
    require(inputs["Audit.lean"] == old("Audit.lean"), "Stock audit source changed")
    old_source_count = 0
    for path, digest in previous["source_sha256"].items():
        if path == "Overfull.lean":
            continue
        require(path in inputs and sha(inputs[path]) == digest, "Baseline proof changed: " + path)
        old_source_count += 1
    before_imports = old("Overfull.lean")
    import_anchor = b"import Overfull.OrdinaryCoreColoring\n"
    require(before_imports.count(import_anchor) == 1, "Ambiguous root import anchor")
    imports = load(RUN / "root-imports.json")
    require(isinstance(imports, list) and imports
            and all(isinstance(line, str)
                    and re.fullmatch(r"import Overfull(?:\.[A-Za-z0-9_]+)+\n", line)
                    for line in imports), "Malformed root import additions")
    require(len(set(imports)) == len(imports), "Duplicate root import additions")
    require(all(line.encode() not in before_imports for line in imports),
            "Registered root import already exists in baseline")
    expected_imports = before_imports.replace(
        import_anchor, import_anchor + "".join(imports).encode(), 1)
    require(inputs["Overfull.lean"] == expected_imports,
            "Root imports changed beyond the registered additive imports")
    expected_verifier = old("scripts/verify.py").decode()
    edits = load(RUN / "verifier-additions.json")
    for edit in edits:
        require(edit["kind"] == "additive" and edit["old"] in edit["new"]
                and len(edit["new"]) > len(edit["old"]), "Nonadditive verifier edit")
        require(expected_verifier.count(edit["old"]) == 1, "Ambiguous verifier anchor")
        expected_verifier = expected_verifier.replace(edit["old"], edit["new"], 1)
    require(inputs["scripts/verify.py"].decode() == expected_verifier,
            "Verifier differs from registered additive edits")
    for path, digest in previous["verification_input_sha256"].items():
        if path in {"README.md", "docs/coverage.json", "docs/manuscript-source.json",
                    "docs/continuation-handoff.md", "docs/next-verification-target.md", "scripts/verify.py"}:
            continue
        require(path in inputs and sha(inputs[path]) == digest,
                "Previous immutable verification input changed: " + path)
    before = json.loads(old("docs/coverage.json"))
    after = load(ROOT / "docs/coverage.json")
    require(set(after) == set(before), "Unexpected coverage metadata keys")
    require(after["numbered_assertions"] == before["numbered_assertions"],
            "A pinned numbered assertion or its status changed")
    require(after["fully_verified_numbered_assertion_count"] == 51
            and after["numbered_assertion_count"] == 69
            and after["main_theorem_verified"] is False, "Unreviewed coverage claim")
    catalog = before["checked_component_catalog"]
    require(after["checked_component_catalog"][:len(catalog)] == catalog,
            "Previous checked components changed")
    for key in before.keys() - {"scope", "checked_component_catalog"}:
        require(after[key] == before[key], "Unexpected coverage metadata edit: " + key)
    old_ms = json.loads(old("docs/manuscript-source.json"))
    new_ms = load(ROOT / "docs/manuscript-source.json")
    require(set(new_ms) == set(old_ms), "Unexpected manuscript metadata keys")
    old_support = old_ms["additional_checked_components"]
    require(new_ms["additional_checked_components"][:len(old_support)] == old_support,
            "A previous source support mapping changed")
    for key in old_ms.keys() - {"additional_checked_components"}:
        require(new_ms[key] == old_ms[key], "Pinned manuscript metadata changed: " + key)
    source = load(ROOT / "docs/two-pair-native-source.json")
    require(source["numbered_assertions_completed"] == 0
            and source["main_theorem_verified"] is False, "Unreviewed source promotion")
    require(source["baseline_commit"] == BASELINE and source["baseline_tree"] == TREE,
            "New source manifest has a different baseline")
    modules = source["modules"]
    module_names = {item["module"] for item in modules}
    module_paths = {item["path"] for item in modules}
    require(len(module_names) == len(modules) == len(module_paths) == source["module_count"],
            "Duplicate or uncounted new source module")
    new_math_paths = {path for path in inputs if path.startswith("Overfull/")
                      and path.endswith(".lean")} - set(previous["source_sha256"])
    require(new_math_paths == module_paths, "Unregistered new mathematical source")
    for item in modules:
        require(item["path"] == item["module"].replace(".", "/") + ".lean",
                "New source module and path disagree")
        require(item["path"] in inputs and sha(inputs[item["path"]]) == item["sha256"],
                "New module differs from its source manifest: " + item["path"])
    return {"baseline_commit": BASELINE, "baseline_tree": TREE,
            "unchanged_previous_nonroot_mathematical_sources": old_source_count,
            "all_69_numbered_records_identical": True,
            "previous_complete": 51, "current_complete": 51,
            "stock_audit_unchanged": True, "additive_root_imports": len(imports),
            "new_mathematical_modules": len(modules), "additive_verifier_edits": len(edits)}


def final_checks():
    before = json.loads(old("verification/results.json"))
    after = load(ROOT / "verification/results.json")
    require(after["lean_build_passed"] is True and after["axiom_audit_passed"] is True,
            "Actual full verifier did not pass")
    old_decls = {x["name"]: x for x in before["verified_declarations"]}
    new_decls = {x["name"]: x for x in after["verified_declarations"]}
    require(len(new_decls) == after["verified_declaration_count"], "Duplicate audit declaration")
    for name, item in old_decls.items():
        require(new_decls.get(name) == item, "Prior declaration/owner/axioms changed: " + name)
    for name, item in new_decls.items():
        require(set(item["axioms"]) <= ALLOWED_AXIOMS, "Disallowed axiom: " + name)
    for key, value in before["completed_results"].items():
        require(after["completed_results"].get(key) == value, "Prior result mapping changed: " + key)
    require(set(before["imported_project_modules"]) <= set(after["imported_project_modules"]),
            "A previous project module disappeared")
    for key, value in before.items():
        if key.endswith("declaration_map") and isinstance(value, dict) and "path" in value:
            require((ROOT / value["path"]).read_bytes() == old(value["path"]),
                    "Prior declaration map changed: " + value["path"])
    require(after["fully_verified_numbered_assertions"] == before["fully_verified_numbered_assertions"]
            and after["fully_verified_numbered_assertion_count"] == 51
            and after["main_theorem_verified"] is False, "Pinned completion status changed")
    source = load(ROOT / "docs/two-pair-native-source.json")
    mapped = load(ROOT / NEW_MAP)
    modules = {m["module"] for m in source["modules"]}
    source_modules = {m["module"]: m for m in source["modules"]}
    require(set(after["imported_project_modules"]) - set(before["imported_project_modules"]) == modules,
            "Imported new modules differ from the registered source modules")
    require(after["two_pair_native_declaration_map"]["path"] == NEW_MAP
            and sha((ROOT / NEW_MAP).read_bytes()) == after["two_pair_native_declaration_map"]["sha256"],
            "The new declaration map differs from the verifier's recorded hash")
    additions = set(new_decls) - set(old_decls)
    require(additions == {x["name"] for x in mapped["proof_declaration_map"]},
            "New public/private/generated declaration map is incomplete")
    require(len(mapped["proof_declaration_map"]) == len(additions)
            and mapped["verified_declaration_count"] == len(additions),
            "The new declaration map has duplicate or uncounted entries")
    for item in mapped["proof_declaration_map"]:
        require({k: item[k] for k in ("name", "module", "axioms")} == new_decls[item["name"]],
                "Mapped declaration differs from its actual audit entry: " + item["name"])
        owner = source_modules[item["module"]]
        require(item["source_path"] == owner["path"] and item["source_sha256"] == owner["sha256"],
                "Mapped source identity differs: " + item["name"])
    require({new_decls[n]["module"] for n in additions} == modules,
            "Unexpected module in added proof declarations")
    for path, digest in after["source_sha256"].items():
        require(sha((ROOT / path).read_bytes()) == digest, "Verified mathematical bytes changed: " + path)
    for path, digest in after["verification_input_sha256"].items():
        require(sha((ROOT / path).read_bytes()) == digest, "Verified input bytes changed: " + path)
    return {"status": "passed", "old_declarations_preserved": len(old_decls),
            "new_declarations": len(additions), "all_declarations": len(new_decls),
            "old_result_mappings_preserved": len(before["completed_results"]),
            "all_result_mappings": len(after["completed_results"]),
            "new_modules": len(modules), "public_proofs": source["public_theorem_count"],
            "complete_numbered_assertions": 51, "numbered_assertions": 69,
            "main_theorem_verified": False, "allowed_axioms": sorted(ALLOWED_AXIOMS)}
