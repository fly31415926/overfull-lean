#!/usr/bin/env python3
"""Check immutable baseline mathematics and the actual new kernel audit."""
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import subprocess

RUN = Path(__file__).resolve().parent
ROOT = RUN.parents[2]
BASELINE = "ac05c3232425399af6c0f29e1f7d3ddc1037424d"
TREE = "8cfcdcc6cdd08b3209bc21b1823122bb141c330e"
NEW_MAP = "verification/ordinary-core-coloring-declarations.json"
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
    previous = json.loads(old("verification/results.json"))
    old_source_count = 0
    for path, digest in previous["source_sha256"].items():
        if path == "Overfull.lean":
            continue
        require(path in inputs and sha(inputs[path]) == digest, "Baseline proof changed: " + path)
        old_source_count += 1
    before_imports = old("Overfull.lean")
    import_anchor = b"import Overfull.FourCoreReduction.Regular\n"
    require(before_imports.count(import_anchor) == 1, "Ambiguous root import anchor")
    expected_imports = before_imports.replace(
        import_anchor, import_anchor + b"import Overfull.OrdinaryCoreColoring\n", 1)
    require(inputs["Overfull.lean"] == expected_imports,
            "Root imports changed beyond the exact new entry")
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
    old_support = old_ms["additional_checked_components"]
    require(new_ms["additional_checked_components"][:len(old_support)] == old_support,
            "A previous source support mapping changed")
    for key in old_ms.keys() - {"additional_checked_components"}:
        require(new_ms[key] == old_ms[key], "Pinned manuscript metadata changed: " + key)
    source = load(ROOT / "docs/ordinary-core-coloring-source.json")
    require(source["numbered_assertions_completed"] == 0
            and source["main_theorem_verified"] is False, "Unreviewed source promotion")
    return {"baseline_commit": BASELINE, "baseline_tree": TREE,
            "unchanged_previous_nonroot_mathematical_sources": old_source_count,
            "all_69_numbered_records_identical": True,
            "previous_complete": 51, "current_complete": 51,
            "stock_audit_unchanged": True, "additive_verifier_edits": len(edits)}


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
    source = load(ROOT / "docs/ordinary-core-coloring-source.json")
    mapped = load(ROOT / NEW_MAP)
    modules = {m["module"] for m in source["modules"]}
    source_modules = {m["module"]: m for m in source["modules"]}
    require(after["ordinary_core_coloring_declaration_map"]["path"] == NEW_MAP
            and sha((ROOT / NEW_MAP).read_bytes()) == after["ordinary_core_coloring_declaration_map"]["sha256"],
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
