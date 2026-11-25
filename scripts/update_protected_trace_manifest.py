#!/usr/bin/env python3
"""Inventory the current protected-trace continuation against its fixed baseline.

All newly added first-party Lean modules are discovered by subtracting the
baseline mathematical source inventory from the current tree.  This continues
to work after files are staged or committed.  The full verifier separately
audits every public, private, and generated proof declaration.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

from update_global_factorization_manifest import source_proofs

ROOT = Path(__file__).resolve().parents[1]
BASELINE = "f2510d10c114bcf3d0003b5e2e4e35cb0400167d"
TREE = "58fe77f4afaba4b0ab6cf77956afb1c23608cd35"
SOURCE_PATH = "docs/protected-trace-source.json"
REQUIRED_ENDPOINT = (
    "Overfull.NativeReserve."
    "exists_fourTwoOddJoining_decomposition_with_reserved_primary"
)


def baseline_json(path):
    return json.loads(subprocess.check_output(
        ["git", "show", f"{BASELINE}:{path}"], cwd=ROOT
    ))


def make_manifest():
    observed_tree = subprocess.check_output(
        ["git", "rev-parse", f"{BASELINE}^{{tree}}"], cwd=ROOT, text=True
    ).strip()
    if observed_tree != TREE:
        raise ValueError("The protected-trace baseline tree differs from its pin")
    previous = baseline_json("verification/results.json")
    previous_paths = set(previous["source_sha256"])
    paths = sorted(p for p in (ROOT / "Overfull").rglob("*.lean")
                   if p.relative_to(ROOT).as_posix() not in previous_paths)
    if not paths:
        raise ValueError("No new mathematical source modules were found")
    modules = []
    for path in paths:
        relative = path.relative_to(ROOT)
        proofs = source_proofs(path)
        modules.append({
            "module": ".".join(relative.with_suffix("").parts),
            "path": relative.as_posix(),
            "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "public_theorem_count": len(proofs),
            "public_proof_declarations": proofs,
        })
    names = sorted(p["name"] for module in modules
                   for p in module["public_proof_declarations"])
    if len(names) != len(set(names)) or REQUIRED_ENDPOINT not in names:
        raise ValueError("Missing reserved-primary endpoint or duplicate public proof")
    coverage = baseline_json("docs/coverage.json")
    source_assertions = [{k: a[k] for k in
                          ("number", "labels", "statement_sha256", "full_assertion_verified")}
                         for a in coverage["numbered_assertions"]
                         if a["number"] in {"4.4", "4.5"}]
    if len(source_assertions) != 2 or any(a["full_assertion_verified"] for a in source_assertions):
        raise ValueError("This continuation must retain the open pinned assertions")
    return {
        "schema_version": 1,
        "kind": "supporting_continuation",
        "baseline_commit": BASELINE,
        "baseline_tree": TREE,
        "numbered_assertions_completed": 0,
        "main_theorem_verified": False,
        "public_theorems": names,
        "source_assertions": source_assertions,
        "scope": (
            "Supporting constructions for protected joining traces of the native partner reserve. "
            "The four-label original/virtual circuit construction forces selected actual crossings "
            "to be singleton primary pieces. All registered palette, trace, boundary, and star "
            "interfaces retain their explicit actual-copy, parity, regularity, disjointness, and "
            "numerical hypotheses. The final native two-pair external assembly constructs its "
            "joining palette, exact protected traces, zero-or-one-star geometry, complete "
            "exceptional extension, old-core parity, and true core-deficit loads from a safe "
            "regular residual and retained-core/numerical budgets. The precise conclusions and assumptions of each named public "
            "theorem are recorded in the proof map and semantic review. This continuation does not "
            "construct the complete native safe residual or finish the zero-/one-pair multi-star "
            "branches, terminal assembly, or the main theorem. All 69 pinned numbered records, "
            "including their 51 complete statuses, remain unchanged."
        ),
        "review": "docs/protected-trace-semantic-review.md",
        "proof_map": "docs/protected-trace-verification.md",
        "module_discovery": "All current Overfull/*.lean sources absent from the pinned baseline source inventory",
        "module_count": len(modules),
        "public_theorem_count": len(names),
        "modules": modules,
        "required_proof_declarations": names,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-only", action="store_true",
                        help="Parse and validate the inventory without writing files")
    parser.add_argument("--register-root-imports", metavar="RUN_DIRECTORY",
                        help="Also write the exact additive root imports to this run directory")
    args = parser.parse_args()
    if args.check_only and args.register_root_imports:
        parser.error("--check-only cannot write root-import controls")
    source = make_manifest()
    if not args.check_only:
        (ROOT / SOURCE_PATH).write_text(json.dumps(source, indent=2) + "\n")
        if args.register_root_imports:
            run = Path(args.register_root_imports)
            if not run.is_absolute():
                run = ROOT / run
            if not run.is_dir() or run.parent != ROOT / "verification/runs":
                raise ValueError("Root imports must be registered in an existing verification run")
            imports = [f"import {item['module']}\n" for item in source["modules"]]
            (run / "root-imports.json").write_text(json.dumps(imports, indent=2) + "\n")
    print(json.dumps({
        "mode": "check_only" if args.check_only else "written",
        "source_manifest": SOURCE_PATH,
        "module_count": source["module_count"],
        "public_theorem_count": source["public_theorem_count"],
        "module_paths": [m["path"] for m in source["modules"]],
        "numbered_assertions_completed": 0,
        "full_verifier_run": False,
    }, indent=2))


if __name__ == "__main__":
    main()
