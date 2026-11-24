#!/usr/bin/env python3
"""Inventory the exact reconstructed four-core sources for the full verifier."""
import hashlib
import json
from pathlib import Path
import subprocess

from update_global_factorization_manifest import source_proofs

ROOT = Path(__file__).resolve().parents[1]
BASELINE = "1c9404a454c99fe5c11ba8d774cb9c259f291f20"
TREE = "087e26b5f004af1f9423a6f2b137d805f5991f1a"
ASSERTIONS = [
    {"number": "4.16", "label": "three:prop:terminal",
     "statement_sha256": "1ba102e379594ab72de4ba73cf41c88d9fbdadf1c132e2943b48da04e8c2cc1c",
     "lean_theorems": ["Overfull.frequent_pattern_result_one_factorization"]},
    {"number": "4.17", "label": "three:thm:regular-four",
     "statement_sha256": "b271893680e87b1c06c35172a138050dbf84009964eb618dce53c53ba595e322",
     "lean_theorems": ["Overfull.regular_core_one_factorization"]},
]


def main():
    previous = set(subprocess.check_output(
        ["git", "ls-tree", "-r", "--name-only", BASELINE], cwd=ROOT, text=True).splitlines())
    paths = sorted(p for p in (ROOT / "Overfull").rglob("*.lean")
                   if p.relative_to(ROOT).as_posix() not in previous)
    modules = []
    for path in paths:
        proofs = source_proofs(path)
        modules.append({
            "module": ".".join(path.relative_to(ROOT).with_suffix("").parts),
            "path": path.relative_to(ROOT).as_posix(),
            "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "public_theorem_count": len(proofs),
            "public_proof_declarations": proofs,
        })
    names = sorted(p["name"] for module in modules for p in module["public_proof_declarations"])
    endpoints = [name for assertion in ASSERTIONS for name in assertion["lean_theorems"]]
    if len(names) != len(set(names)) or not set(endpoints) <= set(names):
        raise ValueError("Duplicate public names or missing full endpoint in source inventory")
    result = {
        "schema_version": 1,
        "kind": "numbered_assertion_closure_with_supporting_continuations",
        "baseline_commit": BASELINE,
        "baseline_tree": TREE,
        "baseline_publication_status": "both_remote_branches_independently_verified",
        "numbered_assertions_completed": 2,
        "main_theorem_verified": False,
        "source_assertions": ASSERTIONS,
        "public_theorems": endpoints,
        "scope": (
            "Complete Proposition 4.16 for the actual FrequentPatternResult on an arbitrary "
            "finite index type of cardinality three or four, and complete Theorem 4.17 for "
            "the original even-order simple regular host with three or four robust cores. "
            "Uniform choices precede the host and all graph-dependent data. The all-even "
            "and exactly-two-odd four-core branches join the existing three-core and "
            "all-four-odd cases. Actual original edge copies, forest and pair supplies, "
            "and the literal linear exceptional/core-error budget are preserved. "
            "The main theorem remains unverified. The inventory describes current sources; "
            "the new full kernel run and preservation receipt establish verification."
        ),
        "review": "docs/four-core-continuation-semantic-review.md",
        "proof_map": "docs/four-core-continuation-verification.md",
        "module_count": len(modules),
        "public_theorem_count": len(names),
        "modules": modules,
        "required_proof_declarations": names,
    }
    (ROOT / "docs/four-core-continuation-source.json").write_text(json.dumps(result, indent=2) + "\n")
    print(f"Mapped {len(modules)} sources and {len(names)} public proofs; genuine complete verification is required.")


if __name__ == "__main__":
    main()
