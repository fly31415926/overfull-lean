#!/usr/bin/env python3
"""Inventory the exact unrestricted four-label continuation sources."""
import hashlib
import json
from pathlib import Path
import subprocess

from update_global_factorization_manifest import source_proofs

ROOT = Path(__file__).resolve().parents[1]
BASELINE = "3991bb7eee091a329046073e0366daa84a603e5d"
TREE = "6424bf81123aa75b2254aea7eceff6260611f397"
ENDPOINTS = [
    "Overfull.Multigraph.exists_compatibleCircuitPartition_of_four_label",
    "Overfull.Multigraph.exists_compatibleCircuitPartition_of_card_le_four",
    "Overfull.Multigraph.exists_safe_short_circuit_of_four_strictNonlocal",
    "Overfull.FourOdd.exists_compatibleCircuitPartition_of_tight_shore",
    "Overfull.FourOdd.exists_fourJoining_decomposition_of_even_fibers",
    "Overfull.FourOdd.exists_fourJoining_decomposition_of_even_degree_bound",
    "Overfull.FourOdd.exists_fourTwoOddJoining_decomposition",
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
    if len(names) != len(set(names)) or not set(ENDPOINTS) <= set(names):
        raise ValueError("Duplicate public names or missing endpoint in source inventory")
    result = {
        "schema_version": 1,
        "kind": "supporting_continuation",
        "baseline_commit": BASELINE,
        "baseline_tree": TREE,
        "baseline_publication_status": "both_remote_branches_independently_verified",
        "numbered_assertions_completed": 0,
        "main_theorem_verified": False,
        "scope": (
            "Complete compatible-circuit existence on at most four labels from only "
            "the original global half-cut inequalities and even selected degrees. "
            "No bounded multiplicity, bounded degree, connectedness, pre-existing "
            "partition or selector is assumed. Tight nonlocal shores are normalized, "
            "inside and outside partitions are constructed from the proved three-label "
            "theorem, and every original copy is restored through disjoint blocks and "
            "saved closed pieces. Strict nonlocal inputs have a constructed safely "
            "removable pair or triangle; induction uses arbitrary admissible even "
            "residuals. Arbitrary selected copy sets and finite label types of size at "
            "most four are covered. Original-host applications construct unrestricted "
            "even-fiber and two-odd-fiber joining decompositions with exact footprints, "
            "including the even-regular half-joining-degree interface. The full "
            "four-core terminal Proposition 4.16, Theorem 4.17 and main theorem are "
            "not asserted. All 69 numbered records and the 49 completed count remain unchanged."
        ),
        "review": "docs/four-label-existence-semantic-review.md",
        "proof_map": "docs/four-label-existence-verification.md",
        "public_theorems": ENDPOINTS,
        "module_count": len(modules),
        "public_theorem_count": len(names),
        "modules": modules,
        "required_proof_declarations": names,
    }
    (ROOT / "docs/four-label-existence-source.json").write_text(json.dumps(result, indent=2) + "\n")
    print(f"Mapped {len(modules)} sources and {len(names)} public proofs; complete verification is required.")


if __name__ == "__main__":
    main()
