#!/usr/bin/env python3
"""Inventory exact four-label reduction sources; the full verifier certifies them."""
import hashlib
import json
from pathlib import Path

from update_global_factorization_manifest import source_proofs

ROOT = Path(__file__).resolve().parents[1]
BASELINE = "e2e5455b11d5b1691d0a974fd3c5f72e989ec5b8"


def main():
    directory = ROOT / "Overfull/CompatibleCircuits"
    paths = sorted([*directory.glob("FourDegreeTwo*.lean"),
                    directory / "FourCutCriterion.lean",
                    directory / "FourGlobalCoarsening.lean",
                    directory / "FourTriangleSelection.lean",
                    directory / "FourBounded.lean",
                    directory / "FourBoundedJoining.lean"])
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
    names = sorted(proof["name"] for module in modules
                   for proof in module["public_proof_declarations"])
    if len(names) != len(set(names)):
        raise ValueError("Duplicate public proof name in four-label source inventory")
    endpoints = [
        "Overfull.Multigraph.exists_compatibleCircuitPartition_of_four_label_small_degree",
        "Overfull.Multigraph.exists_compatibleCircuitPartition_of_four_label_degree_le_four",
        "Overfull.Multigraph.exists_compatibleCircuitPartition_of_four_label_card_le_eight",
        "Overfull.Multigraph.fourLabel_counterexample_degree_and_size",
        "Overfull.Multigraph.fourLabel_admissibleOn_sdiff_iff_cut_witnesses",
        "Overfull.Multigraph.exists_globally_admissible_localCoarsening",
        "Overfull.FourOdd.exists_fourJoining_decomposition_of_even_fibers_small_cut",
        "Overfull.FourOdd.exists_fourJoining_decomposition_of_even_fibers_bounded_cuts",
        "Overfull.FourOdd.exists_fourTwoOddJoining_decomposition_of_small_even_cut",
    ]
    if not set(endpoints) <= set(names):
        raise ValueError("A claimed endpoint is absent from the exact source inventory")
    record = {
        "schema_version": 1,
        "kind": "supporting_continuation",
        "baseline_commit": BASELINE,
        "baseline_tree": "9013f6d5c07676ba130d4bb794062d700bab6136",
        "baseline_publication_status": "both_remote_branches_independently_verified",
        "numbered_assertions_completed": 0,
        "main_theorem_verified": False,
        "scope": (
            "Constructs exact compatible circuit partitions for admissible Eulerian "
            "four-label multigraphs with any degree at most two, including arbitrary "
            "other even degrees. Combines this with the previous exact four-regular "
            "theorem to cover maximum degree at most four and at most eight actual "
            "copies. Proves that tight local coarsening preserves every global cut "
            "inequality, an elementary compatible-triangle bundle selector, exact "
            "slack-zero/slack-two deletion witnesses, and transports "
            "the constructed partitions to original-host even-fiber and two-odd-fiber "
            "joining matching families under explicit small-boundary hypotheses. "
            "All original copies remain distinct. General four-label existence, full "
            "Proposition 4.16, Theorem 4.17 and the main theorem remain incomplete. "
            "All 69 numbered assertion records and the 49 completed count are unchanged."
        ),
        "review": "docs/four-label-reduction-semantic-review.md",
        "proof_map": "docs/four-label-reduction-verification.md",
        "public_theorems": endpoints,
        "module_count": len(modules),
        "public_theorem_count": len(names),
        "modules": modules,
        "required_proof_declarations": names,
    }
    (ROOT / "docs/four-label-reduction-source.json").write_text(
        json.dumps(record, indent=2) + "\n")
    print(f"Mapped {len(modules)} sources and {len(names)} public proofs; full verification remains required.")


if __name__ == "__main__":
    main()
