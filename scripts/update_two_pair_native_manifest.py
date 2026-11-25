#!/usr/bin/env python3
"""Map the native two-pair continuation without changing numbered coverage."""
import hashlib
import json
from pathlib import Path
from update_global_factorization_manifest import source_proofs

ROOT = Path(__file__).resolve().parents[1]
BASELINE = "5679471018d5d087d942c592c72fca3d24e7ea32"
TREE = "918663f3827a27a29312835f7b2218d850326a0d"
PATHS = [
    "Overfull/AssignedParts/TwoPairs.lean",
    "Overfull/AssignedParts/PartnerSignatures.lean",
    "Overfull/AssignedParts/PartnerLabels.lean",
    "Overfull/AssignedParts/TwoPairPalette.lean",
    "Overfull/ResidualPalette/FourProtectedGrouping.lean",
    "Overfull/ResidualPalette/FourTwoOddGrouping.lean",
    "Overfull/ExceptionalPalette/TwoPairs.lean",
    "Overfull/NativeReserve/PartnerPacking.lean",
    "Overfull/NativeReserve/PartnerResidual.lean",
    "Overfull/NativeAssembly/TwoPairBoundary.lean",
    "Overfull/NativeAssembly/TwoPairs.lean",
    "Overfull/NativeAssembly/TwoPairReserve.lean",
    "Overfull/NativeTerminal/TwoPairs.lean",
]


def main():
    modules = []
    for relative in PATHS:
        path = ROOT / relative
        proofs = source_proofs(path)
        modules.append({
            "module": ".".join(path.relative_to(ROOT).with_suffix("").parts),
            "path": relative,
            "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "public_theorem_count": len(proofs),
            "public_proof_declarations": proofs,
        })
    names = sorted(p["name"] for m in modules for p in m["public_proof_declarations"])
    public = [
        "Overfull.AssignedParts.exists_two_pair_assigned_labels",
        "Overfull.AssignedParts.exists_two_pair_assigned_label_transfer",
        "Overfull.AssignedParts.exists_twoPair_joiningPalette_in_host",
        "Overfull.FourOdd.FourTwoOddJoiningDecomposition.exists_protected_palette",
        "Overfull.NativeReserve.exists_linear_partner_boundary_reserve",
        "Overfull.NativeReserve.PartnerBoundaryPacking.exists_residual_pair_injection",
        "Overfull.NativeReserve.JoiningPalette.exists_two_pairFiber_completion",
        "Overfull.NativeAssembly.exists_reserved_two_pair_completion",
        "Overfull.NativeAssembly.exists_partner_two_pair_completion_of_no_unpaired",
        "Overfull.NativeTerminal.exists_uniform_two_shore_two_pair_factorization",
    ]
    if len(names) != len(set(names)) or not set(public) <= set(names):
        raise ValueError("Missing endpoint or duplicate public declaration")
    coverage = json.loads((ROOT / "docs/coverage.json").read_text())
    source_assertions = [{k: a[k] for k in
                          ("number", "labels", "statement_sha256", "full_assertion_verified")}
                         for a in coverage["numbered_assertions"]
                         if a["number"] in {"4.4", "4.5"}]
    if len(source_assertions) != 2 or any(a["full_assertion_verified"] for a in source_assertions):
        raise ValueError("The supporting results do not close the pinned numbered assertions")
    source = {
        "schema_version": 1,
        "kind": "supporting_continuation",
        "baseline_commit": BASELINE,
        "baseline_tree": TREE,
        "numbered_assertions_completed": 0,
        "main_theorem_verified": False,
        "public_theorems": public,
        "source_assertions": source_assertions,
        "scope": (
            "Construct four actual assigned fibers for two exceptional matching pairs, a finite "
            "partner code preserving both pair identities and both core assignments, and a linear "
            "disjoint reserve of actual compressed boundaries for every exceptional set of size at most five. "
            "Transport actual pair copies into reserve-avoiding residuals. Construct four-label joining "
            "palettes from the completed circuit decomposition, with protected-primary grouping, and "
            "simultaneously complete two internal pair pools relative to one original joining palette, "
            "allowing both prescribed copies to share a protected color. Native assembly preserves exact "
            "whole boundaries under its explicit joining-trace and pair-support hypotheses. Extend "
            "terminal factorization to two separately closed pair components using the original edge copies. "
            "The native safe residual, protected traces and degree budgets, two-pair-plus-one-star assembly, "
            "and the zero-/one-pair multi-star branches remain unfinished. All 69 pinned numbered "
            "records, including their 51 complete statuses, remain unchanged; the main theorem is unverified."
        ),
        "review": "docs/two-pair-native-semantic-review.md",
        "proof_map": "docs/two-pair-native-verification.md",
        "module_count": len(modules),
        "public_theorem_count": len(names),
        "modules": modules,
        "required_proof_declarations": names,
    }
    (ROOT / "docs/two-pair-native-source.json").write_text(json.dumps(source, indent=2) + "\n")
    print(f"Mapped {len(modules)} modules and {len(names)} public proofs; no numbered promotion.")


if __name__ == "__main__":
    main()
