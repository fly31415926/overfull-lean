#!/usr/bin/env python3
"""Build the formalized subset, audit its axioms, and record exact source hashes."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "verification"
MATHLIB_REVISION = "f897ebcf72cd16f89ab4577d0c826cd14afaafc7"
NUMBERED_ASSERTION_COUNT = 69
COMPLETED_NUMBERED_ASSERTION_COUNT = 39


def run(arguments: list[str], log_name: str) -> str:
    result = subprocess.run(
        arguments, cwd=ROOT, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
    )
    (OUTPUT / log_name).write_text(result.stdout, encoding="utf-8")
    print(result.stdout, end="")
    if result.returncode:
        raise SystemExit(result.returncode)
    return result.stdout


def main() -> None:
    OUTPUT.mkdir(exist_ok=True)
    # Any failed check must invalidate a report from an earlier source version.
    results_path = OUTPUT / "results.json"
    results_path.unlink(missing_ok=True)
    run([sys.executable, "scripts/setup_vizing.py"], "vizing-source.log")
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    mathlib = next(p for p in manifest["packages"] if p["name"] == "mathlib")
    if mathlib["rev"] != MATHLIB_REVISION:
        raise SystemExit("The mathlib revision differs from the reviewed project revision.")
    toolchain = (ROOT / "lean-toolchain").read_text().strip()
    if toolchain != "leanprover/lean4:v4.24.0":
        raise SystemExit("The Lean toolchain differs from the reviewed project toolchain.")

    # Included external proofs must match their recorded source adaptations.
    for provenance_name in ("bmatching-source.json", "circulation-source.json"):
        provenance = json.loads((ROOT / "docs" / provenance_name).read_text())
        included = ROOT / provenance["included_path"]
        digest = hashlib.sha256(included.read_bytes()).hexdigest()
        if digest != provenance["included_sha256"]:
            raise SystemExit(f"Included external source differs from its provenance: {included.name}")
        for key in ("license_file", "attribution_file"):
            if not (ROOT / provenance[key]).is_file():
                raise SystemExit(f"Missing external-source notice: {provenance[key]}")

    # Every first-party mathematical file must be included in the library build.
    modules = {"Overfull": ROOT / "Overfull.lean"}
    modules.update({
        ".".join(path.relative_to(ROOT).with_suffix("").parts): path
        for path in (ROOT / "Overfull").rglob("*.lean")
    })
    reachable: set[str] = set()
    pending = ["Overfull"]
    while pending:
        module = pending.pop()
        if module in reachable:
            continue
        reachable.add(module)
        imports = re.findall(r"^import\s+(\S+)", modules[module].read_text(), re.MULTILINE)
        pending.extend(name for name in imports if name in modules and name not in reachable)
    if missing := sorted(set(modules) - reachable):
        raise SystemExit("Mathematical modules excluded from the build: " + ", ".join(missing))

    version = run(["lake", "env", "lean", "--version"], "lean-version.log").strip()

    # Check the actual source checkouts as well as the declared revision pins.
    dependency_revisions = {}
    for dependency in manifest["packages"]:
        if dependency["type"] != "git":
            continue
        directory = ROOT / ".lake" / "packages" / dependency["name"]
        actual = subprocess.check_output(
            ["git", "-C", str(directory), "rev-parse", "HEAD"], text=True,
        ).strip()
        if actual != dependency["rev"]:
            raise SystemExit(f"Dependency source is at the wrong revision: {dependency['name']}")
        if subprocess.run(
            ["git", "-C", str(directory), "diff", "--quiet", "HEAD", "--"],
            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        ).returncode:
            raise SystemExit(f"Dependency has modified tracked sources: {dependency['name']}")
        dependency_revisions[dependency["name"]] = actual

    run(["lake", "build", "--wfail"], "build.log")
    audit = run(["lake", "env", "lean", "Audit.lean"], "axioms.log")
    match = re.search(r"OVERFULL_AXIOM_AUDIT_OK (\d+)", audit)
    declarations = [json.loads(line) for line in
                    re.findall(r"VERIFIED_DECLARATION ([^\n]+)", audit)]
    if not match or int(match.group(1)) != len(declarations):
        raise SystemExit("The axiom audit did not return a complete declaration list.")
    imported = set(re.findall(r"IMPORTED_PROJECT_MODULE (\S+)", audit))
    external_imports = set(re.findall(r"IMPORTED_EXTERNAL_MODULE (\S+)", audit))
    if imported != set(modules):
        raise SystemExit("The modules actually imported by Lean differ from the source inventory.")

    completed_results = {
        "sharpness_proposition": "Overfull.sharpness_family",
        "density_corollary": "Overfull.arbitrarily_large_class_two_graphs",
        "robust_range_reduction": "Overfull.robust_range_reduction",
        "bipartite_edge_deletion": "Overfull.IsBipartiteRobustExpander.after_edge_deletion_of_degree_bound",
        "bipartite_vertex_deletion": "Overfull.IsBipartiteRobustExpander.after_vertex_deletion",
        "cycle_absorber": "Overfull.Dense.CycleAbsorber.in_host",
        "perfect_matching_distribution": "Overfull.FractionalMatching.exists_perfectMatching_distribution",
        "vizing_bound": "Overfull.finite_vizing_bound",
        "vizing_for_arbitrary_finite_graphs": "Overfull.vizing_finite",
        "odd_cut_failure_bound": "Overfull.MatchingProbability.Distribution.odd_failure_probability",
        "even_set_toggle_failure_bound": "Overfull.MatchingProbability.Distribution.even_toggles_failure_probability",
        "family_cut_failure_bound": "Overfull.MatchingProbability.Distribution.family_failure_probability",
        "overfull_subgraph_equivalence": "Overfull.no_overfull_iff_not_exists_same_degree_overfull_subgraph",
        "hall_theorem": "Overfull.bipartite_hall_iff",
        "hall_deficiency": "Overfull.bipartite_hall_defect",
        "tutte_berge_formula": "Overfull.TutteBerge.tutte_berge_integer_maximum",
        "maximum_matching_existence": "Overfull.TutteBerge.exists_maximum_matching",
        "matching_polytope": "Overfull.Multigraph.matching_polytope",
        "multigraph_saturating_matching_distribution": "Overfull.Multigraph.exists_uniform_matching_distribution",
        "multigraph_perfect_matching_distribution": "Overfull.Multigraph.exists_perfectMatching_distribution",
        "bipartite_augmenting_path": "Overfull.bipartite_robust_augmenting_path",
        "multigraph_small_cut_lemma": "Overfull.SmallCuts.small_cut_lemma",
        "dense_signed_flow": "Overfull.dense_signed_flow",
        "dense_unequal_flow": "Overfull.dense_unequal_flow",
        "bipartite_range_reduction": "Overfull.bipartite_robust_range_reduction",
        "multigraph_odd_cut_failure_bound": "Overfull.MultigraphMatchingProbability.Distribution.odd_failure_probability",
        "multigraph_even_set_toggle_failure_bound": "Overfull.MultigraphMatchingProbability.Distribution.even_toggles_failure_probability",
        "multigraph_family_cut_failure_bound": "Overfull.MultigraphMatchingProbability.Distribution.family_failure_probability",
        "multigraph_residual_cut": "Overfull.MultigraphMatchingProbability.cutFailure_iff_actual_cut",
        "konig_multigraph_coloring": "Overfull.Multigraph.konig_edgeColoring_iff",
        "geometric_correction_series": "Overfull.GeometricCorrection.exists_exact_correction",
        "fractional_triangle_decomposition": "Overfull.dense_fractional_triangles",
        "balanced_multigraph_coloring": "Overfull.Multigraph.balanced_edgeColoring",
        "one_high_degree_coloring": "Overfull.Multigraph.edgeColoring_one_high",
        "sparse_vertex_deletion_coloring": "Overfull.Multigraph.edgeColoring_sparse_vertex_deletion_real",
        "minimal_noncolorable_edge_restriction": "Overfull.Multigraph.exists_kMinimal_subset",
        "two_edge_fan_elementarity": "Overfull.Multigraph.IsKMinimal.two_edge_fan_elementary",
        "critical_endpoint_degree_sum": "Overfull.Multigraph.IsKMinimal.endpoint_degree_sum",
        "fan_low_degree_set": "Overfull.Multigraph.IsKMinimal.fan_low_degree_set_real",
        "first_fan_core_exclusion": "Overfull.Multigraph.first_fan",
        "bounded_core_move": "Overfull.Multigraph.bounded_core_move_full",
        "balanced_robust_realization": "Overfull.balanced_robust_realization",
        "random_bipartite_reserve": "Overfull.RandomReserve.bipartite_random_reserve",
        "common_probability_chernoff": "Overfull.Bernoulli.chernoff",
        "unequal_probability_chernoff": "Overfull.IndependentBernoulli.chernoff_of_independent_indicators",
        "hypergeometric_chernoff": "Overfull.Hypergeometric.chernoff",
        "actual_packing_degree_accounting": "Overfull.BipartitePackingAccounting.working_degree_bounds",
        "disjoint_augmenting_paths": "Overfull.BipartitePathPacking.exists_disjoint_paths",
        "matching_completion_through_reserve": "Overfull.BipartiteMatchingCompletion.exists_completion_in_graph",
        "actual_packing_working_matching": "Overfull.BipartitePackingWorking.exists_large_matching_outside_reserve",
        "packing_reserve_recurrence": "Overfull.BipartitePackingBounds.reserve_recurrence_bound",
        "actual_adaptive_packing_round": "Overfull.BipartitePackingRound.exists_round",
        "adaptive_packing_strategy": "Overfull.BipartitePackingStrategy.exists_strategy",
        "adaptive_bipartite_packing": "Overfull.adaptive_bipartite_packing",
        "prescribed_bipartite_packing": "Overfull.bipartite_matching_packing",
        "bipartite_perfect_matching_packing": "Overfull.bipartite_perfect_matching_packing",
        "almost_regular_robust_reserve": "Overfull.RandomReserve.exists_almost_regular_reserve",
        "maximum_matching_preserving_coverage": "Overfull.MatchingExtension.exists_maximum_covering",
        "maximum_matching_covering_small_set": "Overfull.MatchingExtension.exists_maximum_covering_small_set",
        "bipartite_maximum_matching_deficiency": "Overfull.BipartitePackingDeficiency.maximum_matching_deficiency",
        "bipartite_packing_matching_selection": "Overfull.BipartitePackingStep.exists_packing_matching",
        "ordinary_random_reserve": "Overfull.OrdinaryRandomReserve.ordinary_random_reserve",
        "ordinary_reserve_degree_control": "Overfull.OrdinaryRandomReserve.exists_reserve_with_degree_control",
        "ordinary_almost_regular_reserve": "Overfull.OrdinaryRandomReserve.exists_almost_regular_reserve",
        "ordinary_edge_and_vertex_deletion": "Overfull.IsRobustExpander.after_edge_and_vertex_deletion",
        "ordinary_unused_reserve_robustness": "Overfull.OrdinaryPackingReserve.unused_reserve_robust",
        "ordinary_residual_graph_robustness": "Overfull.OrdinaryPackingReserve.residual_graph_robust",
        "ordinary_maximum_matching_deficiency": "Overfull.OrdinaryPackingDeficiency.maximum_matching_deficiency",
        "ordinary_deficiency_scale": "Overfull.OrdinaryPackingDeficiency.deficiency_scale",
        "ordinary_saturated_matching_selection": "Overfull.OrdinaryPackingDeficiency.exists_matching_covering_saturated_load",
        "ordinary_actual_working_matching": "Overfull.OrdinaryPackingWorking.exists_large_matching_outside_reserve",
        "prescribed_pair_cut_sampling": "Overfull.PairedCut.exists_prescribed_pair_cut",
        "paired_cut_total_degree_loss": "Overfull.PairedCut.robust_after_total_degree_loss",
        "paired_cut_robust_quotient": "Overfull.PairedCut.robust_quotient",
        "paired_cut_regular_clusters": "Overfull.PairedCut.exists_robust_regular_clusters",
        "paired_cut_robust_lifting": "Overfull.PairedCut.balanced_cluster_cut_expands",
        "paired_cut_from_clusters": "Overfull.PairedCut.exists_prescribed_pair_cut_from_clusters",
        "prescribed_pair_robust_cut": "Overfull.PairedCut.paired_cut",
        "matching_pairing_even_uncovered": "Overfull.MatchingPairing.exists_pairing_of_even_uncovered",
        "matching_pairing": "Overfull.MatchingPairing.exists_pairing",
        "ordinary_initial_reserve": "Overfull.OrdinaryPackingInitial.exists_initial_reserve",
        "ordinary_reserve_step_bound": "Overfull.OrdinaryPackingBounds.reserve_step_bound",
        "ordinary_reserve_recurrence_bound": "Overfull.OrdinaryPackingBounds.reserve_recurrence_bound",
        "ordinary_deficiency_total_bound": "Overfull.OrdinaryPackingBounds.deficiency_with_total_bound",
        "ordinary_completion_budget": "Overfull.OrdinaryPackingBounds.completion_budget",
        "ordinary_matching_completion": "Overfull.OrdinaryMatchingCompletion.exists_completion_of_balanced_cut",
        "ordinary_matching_completion_outside_set": "Overfull.OrdinaryMatchingCompletion.exists_completion_outside_set",
        "matching_preserving_robust_cut": "Overfull.PairedCut.exists_matching_cut",
        "ordinary_packing_reserve_parameters": "Overfull.OrdinaryPackingParameters.reserve_parameters",
        "ordinary_packing_error_parameter": "Overfull.OrdinaryPackingParameters.exists_error_parameter",
        "actual_ordinary_packing_round": "Overfull.OrdinaryPackingRound.exists_round",
        "ordinary_packing_strategy": "Overfull.OrdinaryPackingStrategy.exists_rule",
        "adaptive_ordinary_packing": "Overfull.adaptive_ordinary_packing",
        "balanced_core_extraction": "Overfull.BalancedCore.balanced_core_of_bipartite_outcome",
        "matching_repair_released_degree": "Overfull.MatchingRepairAccounting.released_degree_le",
        "matching_repair_released_union_degree": "Overfull.MatchingRepairAccounting.released_union_degree_le",
        "matching_repair_internal_endpoint_bound": "Overfull.MatchingRepairLoad.actual_load_le_internal_add_endpoints",
        "matching_repair_internal_capacity": "Overfull.MatchingRepairLoad.internalLoad_update_insert_matching",
        "matching_repair_total_use": "Overfull.MatchingRepairLoad.total_actual_load_update_insert",
        "matching_repair_saturation_bound": "Overfull.MatchingRepairLoad.saturated_internal_count_le_actual",
        "matching_repair_error_parameter": "Overfull.MatchingRepairParameters.exists_error",
        "matching_repair_order_threshold": "Overfull.MatchingRepairParameters.exists_order_threshold",
        "matching_repair_actual_completion": "Overfull.MatchingRepairStep.exists_protected_completion",
        "matching_repair_fresh_disjointness": "Overfull.MatchingRepairFamily.fresh_disjoint_union",
        "matching_repair_family_update": "Overfull.MatchingRepairFamily.update_pairwise_disjoint",
        "matching_repair_actual_load_bound": "Overfull.MatchingRepair.Invariant.load_le",
        "matching_repair_internal_total_bound": "Overfull.MatchingRepair.Invariant.internal_total_le",
        "matching_repair_actual_reserve_union": "Overfull.MatchingRepair.reserve_union_degree",
        "reserve_repair": "Overfull.MatchingRepair.reserve_repair",
        "balanced_auxiliary_neighbors": "Overfull.AuxiliaryCompletion.exists_auxiliary_neighbors",
        "balanced_auxiliary_incidence_graph": "Overfull.AuxiliaryCompletion.exists_balanced_incidence_graph",
        "auxiliary_singleton_incidence_bound": "Overfull.AuxiliaryCompletion.twice_incidence_card_le_deficiency_sum_add_one",
        "auxiliary_core_cut_bound": "Overfull.AuxiliaryCompletion.core_cut_gt",
        "auxiliary_original_edge_copies": "Overfull.AuxiliaryCompletion.internal_original_edges",
        "auxiliary_added_edge_simplicity": "Overfull.AuxiliaryCompletion.added_edge_simple",
        "auxiliary_odd_set_preservation": "Overfull.AuxiliaryCompletion.no_overfull",
        "auxiliary_robust_core_construction": "Overfull.AuxiliaryCompletion.exists_auxiliary_core",
        "robust_auxiliary_completion": "Overfull.robust_auxiliary_completion",
        "dense_coloring_triangle_encoding": "Overfull.dense_encoding",
        "finite_balanced_remainders": "Overfull.Dense.FiniteAbsorber.remainderCycles_exists",
        "finite_remainder_absorber": "Overfull.Dense.FiniteAbsorber.finite_absorber_subgraph",
        "six_pair_balanced_reserve": "Overfull.dense_reserve",
        "dense_balance_repair_routing_bounds": "Overfull.Dense.BalanceRepairBounds.routing_bounds",
        "dense_balance_repair_thresholds": "Overfull.Dense.BalanceRepairBounds.thresholds",
        "dense_balance_repair_actual_paths": "Overfull.Dense.BalanceRepair.exists_routing_path",
        "dense_balance_repair_graph_difference": "Overfull.Dense.BalanceRepair.eraseArcs_eq_sdiff",
        "dense_balance_repair_actual_degree": "Overfull.Dense.BalanceRepair.selectArcs_degree",
        "dense_balance_repair_local_balance": "Overfull.Dense.BalanceRepair.locallyBalanced_iff",
        "dense_balance_repair_residual_routing": "Overfull.Dense.BalanceRepair.routingConditions_after_deletion",
        "dense_balance_repair_cancellation_degree": "Overfull.Dense.BalanceRepair.CancellationState.deleted_degree_le",
        "dense_balance_repair_saturated_count": "Overfull.Dense.BalanceRepair.CancellationState.saturated_card_bound",
        "dense_balance_repair_finite_cancellation": "Overfull.Dense.BalanceRepair.exists_balanced_deletion",
        "dense_balance_repair_positive_mass": "Overfull.Dense.BalanceRepair.positive_balance_sum_le",
        "dense_balance_repair": "Overfull.dense_balance_repair",
        "replacement_uniform_parameters": "Overfull.Replacement.exists_replacement_parameters",
        "replacement_degree_identity": "Overfull.Replacement.graph_degree_identity",
        "replacement_induced_edge_identity": "Overfull.Replacement.graph_internal_count_identity",
        "replacement_actual_core_cut": "Overfull.Replacement.cut_core_le",
        "replacement_small_shore_comparison": "Overfull.Replacement.regular_small_shore_comparison",
        "replacement_overfull_preservation": "Overfull.Replacement.no_overfull_of_core_cuts",
        "replacement_degree_loss": "Overfull.Replacement.core_degree_loss",
        "replacement_core_robustness": "Overfull.Replacement.core_robust",
        "robust_core_replacement": "Overfull.robust_core_replacement",
        "forbidden_set_subfamily": "Overfull.ForbiddenSetWitness.exists_subfamily",
        "forbidden_set_vertex_witness": "Overfull.ForbiddenSetWitness.exists_vertex_witness",
        "six_family_connectivity_witness": "Overfull.ForbiddenSetWitness.exists_six_family_witness",
        "prescribed_matching_short_paths": "Overfull.PrescribedMatching.short_path_avoiding",
        "prescribed_matching_core_witness": "Overfull.PrescribedMatching.exists_core_connection_witness",
        "prescribed_matching_component_bound": "Overfull.PrescribedMatching.component_card_le_cores_add_exceptional",
        "prescribed_matching_core_attachment": "Overfull.PrescribedMatching.core_attachment_after_deletion",
        "prescribed_matching_component_survival": "Overfull.PrescribedMatching.component_has_survivor",
        "prescribed_matching_actual_connectivity": "Overfull.PrescribedMatching.reachable_reflection_of_witness",
        "prescribed_matching_component_parity": "Overfull.PrescribedMatching.matching_component_inter_even",
        "prescribed_matching_odd_component_transfer": "Overfull.PrescribedMatching.oddComponents_after_remaining_deletion",
        "prescribed_matching_remaining_odd_bound": "Overfull.PrescribedMatching.remaining_odd_bound",
        "prescribed_matching_tutte_completion": "Overfull.PrescribedMatching.complete_of_induced_odd_bounds",
        "prescribed_matching_discard_bound": "Overfull.PrescribedMatching.avoidVertices_omitted_edges_le",
        "prescribed_matching_covered_core_bound": "Overfull.PrescribedMatching.matching_covered_outside_le",
        "prescribed_matching_actual_selection": "Overfull.PrescribedMatching.select_prescribed_matching",
        "prescribed_matching_final_edge_difference": "Overfull.PrescribedMatching.omitted_edges_le_of_extension",
        "prescribed_matching_witness_completion": "Overfull.PrescribedMatching.complete_avoiding_witness",
        "prescribed_exceptional_core_matching": "Overfull.prescribed_exceptional_core_matching",
        "compression_four_label_forest": "Overfull.Compression.four_label_parity_forest",
        "compression_actual_parity_selection": "Overfull.Compression.exists_parity_subset",
        "compression_endpoint_parity_forest": "Overfull.Compression.exists_endpoint_parity_forest",
        "compression_selected_matching": "Overfull.Compression.exists_selected_matching",
        "compression_selected_vertex_count": "Overfull.Compression.selectedMatching_verts_card",
        "compression_core_cut_parity": "Overfull.Compression.selected_core_cut_parity",
        "compressed_matching": "Overfull.Compression.exists_compressed_matching",
        "force_core_perfect_matching_threshold": "Overfull.ForceMatching.exists_ordinary_perfect_matching_threshold",
        "force_core_completion_parameters": "Overfull.ForceMatching.exists_core_completion_parameters",
        "compressed_matching_completion": "Overfull.ForceMatching.exists_compressed_completion_parameters",
        "force_residual_core_degree": "Overfull.ForceMatching.residualCore_degree_loss",
        "force_residual_core_robustness": "Overfull.ForceMatching.residualCore_robust",
        "force_whole_union_card": "Overfull.ForceMatching.wholeUnions_card_le",
        "force_star_probability": "Overfull.ForceMatching.Distribution.star_hit_probability",
        "safe_star_sampling": "Overfull.ForceMatching.exists_star_matching",
        "compressed_cut_comparison": "Overfull.ForceMatching.completed_cut_comparison",
        "force_toggle_cut_comparison": "Overfull.ForceMatching.toggle_cut_le_of_cut_subset",
        "force_family_safety": "Overfull.ForceMatching.family_safe_after_completion",
        "force_whole_union_classification": "Overfull.ForceMatching.classified_of_minority",
        "force_residual_no_overfull": "Overfull.ForceMatching.residual_no_overfull",
        "force_star_retention": "Overfull.ForceMatching.starHit_of_exceptional_retention",
        "force_uniform_parameters": "Overfull.ForceMatching.uniform_order_threshold",
        "safe_compressed_completion": "Overfull.ForceMatching.exists_safe_completion_parameters",
        "force_exceptional_star": "Overfull.force_exceptional_star",
        "safe_boundary_adjacency": "Overfull.SafePrescription.pair_mem_boundaryEdges",
        "safe_boundary_edge_count": "Overfull.SafePrescription.boundaryEdges_card_bound",
        "safe_actual_boundary_submatching": "Overfull.SafePrescription.exists_boundary_submatching",
        "safe_prescription_finite_sampling": "Overfull.SafePrescription.exists_bounded_matching_for_family",
        "safe_prescription_sampling_constants": "Overfull.SafePrescription.exists_bounded_matching",
        "safe_prescription_sampled_boundary": "Overfull.SafePrescription.exists_sampled_boundary",
        "safe_cut_incidence_degree": "Overfull.SafePrescription.cutGraph_degree",
        "safe_core_boundary_degree": "Overfull.SafePrescription.cut_incident_core_bound",
        "safe_exceptional_boundary_degree": "Overfull.SafePrescription.cut_incident_cluster_bound",
        "safe_cluster_neighbor_count": "Overfull.SafePrescription.same_cluster_neighbors_lower",
        "safe_clique_auxiliary_matching": "Overfull.SafePrescription.cliqueAux_has_perfect_matching",
        "safe_retained_original_edges": "Overfull.SafePrescription.cliqueAux_original_edge",
        "safe_retained_core_parity_transport": "Overfull.SafePrescription.uncovered_embed_union_card",
        "safe_retained_partial_matching": "Overfull.SafePrescription.exists_retained_partial_matching",
        "safe_family_cluster_membership": "Overfull.SafePrescription.family_same_label",
        "safe_family_whole_cores": "Overfull.SafePrescription.family_whole_cores",
        "safe_cluster_union_approximation": "Overfull.SafePrescription.cluster_union_approximation",
        "safe_simultaneous_toggle_identity": "Overfull.SafePrescription.cut_symmDiff_identity",
        "safe_simultaneous_toggle_bound": "Overfull.SafePrescription.cut_symmDiff_lower_bound",
        "safe_small_cut_classification": "Overfull.SafePrescription.classified_small_cut",
        "safe_robust_small_cut_classification": "Overfull.SafePrescription.classified_robust_small_cut",
        "safe_exterior_matching_count": "Overfull.SafePrescription.exteriorEdges_card_le",
        "safe_matching_cut_exterior_bound": "Overfull.SafePrescription.matching_cut_le_exterior_add_one",
        "safe_original_cut_from_residual": "Overfull.SafePrescription.original_cut_lt_of_overfull",
        "safe_residual_no_overfull": "Overfull.SafePrescription.residual_no_overfull_of_small_cut_classification",
        "safe_prescription_uniform_parameters": "Overfull.SafePrescription.exists_prescription_parameters",
        "safe_prescription": "Overfull.safe_prescription",
        "ordinary_finite_prefix_rule": "Overfull.OrdinaryPackingStrategy.exists_prefix_rule",
        "adaptive_ordinary_packing_prefix": "Overfull.adaptive_ordinary_packing_prefix",
        "foreign_minority_card_bound": "Overfull.ForeignRefinement.minorityVertices_card_le",
        "foreign_minority_core_subset": "Overfull.ForeignRefinement.minorityVertices_subset",
        "foreign_surviving_core_membership": "Overfull.ForeignRefinement.surviving_core_membership",
        "foreign_minority_deletion": "Overfull.ForeignRefinement.minority_shore_deletion",
        "selected_host_matching_adapter": "Overfull.ForeignColoring.selectedMatching_isMatching_of_edge_copies",
        "selected_host_matching_disjointness": "Overfull.ForeignColoring.selectedMatching_spanning_disjoint",
        "host_color_class_membership": "Overfull.ForeignColoring.mem_hostColorClass",
        "host_color_class_subset": "Overfull.ForeignColoring.hostColorClass_subset",
        "host_color_class_matching": "Overfull.ForeignColoring.hostColorClass_isMatching",
        "host_color_class_disjointness": "Overfull.ForeignColoring.hostColorClass_pairwise_disjoint",
        "host_color_class_union": "Overfull.ForeignColoring.hostColorClass_union",
        "selected_matching_graph_union": "Overfull.ForeignColoring.selectedMatching_edgeUnion",
        "actual_host_color_classes": "Overfull.ForeignColoring.exists_color_classes",
        "three_quarter_host_color_classes": "Overfull.ForeignColoring.exists_three_quarter_color_classes",
    }
    audited_names = {item["name"] for item in declarations}
    if missing := sorted(set(completed_results.values()) - audited_names):
        raise SystemExit("Completed results absent from the axiom audit: " + ", ".join(missing))

    coverage = json.loads((ROOT / "docs/coverage.json").read_text())
    if (coverage["numbered_assertion_count"] != NUMBERED_ASSERTION_COUNT
            or len(coverage["numbered_assertions"]) != NUMBERED_ASSERTION_COUNT):
        raise SystemExit("The manuscript assertion inventory is inconsistent.")
    for component in coverage["checked_component_catalog"]:
        if missing := sorted(set(component["lean_declarations"]) - audited_names):
            raise SystemExit(
                f"A checked component lacks audited declarations ({component['id']}): "
                + ", ".join(missing)
            )
    completed_assertions = [a for a in coverage["numbered_assertions"]
                            if a["full_assertion_verified"]]
    if len(completed_assertions) != coverage["fully_verified_numbered_assertion_count"]:
        raise SystemExit("The coverage assertion count is inconsistent.")
    if len(completed_assertions) != COMPLETED_NUMBERED_ASSERTION_COUNT:
        raise SystemExit("The completed assertion count differs from the reviewed scope.")
    manuscript_source = json.loads((ROOT / "docs/manuscript-source.json").read_text())
    if manuscript_source["fully_verified_numbered_assertions"] != len(completed_assertions):
        raise SystemExit("The manuscript source record has an inconsistent completed count.")
    for assertion in completed_assertions:
        names = assertion.get("lean_theorems", [])
        if not names or not set(names) <= audited_names:
            raise SystemExit(f"A completed assertion lacks audited proof declarations: {assertion['number']}")
    if coverage["main_theorem_verified"]:
        raise SystemExit("The main theorem is not proved by this version of the development.")

    sources = [ROOT / "Overfull.lean", ROOT / "Audit.lean"]
    sources += sorted((ROOT / "Overfull").rglob("*.lean"))
    results = {
        "status": "partial_formalization",
        "main_theorem_verified": False,
        "full_sharpness_proposition_verified": True,
        "density_corollary_verified": True,
        "completed_results": completed_results,
        "lean_build_passed": True,
        "axiom_audit_passed": True,
        "lean_version": version,
        "toolchain": toolchain,
        "mathlib_revision": MATHLIB_REVISION,
        "dependency_source_revisions": dependency_revisions,
        "vizing_source": json.loads((ROOT / "docs/vizing-source.json").read_text()),
        "matching_polytope_source": json.loads((ROOT / "docs/bmatching-source.json").read_text()),
        "circulation_source": json.loads((ROOT / "docs/circulation-source.json").read_text()),
        "allowed_logical_axioms": ["propext", "Classical.choice", "Quot.sound"],
        "verified_declaration_count": len(declarations),
        "declaration_count_includes_generated_support_lemmas": True,
        "verified_declarations": sorted(declarations, key=lambda item: item["name"]),
        "imported_project_modules": sorted(imported),
        "audited_external_modules": sorted(external_imports),
        "fully_verified_numbered_assertion_count": len(completed_assertions),
        "fully_verified_numbered_assertions": [a["number"] for a in completed_assertions],
        "source_sha256": {
            str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in sources
        },
        "verification_input_sha256": {
            str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in sorted([
                ROOT / "lean-toolchain", ROOT / "lakefile.toml", ROOT / "lake-manifest.json",
                ROOT / "README.md", ROOT / ".github/workflows/lean.yml",
                *(ROOT / "scripts").glob("*.py"), *(ROOT / "docs").glob("*.json"),
                *(ROOT / "docs").glob("*.md"), *(ROOT / "patches").glob("*.patch"),
                ROOT / "THIRD_PARTY_NOTICES.txt", ROOT / "CIRCULATION_NOTICE.txt",
                ROOT / "LICENSE_BMATCHING.txt",
            ])
        },
        "scope": (
            "The named supporting results and the full sharpness results are proved "
            "by audited declarations. Vizing's bound is proved. The final implication "
            "to the main theorem still assumes LargeCriticalExclusion, which is not "
            "proved. A successful build is not a verification of the main theorem "
            "or the full manuscript."
        ),
    }
    results_path.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print(f"Checked {len(declarations)} project declarations; full manuscript status: unverified.")


if __name__ == "__main__":
    main()
