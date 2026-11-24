# Four-label reduction: source and verification map

The complete machine-readable source inventory is
`docs/four-label-reduction-source.json`. It records every new module's exact
SHA-256, each public theorem name and source line, and the reviewed endpoints.
The full verifier produces
`verification/four-label-reduction-declarations.json`, including private and
generated proof declarations, owning modules, source hashes and transitive
axiom sets. The latter file is generated only by a successful actual audit.

| Source | Proof responsibility |
| --- | --- |
| `FourDegreeTwoSupport.lean` | Exact selected-support restriction, vertex embedding, three-active-label and degree-zero existence |
| `FourDegreeTwoParallel.lean` | Shore movement, compatible degree-two parallel pair, safe deletion and restoration |
| `FourDegreeTwoSuppression.lean` | Changed-copy graph and incidence class, both exact cut identities, admissibility and degree transfer |
| `FourDegreeTwoReassembly.lean` | Congruence on selected copies and disjoint union of exact circuit partitions |
| `FourDegreeTwoLift.lean` | Compatibility and even degrees of the expanded part, ordinary decomposition and exact restoration |
| `FourDegreeTwo.lean` | Constructed degree-two reduction and complete low-degree four-label endpoint |
| `FourCutCriterion.lean` | Exact slack-zero/slack-two witness criterion and pair/triangle specialization |
| `FourGlobalCoarsening.lean` | Tight local coarsening preserves all global half-cut bounds and original compatibility |
| `FourTriangleSelection.lean` | Compatible choice from three actual-copy bundles or a common monochromatic corner |
| `FourBounded.lean` | Maximum degree four, eight-copy bound, necessary counterexample range and arbitrary finite labels |
| `FourBoundedJoining.lean` | Original-host all-even and two-odd matching-piece constructions under explicit small-boundary assumptions |

Every source path in the table is under `Overfull/CompatibleCircuits/`.

## Principal endpoints

- `Overfull.Multigraph.exists_compatibleCircuitPartition_of_four_label_small_degree`
- `Overfull.Multigraph.exists_compatibleCircuitPartition_of_four_label_degree_le_four`
- `Overfull.Multigraph.exists_compatibleCircuitPartition_of_four_label_card_le_eight`
- `Overfull.Multigraph.fourLabel_counterexample_degree_and_size`
- `Overfull.Multigraph.fourLabel_admissibleOn_sdiff_iff_cut_witnesses`
- `Overfull.Multigraph.exists_globally_admissible_localCoarsening`
- `Overfull.FourOdd.exists_fourJoining_decomposition_of_even_fibers_small_cut`
- `Overfull.FourOdd.exists_fourJoining_decomposition_of_even_fibers_bounded_cuts`
- `Overfull.FourOdd.exists_fourTwoOddJoining_decomposition_of_small_even_cut`

The finite-copy restriction and all boundary-size assumptions are visible in
the theorem statements. None of these endpoints closes a new numbered
manuscript assertion. Coverage stays **49/69**, and the main theorem remains
unverified.

## Complete gate and preservation

The baseline is public commit
`e2e5455b11d5b1691d0a974fd3c5f72e989ec5b8`, tree
`9013f6d5c07676ba130d4bb794062d700bab6136`; both branches were independently
read back before work began. The new run is
`verification/runs/20261124T120200Z/`.

The complete gate freezes mathematical sources, dependencies, documentation,
manifests, verifier, and verification controls before running the actual strict
build and unchanged `Audit.lean`. It requires unchanged frozen inputs and only
the permitted axioms `propext`, `Classical.choice`, and `Quot.sound`.

Supplementary preservation compares all previous proof declarations, owners,
axiom sets, completed-result mappings, source/declaration maps, and all 69
assertion records with the baseline. Previous nonroot mathematical sources
are byte-identical. The new root imports and verifier registration are exact
reviewed additive changes.

Setup failures, interrupted preliminary builds, and all completed focused
attempts are retained with actual commands, captured output, source snapshots,
hashes, and observed status. An interrupted tool exit is not represented as an
observed Lean child exit when the latter was not captured. Publication has
separate commit, exact-tree and both-branch readbacks; a local build does not
constitute a publication receipt.
