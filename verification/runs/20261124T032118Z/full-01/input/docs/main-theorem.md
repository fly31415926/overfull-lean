# Main theorem: statement and remaining proof

**The main theorem has not been verified in Lean.** The project contains its
exact statement, checked graph reductions, and several of its supporting
results. It contains no unconditional theorem proving `Overfull.MainTheorem`.

## The formal target

For every real `ε > 0`, there is an order threshold `n₀` such that every finite
simple graph `G` on `Fin n`, where `n ≥ n₀` and

```text
(1/4 + ε) * n ≤ G.maxDegree,
```

has a proper edge coloring with `G.maxDegree` colors if and only if no vertex
set `X` has more than

```text
G.maxDegree * floor(X.card / 2)
```

internal edges. This is the proposition `Overfull.MainTheorem` in
[`Specifications.lean`](../Overfull/Specifications.lean). Its order threshold
is allowed to depend on `ε`; `ε` does not depend on the graph order.

The coloring assigns colors to mathlib's unordered graph edges. Properness
requires two edges with a common endpoint and the same color to be equal.
Internal edges are counted from those same graph edges.

[`OverfullSubgraphs.lean`](../Overfull/OverfullSubgraphs.lean) proves that this
vertex-set formulation is equivalent to the manuscript's overfull-subgraph
formulation. In particular, an overfull set at `G.maxDegree` induces an
intrinsically overfull graph whose maximum degree equals `G.maxDegree`.
The equality of maximum degrees is proved from the degree sum and simplicity.
The converse covers every mathlib subgraph, including noninduced subgraphs.

## The checked reduction

[`MainReduction.lean`](../Overfull/MainReduction.lean) proves that a finite
graph failing a specified coloring bound contains an edge-minimal graph
failing that bound. Restricting to its nonisolated vertices preserves the
coloring obstruction and the no-overfull property. The resulting graph is
transported by a graph isomorphism to a vertex type `Fin m`.

Vizing's upper bound supplies equality of the two maximum degrees. The
reduction proves both order bounds `m ≤ n` and `Δ + 1 ≤ m`. It then transfers
the density margin to the smaller graph and proves that the graph remains
above the required structural threshold. The choices are exactly
`θ = min ε (1/12)` and `n₀ = 4 n₁`.

The remaining structural proposition is named
`Overfull.LargeCriticalExclusion`. It says that for each `0 < θ ≤ 1/12`,
sufficiently large graphs cannot simultaneously have all four properties:

1. Edge-minimal failure of a coloring with their maximum degree many colors.
2. No isolated vertices.
3. Maximum degree at least `(1/4 + θ)` times their order.
4. No overfull vertex set at that maximum degree.

This proposition is a definition, not an axiom or an established theorem.
The manuscript's robust partition and its five case exclusions must prove it.
An implication with `LargeCriticalExclusion` as a hypothesis does not verify
the main theorem.

Vizing's bound is now supplied by its proved adapter in
[`Vizing/Theorem.lean`](../Overfull/Vizing/Theorem.lean). Consequently the
checked final implication is

```lean
Overfull.mainTheorem_of_criticalExclusion
    (h : Overfull.LargeCriticalExclusion) : Overfull.MainTheorem
```

The hypothesis `h` remains unproved.

## Supporting results proved in this development

The following results are separate from that unproved structural exclusion.

| Result | Checked declaration |
| --- | --- |
| Both concentration cases in finite-law form, with unequal indicator probabilities and actual hypergeometric sampling | `Overfull.IndependentBernoulli.chernoff_of_independent_indicators` and `Overfull.Hypergeometric.chernoff` |
| Hall's theorem and its deficiency form for actual bipartite matching subgraphs | `Overfull.bipartite_hall_iff` and `Overfull.bipartite_hall_defect` |
| König's edge-coloring theorem for finite loopless bipartite multigraphs | `Overfull.Multigraph.konig_edgeColoring_iff` |
| Both fan consequences for k-minimal loopless multigraphs | `Overfull.Multigraph.IsKMinimal.endpoint_degree_sum` and `fan_low_degree_set_real` |
| The first-fan exclusion of core edges and the resulting exceptional degree bound | `Overfull.Multigraph.first_fan` |
| Coloring after moving a bounded vertex set out of a simple core, including the empty-core case | `Overfull.Multigraph.bounded_core_move_full` |
| The complete matching polytope for finite loopless multigraphs, including parallel edge copies | `Overfull.Multigraph.matching_polytope` |
| Balanced multigraph color classes with all exceptional vertices covered, spread at most two, and both footprint bounds | `Overfull.Multigraph.balanced_edgeColoring` |
| Coloring with one high-degree vertex and coloring after a sparse vertex deletion | `Overfull.Multigraph.edgeColoring_one_high` and `edgeColoring_sparse_vertex_deletion_real` |
| A linear minimum degree allows the tested robust-expansion range to shrink | `Overfull.robust_range_reduction` |
| Robust expansion survives the stated spanning edge deletions | `Overfull.IsRobustExpander.after_edge_deletion` |
| Both deletion assertions for bipartite robust expanders | `Overfull.IsBipartiteRobustExpander.after_edge_deletion_of_degree_bound` and `after_vertex_deletion` |
| The independent random reserve lemma, with a stronger failure-probability estimate | `Overfull.RandomReserve.bipartite_random_reserve` |
| One actual reserve with simultaneous robust expansion and all almost-regular degree bounds | `Overfull.RandomReserve.exists_almost_regular_reserve` |
| An actual maximum matching preserving a prescribed matching’s covered vertices, including the greedy small-set coverage input | `Overfull.MatchingExtension.exists_maximum_covering` and `exists_maximum_covering_small_set` |
| An actual Hall witness and the matching-deficiency bound `(2am+t)/d` from ordinary degree and total-load bounds | `Overfull.BipartitePackingDeficiency.maximum_matching_deficiency` |
| A maximum matching covering the saturated vertices, with equal uncovered-side counts and the exact bound `(16+2c₀)εm/γ` | `Overfull.BipartitePackingStep.exists_packing_matching` |
| Full adaptive bipartite packing, with one fixed rule and robust expansion after every prefix | `Overfull.adaptive_bipartite_packing` |
| Direct prescribed-set and perfect-matching packing statements, with robust expansion after any subfamily is removed | `Overfull.bipartite_matching_packing` and `Overfull.bipartite_perfect_matching_packing` |
| A balanced bipartite robust expander with the stated minimum crossing degrees has a perfect matching | `Overfull.bipartite_robust_perfect_matching` |
| The Tutte–Berge formula, with an attained maximum of the actual integer deficiencies and an actual maximum matching | `Overfull.TutteBerge.tutte_berge_integer_maximum` and `exists_maximum_matching` |
| A short alternating path avoids the specified set, even when the matching is not contained in the robust graph | `Overfull.bipartite_robust_augmenting_path` |
| A small cut differs from a union of whole robust cores by at most one core vertex | `Overfull.SmallCuts.small_cut_lemma` |
| A prescribed almost constant degree sequence of even sum has a simple robust realization, with uniform constants | `Overfull.balanced_robust_realization` |
| An almost regular loopless multigraph has the prescribed even regular completion, with a robust auxiliary core and no new overfull set | `Overfull.robust_auxiliary_completion` |
| An ordinary sampled reserve has robust expansion and simultaneous almost-regular degree control | `Overfull.OrdinaryRandomReserve.exists_almost_regular_reserve` |
| Ordinary robust expansion survives the stated simultaneous edge and vertex deletion | `Overfull.IsRobustExpander.after_edge_and_vertex_deletion` |
| Tutte–Berge and actual graph degrees imply the ordinary deficiency bound `(m+2am+t)/(d−a+1)` | `Overfull.OrdinaryPackingDeficiency.maximum_matching_deficiency` |
| An actual matching in the ordinary working graph covers the saturated vertices and satisfies the scaled deficiency bound | `Overfull.OrdinaryPackingWorking.exists_large_matching_outside_reserve` |
| An equal cut splits every prescribed pair, preserves crossing minimum degree, and has bipartite robust expansion, with uniform constants | `Overfull.PairedCut.paired_cut` |
| Every matching on an even vertex set extends to a partition into pairs | `Overfull.MatchingPairing.exists_pairing` |
| One ordinary reserve has a reduced robust range, the required minimum degree and degree deviations, and uniform order slack | `Overfull.OrdinaryPackingInitial.exists_initial_reserve` |
| An actual matching is completed through a supplied robust cut while avoiding forbidden vertices and controlling reserve use at protected vertices | `Overfull.OrdinaryMatchingCompletion.exists_completion_outside_set` |
| The ordinary reserve-load recurrence gives the bound with `c₀ = exp(120ℓ/γ)−1` and the required completion budget | `Overfull.OrdinaryPackingBounds.reserve_recurrence_bound` and `completion_budget` |
| Positive ordinary-packing reserve, error, and capacity parameters can be chosen in the required order | `Overfull.OrdinaryPackingParameters.reserve_parameters` and `exists_error_parameter` |
| One actual ordinary-packing round preserves capacity and the geometric total-load bound | `Overfull.OrdinaryPackingRound.exists_round` |
| A fixed ordinary-packing rule preserves the invariant for every admissible adaptive policy | `Overfull.OrdinaryPackingStrategy.exists_rule` |
| Full adaptive ordinary packing, with uniform constants, actual matchings, and robust expansion after every prefix | `Overfull.adaptive_ordinary_packing` |
| One fixed rule works at every stopping prefix, with admissibility required only for inputs already presented | `Overfull.adaptive_ordinary_packing_prefix` |
| An actual balanced robust cut crosses every edge of the supplied matching | `Overfull.PairedCut.exists_matching_cut` |
| The bipartite outcome yields actual equal retained sides of size at least `n/3` and the stated crossing-degree bounds | `Overfull.BalancedCore.balanced_core_of_bipartite_outcome` |
| An actual robust core replacement retains the exterior and preserves the maximum-degree bound and every overfull-set inequality | `Overfull.robust_core_replacement` |
| Actual released-edge degree is bounded by actual reserve-use degree, including disjoint families | `Overfull.MatchingRepairAccounting.released_degree_le` and `released_union_degree_le` |
| Actual reserve use is bounded by internal load plus endpoint incidence, and insertion preserves internal capacity | `Overfull.MatchingRepairLoad.actual_load_le_internal_add_endpoints` and `internalLoad_update_insert_matching` |
| One matching is completed in the actual unused reserve while protecting the specified covered vertices | `Overfull.MatchingRepairStep.exists_protected_completion` |
| Repair errors and order thresholds can be chosen uniformly before the graph and family | `Overfull.MatchingRepairParameters.exists_error` and `exists_order_threshold` |
| Using only original edges and unused reserve edges preserves disjointness of the repaired family | `Overfull.MatchingRepairFamily.update_pairwise_disjoint` |
| Full reserve repair constructs the family and bounds both actual edge unions by `μm` at every vertex | `Overfull.MatchingRepair.reserve_repair` |
| A positive regular graph with no overfull set has a finite perfect-matching distribution with every edge marginal equal to `1/k` | `Overfull.FractionalMatching.exists_perfectMatching_distribution` |
| Uniform edge-copy marginals for loopless multigraphs, with positive-weight matchings covering every degree-`k` vertex | `Overfull.Multigraph.exists_uniform_matching_distribution` |
| Perfect-matching distributions for positive regular loopless multigraphs | `Overfull.Multigraph.exists_perfectMatching_distribution` |
| The explicit absorber for every positive cycle length, with both triangle decompositions and its exact edge and auxiliary-vertex counts | `Overfull.Dense.CycleAbsorber.in_host` |
| One bounded absorber in the actual dense host for every balanced remainder on U, with exact total bound `4h²2^(h²)` | `Overfull.Dense.FiniteAbsorber.finite_absorber_subgraph` |
| All three matching-deletion probability bounds, including all one-vertex changes of an even set | `Overfull.MatchingProbability.Distribution.odd_failure_probability`, `even_toggles_failure_probability`, and `family_failure_probability` |
| The same three probability bounds for loopless multigraphs, with the actual deleted-edge graph identified | `Overfull.MultigraphMatchingProbability.Distribution.odd_failure_probability`, `even_toggles_failure_probability`, and `family_failure_probability` |
| An actual perfect matching retains all but at most `135720` prescribed exceptional matching edges | `Overfull.prescribed_exceptional_core_matching` |
| A prescribed exceptional matching is retained apart from at most `2q₀+4c₀` edges in a perfect matching whose deletion leaves no overfull set, with uniform constants | `Overfull.safe_prescription` |
| An actual deletion of at most one minority vertex preserves the core partition and places each surviving core on one cut shore | `Overfull.ForeignRefinement.minority_shore_deletion` |
| Actual bipartite host edges of degree at most `3h₀/4` partition into `floor(3h₀/4)` matching subgraphs | `Overfull.ForeignColoring.exists_three_quarter_color_classes` |
| Signed flows with the balanced bound `d/λ` and unequal-side bound `3θ/(2c−1)` | `Overfull.dense_signed_flow` and `Overfull.dense_unequal_flow` |
| The exact equivalence between extending the prescribed edge-copy coloring and decomposing the encoded graph into triangles | `Overfull.dense_encoding` |
| Positive, exactly balanced probabilities on all six directed pairs, with constants depending only on the density parameter | `Overfull.dense_reserve` |
| Actual short directed paths in all nine endpoint-part cases | `Overfull.Dense.BalanceRepair.exists_routing_path` |
| Finite cancellation of the cyclic imbalance using actual deleted arcs | `Overfull.Dense.BalanceRepair.exists_balanced_deletion` |
| An actual deleted subgraph of degree at most `5√ξn` whose residual is exactly locally balanced | `Overfull.dense_balance_repair` |
| The fractional triangle decomposition with exact edge incidences and weights in `[1/(2k),3/(2k)]` | `Overfull.dense_fractional_triangles` |
| The exact smaller bipartite robust range and parameter `min(ν,ασ/4)` | `Overfull.bipartite_robust_range_reduction` |

The full matching-polytope result reduces degree inequalities to perfect
degree equations in a doubled multigraph. The degree and odd-cut inequalities,
the projection, and the interpretation of integral points as actual matchings
are all proved. Its perfect `b`-matching input is a compiled proof, not an
assumed polytope statement. Source attribution is recorded in
[`THIRD_PARTY_NOTICES.txt`](../THIRD_PARTY_NOTICES.txt).

The signed-flow proofs use the included, proved finite circulation theorem.
They derive the required cut inequalities from graph degrees. The unequal-side
argument proves the stronger bound `2θ/(2c−1)` as well. Its source and
adaptation are recorded in
[`circulation-source.json`](circulation-source.json).

The fractional triangle-decomposition theorem composes the actual link-flow
construction, a proved residual contraction, and a convergent correction
series. Its positive error threshold depends only on the density margin and
is chosen before the graph. The fractional result does not supply the later
integral packing or the complete dense extension theorem.

The explicit cycle construction is now combined with proved cycle partitions,
finite remainder enumeration, and simultaneous disjoint placements in the
actual dense host. This proves the finite absorber lemma with the exact
edge-plus-auxiliary-vertex bound `4h²2^(h²)`. The subsequent approximate integral
packing and iterative absorption are still required for the dense extension.

Lemma 2.2 is proved in finite-law form for independent indicators with
possibly different success probabilities and for hypergeometric sampling.
The actual mean, exponential moments, and both tails are proved. An
additional interface to independent measurable variables on an arbitrary
underlying measure space is not included.

Theorem 2.16 is also complete. It assembles the actual reserve, working
graph, matching completion, reserve-load recurrence, and adaptive induction.
The constants are chosen before the graph, and one fixed rule is chosen
before the adaptive input. Each output is an actual matching perfect outside
the current forbidden set. All outputs are edge-disjoint, and the remaining
graph has the required robust expansion after every prefix. Direct
prescribed-sequence and perfect-matching corollaries are proved as well.
See [`adaptive-packing.md`](adaptive-packing.md) for the proof map and the
precise correspondence with the manuscript.

The fan results use actual colorings of all parallel edge copies. The
two-edge elementarity statement is proved by a recoloring; it is not an
assumed premise. The bounded-core-move theorem retains exactly the core
edges induced by the remaining vertices.

Lemma 2.21 is complete on the prescribed labels. Its robust parameter and
order threshold are fixed before the degree sequence. Exact cycle-power
degrees, disjoint added or deleted pairs, the block expansion argument,
and relabeling are all proved. It does not assume that the sequence is
graphical.

Lemma 2.19 is complete. Its constants precede the graph and prescribed
pairing. The proof obtains actual equal clusters and a robust reduced
graph from mathlib's equitable regularity theorem, then combines pair
orientation with lower bounds on cluster edge counts. The resulting
crossing graph uses the manuscript's side-normalized, ordered definition
of bipartite robust expansion. The required ordinary regularity and
inheritance results are proved directly, without assuming the cited
directed statements.

Lemma 2.20 is complete. Its proof combines the ordinary reserve, actual
working matching, matching-preserving robust cut, protected completion,
and reserve-load recurrence. The positive error, retained robust parameter,
and order threshold are chosen before the graph. One fixed rule is then
chosen before the adaptive forbidden-set policy. Every admissible prefix
consists of actual edge-disjoint matchings perfect outside their presented
sets, and its residual graph has robust expansion in the prescribed range.
The parameter choices, one-round construction, and adaptive induction are
separately checked.
The finite-prefix theorem also permits stopping at any admissible prefix
without imposing conditions on future inputs. Its one rule precedes both
the adversary and the stopping index, and its local feasibility is supplied
by the proved round construction.

Lemma 2.22 is also complete. It constructs the actual even regular
completion with the least prescribed auxiliary order, preserves the
original edge copies, and proves that every added edge has multiplicity
one. Its new vertices induce the required robust graph, and the actual
odd-set inequalities rule out every overfull set. A coloring of this
completion remains a separate task in the later manuscript arguments.
See [`auxiliary-completion.md`](auxiliary-completion.md).

Lemma 2.25 is complete from the precise bipartite outcome properties in
Lemma 2.24. The proof deletes the actual set of vertices with too few
crossing neighbors, equalizes the surviving sides, and verifies their size
and the degrees of the actual crossing graph. It retains equal sides of
size at least `n/3`, loses at most `6√ρn` vertices, and bounds every crossing
degree between `Δ−8√ρn` and `Δ`. Lemma 2.24 itself remains unproved.

Lemma 4.1 is complete. Its uniform constants precede the graph and matching
family. The proof constructs each matching in the actual unused reserve,
protects covered vertices at the integer internal capacity, and proves the
capacity and total-use bounds through the finite-family induction. The
outputs are actual disjoint matchings perfect outside the prescribed sets.
The degree bounds apply to the unions of actual used reserve edges and
actual released original edges. See [`matching-repair.md`](matching-repair.md).

Lemma 5.11 is complete. The cyclic imbalance is defined from actual graph
edges. The proof bounds its initial positive mass, constructs short paths
in every ordered endpoint-part case, and cancels the imbalance while
controlling internal incidence. The deleted and residual tripartite graphs
are actual subgraphs with the exact simple-graph difference identity. The
deleted degree is at most `5√ξn`, and the residual is locally balanced.
All routing hypotheses are derived from the stated graph densities and
the proved deletion bounds.

Lemma 3.3 is complete. It constructs the replacement core on its actual
vertex set, deletes every forbidden exterior edge, and proves the degree
and robust-expansion bounds. Actual core cuts and exact induced-edge
identities rule out every new overfull set. The constants precede the
graph and original core. See [`replacement.md`](replacement.md).

Lemma 4.8 is complete. Its twelve-vertex paths and finite witness are
constructed from the graph. Restricting the prescribed matching to avoid
that witness loses at most `135720` actual edges. The proof establishes
the required component correspondences, parity transfer, and all Tutte
inequalities before constructing the perfect matching. See
[`prescribed-matching.md`](prescribed-matching.md).

Lemma 4.9 is complete as a one-step result. For a fixed marked-set bound
`t₀`, its error tolerance and order threshold precede the graph and actual
exceptional order. Sampling constructs a perfect matching that preserves
the tested cuts and uses at most `q₀ = 4096(t₀+6)` boundary edges. The
boundary is fixed exactly. A global application of Lemma 4.8 and actual
compression give a retained partial matching losing at most `2q₀+c₀`
prescribed edges, where `c₀ = 135720`. Completion inside the actual cores
retains that partial matching and satisfies the manuscript allowance
`c₁ = 2q₀+4c₀`. The small-cut classification is proved from the group
condition and actual robust cores; it rules out every overfull set in the
residual. Proposition 4.10 now constructs the corresponding iterative process.

The proof of Proposition 4.10 includes actual maximizing
assignments and foreign color classes; an actual small-cut refinement with
surviving robust cores and encoded cluster labels; recorded-cut and heavy-set
bounds; exterior-incidence accounting for the precise adaptive input;
fixed-rule transcript and next-output theorems; safe ambient completion
from those outputs; and uniform parameters for the restarts. Actual
completed-phase and final-incidence counting yield the coefficient
`256*(c₁+6+t₀)`, using the final phase's fresh assignment.

`Overfull.foreign_edge_reduction` constructs the actual sequence. The inner
induction either completes every current class or returns an actual small
triggering cut. The outer induction constructs the resulting refinement,
transports the recorded-cut history, changes the actual core vertex sets,
and restarts every fixed rule and the fresh foreign classes. Its state
contains the original-host matching sequence and exact current residual.
At the final possible epoch the core labels are injective, so no trigger
exists. The degree reserve is proved at every construction prefix.

`Overfull.foreign_edge_reduction_with_small_error` fixes positive surviving
robustness before the requested final error tolerance, and then chooses one
original error and one order threshold before the graph and exceptional
order. The result contains the actual surviving cores and bounds their
combined error and exceptional order relative to the final degree.
See [`foreign-edge-reduction.md`](foreign-edge-reduction.md).

Lemma 4.11 is complete as a one-step result. For each exceptional-centered
star with more than `11*2^(t+4)` edges, it constructs a perfect matching
meeting that star, with an actual compressed matching and forest projection
as intermediate witnesses. Its deletion leaves no overfull set at the
remaining degree. The range and error tolerance are chosen before `t`;
only the graph-order threshold may depend on `t`. The adaptive preparation
theorem separates the compressed partial matching from its eventual core
completion and proves safety for every compatible robust completion.

Proposition 4.12 is complete. `Overfull.bounded_exceptional_absorption`
first fixes positive output robustness, then, for every positive function
of the final exceptional cardinality, chooses the exceptional bound, error
tolerance, and order threshold before the graph. The proof selects a light
threshold band, actually enlarges the cores by the vertices below it, and
constructs a terminating sequence of perfect-matching deletions using one
fixed certified packing rule per core. The potential counts every current
neighbor outside the assigned enlarged core, including exceptional
neighbors. A second actual enlargement absorbs the selected band.
The result retains at least three quarters of the original degree, has
no overfull set, and supplies the enlarged robust cores with the requested
error evaluated at the actual remaining exceptional cardinality. No
monotonicity of that function and no per-round completion oracle are
assumed. See [`exceptional-absorption.md`](exceptional-absorption.md).

Lemma 4.13 is complete. `Overfull.frequent_boundary_patterns` constructs
the actual pattern reduction and absorbs every remaining exceptional
vertex. One fixed encoding of the core labels is shared by the fractional
matching distribution. A common proposal and simultaneous discard plan
produce actual boundary matchings, completed using fixed certified core
rules. Exact actual cut accounting proves safety at every prefix. The
residual and integer reserve are at least `k/(3*b4(t))`; the final robust
cores cover all vertices and have arbitrary requested relative error.
For four odd enlarged parts the fixed joining forest is a perfect matching
or three-edge star, with actual pair and cut supply. Positive output
robustness precedes the requested error, while the explicit input range
depends on `t`. See [`frequent-patterns.md`](frequent-patterns.md).

There are complete proofs of **47 of the 69** numbered assertions, including
[ordinary-core Lemma 4.2](ordinary-factorization-full.md),
[boundary extension Lemma 4.14](boundary-extension.md), and
[four-odd Lemma 4.15](four-odd-decomposition.md). The remaining
22 include the main theorem and the structural exclusion on which its
checked reduction depends.

### Boundary extension reduction

`Overfull.boundary_extension_reduction` proves the full constructive reduction underlying Lemma 4.14. It starts with the actual prescribed one-or-three boundary coloring, completes all triple classes through the robust core, and deletes their exact original edge copies. The residual core, degree, and singleton boundary are constructed and counted. Its exterior contraction is proved even, regular, and free of overfull sets. The result reconstructs the exact prescribed extension from an actual coloring of that returned contraction, preserving properness at original exterior endpoints.

The reduction does not itself assert existence of that contracted coloring.
The completed direct one-apex and two-apex factorization now supplies it, so
full Lemma 4.14 is proved. Separately, the bounded-exterior closure completes
full ordinary-core Lemma 4.2 by preserving a linear original-color reserve
through the first matching group and factoring the exact residual. Its
specialized forbidden-label step uses permutation counting, greedy repair
and Vizing, without assuming the general Kahn theorem. General Theorem 6.1
remains incomplete. The current complete count is **47 of 69**, with **22**
remaining. See [the ordinary closure](ordinary-factorization-full.md),
[boundary extension](boundary-extension.md), and
[remaining targets](next-verification-target.md).

## What remains

Theorem 2.23 now supplies the [complete robust partition](robust-partition.md)
for almost-regular finite simple graphs. The structural argument still needs
the critical-graph degree estimate and its application in Proposition 2.24,
and the coloring theorems for the five possible configurations.
The remaining extensions include the dense bipartite and general robust
bipartite cases and their compositions with the structural reduction. Full
ordinary-core factorization is now available. The checked local absorbers,
matching results and deletion lemmas do not supply all remaining cases.

Substantial published inputs also remain to be connected to complete checked
proofs. They include the critical-graph degree estimate of Cao–Chen,
Kahn's list-edge-coloring theorem, Fan–Zhang's compatible circuit theorem,
the weighted matching theorem of Ehard–Glock–Joos, and the robust
decomposition theorem used from Granet. The robust-partition conclusion
stated in Theorem 2.23 and the tripartite link-packing instance in Lemma 5.12
are now proved locally; the broader KLOS and BKLOT theorems are not
separately claimed.
The specialized bounded-forbidden-label consequence of Kahn needed in
the ordinary-core preprocessing is now proved independently; this does
not claim a formal proof of Kahn's general theorem.

[`coverage.json`](coverage.json) gives the assertion-by-assertion inventory.
The build and axiom audit certify the included declarations. They do not
certify an assertion listed there as unproved. A missing Lean proof is not
a counterexample to the corresponding mathematical statement.
