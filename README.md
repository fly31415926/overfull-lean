# Lean formalization of the overfull manuscript

[Repository](https://github.com/fly31415926/overfull-lean) · [Verification workflow](https://github.com/fly31415926/overfull-lean/actions)

**The main theorem is not yet verified in Lean.** This project proves several of its supporting results, Vizing's edge-coloring bound, the critical-graph reduction, and the full sharpness construction. The structural exclusion needed to finish the main theorem remains unproved.

The source manuscript is *An Asymptotically Sharp Form of the Overfull Conjecture*, version `Four_Robust_Component_Cases_2026-11-20.tex`. Its exact filename and SHA256 are recorded in [`docs/manuscript-source.json`](docs/manuscript-source.json).

## The main theorem

The formal target is `Overfull.MainTheorem` in [`Overfull/Specifications.lean`](Overfull/Specifications.lean). For every fixed real `ε > 0`, it asserts that all sufficiently large finite simple graphs satisfying

```text
Δ(G) ≥ (1/4 + ε) * |V(G)|
```

have a proper edge coloring with `Δ(G)` colors if and only if they have no overfull vertex set at that maximum degree. The order threshold may depend on `ε`. A set `X` is overfull at `Δ(G)` when its actual number of internal edges exceeds `Δ(G) * floor(|X|/2)`.

The definition is not an axiom. No unconditional theorem of this type is proved in this project.

[`Overfull/OverfullSubgraphs.lean`](Overfull/OverfullSubgraphs.lean) proves that the vertex-set predicate is equivalent to the absence of an intrinsically overfull subgraph with maximum degree exactly `Δ(G)`. Thus the formal target uses the same obstruction as the manuscript, including arbitrary vertex and edge deletions.

### The reduction that is proved

[`Overfull/MainReduction.lean`](Overfull/MainReduction.lean) extracts an edge-minimal counterexample, removes its isolated vertices, and proves that the no-overfull property is inherited. Vizing's bound supplies equality of the maximum degrees. The proof transports the resulting graph to `Fin m` and checks both order bounds, the density inequality, and the threshold transfer used in the manuscript.

Vizing's bound is proved in [`Overfull/Vizing/Theorem.lean`](Overfull/Vizing/Theorem.lean), using the compiled Misra–Gries formalization and adapters to the project's graph and coloring definitions. This gives the checked implication

```lean
Overfull.mainTheorem_of_criticalExclusion
    (h : Overfull.LargeCriticalExclusion) :
    Overfull.MainTheorem
```

`LargeCriticalExclusion` is the remaining structural assertion: sufficiently large edge-minimal counterexamples above the stated density threshold cannot have no overfull set. Its proof requires the robust partition and the five coloring cases. It is a transparent proposition definition, not an assumed axiom. The implication above does not constitute a verification of the main theorem.

[`docs/main-theorem.md`](docs/main-theorem.md) records the formal statement, the checked reduction, and the outstanding work.

## Complete numbered manuscript results

| Manuscript result | Lean declaration | Scope |
| --- | --- | --- |
| Lemma 2.2: concentration | `Overfull.IndependentBernoulli.chernoff_of_independent_indicators` and `Overfull.Hypergeometric.chernoff` | Both distributional cases, including unequal indicator probabilities, with the actual means; formulated as finite probability laws |
| Theorem 2.3: Hall's theorem | `Overfull.bipartite_hall_iff` | Full equivalence for actual bipartite matching subgraphs, with arbitrary side sizes |
| Corollary 2.4: Hall's deficiency form | `Overfull.bipartite_hall_defect` | At most `h` uncovered left vertices under the stated deficiency inequalities |
| Theorem 2.5: the Tutte–Berge formula | `Overfull.TutteBerge.tutte_berge_integer_maximum` | The exact attained maximum of `o(G−X)−\|X\|`, using integer differences and actual maximum matchings |
| Lemma 2.6: fan consequences | `Overfull.Multigraph.IsKMinimal.endpoint_degree_sum` and `fan_low_degree_set_real` | Both the endpoint-degree inequality and the exclusion of edges to the low-degree set, with parallel edge copies |
| Lemma 2.7: the first fan argument | `Overfull.Multigraph.first_fan` | No internal core edge, exclusion of the specified exceptional-to-core edges, and the resulting degree bounds |
| Lemma 2.8: moving a bounded set out of the core | `Overfull.Multigraph.bounded_core_move_full` | An actual coloring after the move and the stated degree bound, including an empty core |
| Theorem 2.9: the matching polytope | `Overfull.Multigraph.matching_polytope` | Both directions for all finite loopless multigraphs, retaining parallel edge copies |
| Lemma 2.10: balanced color classes | `Overfull.Multigraph.balanced_edgeColoring` | Exceptional coverage, equal side coverage, spread at most two, exact vertex incidence, and both footprint bounds |
| Lemma 2.11: one high-degree vertex | `Overfull.Multigraph.edgeColoring_one_high` | A proper coloring of every edge copy under the strict `2s < k` bound |
| Lemma 2.12: sparse vertex deletion | `Overfull.Multigraph.edgeColoring_sparse_vertex_deletion_real` | The full coloring conclusion, including real error bounds and parallel edge copies |
| Lemma 2.13: bipartite robust expansion after deletions | `Overfull.IsBipartiteRobustExpander.after_edge_deletion_of_degree_bound` and `after_vertex_deletion` | Both assertions, with graph degrees, actual induced graphs, and side normalization |
| Lemma 2.14: an independent random reserve | `Overfull.RandomReserve.bipartite_random_reserve` | The actual sampled subgraph satisfies the robust-expansion probability bound; the failure estimate is stronger by a factor of two |
| Lemma 2.15: a short augmenting path | `Overfull.bipartite_robust_augmenting_path` | A simple alternating path avoiding the prescribed set, with at most `ceil(2/θ)+1` matching edges |
| Theorem 2.16: adaptive bipartite packing | `Overfull.adaptive_bipartite_packing` | Uniform constants, one rule for every admissible adaptive input sequence, actual edge-disjoint matchings perfect outside the presented sets, and robust expansion after every prefix |
| Lemma 2.17: reducing the robust range | `Overfull.robust_range_reduction` | Every allowed smaller range; actual neighbor counts |
| Lemma 2.18: small cuts through robust cores | `Overfull.SmallCuts.small_cut_lemma` | Real degree and error bounds, a uniform order threshold, and an actual union of whole cores differing by at most one vertex |
| Lemma 2.19: a robust cut splitting prescribed pairs | `Overfull.PairedCut.paired_cut` | A balanced cut splitting every pair, crossing minimum degree at least `αn/3`, and bipartite robust expansion with constants chosen before the graph and pairing |
| Lemma 2.20: adaptive ordinary packing | `Overfull.adaptive_ordinary_packing` | Uniform constants, one rule for every admissible adaptive input sequence, actual edge-disjoint matchings perfect outside the presented sets, and ordinary robust expansion after every prefix |
| Lemma 2.21: balanced robust realization | `Overfull.balanced_robust_realization` | Exact prescribed labelled degrees, a simple robust expander, and constants chosen before the order and degree sequence |
| Lemma 2.22: robust auxiliary completion | `Overfull.robust_auxiliary_completion` | The least auxiliary order, even regular completion, original edge copies retained, simple added edges, a robust auxiliary core, and no overfull set |
| Lemma 2.25: balanced-core extraction | `Overfull.BalancedCore.balanced_core_of_bipartite_outcome` | From the stated bipartite outcome, actual equal retained sides of size at least `n/3`, at most `6√ρn` deleted vertices, and crossing degrees between `Δ−8√ρn` and `Δ` |
| Lemma 3.3: replacing a dense core | `Overfull.robust_core_replacement` | An actual robust replacement on the prescribed even vertex set, retaining the exterior and preserving the maximum-degree bound and every overfull-set inequality, with uniform constants |
| Lemma 4.1: reserve repair | `Overfull.MatchingRepair.reserve_repair` | Uniform constants, actual disjoint repaired matchings perfect outside the prescribed sets, and degree at most `μm` in both the used-reserve and released-original-edge unions |
| Lemma 4.7: matching-deletion probabilities | `Overfull.MatchingProbability.Distribution.odd_failure_probability`, `even_toggles_failure_probability`, and `family_failure_probability` | All three probability bounds, with the actual residual graph identified; also generalized to loopless multigraphs |
| Lemma 4.8: retaining prescribed exceptional edges | `Overfull.prescribed_exceptional_core_matching` | An actual perfect matching omitting at most `135720` prescribed matching edges, with all path, connectivity, parity, and Tutte conditions proved from the graph |
| Lemma 4.9: preserving prescribed exceptional edges | `Overfull.safe_prescription` | An actual perfect matching retaining all but `c₁ = 2q₀ + 4c₀` prescribed edges, fixing the sampled boundary and leaving no overfull set, with uniform constants |
| Proposition 4.10: reducing foreign exceptional incidence | `Overfull.foreign_edge_reduction` and `Overfull.foreign_edge_reduction_with_small_error` | An actual original-host sequence of perfect matchings, final degree at least `k₀/256`, no overfull set, actual surviving robust cores, and bounded total exceptional incidence outside assigned cores; fixed output robustness precedes any requested final error tolerance |
| Lemma 4.11: forcing an exceptional star | `Overfull.force_exceptional_star` | For each exceptional-centered star of more than `11*2^(t+4)` edges, an actual perfect matching meeting that star, obtained from a compressed matching with a proved forest projection; its deletion leaves no overfull set |
| Proposition 4.12: bounded exceptional-set absorption | `Overfull.bounded_exceptional_absorption` | An actual sequence of safe perfect-matching deletions and two actual core enlargements, retaining at least three quarters of the degree, fixed positive robustness, at most a uniform number of exceptional vertices, and core error bounded by an arbitrary positive function of the actual final exceptional cardinality |
| Lemma 4.13: frequent boundary patterns | `Overfull.frequent_boundary_pattern` | Actual safe perfect-matching deletions, residual degree at least `k/(3B)`, complete absorption into robust cores, arbitrary relative core error, and actual joining-edge and cut supplies for the retained forest; output robustness is fixed before the requested error |
| Lemma 5.3: encoding a precoloring by triangles | `Overfull.dense_encoding` | Local balance, exact deficit identities, and both directions of the extension/decomposition equivalence |
| Lemma 5.4: the explicit cycle absorber | `Overfull.Dense.CycleAbsorber.in_host` | Every positive cycle length; both triangle decompositions and the exact counts |
| Lemma 5.5: the finite absorber | `Overfull.Dense.FiniteAbsorber.finite_absorber_subgraph` | One actual absorber for every allowed balanced remainder, with simultaneous placement and total size at most `4h²2^(h²)` |
| Lemma 5.6: a bounded signed flow | `Overfull.dense_signed_flow` | Prescribed row and column sums with edge weights bounded by `d/λ` |
| Lemma 5.7: a fractional triangle decomposition | `Overfull.dense_fractional_triangles` | Actual triangle weights with incidence one at each edge and the exact bounds `1/(2k)` and `3/(2k)` |
| Lemma 5.9: a signed flow with unequal sides | `Overfull.dense_unequal_flow` | The stated bound `3θ/(2c−1)`, with the stronger bound `2θ/(2c−1)` also proved |
| Lemma 5.10: balancing six directed pairs | `Overfull.dense_reserve` | Positive edge probabilities, exact balance at every vertex, and explicit constants depending only on `c` |
| Lemma 5.11: integer balance repair | `Overfull.dense_balance_repair` | Actual deleted edges, an exactly locally balanced residual, and deleted degree at most `5√ξn`, with uniform constants |
| Lemma 6.4: reducing the bipartite robust range | `Overfull.bipartite_robust_range_reduction` | The smaller range `σ` and the exact new parameter `min(ν,ασ/4)` |
| Proposition 7.1: the sharpness family | `Overfull.sharpness_family` | Connectivity, order, maximum degree, class 2, edge count, and no overfull set |
| Corollary 7.2: arbitrarily large examples below one quarter | `Overfull.arbitrarily_large_class_two_graphs` | Every real coefficient below `1/4` and every order threshold |

These are 42 of the manuscript's 69 numbered assertions. The remaining 27, including Theorem 1.1, have no complete proof here. Checked components of other assertions are listed separately in [`docs/coverage.json`](docs/coverage.json). The count records complete numbered statements, not the relative size or difficulty of the remaining work.

## Further checked inputs

### Vizing's theorem

`Overfull.vizing_finite` proves the upper bound `Δ(G) + 1` for arbitrary finite simple graphs with the project's proper edge-coloring definition. The adapter uses actual adjacency and unordered edges; a partial upstream coloring is accepted only after the upstream completeness theorem proves that every graph edge is colored.

The upstream source is Arohee Bhoja's [Vizing formalization](https://github.com/aroheebhoja/vizing), pinned to commit `c4fc77be6af1a48a44351234120898ad3cf6b545`. The project fetches that version and applies a recorded compatibility patch. The exact file hashes and source provenance are in [`docs/vizing-source.json`](docs/vizing-source.json). The complete upstream source is not redistributed in this archive.

### König's theorem

[`Overfull/Konig.lean`](Overfull/Konig.lean) proves that a finite loopless bipartite multigraph has a proper `k`-edge-coloring if and only if every degree is at most `k`. Its coloring assigns a value to every actual edge copy. The proof uses a matching covering every maximum-degree vertex, deletes those copies, and inducts on the degree bound. It includes `k = 0` and arbitrary parallel multiplicities.

### Matchings, the matching polytope, and their probabilities

[`Overfull/BipartiteMatching.lean`](Overfull/BipartiteMatching.lean) proves the Hall inequalities and constructs a perfect matching in a balanced bipartite robust expander with the stated minimum crossing degrees.

[`Overfull/TutteBerge.lean`](Overfull/TutteBerge.lean) proves that a maximum matching leaves exactly `max_X (o(G−X)−|X|)` vertices uncovered. It uses the actual odd components of the graph after vertex deletion and counts actual unordered matching edges. The proof adds universal vertices, applies mathlib's proved Tutte theorem, and restricts the resulting perfect matching. It proves both the upper bound for every integer difference and attainment by a vertex set, as well as the existence of a maximum matching. The empty graph is included.

[`Overfull/FractionalMatching.lean`](Overfull/FractionalMatching.lean) proves that every positive `k`-regular simple graph with no `k`-overfull set admits a finite probability distribution on perfect matchings in which each edge has marginal `1/k`. It proves the degree and odd-cut hypotheses of the perfect-matching polytope theorem and identifies its integral points with mathlib perfect-matching subgraphs.

[`Overfull/MatchingPolytope.lean`](Overfull/MatchingPolytope.lean) proves the full matching-polytope theorem for loopless multigraphs. It doubles the graph, adds one edge between the two copies of each vertex, and proves all required odd-cut inequalities before applying the perfect-matching polytope theorem. Projection gives a convex combination of actual matchings. The converse, the degree inequalities, and the exact interpretation of zero–one vectors as matchings are proved as well.

It also constructs uniform-marginal distributions for nonregular multigraphs with maximum degree at most `k` and no `k`-overfull set. Every matching of positive weight covers every degree-`k` vertex. For a regular multigraph, removing zero-weight indices gives a distribution on actual perfect matchings. The edge type distinguishes parallel copies throughout.

The underlying perfect `b`-matching proof is adapted from [Shengtong Zhang's repository](https://github.com/shengtongz/lovasz-opus). Its mathematical proof compiles unchanged with the required mathlib imports. The source commit, license, and adaptation are recorded in [`docs/bmatching-source.json`](docs/bmatching-source.json), [`THIRD_PARTY_NOTICES.txt`](THIRD_PARTY_NOTICES.txt), and [`LICENSE_BMATCHING.txt`](LICENSE_BMATCHING.txt).

[`Overfull/MatchingProbability.lean`](Overfull/MatchingProbability.lean) then proves the failure bounds `<1/k`, `≤10/k`, and `≤11ℓ/k`. The proof derives the cut parity, toggle identities, expectations, and finite union and Markov bounds. It also proves that its failure event is precisely the odd-cut failure in the actual graph obtained by deleting the matching, and that the residual graph is `(k−1)`-regular.

[`Overfull/MultigraphMatchingProbability.lean`](Overfull/MultigraphMatchingProbability.lean) proves all three bounds for loopless multigraphs. Its residual multigraph has exactly the remaining edge copies; the cut and degree identities are proved for that graph. This covers the multiplicities appearing in the completion arguments.

### Robust cores and signed flows

The augmenting-path theorem permits the supplied matching to lie outside `G`. Its conclusion records the two injective vertex sequences, actual alternating edges, avoidance of the forbidden set, and the quantitative length bound. Separate theorems establish distinctness of the matching edges and that the forward graph edges do not belong to the matching.

The small-cut theorem represents each simple core by an injective, endpoint-preserving map into the multigraph edge copies. It proves that distinct cores contribute disjoint edge sets. The explicit sufficient order condition is `3 < ν²c²n`; the public theorem chooses a uniform order threshold before quantifying the graph, the real degree and error bounds, or the cut.

The signed-flow proofs derive all cut inequalities from actual crossing degrees. The resulting weights vanish on nonedges and have the prescribed sums. The finite circulation proof is included with its pinned source and compatibility changes in [`docs/circulation-source.json`](docs/circulation-source.json) and [`CIRCULATION_NOTICE.txt`](CIRCULATION_NOTICE.txt). Both flow statements include empty vertex classes.

The bipartite range lemma proves the exact neighborhood-expansion conclusion. At positive order, its hypotheses also imply the usual admissibility of the new robust parameter. The empty-graph branch proves the expansion inequality without asserting that additional parameter bound.

### Balanced and sparse multigraph colorings

[`Overfull/CriticalMultigraph.lean`](Overfull/CriticalMultigraph.lean) constructs minimal noncolorable restrictions of the actual edge copies and proves the missing-color counts. [`Overfull/MultigraphFan.lean`](Overfull/MultigraphFan.lean) proves the two-edge fan property by an actual recoloring, then derives both conclusions of Lemma 2.6. [`Overfull/MultigraphFanApplications.lean`](Overfull/MultigraphFanApplications.lean) proves the first-fan and bounded-core-move lemmas. The host may have parallel edges; only the distinguished core must be simple in the bounded-move argument. Its full wrapper includes the empty-core case without an extra assumption that the exterior degree bound is nonnegative.

[`Overfull/BalancedColoring.lean`](Overfull/BalancedColoring.lean) proves the balanced-coloring lemma from a supplied proper coloring. It constructs actual switches on unions of two-color components and proves their effects on vertex coverage. Two finite minimizations give equal side coverage and spread at most two. The component argument retains parallel copies in its degree and endpoint counts; connectedness alone uses the underlying simple graph. The exceptional vertices are covered in every color, and both footprint estimates follow from the actual incidence counts.

[`Overfull/MultigraphGreedy.lean`](Overfull/MultigraphGreedy.lean) first colors the star at the distinguished high-degree vertex injectively and extends the coloring across the remaining edge copies. [`Overfull/SparseColoring.lean`](Overfull/SparseColoring.lean) proves the sparse-deletion lemma by coloring the core and the two-star subgraph, then using Hall's theorem to assign distinct available colors to the two-star classes. The central parallel edges receive the remaining colors. The actual vertex deletion and all degree comparisons are proved.

### Random reserves and degree control

[`Overfull/Probability/Bernoulli.lean`](Overfull/Probability/Bernoulli.lean) defines the finite independent sampling distribution and proves its normalization and joint coordinate probabilities. [`Overfull/RandomReserve.lean`](Overfull/RandomReserve.lean) then proves Lemma 2.14 for the actual sampled graph. Its failure bound is

```text
4^m * exp(-p * ν^2 * m^2 / 24).
```

This is stronger than the manuscript's bound with leading factor two. The proof constructs the vertex-set witnesses to failed robust expansion and bounds their actual sampled crossing-edge counts.

[`Overfull/Probability/Concentration.lean`](Overfull/Probability/Concentration.lean) proves the two-sided Chernoff estimate with constant `1/3` for the common-probability finite Bernoulli model, along with the additive bound used for degrees. [`Overfull/Probability/IndependentBernoulli.lean`](Overfull/Probability/IndependentBernoulli.lean) allows a different success probability at every coordinate and transfers the estimate to any finite probability law with the independent joint distribution. [`Overfull/Probability/Hypergeometric.lean`](Overfull/Probability/Hypergeometric.lean) proves the same estimate for actual uniform sampling without replacement. Both modules prove the stated mean and derive the exponential-moment estimate; neither assumes a concentration conclusion. This completes the two distributional cases of Lemma 2.2 in finite-law form. There is no separate interface to `Mathlib.iIndepFun` on an arbitrary underlying measure space.

[`Overfull/RandomReserveDegrees.lean`](Overfull/RandomReserveDegrees.lean) combines the expansion and degree estimates in one sample. It proves a uniform order threshold before quantifying the graph and obtains an actual contained bipartite reserve with all degree deviations from `p*Δ` strictly below `2εm`. This supplies the reserve-selection input in Step 1 of the complete adaptive packing proof.

[`Overfull/MatchingExtension.lean`](Overfull/MatchingExtension.lean) proves that a maximum matching can retain every vertex covered by a prescribed matching. It also constructs a matching covering any set `Z` when each vertex of `Z` has degree greater than `2|Z|`, then extends its coverage to a maximum matching. These are actual matching subgraphs, and maximality compares their actual edge counts. They supply the coverage-preserving selection used in Step 2 of adaptive packing.

[`Overfull/BipartitePackingDeficiency.lean`](Overfull/BipartitePackingDeficiency.lean) derives an actual Hall witness from maximum matching size and counts the graph edges between the witness and its neighborhood. Under ordinary degree bounds `d−a ≤ d_G(v) ≤ d+a+u(v)`, nonnegative load of total at most `t`, and side orders at most `m`, it proves that the number missed on the left is at most `(2am+t)/d`. Equal side orders imply equal uncovered counts. The ambient `m` may exceed the actual side order, as required after deleting the prescribed vertices.

[`Overfull/BipartitePackingStep.lean`](Overfull/BipartitePackingStep.lean) combines these results into the matching-selection conclusion and proves the manuscript bound `h ≤ (16+2c₀)εm/γ`. A separate variant derives the saturated set directly from a positive capacity and the total load. [`Overfull/BipartitePackingWorking.lean`](Overfull/BipartitePackingWorking.lean) applies this to the actual graph obtained by deleting the reserve, previously used edges, and the current forbidden vertices. Its degree and load bounds are derived from that graph.

### Adaptive bipartite packing

[`Overfull/BipartitePacking.lean`](Overfull/BipartitePacking.lean) proves Theorem 2.16. It chooses `ε` and `m₀` before the graph, and then chooses one fixed rule before any adaptive input sequence. The rule receives only the earlier sets and matchings and the current forbidden set. Every output is an actual subgraph of `G`, is a matching with vertex set exactly the complement of the current forbidden set, and has no edge in an earlier matching.

The proof constructs vertex-disjoint alternating paths in the unused reserve and performs the simultaneous switches needed to complete each matching. Its capacity and total-load bounds count actual reserve edges in the union of the chosen matchings. The one-round recurrence proves that a matching preserving the geometric load bound always exists, and the fixed rule maintains this bound throughout all `max(0, floor(Δ−γm))` rounds. After every prefix, the remaining graph is a bipartite robust `(pν/4, τ)`-expander.

[`Overfull/BipartitePackingCorollaries.lean`](Overfull/BipartitePackingCorollaries.lean) gives direct statements for a prescribed sequence of forbidden sets and for the case in which every set is empty. The latter produces actual pairwise edge-disjoint perfect matchings. Both statements give the robust-expansion conclusion after removing any subfamily, hence after every prefix. The prescribed-sequence theorem assumes the manuscript's total incidence bound explicitly. The adaptive theorem uses the weaker bound on past incidences at each round.

[`docs/adaptive-packing.md`](docs/adaptive-packing.md) records the statement, the proof components, and the correspondence with the manuscript. The packing theorem is one supporting result; it does not establish the remaining structural and coloring arguments for the main theorem.

### Adaptive ordinary packing

[`Overfull/OrdinaryRandomReserve.lean`](Overfull/OrdinaryRandomReserve.lean) samples each unordered edge once and proves ordinary robust expansion with parameter `pν/4`. Its failure bound is `4^n exp(−pν²n²/48)`. The counting proof permits the two witness vertex sets to overlap. [`Overfull/OrdinaryRandomReserveDegrees.lean`](Overfull/OrdinaryRandomReserveDegrees.lean) chooses one actual contained reserve satisfying both expansion and all degree bounds, with a threshold uniform over the graph.

[`Overfull/OrdinaryPackingDeficiency.lean`](Overfull/OrdinaryPackingDeficiency.lean) uses the proved Tutte–Berge formula and actual component boundary counts to obtain

```text
h ≤ (m + 2am + t)/(d − a + 1)
```

under the specified degree and total-load bounds. It derives the manuscript estimate `h ≤ (30/γ)(εm+t/m)` and constructs a maximum matching covering the saturated vertices. [`Overfull/OrdinaryPackingWorking.lean`](Overfull/OrdinaryPackingWorking.lean) applies this to the actual graph after deleting the reserve, prior matching edges, and the forbidden vertices. The resulting ambient matching has even uncovered count and the required edge avoidance and coverage properties.

[`Overfull/OrdinaryRobustStability.lean`](Overfull/OrdinaryRobustStability.lean) proves robust expansion after simultaneous bounded edge and vertex deletion. It also applies the actual reserve-load identities to the unused reserve and residual graph. [`Overfull/OrdinaryPackingInitial.lean`](Overfull/OrdinaryPackingInitial.lean) first reduces the robust range of the original graph, then chooses one actual reserve with the required minimum degree and degree deviations. Its order threshold is uniform over the graph and nominal degree.

[`Overfull/MatchingPairing.lean`](Overfull/MatchingPairing.lean) extends an actual matching on an even vertex set to a partition into pairs. [`Overfull/OrdinaryMatchingCompletion.lean`](Overfull/OrdinaryMatchingCompletion.lean) completes a matching through a supplied actual balanced robust cut, using the proved bipartite augmenting-path construction. The result is an ambient matching perfect outside the forbidden set. It uses only original matching edges and unused reserve edges, uses no reserve edge at a protected vertex, and bounds the total reserve degree by `ℓh`, where `h` is the total uncovered count.

[`Overfull/OrdinaryPackingBounds.lean`](Overfull/OrdinaryPackingBounds.lean) proves the reserve-load recurrence and the bound with `c₀ = exp(120ℓ/γ)−1`, together with the numerical budget for the protected vertices and augmenting paths. [`Overfull/OrdinaryPackingParameters.lean`](Overfull/OrdinaryPackingParameters.lean) chooses the positive reserve, error, and capacity constants in the required order. [`Overfull/PairedCut/Matching.lean`](Overfull/PairedCut/Matching.lean) constructs the actual robust cut crossing a given matching.

[`Overfull/OrdinaryPackingRound.lean`](Overfull/OrdinaryPackingRound.lean) proves that a new matching satisfying the capacity and total-load bounds exists at every admissible step. [`Overfull/OrdinaryPackingStrategy.lean`](Overfull/OrdinaryPackingStrategy.lean) chooses one fixed rule and proves its invariant for every adaptive forbidden-set policy. [`Overfull/OrdinaryPacking.lean`](Overfull/OrdinaryPacking.lean) assembles these results into full Lemma 2.20. The positive error, retained robust parameter, and order threshold precede the graph; the rule precedes the adaptive input. Every output is an actual matching perfect outside its current forbidden set, the matchings are edge-disjoint, and the remaining graph retains the prescribed robust range after every prefix.

[`Overfull/OrdinaryPackingPrefix.lean`](Overfull/OrdinaryPackingPrefix.lean) strengthens the strategy interface for an interrupted phase. One fixed rule gives an actual packing and a robust unused graph after every prefix whose inputs satisfy the size, parity, and incidence conditions up to that point. The rule is chosen before both the adaptive input and the stopping index. No condition is imposed on later inputs; the constants retain the quantifier order of Lemma 2.20.

### A cut splitting prescribed pairs

[`Overfull/PairedCut/Full.lean`](Overfull/PairedCut/Full.lean) proves Lemma 2.19. For fixed `α > 0` and `0 < ν ≤ τ ≤ 1/8`, it chooses `ξ > 0` and an order threshold before the graph and prescribed pairing. The resulting equal bipartition splits every pair, has crossing minimum degree at least `αn/3`, and is a bipartite robust `(ξ,4τ)`-expander.

The proof constructs an equitable regularity partition using mathlib's proved regularity theorem. [`Overfull/PairedCut/Regularity.lean`](Overfull/PairedCut/Regularity.lean) bounds the total degree lost on discarded edges, proves robust expansion in the actual reduced graph, and trims the parts to equal clusters with a small exceptional set. [`Overfull/PairedCut/Labels.lean`](Overfull/PairedCut/Labels.lean) orients the prescribed pairs to balance these clusters and preserve crossing degrees. [`Overfull/PairedCut/Lifting.lean`](Overfull/PairedCut/Lifting.lean) derives expansion of the cut from lower bounds on actual cluster edge counts. Its last step uses the side size in both the neighborhood threshold and expansion surplus. The required ordinary regularity and inheritance statements are proved within the project; the general directed regularity statements cited in the manuscript are not claimed separately.

### Balanced robust realization and auxiliary graphs

[`Overfull/RobustRealization.lean`](Overfull/RobustRealization.lean) proves Lemma 2.21 on the prescribed labels. It constructs the exact degree multiset from cycle powers and disjoint added or deleted pairs, proves robustness using consecutive blocks, and permutes the vertices to match the required sequence. The positive robust parameter and order threshold depend only on the fixed density and robust range, and precede the order and sequence. All parity cases and the complete graph are included.

[`Overfull/AuxiliaryCompletion.lean`](Overfull/AuxiliaryCompletion.lean) proves full Lemma 2.22. Its constants precede the original multigraph, and it uses the least allowed auxiliary order. The completion is even-order and regular, retains every original edge copy, has multiplicity one at each added edge, and induces the required simple robust graph on the new vertices. Balanced neighbor sets give each new vertex at most one neighbor of original deficiency one. This supplies the estimate for an odd set containing exactly one new vertex; the other odd sets are controlled by the original inequalities and the auxiliary cuts. The proof establishes that the actual completion has no overfull set. [`docs/auxiliary-completion.md`](docs/auxiliary-completion.md) records its construction and proof map.

### Balanced-core extraction

[`Overfull/BalancedCore.lean`](Overfull/BalancedCore.lean) proves Lemma 2.25 from the precise bipartite outcome properties supplied by Lemma 2.24. It defines the vertices with too few neighbors across the original partition, deletes this actual set, and trims the larger surviving side. The retained sides have the same size, at least `n/3`; at most `6√ρn` vertices are lost, and every degree in the actual crossing graph lies between `Δ−8√ρn` and `Δ`. The construction includes the zero-error case. The preceding existence and classification assertion in Lemma 2.24 remains unproved.

### Replacing a dense core

[`Overfull/Replacement.lean`](Overfull/Replacement.lean) proves full Lemma 3.3. For fixed `β > 0` and `0 < τ ≤ min(β/16,1/4)`, it chooses positive `μ`, `ξ`, and an order threshold before the graph and its even core vertex set. The output is an actual robust `(μ,τ)`-expander on that set, with minimum degree at least `k−2a−1`. Its edges avoid the retained exterior, and the ambient replacement has maximum degree at most `k` and no `k`-overfull set.

The proof constructs a regular robust graph using Lemma 2.21 and deletes its forbidden exterior edges. Exact graph identities control the degrees and induced edge counts. Actual robust core cuts reduce a possible overfull set to the four small or complementary-small core intersections; regular degree counts handle each case. [`docs/replacement.md`](docs/replacement.md) gives the statement and proof map. The subsequent coloring of the comparison graph remains a separate task.

### Repairing a family of matchings

[`Overfull/MatchingRepair.lean`](Overfull/MatchingRepair.lean) proves full Lemma 4.1. For every sufficiently small positive `μ`, it chooses a positive error and an order threshold before the reserve graph and matching family. The resulting matchings are perfect outside the prescribed forbidden sets, use only their own original edges and reserve edges, and are pairwise edge-disjoint. Both the actual used-reserve union and the actual released-original-edge union have degree at most `μm` at every vertex.

The proof constructs each repair in the unused reserve. [`Overfull/MatchingRepairStep.lean`](Overfull/MatchingRepairStep.lean) constructs the required robust cut and completes a matching while protecting specified covered vertices. [`Overfull/MatchingRepairLoad.lean`](Overfull/MatchingRepairLoad.lean) separates internal reserve incidence from incidence at the original uncovered vertices and preserves the integer internal capacity through each update. [`Overfull/MatchingRepairFamily.lean`](Overfull/MatchingRepairFamily.lean) proves disjointness of the updated family, and [`Overfull/MatchingRepairAccounting.lean`](Overfull/MatchingRepairAccounting.lean) bounds released-edge degree by used-reserve degree. All parameter choices and the finite-family induction are proved. [`docs/matching-repair.md`](docs/matching-repair.md) records the hypotheses, numerical choices, and proof map.

### Retaining prescribed exceptional edges

[`Overfull/PrescribedMatching.lean`](Overfull/PrescribedMatching.lean) proves full Lemma 4.8. In a graph with at most four large core cliques and an exceptional set, an actual perfect matching retains all but at most `135720` edges of the prescribed matching. The hypotheses include the existence of an initial perfect matching, as in the manuscript. The formal theorem also permits overlapping core cliques and prescribed edges with both endpoints exceptional.

The proof constructs paths with at most twelve vertices and a bounded set preserving core connectivity after any deletion of at most three vertices. It discards only prescribed matching edges meeting that set, proves actual component and parity comparisons, checks all three ranges of Tutte deletion sets, and completes the retained matching. No path, witness, or Tutte feasibility statement is assumed in the public theorem. [`docs/prescribed-matching.md`](docs/prescribed-matching.md) records the exact hypotheses and the six proof modules.

### Preserving prescribed edges and odd-set inequalities

[`Overfull/SafePrescription.lean`](Overfull/SafePrescription.lean) proves Lemma 4.9. For the stated regular graph, robust cores, cluster groups, and prescribed exceptional matching, it constructs a perfect matching whose deletion leaves no overfull set and which omits at most `c₁ = 2q₀ + 4c₀` prescribed edges. Here `q₀ = 4096(t₀+6)` and `c₀ = 135720`. The marked-set bound `t₀` is fixed before the error tolerance and order threshold. Both constants precede the graph and the actual exceptional order, which may grow with `n` subject to `a + |Z| + 1 ≤ εn`.

The proof samples an actual perfect matching preserving the tested cuts and constructs its exact boundary submatching, consisting of edges meeting the marked set or joining different clusters. The finite Markov estimate bounds this submatching by `q₀` edges. After its vertices are removed, one application of Lemma 4.8 across all surviving cores, followed by compression, gives an actual retained partial matching `F`. This proves the stronger intermediate loss bound `2q₀ + c₀`. Every retained edge belongs to the original graph, and completion inside the actual robust cores preserves `F`.

The proof derives the small-cut classification from the group condition and actual core expansion. Fixing the boundary transfers the tested odd-cut inequalities on whole-cluster unions and their one-vertex changes. The residual core bounds then exclude every overfull set after the perfect matching is deleted. This proves one safe-prescription step. The iterative refinement in Proposition 4.10 and the repeated forcing and absorption in Proposition 4.12 are proved below.

### Forcing an exceptional star

[`Overfull/ForceMatching.lean`](Overfull/ForceMatching.lean) proves Lemma 4.11. In the stated `h`-regular graph with no `h`-overfull set, at most four disjoint robust cores, and at most `t` exceptional vertices, every star of more than `11*2^(t+4)` edges centered at an exceptional vertex is met by a perfect matching whose deletion leaves no overfull set at degree `h−1`. The robust range and positive error tolerance are fixed before `t`; only the lower bound on the graph order may depend on `t`.

The proof constructs all three actual matchings: the sampled perfect matching, its compressed submatching, and the perfect completion inside the cores. [`Overfull/Compression/Matching.lean`](Overfull/Compression/Matching.lean) retains every exceptional-incident edge and at most three joining edges whose projected labels form a forest, and proves even uncovered order in every core. The probability argument counts the actual tested family and uses the exact star probability `|S|/h`. Completion preserves the whole-union cut-edge sets of the compressed matching. The parity of perfect-matching cuts controls every one-vertex toggle, and the small-cut theorem then excludes every overfull set in the actual residual graph.

[`Overfull/ForceMatching/Adaptive.lean`](Overfull/ForceMatching/Adaptive.lean) also prepares the compressed partial matching before its core completion is chosen. Its safety clause applies to every compatible completion with the stated residual robust cores. Proposition 4.12 uses this preparation with one fixed certified rule per core throughout its forcing phase.

### Foreign-edge reduction with actual refinements

[`Overfull/ForeignEdges/Reduction.lean`](Overfull/ForeignEdges/Reduction.lean) proves Proposition 4.10. It constructs fresh maximizing core assignments, actual foreign matching classes, actual small-cut refinements with surviving robust cores, and Fin-4 labels. Recorded-cut accounting bounds the actual intercluster edge count and the number of heavy marked vertices. The incidence budget for adaptive packing is derived from distinct actual exterior edges, including the current partial matching before its completion exists.

The preparation theorem in [`Overfull/SafePrescription/Adaptive.lean`](Overfull/SafePrescription/Adaptive.lean) separates the bounded exceptional partial matching from its core completion. Fixed-rule transcript, next-step, and completion theorems then construct the actual local and ambient matchings, retaining the exact whole unused cores and their fixed robust parameters. The restart schedule and one original error and order threshold are chosen before the graph.

The inner induction constructs an actual interrupted or completed epoch. The outer induction carries the original-host matching sequence, exact residual graph, actual cut history, changed core sets, and all quantitative bounds. Every refinement strictly increases the number of occupied core groups; after three refinements the core labels are injective and no triggering shore exists. Every prefix satisfies the required degree reserve. The full current foreign graph is rebuilt and recolored at each restart.

The final completed epoch supplies the actual incidence bound `256*(c₁+6+t₀)*h`, with `k₀ ≤ 256*h`. This improves the manuscript allowance containing `4c₁`. The result contains one sequence of actual perfect matchings in the original graph, its exact final residual, and surviving core error at most `a+3`. [`Overfull/ForeignEdges/ReductionError.lean`](Overfull/ForeignEdges/ReductionError.lean) fixes the positive output robustness parameter before an arbitrary requested final error tolerance, then chooses the original error and order threshold. [`docs/foreign-edge-reduction.md`](docs/foreign-edge-reduction.md) records the quantified statement and the two constructed inductions. This completes one more numbered assertion; the main theorem remains unverified.

### Bounded exceptional-set absorption

[`Overfull/Absorption/Bounded.lean`](Overfull/Absorption/Bounded.lean) proves Proposition 4.12. Its positive output robustness is fixed before an arbitrary positive function `f`. The exceptional bound, original error tolerance, and order threshold are then chosen before the graph. The actual result contains a sequence of perfect matchings in the original host, its exact residual of degree at least `3h/4`, no overfull set, and enlarged robust cores covering all but at most the uniform bound of exceptional vertices. The final core error is at most `f(|Z_final|) * h_final`, with no monotonicity assumption on `f`.

The proof selects a light band from the original foreign-neighbor counts and absorbs the vertices below that band into their assigned cores. One fixed certified rule per enlarged core supplies every completion during the forcing phase. The actual potential counts all neighbors outside each selected vertex's assigned enlarged core, including remaining exceptional neighbors, and decreases whenever the corresponding star is forced. Its initial bound is strictly below `h/4`. A second actual enlargement absorbs the selected band; the terminal outside-degree bound supplies the final error without a second exceptional-order term. [`docs/exceptional-absorption.md`](docs/exceptional-absorption.md) records the parameter order, graph constructions, and complete proof map.

### Frequent boundary patterns

[`Overfull/Patterns/Frequent.lean`](Overfull/Patterns/Frequent.lean) proves Lemma 4.13. For a bounded exceptional set and three or four robust cores, it fixes positive output robustness before an arbitrary requested relative error, then chooses the initial tolerance and order threshold before the graph. The exact residual is obtained by deleting constructed perfect matchings, has no overfull set after every prefix, and retains degree at least `k/(3B)`, where `B = 2^(t.choose 2) * 4^t * 2^6`.

The proof encodes a proved perfect-matching distribution, chooses and rounds a frequent pattern, realizes the selected copies with actual fresh boundary edges, and completes them through fixed certified core rules. Original weighted capacities and exact subtraction of realized cut counts establish residual safety. No fractional decomposition of the realized residual is assumed. Actual surviving edge pools then absorb every exceptional vertex into its assigned core and provide the retained forest's joining-edge and cut supplies. When all four enlarged parts are odd, the forest is an explicit perfect matching or three-edge star. [`docs/frequent-pattern.md`](docs/frequent-pattern.md) gives the complete construction and parameter order.

The next target is the boundary-extension argument of Lemma 4.14, including its unresolved bounded-input factorization dependency. [`docs/next-verification-target.md`](docs/next-verification-target.md) records that work and the later compatible-circuit and terminal-factorization dependencies. The manuscript main theorem remains unverified.

### The coloring encoding and balanced reserve

[`Overfull/Dense/Encoding.lean`](Overfull/Dense/Encoding.lean) models the simple part by an injective map into the host edge copies. The prescribed coloring remains fixed on every complementary copy, including parallel edges. Its missing colors define the other two parts of the encoded tripartite graph. The proof establishes local balance, all stated deficit identities, and an exact equivalence between full coloring extensions and actual triangle decompositions.

[`Overfull/Dense/Reserve.lean`](Overfull/Dense/Reserve.lean) proves the six-pair reserve lemma from actual directed degrees and pair edge counts. The common vertex demands are derived from the graph, and the unequal-side flow theorem corrects the initial constant edge weights. The explicit choices are `c₁ = 12/(2c−1)` and `θ₀ = min(1/4, 1/(4c₁))`. The resulting probabilities lie strictly between zero and one on every edge and have equal incoming and outgoing sums at every vertex. This is the expected-balance conclusion; subsequent sampling and integral decomposition remain separate steps.

### Fractional triangle decomposition

[`Overfull/Dense/FractionalTriangles.lean`](Overfull/Dense/FractionalTriangles.lean) proves Lemma 5.7 from its graph hypotheses. The tripartite model has a corresponding simple graph, actual triangle coordinates, and an incidence map that sums triangle weights at each actual edge. The conclusion gives incidence exactly one and weights between `1/(2k)` and `3/(2k)`.

The proof first solves signed flows in the actual link graphs, then distributes the remaining weights on the first two parts across their triangles. It proves a contraction of the residual and sums the resulting correction series. The sufficient choice is `ε₀ = min(η, 1/(32(2+10/η)))`, depending only on `η`; it is quantified before every graph and part type. The empty-side case is included. No flow, correction, contraction, or convergence conclusion is assumed in the final theorem.

This verifies the fractional decomposition. The subsequent approximate integral packing and the full dense extension remain unproved.

### Integer balance repair

[`Overfull/Dense/BalanceRepair.lean`](Overfull/Dense/BalanceRepair.lean) proves full Lemma 5.11. From the prescribed tripartite sizes, pair densities, and actual cyclic degree imbalances, it constructs a deleted subgraph and a locally balanced residual. Their simple graphs satisfy the exact deletion identity, and the deleted graph has degree at most `5√ξn` at every vertex.

The constants are `c₀ = min(η,1)/1000`, `c₁ = 5`, and `ξ₀ = (c₀/100)²`; the order threshold is chosen after fixing `0 < ξ ≤ ξ₀`. [`Overfull/Dense/BalanceRepair/Routing.lean`](Overfull/Dense/BalanceRepair/Routing.lean) constructs the required paths in all nine ordered endpoint-part cases. [`Overfull/Dense/BalanceRepair/Cancellation.lean`](Overfull/Dense/BalanceRepair/Cancellation.lean) proves finite cancellation with bounded internal incidence. The graph identities and numerical estimates prove that every residual graph meets the routing hypotheses. The public theorem assumes no routing or balance-repair existence statement. This proves integer balance repair; the full dense extension remains unproved.

### Cycle absorbers and the finite absorber

[`Overfull/Dense/CycleAbsorber.lean`](Overfull/Dense/CycleAbsorber.lean) defines the listed absorber edges for every positive length `ℓ`. An injective placement in a host graph, together with the presence of those edges, gives both triangle decompositions, edge-disjointness from the cycle, exactly `9ℓ` absorber edges, and exactly `2ℓ+1` support vertices outside the cycle. Each absorber edge meets a vertex outside the cycle.

[`Overfull/Dense/FiniteAbsorber.lean`](Overfull/Dense/FiniteAbsorber.lean) proves the subsequent finite absorber lemma from the actual dense-host hypotheses. It enumerates every locally balanced remainder on `U`, proves its decomposition into simple directed cycles, and places separate gadgets with pairwise disjoint auxiliary vertices. The resulting single absorber has both its default decomposition and a decomposition after adjoining any allowed remainder. Its edges avoid `G[Z]`, and its support outside `U` avoids `Z`.

[`Overfull/Dense/FiniteAbsorberSubgraph.lean`](Overfull/Dense/FiniteAbsorberSubgraph.lean) returns a literal mathlib subgraph whose vertex set is exactly its support, with the same actual edges and decompositions.

The complete edge-plus-auxiliary-vertex budget is `4h²2^(h²)`. The order threshold depends only on `h`, `η`, and `γ`, and is chosen before the graph, `ε`, `U`, or `Z`. The condition involving `ε` is expressed as `16hε ≤ γ`, which also includes `h = 0`. This proves the bounded finite absorber; the approximate integral packing and iterative absorption needed for the full dense extension remain unproved.

## The sharpness conclusion

For every odd integer `Δ ≥ 3`, Lean proves the existence of a connected simple graph satisfying

```text
|V(G)| = 4Δ + 5
Δ(G) = Δ
χ′(G) = Δ + 1
|E(G)| = 2Δ(Δ + 1),
```

with no `Δ`-overfull vertex set. The class-2 conclusion consists of a proof that no `Δ`-coloring exists and an explicit proper `(Δ+1)`-coloring. The no-overfull statement quantifies over every vertex subset.

For every real `c < 1/4` and natural `N`, the development constructs such a graph of order `n ≥ N` with `Δ(G) ≥ c*n`. The ratio `Δ/(4Δ+5)` approaches `1/4` from below. Thus a coefficient below `1/4` cannot support the proposed general coloring conclusion. These examples leave the exact boundary `Δ ≥ n/4` open.

[`docs/sharpness.md`](docs/sharpness.md) explains the complete checked construction and its proof modules.

## Reproducing the verification

The project pins Lean to `leanprover/lean4:v4.24.0`, mathlib to commit `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`, and all transitive dependencies in `lake-manifest.json`.

With Lean's version manager, Python 3, Git, and the standard `patch` command installed, run from the project root:

```sh
python3 scripts/setup_vizing.py
lake exe cache get Mathlib.Combinatorics.SimpleGraph.Matching Mathlib.Combinatorics.SimpleGraph.Coloring Mathlib.Combinatorics.SimpleGraph.Tutte Mathlib.Tactic Mathlib.Data.Real.Archimedean Mathlib.Data.Nat.Choose.Basic Mathlib.Analysis.Convex.Combination Mathlib.Analysis.Normed.Operator.Banach Mathlib.Analysis.Normed.Module.FiniteDimension Mathlib.Combinatorics.Hall.Finite
python3 scripts/verify.py
```

The first command fetches and verifies the pinned Vizing source. It can instead use a pristine local copy with `--source /path/to/upstream`. Once the prepared source is present, it verifies the local files without downloading them. Do not run `lake update` to reproduce the recorded versions; the committed manifest already supplies them.

The verification script checks the source pins, performs a strict build with `lake build --wfail`, and audits the transitive axioms of the proved declarations. It also checks that every project module is imported and that every assertion marked complete has an audited proof declaration.

The only permitted logical axioms are

```text
propext
Classical.choice
Quot.sound
```

The audit rejects any added axiom, `sorryAx`, or the additional axiom used by `native_decide`. Generated and private support theorems are included. The declaration count is therefore not a count of independently proved manuscript results.

[`verification/results.json`](verification/results.json) records the exact proof-source hashes, imported modules, proof declarations, dependency revisions, and axioms. Build and audit logs are in the same directory. A failed check removes any previous success report. The GitHub Actions workflow is configured to run the same commands; a local success report does not claim a remote Actions run or GitHub publication.
