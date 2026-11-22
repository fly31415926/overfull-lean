# Complete prescribed boundary extension: Lemma 4.14

**Lemma 4.14 is complete. The numbered inventory is 46 of 69, with 23
assertions remaining.** The public theorem
[`Overfull.boundary_extension`](../Overfull/BoundaryExtension/Full.lean)
constructs a proper coloring of every original edge copy incident with the
odd robust core and preserves every prescribed boundary label exactly.
The main theorem remains unverified.

The new proof supplies the actual one-apex factorization that was the
explicit missing input to `boundary_extension_reduction`. Its direct
one-apex and two-apex construction uses the proved cut, coloring, repair,
and packing results. The full general Lemma 4.2, Corollary 4.6, and Theorem
6.1 remain open; none is assumed in this proof.

## Source identity

The manuscript assertion is Lemma 4.14, label `three:lem:boundary`. The
numbered inventory remains pinned to
`Four_Robust_Component_Cases_2026-11-20.tex`, identified in
[manuscript-source.json](manuscript-source.json). Its statement occupies
lines 3119–3128 and has SHA256
`67baedd4ae2e0451a8842fd27ea0976f50db94c9054eacd2f5dd40ce2cfa21e3`.
The statement at lines 3267–3276 of the inspected November 21 source has
the same hash. The inventory has not been rebased.

The [source mapping](boundary-extension-full-source.json) records both
source identities, the public declaration, the module hashes, and the
required proof declarations. The
[semantic review](boundary-extension-full-semantic-review.md) checks the
source clauses, parameter order, original-copy accounting, and the
alternative to the source's invocation of Corollary 4.6. The exact strict
build and transitive axiom audit for the recorded checkpoint are bound to
source hashes in [verification/results.json](../verification/results.json).

## Full statement and quantifier order

Fix

```text
0 < α ≤ 1,  0 < γ,  0 < ν ≤ τ ≤ α/8.
```

The theorem chooses a positive error tolerance `ε` and an order threshold
`m₀` before the host, core, degree, error, or prescribed coloring. Its input
is a loopless multigraph `G` with finitely many edge copies and an odd
finite core vertex set `U`, with `m = U.card ≥ m₀`. An embedded simple
graph `C.graph` on `U` is an ordinary `(ν,τ)`-robust expander. The input
satisfies

```text
degree_G(v) = d                    for every v ∈ U,
α*m ≤ d,
0 ≤ a ≤ ε*m,
d-a ≤ degree_C(v)                 for every v ∈ U.
```

The supplied `BoundaryColoring G U d` properly colors the actual copies in
`G.cutEdges U` with `Fin d`. Every color has exactly one or three boundary
copies, and at least `γ*m` colors have one copy. Properness is required at
all original endpoints, including those outside `U`.

The conclusion is

```lean
∃ full : (retainedGraph G U).EdgeColoring d,
  ∀ e : G.cutEdges U,
    full.color (boundaryLift G U e) = c.color e
```

`retainedGraph G U` contains precisely the original copies with at least
one endpoint in `U`. The output therefore colors all required interior
and boundary edges. The final equation retains the input label on each
individual original boundary copy. Copies with both endpoints outside
`U` are outside the extension problem.

The host need not be regular outside `U`, and the ambient vertex type need
not be finite. The core is finite, the edge-copy type is finite, and the
contracted graph has finite vertex type `U ⊕ Unit`. Parallel copies are
retained throughout; no step substitutes simple adjacency for their
multiplicity.

## 1. Complete the triple colors and obtain the exact one-apex graph

The earlier public theorem
[`boundary_extension_reduction`](../Overfull/BoundaryExtension/Reduction.lean)
remains the first part of the full construction. It derives the packing
inputs from the actual prescribed coloring.

A boundary edge has exactly one core endpoint. Properness makes that
endpoint map injective within each class, so its core footprint has the
same size as the class. The number of footprints containing a core vertex
is its actual boundary degree. The embedded-core identity

```text
degree(complement of coreEdges C, v) + degree(C.graph, v)
  = degree(G, v)
```

bounds that load by `a`. If `q` is the number of triple colors, the
singleton/triple partition gives

```text
singletonColors.card + tripleColors.card = d,
q ≤ floor(d-γ*m).
```

The proved ordinary packing theorem constructs pairwise edge-disjoint
core matchings perfect outside the three-vertex footprints. Joining each
to its prescribed boundary class covers every core vertex exactly once.
These completed triple classes retain their original labels and their
original exterior endpoints.

Deleting their exact union leaves degree `h = d-q` at every core vertex.
The surviving boundary copies are in bijection with the original singleton
colors. Hence their number is exactly `h`, with `γ*m ≤ h`, and their
prescribed labels are distinct. The surviving embedded simple core has
minimum degree at least `h-a` and retains proved ordinary robustness.

The construction keeps only surviving copies incident with `U` and maps
all exterior endpoints to one apex. This produces an actual `h`-regular
multigraph on `U ⊕ Unit`, with even order and the same odd core. The
existing small-cut argument also proves that the contraction has no
`h`-overfull set. The new factorization theorem constructs its coloring
from regularity and the robust core; it does not require a separately
assumed no-overfull or factorization result.

## 2. Factor the one-apex graph while preserving a useful moved vertex

[`OneCore.exists_uniform_one_apex_factorization`](../Overfull/OneCore/Factorization.lean)
now proves the required full coloring of a regular graph with one exterior
vertex and an odd dense robust core. Its constants precede the graph.

The proof moves one ordinary core vertex `y` to the exterior. The core
becomes even, the exterior consists exactly of the old apex and `y`, and
`even_core_complement` constructs a proper coloring of its actual
exceptional complement. Deleting the one core vertex gives the proved
core-error and robust-expansion bounds.

The moved vertex must retain a linear incidence supply into both shores
of the later bipartite residual. Two actual choices establish this:

1. **Choose the prescribed pairs from its original neighbors.**
   `MovedNeighbors.lean` identifies its distinct simple-core neighbors in
   the surviving core and maps them to actual host copies. The finite
   theorem in `NeighborPairing.lean` pairs those neighbors internally,
   apart from at most one vertex, and pairs the remaining population.
   Every cut splitting these pairs contains at least half the neighbor
   set, rounded down, on each shore. The already proved paired-cut theorem
   therefore supplies a robust balanced cut with this additional property.
2. **Choose the first completed labels from the two actual incidence
   rows.** `ApexPalette.lean` selects balanced numbers of labels from the
   moved vertex's two shore rows. Properness supplies the exact
   correspondence between its incident copies and their colors.
   `ApexChoices.lean` proves the resulting residual row counts. The core
   matchings used to complete those colors cannot remove extra incidences
   at the exterior vertex `y`.

The first-half construction and residual reduction now accept these
chosen pairs and labels. They construct actual perfect matchings and the
actual regular residual, with a balanced robust bipartite core and
arbitrarily small side-normalized error. The moved vertex retains at least
`(α/100)` times the side order in each actual shore row. The original apex
does not need such a two-sided supply.

`ResidualShores.lean` identifies the core pulled back along the shore
indexing with the precise cut-sides graph carrying the proved expansion
estimate. Its ambient shore images are exactly the sets used in the
incidence bounds. The resulting graph and counted copies are unchanged.

## 3. Construct the two-apex factorization

[`TwoApexFactorization.exists_uniform_two_apex_factorization`](../Overfull/TwoApexFactorization/Theorem.lean)
uses a balanced bipartite core of side order `m`, regular host degree `k`,
core degree at least `k-a`, and exactly two exterior vertices. One exterior
vertex has at least `λ*m` incidences into each shore. Its parameter domain is

```text
0 < α < 1,  0 < λ ≤ α/4,  0 < ν ≤ τ < α/16.
```

There is no extra restriction comparing the robust range `τ` with `λ`.
The existing bipartite range-reduction and packing results provide the
needed smaller range. The theorem assumes no coloring of the complement,
selected graph, or final residual.

It constructs

```text
r = ceil(λ*m/4),
q = k-r.
```

The uniform order threshold handles rounding and gives `q ≥ α*m/2` and
`k ≤ 2q`. The two rows of the supplied apex both have size at most `q`; at
least one row of the other apex has size at most `q`. Choosing which apex
joins the left augmented shore makes all mandatory same-shore incidences
fit the `q`-color selection. This exchanges only the apex assignments,
leaving the original forward robust core unchanged.

Let `b` be the common number of copies from either apex into the core;
regularity proves these two counts agree. `Selection.lean` constructs an
actual set `F` containing every exceptional copy internal to the core,
every mandatory same-shore apex copy, enough further apex-to-core copies,
and exactly `q-b` apex-to-apex copies, with natural subtraction. Both
selected apex degrees are exactly `q`, and each selected apex-to-core
degree is exactly `min q b`. The selected degree at every core vertex is
at most `a`. Every unselected original copy crosses the augmented
bipartition.

The error choice proves `2a < q` and `2a < min q b`.
`Balance.lean` applies the proved multigraph fan criterion to construct a
proper `q`-coloring of `F`. The initially colored inactive residue consists
only of copies between the two apices and is colored by König's theorem.
The fan argument therefore does not assume the selected coloring it is
meant to construct.

Regularity and the actual bipartite unselected graph give equal selected
degree sums on the two core shores after the equal apex contributions are
removed. The proved balanced-coloring theorem then makes each selected
color's core footprint balanced and bounds its size by `2*m*a/q + 4`.
Its incidence load at each core vertex is the actual selected degree,
bounded by `a`.

The uniform fixed-footprint bipartite packing theorem completes all `q`
selected colors. Each resulting class is a perfect matching of the entire
host, and distinct classes are disjoint on original copy identities.
Exactly `q` incidences are deleted at every vertex. The whole remaining
graph is a subgraph of the explicitly bipartite unselected host, regular
of degree `k-q`. König supplies its coloring, and disjoint palettes give
an actual `k`-coloring of the whole original two-apex graph.

## 4. Restore every prescribed original label

The obtained two-apex coloring is reconstructed through the first-group
perfect matchings to color the contracted one-apex graph. At its apex,
regularity makes the colors of all remaining boundary incidences distinct.
The proved palette permutation sends each of those colors to the
corresponding original singleton label.

The coloring is pulled back to the retained original vertices and edge
copies. Properness at the original exterior vertices follows from the
prescribed boundary coloring. The completed triple classes are then
reinserted with their original labels. The singleton and triple palettes
are disjoint and partition the original `Fin d` palette.

The final wrapper takes `β = min γ 1`. The boundary reduction gives
`0 < θ ≤ σ ≤ β/20`, which satisfies the one-apex theorem's range bound
`σ ≤ β/8`. The final input error is the minimum of the reduction and
factorization errors; the final order threshold is their maximum. These
choices are made before the original graph and prescribed coloring.
`BoundaryReduction.extend` is now applied to a constructed coloring of
its precise contraction, discharging its previously explicit argument.

## Proof map

| Obligation | Main files or declaration |
| --- | --- |
| Original boundary classes, footprints, and singleton/triple counts | [BoundaryData.lean](../Overfull/BoundaryExtension/BoundaryData.lean), [Triples.lean](../Overfull/BoundaryExtension/Triples.lean) |
| Actual triple completion and exact surviving robust core | [Packing.lean](../Overfull/BoundaryExtension/Packing.lean), [Assembly.lean](../Overfull/BoundaryExtension/Assembly.lean), [Residual.lean](../Overfull/BoundaryExtension/Residual.lean) |
| Exact singleton boundary and one-apex contraction | [SurvivingLabels.lean](../Overfull/BoundaryExtension/SurvivingLabels.lean), [Contraction.lean](../Overfull/BoundaryExtension/Contraction.lean), [ContractionCuts.lean](../Overfull/BoundaryExtension/ContractionCuts.lean) |
| Moved vertex, prescribed neighbor pairs, and retained incidence rows | [MovedNeighbors.lean](../Overfull/OneCore/MovedNeighbors.lean), [NeighborPairing.lean](../Overfull/OneCore/NeighborPairing.lean), [ApexChoices.lean](../Overfull/OneCore/ApexChoices.lean), [ApexPalette.lean](../Overfull/OrdinaryFactorization/ApexPalette.lean) |
| Uniform reduction retaining both rows and exact shore transport | [OneCore/Reduction.lean](../Overfull/OneCore/Reduction.lean), [ResidualShores.lean](../Overfull/OneCore/ResidualShores.lean) |
| Actual selected copies and constructed balanced coloring | [TwoApexFactorization/Selection.lean](../Overfull/TwoApexFactorization/Selection.lean), [Balance.lean](../Overfull/TwoApexFactorization/Balance.lean), [Shores.lean](../Overfull/TwoApexFactorization/Shores.lean) |
| Uniform core completion and actual bipartite remainder coloring | [TwoApexFactorization/Packing.lean](../Overfull/TwoApexFactorization/Packing.lean), [Completion.lean](../Overfull/TwoApexFactorization/Completion.lean), [Theorem.lean](../Overfull/TwoApexFactorization/Theorem.lean) |
| Full one-apex factorization | [OneCore/Factorization.lean](../Overfull/OneCore/Factorization.lean), `exists_uniform_one_apex_factorization` |
| Prescribed-label restoration and original-copy reassembly | [Palette.lean](../Overfull/BoundaryExtension/Palette.lean), [Colors.lean](../Overfull/BoundaryExtension/Colors.lean), [Reassembly.lean](../Overfull/BoundaryExtension/Reassembly.lean) |
| Full Lemma 4.14 with uniform constants | [BoundaryExtension/Full.lean](../Overfull/BoundaryExtension/Full.lean), `Overfull.boundary_extension` |

## Scope of the completion

This proves the full boundary extension asserted in Lemma 4.14. The
broader ordinary-core Lemma 4.2, bounded-input Corollary 4.6, Theorem 6.1,
and its spanning-setup and absorber infrastructure remain separate
obligations. The two-apex theorem requires the derived two-shore incidence
supply at one apex; it does not assert factorization for every arbitrary
bounded exceptional configuration.

The full terminal Proposition 4.16 also remains open. Its all-even and
mixed-parity branches still require their own joining-edge constructions
and general factorization input. The completed Lemmas 4.14 and 4.15 supply
substantial inputs to the four-odd-part branch, but they do not constitute
an already assembled proof of every terminal case. The
[next-target document](next-verification-target.md) records the remaining
work and the acceptance conditions for another numbered assertion.
