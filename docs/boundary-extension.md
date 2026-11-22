# Boundary-color extension: proved components and the remaining factorization

**Lemma 4.14 remains unverified. The completed assertion count remains
42 of 69.** The public theorem `Overfull.boundary_extension_reduction`
constructs the prescribed triple-color completions, preserves actual edge
copies under an apex contraction, proves the required no-overfull
conclusion for that contraction, and restores an actual residual coloring
to the prescribed original palette. It does not yet supply the
factorization of the contracted residual.

The manuscript statement is `three:lem:boundary`, lines 3119–3128 of the
pinned November 20 source. Its statement SHA256 is
`67baedd4ae2e0451a8842fd27ea0976f50db94c9054eacd2f5dd40ce2cfa21e3`.
The entire source is identified separately in
[`manuscript-source.json`](manuscript-source.json). The statement and proof
of this lemma, and those of Lemma 4.2, are unchanged in the November 21
manuscript inspected during this continuation.

## The extension problem

The host is a loopless multigraph with a finite type of edge copies. A
simple robust graph is embedded on an odd finite vertex set `U`, of order
`m`. The embedding specifies a distinct original host copy for each core
edge. Every core vertex has ambient degree `d`, and the embedded core has
minimum degree at least `d-a`. The host need not be regular outside `U`.

The input `BoundaryColoring G U d` colors the actual copies in `G.cutEdges U`
properly with `Fin d`. Every color has exactly one or three boundary copies,
and at least `γ*m` colors have one copy. Properness is imposed at all
original vertices, including exterior endpoints.

The required final coloring concerns exactly the original edges with an
endpoint in `U`. Its palette is still `Fin d`, and its color on every
original boundary copy must equal the prescribed color. Edges with both
ends outside `U` are outside this extension problem. Keeping a separate
edge-copy type is essential: the contraction may create parallel edges
even when the original host is simple.

## Uniform reduction theorem

[`Reduction.lean`](../Overfull/BoundaryExtension/Reduction.lean) proves
`Overfull.boundary_extension_reduction`. Given
`0 < α ≤ 1`, `0 < γ`, and `0 < ν ≤ τ ≤ α/8`, it chooses
`ε`, `θ`, `σ`, and `m₀` before every graph, embedded core, degree,
error, and prescribed boundary coloring. The output parameters satisfy

```text
0 < ε, 0 < θ ≤ σ, 0 < σ ≤ τ, σ ≤ min γ 1 / 20.
```

For every input above with `m₀ ≤ U.card`, odd core order,
`α*U.card ≤ d`, core robustness `(ν,τ)`, and
`0 ≤ a ≤ ε*U.card`, the theorem constructs
`Nonempty (BoundaryReduction G U d a γ θ σ c)`. Its hypotheses contain
neither completed matchings, a robust residual, nor a coloring or
factorization oracle.

The retained density is controlled by `β = min γ 1`. The proof chooses
`σ = min τ (β/100)`, asks the triple-packing theorem for robustness at
that range, and then sets `θ = min θ₀ σ` and
`ε = min ε₀ (β/20)`. The order threshold is the maximum of the packing
and contraction-cut thresholds. These choices ensure that the small-cut
theorem applies at the density of the retained graph, independently of
the original density parameter `α`.

## Actual boundary classes and packing

[`BoundaryData.lean`](../Overfull/BoundaryExtension/BoundaryData.lean)
defines the boundary classes and their core footprints. A boundary edge
has exactly one endpoint in `U`. Properness makes this endpoint map
injective within each color class, giving

```text
footprint(i).card = classEdges(i).card.
```

`footprint_incidence_eq_degree` proves that the number of colors whose
footprints contain a fixed core vertex is exactly its actual boundary
degree. `selected_footprint_incidence_le` gives the corresponding bound
for an injectively selected subpalette.

The embedding bridge in
[`OneCore/Complement.lean`](../Overfull/OneCore/Complement.lean) records
the core copies as `coreEdges C` and proves the exact identity

```text
degree(complement of coreEdges C, v) + degree(C.graph, v)
  = degree(G, v).
```

Core copies are disjoint from the boundary. Consequently
`boundary_degree_le_error` in
[`Triples.lean`](../Overfull/BoundaryExtension/Triples.lean) derives the
boundary incidence bound `a` using ambient regularity only at vertices of
`U`. No bound on exterior vertex degrees is needed for this step.

Let `q` be the number of triple colors. Their actual labels are enumerated
by `tripleLabel : Fin q ↪ Fin d`. Since every color has size one or three,

```text
singletonColors.card + tripleColors.card = d,
q ≤ floor(d-γ*m).
```

Each selected footprint has size three, hence has the parity of the odd
core order. The order threshold ensures that three is within the packing
allowance. The per-vertex footprint load is bounded by `a` and therefore by
the chosen error allowance.

[`Packing.lean`](../Overfull/BoundaryExtension/Packing.lean), theorem
`pack_fixed_forbidden_sets`, applies the proved adaptive finite-prefix
packing theorem to the actual fixed footprint family. It chooses positive
error and output robustness parameters, and an order threshold, before
the graph, degree, number of colors, and forbidden sets. Its result
`CorePacking` contains actual pairwise edge-disjoint core matchings,
perfect outside their prescribed footprints, and robustness of the exact
remaining core graph.

`exists_triple_core_packing` derives every packing hypothesis from the
boundary-extension input. In particular, it obtains the upper core degree
bound from the actual embedding into the ambient graph; the lower bound
is the supplied core error condition. The singleton reserve supplies the
packing horizon. The result assumes neither the completions nor a robust
residual graph.

`CorePacking.degree_identity` also records the exact degree equation

```text
remaining.degree(v) + q
  = originalCore.degree(v) + number of selected footprints containing v.
```

Thus the remaining simple core has minimum degree at least `d-q-a`.

## Completing classes in the original host

[`Assembly.lean`](../Overfull/BoundaryExtension/Assembly.lean) maps each
packed internal matching through the core's specified edge embedding and
unites those actual copies with the original boundary class. The resulting
`completedColor` is a matching in the original multigraph. It covers every
core vertex exactly once, has precisely its prescribed boundary copies,
and is edge-disjoint from every other completed class.

The internal and boundary pieces are vertex-disjoint because the internal
matching avoids the boundary footprint. Original boundary properness
handles all exterior vertices. Every completed edge has an endpoint in
`U`, so no unrelated exterior edge is selected.

[`Residual.lean`](../Overfull/BoundaryExtension/Residual.lean) defines the
actual residual host exactly as

```text
T = univ.biUnion completedColor,
R = G.restrictEdges Tᶜ.
```

`remainingAmbient_degree_add` proves that deleting these classes removes
one incidence per selected color at each core vertex, giving ambient
degree `h = d-q` on `U`. `coreCopy_survives_iff` identifies precisely which
original embedded core copies survive. `remainingEmbeddedCore` therefore
embeds the packing's actual remaining simple graph into this exact
residual host, with degree at least `h-a` and the packing's robust
parameters.

[`SurvivingLabels.lean`](../Overfull/BoundaryExtension/SurvivingLabels.lean)
constructs an edge-copy-preserving bijection between the surviving
boundary and the original singleton palette. The premise that exactly
the triple-colored boundary copies were deleted is supplied by
`completedTriples_boundary`. The actual boundary count
`residual_cutSize_eq_sub` is consequently `h`, and `residualLabel` is
injective on surviving boundary copies. These are conclusions of the
constructed deletion, not extra residual assumptions.

## The edge-copy-preserving contraction and its cuts

[`Contraction.lean`](../Overfull/BoundaryExtension/Contraction.lean)
first retains exactly the original copies with an endpoint in `U`, then
maps every exterior endpoint to one apex. Its vertex type is `U ⊕ Unit`.
The original retained graph and the contracted graph use the same edge
type, `RetainedEdge`.

The proofs establish all of the following directly:

- Contraction creates no loop, because every retained edge has a core
  endpoint and distinct original endpoints remain distinct at that end.
- Incidence and degree at each core vertex are preserved exactly.
- Apex incidences correspond bijectively to original boundary copies.
- The apex degree is the actual boundary size.
- `contractCore` embeds the original simple core into the contracted host
  without changing its degrees or robust parameters.
- An odd core gives an even contracted order.

For the actual residual above, the contraction is therefore `h`-regular
of even order, with one exterior vertex and a simple robust core of degree
at least `h-a`.

[`OneCore/Cuts.lean`](../Overfull/OneCore/Cuts.lean) proves the uniform
theorem `robust_one_exterior_no_overfull`. Its core-order-normalized
conditions include `τ ≤ α/20`, `α*|U| ≤ h`, and
`a ≤ α*|U|/20`. The host upper-degree bound needed by the small-cut theorem
is derived from the simple core and its degree error. The theorem does
not assume that the ambient multigraph is simple.

If an odd cut were smaller than `h`, the proved small-cut theorem would
give a shore with at most one core vertex. Both shores are odd because the
whole host order is even. With at most one exterior vertex, that shore has
at most two vertices and hence is a singleton. Its cut is exactly `h`, a
contradiction. `no_overfull_of_odd_cuts` then rules out all overfull vertex
sets, including the even sets in the definition.

[`ContractionCuts.lean`](../Overfull/BoundaryExtension/ContractionCuts.lean)
applies this result to the actual contraction. No factorization hypothesis
is used to prove its cut inequalities or no-overfullness.

## Palette restoration and exact reassembly

[`Palette.lean`](../Overfull/BoundaryExtension/Palette.lean) proves that a
proper coloring with a finite palette uses every palette color exactly
once at a vertex whose degree equals the palette cardinality. The actual
incident edge copies give an explicit palette bijection. Prescribed
distinct labels can also be embedded into a larger original palette,
allowing previously removed labels to stay unavailable.

Given an actual `h`-coloring of the exact residual contraction,
[`Colors.lean`](../Overfull/BoundaryExtension/Colors.lean) aligns its
colors with the distinct prescribed singleton labels. Pullback preserves
properness at every original vertex: original incidence implies incidence
at its contracted image, and the edge-copy map is the identity. Injectivity
of the vertex map is unnecessary. The restored coloring uses only the
surviving prescribed labels.

[`Reassembly.lean`](../Overfull/BoundaryExtension/Reassembly.lean), theorem
`reassemble_deleted_colors`, combines that actual residual coloring with
the completed classes. It accepts the actual matching classes, their
disjointness and exact boundary membership, and a residual coloring which
avoids the selected labels. It returns an actual
`EdgeColoring (retainedGraph G U) d` and proves:

- Exact agreement on every original boundary copy.
- Exact selected labels on every completed matching class.
- Exact preservation of the residual coloring on surviving copies.

The result proves properness at exterior vertices as well as at core
vertices. This is a proved implication from an actual residual coloring;
it is not an existence theorem for that coloring.

## Component interfaces

All declarations below are in `Overfull.BoundaryExtension`, except the
public theorem in `Overfull` and the listed `OneCore` declarations in
`Overfull.OneCore`.

| Construction or obligation | Main declarations |
| --- | --- |
| Uniform construction from the original prescribed coloring | `Overfull.boundary_extension_reduction` |
| Original boundary copies, prescribed labels, and core footprints | `BoundaryColoring`, `BoundaryColoring.footprint_card`, `BoundaryColoring.footprint_incidence_eq_degree` |
| Exact triple enumeration and reserve horizon | `BoundaryColoring.tripleLabel`, `BoundaryColoring.tripleLabel_range`, `BoundaryColoring.triple_horizon` |
| Fixed finite packing and its actual residual | `CorePacking`, `pack_fixed_forbidden_sets`, `CorePacking.degree_identity` |
| Derive triple packing from the manuscript input | `boundary_degree_le_error`, `exists_triple_core_packing` |
| Assemble actual original-host matching classes | `completedColor`, `completedColor_isMatching`, `completedColor_covers_uniquely`, `completedColor_boundary`, `completedColor_disjoint` |
| Exact residual host and simple-core embedding | `completedUnion`, `remainingAmbient`, `remainingAmbient_degree_add`, `remainingEmbeddedCore`, `coreCopy_survives_iff` |
| Surviving singleton labels and actual boundary size | `BoundaryColoring.singletonBoundaryEquiv`, `BoundaryColoring.residualLabel_injective`, `BoundaryColoring.residual_cutSize_eq_sub` |
| Actual contraction, retained copies, degrees, and core | `retainedGraph`, `contract`, `boundaryApexEquiv`, `contract_regular`, `contractCore` |
| Derived odd-cut inequalities and no-overfullness | `OneCore.robust_one_exterior_no_overfull`, `exists_contraction_cut_threshold` |
| Restore labels from an actual contracted coloring | `restoreSingletonLabels`, `restoreSingletonLabels_boundary`, `restoreSingletonLabels_range` |
| Reinsert actual completed color classes | `reassemble_deleted_colors` |
| Even-core shortcut for a one-apex host | `OneCore.restrictCore`, `OneCore.restrictCore_edges`, `OneCore.even_core_complement` |

[`Result.lean`](../Overfull/BoundaryExtension/Result.lean) defines
`BoundaryReduction`, recording the actual completed classes and deleted
set, exact residual degrees and boundary size, retained density, an
embedded robust residual core, and the regular even-order non-overfull
contraction. Its `extend` field accepts an actual coloring of that precise
contraction and returns the required original extension. Existence of a
contracted coloring is not a field. The public uniform theorem constructs
this structure from the original input. Its helper
`extend_from_completed_triples` performs the actual palette restoration
and reassembly once a coloring of the returned contraction is supplied.

| Required fact | `BoundaryReduction` field |
| --- | --- |
| Actual selected classes and exact deleted union | `completed`, `deleted`, `deleted_eq` |
| Matching, disjointness, and one incidence at each core vertex | `completed_matching`, `completed_disjoint`, `completed_covers` |
| Every selected edge belongs to the extension problem | `completed_retained` |
| Exact prescribed triple colors on boundary copies | `completed_boundary` |
| Exact residual core degree and boundary size `h=d-q` | `residual_degree`, `residual_boundary` |
| Positive linear degree reserve | `retained_density` |
| Actual surviving embedded simple core | `core`, `core_degree`, `core_robust` |
| Regular, even, no-overfull apex graph | `contracted_regular`, `contracted_even`, `contracted_no_overfull` |
| Original extension from an actual coloring of that graph | `extend` |

## A shorter route to the missing one-apex factorization

The manuscript invokes Corollary 4.6, whose proof uses Lemma 4.4 and the
Fan–Zhang compatible-circuit theorem. The special one-apex graph needed
here admits a more direct reduction to Lemma 4.2.

In `OneCore/Complement.lean`, `one_apex_complement_colorable` observes that
every vertex except the apex has degree at most `a` in the exceptional
complement. The proved `Multigraph.edgeColoring_one_high` supplies a
`k`-coloring when `2a < k`.

Choose a vertex `x` of the odd core and move it outside. The actual
`restrictCore C {x}` retains exactly the original core copies whose ends
both survive. `even_core_complement` proves, under `3(a+1) < k` and the
explicit vertex-deletion robustness bounds, that:

- The surviving core has even order.
- Its exterior consists of exactly the old apex and `x`.
- Its exceptional complement has an actual `k`-coloring, by the proved
  bounded-core-move theorem.
- Its minimum degree is at least `k-(a+1)`.
- Its robust parameters are `(ν/2,2τ)`.

Thus a proved Lemma 4.2 with exceptional bound `s=2` would factor this
graph directly. This route avoids the full fixed-pattern and compatible-
circuit machinery for Lemma 4.14. It does not prove Lemma 4.2 itself.

## Remaining dependencies and verification boundary

The full Lemma 4.2 (`two:lem:ordinary-special`) remains unproved, but its
ordinary-core preprocessing is now constructed by
`OrdinaryFactorization.exists_uniform_bipartite_reduction`. The theorem
chooses constants uniformly and constructs the actual first group of
perfect matchings, exact residual crossing core, and actual coloring of
that core's complement. See [ordinary-factorization.md](ordinary-factorization.md).

| Input or bridge | Current status |
| --- | --- |
| Accurate cut, side-specific reserve, equitable exterior classes, constrained balancing, and actual reserve repair | Proved and assembled in the uniform ordinary-core reduction. |
| Forbidden exterior colors in the internal graph | The needed specialized result is proved by permutation counting and greedy repair, using Vizing for the initial simple-graph coloring. The general Kahn theorem remains unformalized and is not assumed by this construction. |
| Theorem 6.1, `ext:thm:robust` | Still unformalized. It factors the whole residual regular multigraph through its bipartite robust core. The ambient residual is not necessarily bipartite, so König's theorem does not apply to it. |
| Robust decomposition and Hamilton decomposition infrastructure | The manuscript's inputs to Theorem 6.1, including the cited Granet lemma, still need formalization or a proved sufficient replacement. |

The required one-apex factorization is itself substantial. Deleting one
vertex from an even-order simple regular robust graph gives an odd core
with error at most one, so such a factorization theorem would already
cover ordinary regular robust graphs. Packing a fixed number of colors
with a positive linear reserve does not automatically factor the final
reserve.

The uniform boundary reduction now exposes the exact contracted residual
and proves that an actual coloring of that graph produces the desired
original extension. This establishes the reduction and transport steps;
it does not establish the missing coloring premise or the full numbered
lemma. No universal factorization oracle, axiom, or unproved external
theorem is supplied by these modules.

Count Lemma 4.14 only after an actual factorization of the constructed
contracted residual is derived, the uniform public extension theorem
preserves every prescribed original label, and the strict build,
transitive axiom audit, and semantic review pass. Until then the coverage
tally remains **42 of 69** and the main theorem remains unverified.
