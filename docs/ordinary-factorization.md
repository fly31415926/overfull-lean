# Ordinary-core factorization: general reduction and complete one-apex case

**The general Lemma 4.2 remains incomplete. The one-apex specialization
needed for Lemma 4.14 is now fully proved.**
`Overfull.OrdinaryFactorization.exists_uniform_bipartite_reduction`
constructs the general ordinary-core preprocessing. The new
[`Overfull.OneCore.exists_uniform_one_apex_factorization`](../Overfull/OneCore/Factorization.lean)
adds actual neighbor-pairing and palette choices, retains a two-shore
incidence supply at the moved ordinary vertex, and applies the new
constructed two-apex cleanup.

This specialization completes the prescribed boundary extension in
[Lemma 4.14](boundary-extension.md), bringing the numbered inventory to
**46 of 69**, with **23** remaining. The full Lemma 4.2, Corollary 4.6,
Theorem 6.1, and the main theorem remain unverified.

The earlier [reserved-remainder continuation](residual-factorization.md)
constructs the coupled numerical parameters and proves the complete final
packing stage through an exact oriented regular core. The missing input
remains the spanning setup, special path systems and robust absorber that
produce the required reservation and support whole-host reconstruction.
Those supporting results do not complete Lemma 4.2. The latest one-apex
proof instead supplies the particular factorization needed by the boundary
extension without the general Section 6 absorber.

This is a formalization status, not a finding of a defect in the
manuscript's mathematical proof. The source proof invokes Theorem 6.1;
the Lean development has not yet established that factorization theorem.

## Public construction and quantifier order

For `0 < α ≤ 1` and `0 < ν ≤ τ ≤ α/8`,
[`exists_uniform_bipartite_reduction`](../Overfull/OrdinaryFactorization/Reduction.lean)
chooses a positive crossing parameter `ξ` first. For every subsequently
requested positive error tolerance `η`, it chooses positive reserve,
repair, coloring, and input-error constants. For every requested minimum
side order, it then chooses an order threshold. All these choices precede
the arbitrary graph, embedded core, regular degree, degree error, and
initial exterior coloring.

The inputs are:

- An even-order finite loopless `k`-regular multigraph `G`, with its
  individual edge copies retained in the edge type.
- An even core vertex set `U` of sufficiently large order `m`.
- An actual embedded simple `(ν,τ)`-robust core `C.graph` on `U`, with
  minimum degree at least `k-a` and `k ≥ αm`.
- A real error `0 ≤ a ≤ εm`.
- An actual `k`-coloring of the complement of the embedded core copies.

No bound on the number of exterior vertices is needed for this
preprocessing. The host and core vertex sets remain unchanged, so a
given exceptional-cardinality bound carries to the residual graph.

The theorem constructs `FirstHalfData` and `BipartiteResidualData`:

- A balanced cut, a robust sampled reserve, and the actual internal
  graph outside that reserve.
- A proper internal coloring avoiding the selected fixed exterior
  footprints, followed by actual repaired matchings.
- `h` pairwise disjoint perfect matchings of the original host, with
  `h ≤ 3k/5` and `h ≥ αm/8`.
- The exact residual on the surviving original copies, of degree
  `k' = k-h ≥ 2k/5` and the same even vertex order.
- An actual embedded crossing core with equal sides of order `m/2`,
  robust parameters `(ξ/2,4τ)`, and minimum degree at least `k'-a'`.
- The error bound `0 ≤ a' ≤ η(m/2)` and residual density
  `k' ≥ (α/2)(m/2)`.
- A constructed proper `k'`-coloring of the complement of that crossing
  core, retaining every inherited compressed exterior color.
- A reconstruction function from an **explicit actual coloring of the
  whole residual graph** to a proper `k`-coloring of the original host.

The reconstruction function does not assert existence of its argument.
The supplied complementary coloring covers only the complement of the
crossing core, not the whole residual host.

## A proved substitute for the specialized list-coloring step

The manuscript uses Kahn's asymptotic list edge-coloring theorem to
respect colors forbidden by fixed exterior incidences. This continuation
proves the specialized consequence needed here by a separate elementary
finite argument. It does not formalize the general Kahn theorem.

Start with an actual proper `r`-coloring, embed its palette into an
`h`-color palette, and suppose each edge forbids at most `b` target labels.
The finite theorem applies whenever a positive integer `t` satisfies

```text
n * b^t < t!
b + 2*(t-1) < h-r.
```

The proof counts permutations of the target labels. Properness makes the
initial colors at a vertex distinct. For any specified `t` incident
edges, at most `(h-t)! * b^t` permutations make all those edges conflict.
A union bound over the incident subsets and vertices yields a
permutation for which every vertex has fewer than `t` conflicting edges.
The case `t > h` is handled by the incident-degree bound. No independence
assumption is introduced.

The conflicting edges are recolored greedily using the `h-r` labels
outside the image of the entire initial palette. These labels are
unused by the unchanged edges. The second inequality supplies an
available permitted label at each greedy step. Every edge that was
already permitted retains its relabeled color.

[`AsymptoticBounds.lean`](../Overfull/ColoringExtension/AsymptoticBounds.lean)
proves a uniform choice of `t` when `b` is a sufficiently small multiple
of `n` and the additional palette has size `ceil(δn)`. The resulting
public simple-graph theorem constructs a coloring with

```text
Δ(J) + 1 + ceil(δn)
```

colors avoiding every supplied forbidden label. The initial coloring is
provided by the proved Vizing theorem. The generic multigraph version
continues to require an actual initial coloring; no Vizing bound for
arbitrary multigraphs is claimed.

The constraints supported by this result exclude a small number of
labels from one common enlarged palette. This specialized statement is
sufficient for the exterior-incidence constraints in Lemma 4.2.

## Balancing, deficits, and repair

[`Balance.lean`](../Overfull/ColoringExtension/Balance.lean) minimizes the
sum of squared class sizes over the finite set of feasible colorings.
When two classes differ by more than `f+1`, their union has enough
vertex-disjoint alternating components to find one avoiding the fixed
footprint of the smaller class. Switching it preserves all forbidden
vertex constraints and decreases the energy. The resulting class sizes
differ by at most `f+1`.

The unconstrained case gives an equitable exterior coloring. Exterior
vertices have full degree `k`, so each color covers each exterior
vertex exactly once. For the actual core footprint `F_i`, the proof gives

```text
k * |F_i| ≤ a*m + 2*k,
number of selected footprints containing v ≤ a.
```

Even host and core order imply even exterior order and hence even
footprint sizes. The initial exterior coloring is equitized; the result
does not claim to preserve its original labels during that preliminary
step. The selected labels are fixed after equitization.

[`Deficits.lean`](../Overfull/ColoringExtension/Deficits.lean) counts the
actual uncovered vertices and missing colors. The near-perfect theorem
keeps the rounding terms in

```text
D = κ*m + 1 + ceil(κ*m).
```

Uniform density and order bounds absorb these terms. The outputs satisfy
both the per-class and per-vertex smallness conditions of the already
proved reserve-repair lemma. The repaired family is therefore
constructed, rather than supplied as a hypothesis. The actual used
reserve union and released internal-edge union each have degree at most
`μm`.

## Cut, reserve, and exact residual bounds

The strengthened paired-cut theorem fixes its positive crossing
robustness constant before the requested degree tolerance. It gives
both side degrees within `δm` of half the original degree.
Side-specific reserve sampling is then combined on the same graph with
ordinary robust expansion. The reserve range is reduced on the original
host before sampling, and the reduced range may be chosen after the
reserve probability.

The actual internal graph has degree near `(1-p)k/2`, with spread at most
`a/2 + 6δm`. Its rounded palette is computed from its actual maximum
degree, not posited as an independent integer with desired bounds.

After repair, a crossing core edge can have been removed only as a used
reserve edge. Thus at most `μm` crossing incidences are lost per vertex.
Since the side order is `m/2`, the corresponding bipartite loss parameter
is `2μ`. Choosing `4μ ≤ ξ` retains robustness `(ξ/2,4τ)`.

Every remaining same-side core edge is either in the reserve or was
released by its own original color class. Together with the surviving
original exterior copies this yields the actual complementary degree
bound

```text
a' = a + (p + 4δ + μ)*m.
```

The unselected exterior labels are compressed to exactly `k-h` labels.
All other edges of the new complement have both endpoints in `U`.
The proved greedy extension colors them when `2a' < k-h`, retaining
the inherited colors.

For a requested `η > 0`, the public reduction chooses

```text
p = min(α/100, η/100, 1/4),
μ = min(μ₀/2, p, ξ/8).
```

The first-half construction gives `ε ≤ p` and `δ ≤ pα/32`. Since
`α ≤ 1`, these imply `a' ≤ 4pm`, hence both `a' ≤ ηm/2` and
`2a' < k-h`. All choices occur before the input graph.

## Complete one-apex specialization

The public theorem
[`OneCore.exists_uniform_one_apex_factorization`](../Overfull/OneCore/Factorization.lean)
uses `0 < α ≤ 1` and `0 < ν ≤ τ ≤ α/8`. It chooses `ε > 0` and `m₀`
before an arbitrary finite loopless regular multigraph, its odd core,
regular degree, error, and single exterior vertex. From

```text
Uᶜ = {z},
degree_G(v) = k for every vertex,
k ≥ α*U.card,
0 ≤ a ≤ ε*U.card,
degree_C(v) ≥ k-a,
C.graph is an ordinary (ν,τ)-robust expander,
```

it constructs `Nonempty (G.EdgeColoring k)`. No original complementary
coloring, selected coloring, or full residual coloring is an assumption.

The proof moves a vertex `y` of the odd core outside and uses the checked
`even_core_complement` construction. The remaining core is even and its
exterior is exactly `{z,y}`. Two additional choices strengthen the
ordinary preprocessing for this graph:

- [NeighborPairing.lean](../Overfull/OneCore/NeighborPairing.lean) pairs the
  moved vertex's original simple-core neighbors internally, apart from
  at most one vertex. Every cut splitting those prescribed pairs gives
  both shores at least half that neighbor count, rounded down.
  [MovedNeighbors.lean](../Overfull/OneCore/MovedNeighbors.lean) connects
  the counted neighbors to actual original incidence copies.
- [ApexPalette.lean](../Overfull/OrdinaryFactorization/ApexPalette.lean)
  chooses balanced numbers of first-group labels from the moved vertex's
  two shore rows. [ApexChoices.lean](../Overfull/OneCore/ApexChoices.lean)
  proves the exact residual incidence identity and a positive linear
  supply in both rows. The core matching completions remove no extra
  copies at this exterior vertex.

The public `exists_uniform_first_half_with_choices` and
`exists_uniform_bipartite_reduction_with_choices` preserve those actual
choices. The earlier general APIs remain available as their special
cases. [OneCore/Reduction.lean](../Overfull/OneCore/Reduction.lean) composes
the moved-core bounds, pair construction, palette choice, and residual
bounds with uniform constants. [ResidualShores.lean](../Overfull/OneCore/ResidualShores.lean)
identifies the exact pulled-back crossing graph and the same ambient
shore images appearing in the retained-incidence estimates.

The output is now sufficient for
[`TwoApexFactorization.exists_uniform_two_apex_factorization`](../Overfull/TwoApexFactorization/Theorem.lean).
That theorem has exactly two exterior vertices and requires a positive
linear supply from one of them into both core shores. It constructs a
selected graph containing every noncore internal copy and all apex copies
incompatible with an augmented bipartition, with equal selected degree
at the two apices. The multigraph fan criterion supplies its coloring;
equal selected side-degree sums permit balanced coloring. Robust
bipartite packing completes its small footprints. The actual whole
remaining host is then bipartite and regular, so König colors it.
This conclusion is stronger than merely obtaining a bipartite core or a
coloring of its complement.

The parameter order also remains uniform. The one-core reduction first
fixes `ν₁,τ₁,ξ` with `τ₁ ≤ α/512`. The two-apex theorem is applied with

```text
density fraction = α/4,
apex supply fraction = α/100,
robust neighborhood parameter = min(ξ/2,4τ₁),
robust range = 4τ₁.
```

Its required error tolerance is passed to the ordinary reduction before
that reduction's reserve and coloring parameters are chosen. Its minimum
side order is passed before the final original order threshold is chosen.
The resulting residual coloring is supplied to the actual reconstruction
function, yielding the full coloring of the one-apex host.

Finally, `Overfull.boundary_extension` applies this theorem to the exact
contraction constructed by the earlier boundary reduction. Its palette
restoration preserves every original prescribed boundary label. The
[boundary-extension notes](boundary-extension.md) give the complete
statement and proof map.

## Module map and remaining general obligation

| Construction | Main modules |
| --- | --- |
| Finite list extension, permutation count, conflict repair | `ColoringExtension/{Greedy,Permutation,ConflictCount,Repair,Finite}` |
| Uniform simple-graph feasibility | `ColoringExtension/{AsymptoticBounds,VertexConstraints,Simple,Uniform}` |
| Fixed-footprint balancing and deficit control | `ColoringExtension/{BalanceComponents,Balance,Deficits,Exterior,NearPerfect}` |
| Quantitative cut and simultaneous reserve | `PairedCut/{QuantitativeSampling,Quantitative}`, `OrdinaryRandomReserveSides`, `OrdinaryFactorization/{Geometry,CutReserve,CutReserveBounds}` |
| Actual class conversion, repair, and first-group construction | `OrdinaryFactorization/{MatchingBridge,ColorRepair,UniformColorRepair,ExteriorSelection,Assembly,FirstHalfData,FirstHalf}` |
| Actual residual core, degrees, palettes, and coloring | `OrdinaryFactorization/{Residual,Palette,ResidualColoring,ResidualGeometry,ResidualInternal,ResidualCore,ResidualComplement}` |
| Uniform public reduction | `OrdinaryFactorization/Reduction` |

For the full Lemma 4.2, the remaining factorization obligation is Theorem
6.1 (`ext:thm:robust`), or another proved result covering every residual
configuration permitted by that lemma. The general residual can have
same-side edges and an arbitrary bounded set of exceptional vertices.
The two-apex cleanup above does not cover all those inputs: it uses exactly
two exterior vertices and a proved two-shore incidence supply at one of
them. The generic preprocessing theorem does not automatically produce
that additional structure for an arbitrary bounded exceptional set.

The source's spanning bi-setup, special path systems, robust absorber,
and final reconstruction for Theorem 6.1 remain separate formalization
work. The checked reserved-remainder stage is still available once its
actual reservation and colored exterior inputs are constructed. Its
existence theorem does not by itself construct those inputs.

The full fixed-pattern and bounded-input results, including Corollary
4.6, therefore remain open. Proposition 4.16 still needs its all-even and
mixed-parity terminal factorizations and the complete joining-edge
assembly. The new one-apex theorem and full Lemma 4.14 resolve one
specific application; they do not establish every terminal case.

Supporting constructions are registered separately from complete numbered
assertions. This checkpoint adds the full Lemma 4.14, producing the current
**46/69** count; the general ordinary-core Lemma 4.2 is not counted.
