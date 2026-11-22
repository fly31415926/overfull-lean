# Ordinary-core factorization: constructive reduction to the bipartite case

**Lemma 4.2 is not yet fully verified.** Its ordinary-core preprocessing
is now constructed by
`Overfull.OrdinaryFactorization.exists_uniform_bipartite_reduction`.
The remaining formalization is factorization of the resulting actual
regular multigraph through its bipartite robust core, as required by
Theorem 6.1. Lemma 4.14 and the main theorem also remain unverified.
The completed numbered-assertion count stays **42 of 69**.

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

## Module map and remaining obligation

| Construction | Main modules |
| --- | --- |
| Finite list extension, permutation count, conflict repair | `ColoringExtension/{Greedy,Permutation,ConflictCount,Repair,Finite}` |
| Uniform simple-graph feasibility | `ColoringExtension/{AsymptoticBounds,VertexConstraints,Simple,Uniform}` |
| Fixed-footprint balancing and deficit control | `ColoringExtension/{BalanceComponents,Balance,Deficits,Exterior,NearPerfect}` |
| Quantitative cut and simultaneous reserve | `PairedCut/{QuantitativeSampling,Quantitative}`, `OrdinaryRandomReserveSides`, `OrdinaryFactorization/{Geometry,CutReserve,CutReserveBounds}` |
| Actual class conversion, repair, and first-group construction | `OrdinaryFactorization/{MatchingBridge,ColorRepair,UniformColorRepair,ExteriorSelection,Assembly,FirstHalfData,FirstHalf}` |
| Actual residual core, degrees, palettes, and coloring | `OrdinaryFactorization/{Residual,Palette,ResidualColoring,ResidualGeometry,ResidualInternal,ResidualCore,ResidualComplement}` |
| Uniform public reduction | `OrdinaryFactorization/Reduction` |

The next factorization obligation is Theorem 6.1 (`ext:thm:robust`), or
a sufficient specialization covering the actual residuals above. The
whole residual multigraph may have same-side and exceptional edges;
König's theorem for bipartite multigraphs does not supply its factorization.
The manuscript's robust decomposition and Hamilton decomposition inputs
to Theorem 6.1 remain separate formalization work.

After that obligation is proved, its constants must be composed with
this reduction, and the resulting ordinary-core factorization must be
composed with the one-apex reduction and the boundary-extension
construction to finish Lemma 4.14. Supporting constructions alone do
not increase the completed numbered-assertion count.
