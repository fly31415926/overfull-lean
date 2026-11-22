# Full ordinary-core factorization: Lemma 4.2

The public results are `Overfull.ordinary_core_factorization` and
`Overfull.ordinary_core_one_factorization` in
[`OrdinaryFactorization/Full.lean`](../Overfull/OrdinaryFactorization/Full.lean).
That file was recovered exactly. Eleven missing supporting modules have
been reconstructed; see the [reconstruction record](checkpoint-reconstruction.md).

## Exact conclusion and quantifiers

Fix a positive density parameter `α`, positive robust expansion parameters
`ν ≤ τ ≤ min α 1 / 8`, and a natural exterior bound `s`. The theorem first
chooses an error tolerance `ε > 0` and an order threshold `m₀`. Only then
are the finite vertex and edge-copy types, loopless multigraph, core,
regular degree and error supplied.

The host is an even-order `k`-regular multigraph. Its embedded simple core
has an even vertex set `U` with `|U| ≥ m₀`, at most `s` exterior vertices,
degree at least `k-a`, density `k ≥ α|U|`, and the stated robust expansion.
The error satisfies `a ≤ ε|U|`. Nonnegativity of `a` follows from an actual
embedded core degree bound. The final input is a proper `k`-coloring of
the complement of the actual embedded core copies.

The output is a proper `k`-coloring of the entire original multigraph.
The factorization wrapper returns `k` actual perfect matchings, pairwise
disjoint as sets of original edge copies, whose union is all copies.
Parallel copies retain distinct identities throughout.

## Constructed proof stages

| Stage | Source modules | Mathematical content |
| --- | --- | --- |
| Balanced paired cut | `PairedCut/BalancedFootprints` | Every even footprint of size at most `s` is balanced with probability at least `2^-s`; a good paired cut balances at least a `2^-(s+1)` fraction of the supplied footprints. |
| First completed colors | `OrdinaryFactorization/BoundedCutReserve`, `FirstHalfBounded`, `ReductionBounded` | Choose the equitable complement coloring before the cut, retain the footprint count, and construct the first perfect matchings and their exact robust bipartite residual. |
| Common exterior split | `BoundedExterior/MatchingSplit`, `ExteriorClasses`, `ReserveLabels`, `ReserveChoice` | Each balanced exterior matching admits a balanced exterior split. At most `2^s` splits occur. Pigeonhole a common split, retain a linear palette, and choose first labels avoiding that palette. |
| Reserve transport | `BoundedExterior/ResidualReserve` | Compress original unselected labels while preserving their original colors and crossing property on every inherited exterior copy. |
| Selected coloring | `BoundedExterior/SelectedColoring` | Keep all internal complementary copies and all nonreserved exterior copies; preserve their exterior colors and extend the coloring across the sparse core. |
| Balanced completion | `BoundedExterior/Factorization`, `ReservedColors` | Derive equal selected core degree sums, balance color footprints and bound their sizes, complete them using robust bipartite packing, and color the genuinely bipartite residue by König. |
| Exact reconstruction | `OrdinaryFactorization/Full`, `BoundedExterior/ColorFactorization` | Reassemble the original coloring and partition all original copies into perfect matchings. |

The recreated proof uses `reserveDenominator s = 2^(2*s+4)` and retains
`floor(k / reserveDenominator s)` original labels. For sufficiently large
`k`, this is at least `k / (2 * reserveDenominator s)` and at most `k/8`.
All such bounds depend only on the initial fixed parameters. The reserve
is chosen before the first-group palette, which has size at most `3k/5`,
so the palettes can be made disjoint.

The residual selected-color theorem constructs its coloring rather than
assuming it. Its hypotheses require a linear selected palette and a linear
reserved palette. Sparse recoloring handles internal complementary copies;
all exterior vertices have exactly the selected degree. Equal exterior
shore sizes and regularity then give the core balance needed by the
existing packing theorem. The unselected exterior colors and the retained
bipartite core all cross the same augmented shores.

## Scope and evidence

The source statement remains pinned to Lemma 4.2 with SHA256
`480b2fb39565bc86acf278addac00ca843da67be5638db6b4328af1ddf08ea97`.
No full general bipartite factorization theorem, spanning setup, absorber,
selected-coloring oracle or residual factorization is assumed. The proof
uses a direct cleanup specialized to a bounded exterior.

See the [source and public proof map](ordinary-factorization-full-source.json),
[semantic review](ordinary-factorization-full-semantic-review.md), and
[fresh verification report](../verification/results.json). The complete
declaration map includes private and generated proof declarations as well
as the public results.
