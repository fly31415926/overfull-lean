# Complete robust partition: Theorem 2.23

`Overfull.robust_partition` proves the full assertion labelled
`bip:part:imported` in the manuscript. This completes one additional numbered
theorem and brought that checkpoint's coverage to **44 of 69**. The subsequent
[complete proof of Lemma 4.15](four-odd-decomposition.md) brings the current
total to **45 of 69**. The remaining 24 numbered assertions, including the
main theorem, are not claimed as complete.

The implementation contains **71 public theorem proofs in nine modules**.
These supporting declarations collectively prove one numbered assertion.
The exact strict build, transitive axiom inventory, and source hashes are
recorded in [the verification report](../verification/results.json).

## Uniform statement and actual graph output

For every `α > 0`, `0 < τ < 1/2`, and function `f` positive on `(0,1)`,
the theorem chooses an order threshold `n₀` and a positive tolerance `γ₀`
before the vertex type, its finite instance, and the graph. If a finite
simple graph has order `n ≥ n₀`, actual minimum degree `d = δ(G)`, and

\[
\alpha n\le d,\qquad \Delta(G)\le d+\gamma_0n,
\]

it constructs real parameters and an actual vertex partition satisfying

\[
\gamma_0\le\rho\le\nu\le\tau,
\qquad \rho\le f(\nu).
\]

The returned `PartitionConclusion` has all four manuscript clauses:

| Clause | Checked conclusion |
| --- | --- |
| Ordinary pieces | Each actual induced graph `G[U]` is a robust `(ν,τ)` expander with at least `√ρ n` vertices. The robust-neighborhood normalization is the order of that induced graph. |
| Almost bipartite pieces | Each whole part is the union of two disjoint ordered shores `A,B`, each of size at least `√ρ n`, with shore-size difference at most `ρn` and `e_G(A)+e_G(B)+e_G(A∪B,(A∪B)ᶜ) ≤ ρn²`. |
| Internal degrees | Every whole part has an explicit exceptional set `Z` of at most `ρn` vertices. Every other vertex has at least `d−ρn` actual neighbors in that part. |
| Weighted component count | With `q` ordinary pieces and `ℓ` almost bipartite pieces, `q+2ℓ ≤ floor((1+ρ^(1/3))*n/d)`. |

The partition is represented by a list of `Piece.ordinary U` and
`Piece.bipartite A B` constructors. Its flattened list of ordinary sets
and bipartite shores is pairwise disjoint and covers all vertices. This
also gives a partition by the whole pieces. `ordinaryCount` and
`bipartiteCount` count the actual constructors, and
`rank_eq_weighted_count` proves that the shore rank is `q+2ℓ`.

The statement uses actual `SimpleGraph.minDegree` and `maxDegree`, actual
induced graphs, actual edge sets, and actual neighbor counts. No partition,
expansion theorem, splitting theorem, or final counting inequality is an
input assumption.

### Stronger parameter features

This proof permits **`n₀ = 1`** for the conclusion stated in Theorem 2.23.
The fixed positive almost-regularity tolerance can be very small; no
quantitative efficiency is asserted.

Only positivity of `f` on `(0,1)` is used. Thus the manuscript's
nondecreasing functions from `(0,1)` to `(0,1)` are included without using
their monotonicity or upper bound. The real-valued function in Lean may
be extended arbitrarily outside that interval: positive `γ₀ ≤ ρ ≤ ν`
and `ν ≤ τ < 1/2` ensure every relevant evaluation lies inside it.

The subsidiary `RobustPartition.exists_uniform_partition` permits any
real degree lower bound `d` with all degrees in `[d,d+γ₀n]`. The public
theorem specializes it to the graph's actual minimum degree.

## Proof construction

### 1. Choose every scale before the graph

Set `a = min α 1` and `K = ceil(2/a)`. A finite backward construction
chooses scales `ρᵢ,νᵢ` for `0 ≤ i ≤ K`, all positive, satisfying

\[
\rho_i\le\nu_i\le\tau,\qquad
\rho_i\le f(\nu_i),\qquad
\rho_i\le a^2/4,\qquad \rho_i\le1.
\]

The errors increase with the stage, and adjacent scales have the margins

\[
\rho_i^2\le\nu_i,\qquad
100\rho_{i+1}^2\le\tau a^2,\qquad
200\nu_i\le a\rho_{i+1}^2.
\]

For example, a backward step first chooses
`νᵢ = a*ρᵢ₊₁²/1000` and then chooses `ρᵢ` below both `νᵢ/2` and
`f(νᵢ)/2`. The construction begins below `τ*a²/1000`. The common
tolerance is `γ₀ = ρ₀²`, which is positive and at most every `ρᵢ` and
`νᵢ`. The scale theorem contains no graph or vertex-type parameter.

### 2. Split a failed actual expansion test

An ordinary block `U` carries a size bound `|U| ≥ an/2` and a small
ambient cut. The proved induced-graph bridge translates failure of
robust expansion into an actual subset `S ⊆ U` whose robust neighborhood
is too small, with the threshold normalized by `|U|`.

`nonexpanding_block_split` constructs disjoint sets `P,Q` with union
exactly `U` and with both sizes at least `an/2`. It proves one of:

- Both new ordinary cuts are at most `μn²`.
- The two shores have imbalance at most `μn` and at most `μn²`
  off-opposite incidences.

The latter incidence count is

\[
\operatorname{bad}(P,Q)
=E(P,Q^c)+E(Q,P^c)
=2e_G(P)+2e_G(Q)+e_G(P\cup Q,(P\cup Q)^c).
\]

The proof uses the failed test and the ambient interval
`[d,d+γ₀n]` for degrees. It proves the split directly from finite
incidence counts; no external robust-partition conclusion is assumed.

### 3. Refine until every ordinary block expands

The initial state is the single ordinary piece containing all vertices.
At stage `i`, every piece has an error budget `ρᵢ²`, and every counted
shore has size at least `an/2`. A nonterminal ordinary piece is replaced
by either two ordinary pieces or one piece with two bipartite shores,
using the split theorem with `μ = ρᵢ₊₁²`.

Each replacement preserves disjointness and coverage and increases the
shore rank by exactly one. Untouched pieces remain valid because the
error scale increases. Since disjoint shores of size at least `an/2`
fit inside `n` vertices, the rank is at most `2/a`, hence at most `K`.
The proved finite bounded-rank argument forces a terminal stage `i < K`.
Every ordinary piece then expands at the common parameter `νᵢ`.

### 4. Derive the final size, degree, and counting bounds

At the terminal stage write `ρ = ρᵢ`. The coarse size bound and
`ρ ≤ a²/4` give the required `√ρ n` sizes. The squared incidence budget
`ρ²n²` implies all the manuscript error bounds because `ρ ≤ 1`.

For the internal-degree clause, each vertex with fewer than `d−ρn`
neighbors inside its whole part loses more than `ρn` incidences to the
outside. Summing those incidences against the cut budget `ρ²n²` bounds
the explicit set of such vertices by `ρn`.

Minimum-degree averaging gives the stronger lower size bound
`d−(2ρ²/a)n` for every ordinary set and every bipartite shore.
Summing over the disjoint shores, using the coarse rank bound and
`ρ ≤ a²/4`, proves

\[
(q+2\ell)d\le(1+\rho)n.
\]

Since `0 < ρ ≤ 1`, one has `ρ ≤ ρ^(1/3)`. Division by `d > 0`
and the natural floor give the exact manuscript bound. The natural
and integer floor conventions agree here because the argument is positive.

## Modules and public proof counts

| Module | Public theorem proofs | Responsibility |
| --- | ---: | --- |
| [Counting.lean](../Overfull/RobustPartition/Counting.lean) | 34 | Actual incidence identities, size bounds, exceptional sets, and sharp numerical count |
| [Induced.lean](../Overfull/RobustPartition/Induced.lean) | 8 | Actual induced robust-neighborhood transport and failed-test witness |
| [Split.lean](../Overfull/RobustPartition/Split.lean) | 2 | Quantitative ordinary/almost-bipartite splitting |
| [Pieces.lean](../Overfull/RobustPartition/Pieces.lean) | 18 | Actual partition representation, replacement, and coarse rank bound |
| [FiniteRefinement.lean](../Overfull/RobustPartition/FiniteRefinement.lean) | 1 | Termination from increasing bounded rank |
| [Scales.lean](../Overfull/RobustPartition/Scales.lean) | 1 | Uniform positive scale ladder |
| [Refinement.lean](../Overfull/RobustPartition/Refinement.lean) | 1 | Actual terminal partition construction |
| [Conclusion.lean](../Overfull/RobustPartition/Conclusion.lean) | 4 | All four quantitative manuscript clauses |
| [Theorem.lean](../Overfull/RobustPartition/Theorem.lean) | 2 | Uniform degree-bound theorem and actual minimum/maximum-degree specialization |

## Source match and scope

The assertion remains pinned to the November 20 manuscript inventory:
number **2.23**, label `bip:part:imported`, original lines **1452–1480**,
statement SHA256
`be076a6b6c07e78af1793be025ddfde0ac2b3360914be0360ff48fb5866dbf31`.

The same statement occupies lines **1600–1628** in
`Four_Robust_Component_Cases_2026-11-21.tex`, whose SHA256 is
`ae6adf685e38637f2a1f18f83e63d0c3d92898b77749c9c8da795447c49ce064`.
Its verbatim statement block, excluding the final newline, has the same
hash. The numbered inventory has not been rebased.

The manuscript cites Kühn–Lo–Osthus–Staden,
[*The robust component structure of dense regular graphs and applications*](https://web.mat.bham.ac.uk/D.Osthus/ham3conn_37.pdf),
Theorem 5.1 and its robust-partition conditions. The construction here
proves the conclusion actually stated in manuscript Theorem 2.23 by
finite refinement. It does not assert the additional bipartite robust
expansion or all cleanup properties of the broader published theorem.

The critical-graph application in Proposition 2.24 still needs its
unformalized degree estimate and the remaining application arguments.
The ordinary and bipartite factorization theorems, approximate triangle
packing, and the main theorem remain unfinished. Completing Theorem 2.23
does not change their numbered status.
