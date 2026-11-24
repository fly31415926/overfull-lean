# Robust realization and auxiliary completion

The development proves Lemmas 2.21 and 2.22 of the recorded manuscript.
Their public declarations are `Overfull.balanced_robust_realization` and
`Overfull.robust_auxiliary_completion`. The main theorem remains unproved.

## Prescribed robust degree sequences

For fixed `0 < δ < 1` and `0 < τ < 1/2`, Lemma 2.21 chooses a positive
robust parameter `ν` and an order threshold before the order `n` and the
degree sequence. Every sequence `d : Fin n → ℕ` above that threshold with

```text
δn ≤ d(v) ≤ n−1,
d(u) ≤ d(v)+1 for all u,v,
Even (sum_v d(v))
```

is realized by a simple graph on those same labels, with degree exactly
`d(v)` at every vertex and robust expansion with parameters `(ν,τ)`.
The pairwise degree inequality is the manuscript's spread-at-most-one
condition. No graph realization is supplied as a hypothesis.

The construction first realizes the multiset of degrees. Even base degrees
use a cycle power and disjoint long chords. Odd base degrees use a cycle
power with disjoint consecutive pairs removed. The complete graph is
handled separately. Each graph contains a cycle power of the required
linear radius after adding back a graph of maximum degree at most one.

A partition into consecutive blocks proves robust expansion. Every vertex
misses at most two vertices of its own block and each adjacent block: itself
and at most one deleted neighbor. A connected path on the blocks supplies
an additional block whenever the heavy blocks do not cover the graph.
The constants and threshold are uniform over the degree sequence.
Finally, a permutation places the larger degrees on the prescribed labels
and preserves both actual degrees and robust expansion.

| Step | Principal declaration |
| --- | --- |
| Exact degree of a cycle power | `Overfull.RobustRealization.cyclePower_degree` |
| Actual graphs on disjoint pairs | `Overfull.RobustRealization.pairGraph_degree` |
| Degree multiset, including all parity cases | `Overfull.RobustRealization.exists_degree_multiset` |
| Expansion from the consecutive blocks | `Overfull.RobustRealization.robust_of_blocks` and `robust_of_cyclePower` |
| Uniform robust parameter and order threshold | `Overfull.RobustRealization.exists_cyclePower_robust_parameters` |
| Relabeling preserves robust expansion | `Overfull.RobustRealization.robust_comap_equiv` |
| Complete labelled realization | `Overfull.balanced_robust_realization` |

## The auxiliary completion statement

Fix `0 < α < 1` and `0 < τ < α/24`. Lemma 2.22 chooses positive `ν, ε`
and an order threshold before the finite vertex and edge types, the
loopless multigraph `G`, and the natural degree bound `k`. Suppose that
`G` has order `n` above the threshold, every degree is at most `k`,
`αn ≤ k ≤ 2n`, and

```text
s = sum_v (k − degree_G(v)) ≤ εn².
```

Suppose also that `G` has no `k`-overfull vertex set. The construction uses
the least integer `m ≥ max(n,k+1)` with `m ≡ n mod 2` and puts
`b = ceil(s/m)`. It returns a loopless multigraph on `V ⊕ Fin m` satisfying
all the manuscript's conclusions:

- Its order is even and every vertex has degree `k`.
- The original vertices induce exactly `G`, retaining every parallel copy.
- Every added edge has multiplicity one in the whole completion.
- The auxiliary vertices induce a simple robust `(ν,τ)`-expander of
  minimum degree at least `k−b`.
- No vertex set is `k`-overfull.

The separate sum types distinguish original vertices from new vertices
and original edge copies from added copies. The edge type is

```text
E ⊕ (CrossEdges N ⊕ H.edgeSet),
```

where `CrossEdges N` has one element for each actual incidence `z ∈ N(v)`.
The original edge map is preserved on the first summand. The induced-edge
equalities and the simplicity of added edges are proved for this graph.

## Constructing the incidences and the core

The neighbor family `N` gives each original vertex exactly
`k−degree_G(v)` new neighbors. Vertices of deficiency one receive distinct
neighbors. A finite minimization of the sum of squared right loads then
balances all right loads while preserving this restriction: a load gap
of at least two permits an incidence transfer from a vertex whose
deficiency is not one. Such a transfer would strictly decrease the sum.
Consequently right loads differ by at most one and are at most `b`.

The auxiliary degrees are exactly `k−rightLoad(z)`. Their sum is even by
the parity of `m` and the original degree sum. The uniform choice
`ε = α/32`, together with the order threshold, gives `8b ≤ k`, `m ≤ 3n`,
and auxiliary minimum degree at least `(α/4)m`. Lemma 2.21 realizes these
degrees by a simple robust graph `H`. The threshold is also chosen so that
`k < ν²m²`.

## Cuts and odd sets

A cut with at least two auxiliary vertices on each side contains more
than `k` edges of `H`. For its smaller auxiliary shore of order `r`, the
case `r < τm` satisfies `r < k/8`, and simplicity gives

```text
cut_H(r) ≥ r(k−b−r+1) > k.
```

For `τm ≤ r ≤ m/2`, robust expansion supplies at least `νm` robust
neighbors outside the shore, each with at least `νm` neighbors inside.
The cut therefore has at least `ν²m² > k` edges.

It remains to check odd shores with zero or one auxiliary vertex, using
the complement when necessary. A shore with no auxiliary vertex has the
same induced edges as in `G`. For a shore `S ∪ {z}` with `S` even, the
deficiency-one restriction gives the actual incidence inequality

```text
2 * |{v ∈ S : z ∈ N(v)}| ≤ sum_{v ∈ S}(k−degree_G(v)) + 1.
```

The even parity of the relevant deficiency expression removes the final
one and gives the required odd-set inequality. Regularity then converts
these cut bounds into the absence of overfull sets of every order.

| Step | Principal declaration |
| --- | --- |
| Least auxiliary order with the required parity | `Overfull.AuxiliaryCompletion.auxiliaryOrder_le_of_le_of_mod_two` and `auxiliaryOrder_mod_two` |
| Balanced actual neighbor family | `Overfull.AuxiliaryCompletion.exists_auxiliary_neighbors` |
| Actual bipartite graph for that family | `Overfull.AuxiliaryCompletion.exists_balanced_incidence_graph` |
| The deficiency-one incidence estimate | `Overfull.AuxiliaryCompletion.twice_incidence_card_le_deficiency_sum_add_one` |
| Uniform construction of the robust auxiliary graph | `Overfull.AuxiliaryCompletion.exists_auxiliary_core` |
| Actual completed degrees | `Overfull.AuxiliaryCompletion.left_degree` and `right_degree` |
| Exact induced original and auxiliary edge copies | `Overfull.AuxiliaryCompletion.internal_original_edges` and `internal_auxiliary_edges` |
| Multiplicity one at every added edge | `Overfull.AuxiliaryCompletion.added_edge_simple` |
| More than `k` edges across each auxiliary cut with both shores of order at least two | `Overfull.AuxiliaryCompletion.core_cut_gt` |
| All odd-set inequalities for the actual completion | `Overfull.AuxiliaryCompletion.no_overfull` |
| Complete auxiliary-completion statement | `Overfull.robust_auxiliary_completion` |

These results construct the regular completion and prove its structural
and odd-set properties. They do not color the completion. The subsequent
ordinary-core coloring and extension arguments, and therefore the main
theorem, remain separate proof obligations.
