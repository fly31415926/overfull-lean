# Nonregular coloring with one, two, or three ordinary robust cores

The endpoint `Overfull.ordinary_cores_coloring` constructs a coloring of the
original finite simple graph from one, two, or three ordinary robust cores.
Its statement matches the current manuscript's `three:thm:main` under the
manuscript's disjoint-partition convention. It permits an arbitrary palette
`k` at least the actual maximum degree, rather than only `k=Δ(G)`.

The [semantic review](ordinary-core-coloring-semantic-review.md) records the
exact current source comparison. The [source map](ordinary-core-coloring-source.json)
records every new public proof and its actual source hash. The genuine full
build, transitive axiom audit, frozen inputs and outputs, and preservation
checks are in [this run](../verification/runs/20261125T002000Z/). These actual
receipts determine kernel verification; source inspection alone does not.

## Public statement

Fix `α>0` and `0<ν≤τ≤min(α,1)/2048000`. There exist `ε>0` and `n₀>0`,
chosen before the graph, core count, palette, and error, such that the following
holds. Let `G` be a finite simple graph of order `n≥n₀`, with every degree at
most `k` and `k≥αn`. Suppose that `G` has no `k`-overfull vertex set.

Let `I` be any finite index type with `1≤|I|≤3`. The actual core sets `U i`
are pairwise disjoint and, together with `Z`, cover all vertices. Each has
order at least `αn` and contains an embedded spanning robust `(ν,τ)`-expander
`H i` of minimum degree at least `k-a`. If `a+|Z|+1≤εn`, the theorem returns
`Nonempty (Overfull.EdgeColoring G k)`: a proper coloring on every original
unordered edge of `G`.

The theorem does not need an original parity assumption or regularity.
It derives `a≥0` from the actual embedded degrees when needed. It also permits
`Z` to overlap the core sets and removes that overlap internally.

## Construction and quantitative transfer

For three cores in the range `k<n`, the total deficiency satisfies
`sum_v(k-d_G(v))≤n(a+|Z|)`. The previously proved auxiliary-completion theorem
adds exactly `n` vertices and actual edges, obtaining a simple `k`-regular
graph on `2n` vertices with no overfull set. The auxiliary vertices form the
fourth robust core. Every original edge copy is retained.

The density and original core-size hypotheses become the required bounds at
density `α/2` on `2n` vertices. The auxiliary core error is at most
`a'=a+|Z|+1`. The full regular error budget is
`a'+|Z|+1≤2(a+|Z|+1)`, so one original tolerance supplies the regular theorem's
budget. The shared robust parameter is the minimum of the original parameter
and the parameter constructed by the auxiliary completion. The complete
regular four-core theorem produces the coloring, which is restricted to the
original graph.

The one-core and two-core theorems already construct their completions.
Taking the minimum of the three positive tolerances and the maximum of their
order thresholds makes the result uniform over all three counts. The final
endpoint normalizes an arbitrary density with `β=min(α,1/2)` and relabels the
actual finite core index type by `Fin |I|`. For `k≥n`, the proved finite
Vizing bound gives `Δ+1≤n≤k` colors and the palette is enlarged.

| Declaration | Scope |
| --- | --- |
| `Overfull.three_core_nonregular_factorization` | Actual three-core auxiliary construction, for `k<n`, with the preprocessing nonnegative-error and disjoint-cover hypotheses. |
| `Overfull.three_core_coloring` | Three-core maximum-degree specialization, deriving nonnegative error and cleaning exceptional overlap internally. |
| `Overfull.ordinary_cores_normalized_factorization` | One common tolerance and order threshold for the three possible core counts. |
| `Overfull.ordinary_cores_coloring` | Current-source endpoint with arbitrary positive density, finite core labels, and palette bound. |

## Source identity and numbered coverage

The recovered current theorem block has SHA-256
`43b21f5ea1e98772ee258c145ddb206ca37e72ffa34b7eb13de25739823509b3`.
The older inventory's Theorem 1.2 is pinned to a different statement hash,
`9b5f67b17f74bda5e830dba24fcf319fb825981566e6282ece5ff73302ae07ac`.
The exact older theorem text was not recovered. Therefore this proof is
recorded as a separately sourced current-manuscript theorem; it does not
silently replace or promote the older assertion.

All 69 older numbered records remain identical, including the 51 complete
statuses. The new mathematical theorem is additional progress beyond that
frozen count. The full main theorem remains unverified. The remaining native
fixed-pattern obstruction for the five-exception multigraph statement is
described in the final section of the semantic review.
