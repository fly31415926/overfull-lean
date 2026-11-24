# Replacing a dense core

`Overfull.robust_core_replacement` proves Lemma 3.3 of the recorded
manuscript. It constructs the replacement graph and proves all of its
degree, expansion, exterior-edge, and overfull-set conclusions.

## Statement and quantifiers

Fix `β > 0` and `0 < τ ≤ min(β/16,1/4)`. The theorem chooses `μ > 0`,
`ξ > 0`, and an order threshold before the finite vertex type and graph.

Let `G` have order `n` above that threshold, all degrees at most `k`,
`k ≥ βn`, and no `k`-overfull set. Let `U` have even order `2m`, where
`m ≥ βn`. The original core `H` is a simple graph on the actual subtype
`U`, is contained in `G[U]`, and has every degree at least `k−a`, with
`a ≥ 0` and `a+1 ≤ ξn`.

The output consists of actual graphs `H'` on `U` and `G'` on the ambient
vertex type. The operation `Replacement.lift` embeds the core's edges
into that ambient type. The theorem proves

```text
G' = (G \ lift U H) ⊔ lift U H'.
```

The inserted and retained edge sets are disjoint. The graph `H'` is a
robust `(μ,τ)`-expander, with every degree at least `k−2a−1`. Every degree
of `G'` is at most `k`, every exterior edge is retained, and `G'` has no
`k`-overfull vertex set.

## Construction and preservation of overfull inequalities

Set `r = δ(H)−1`. Lemma 2.21 constructs an actual `r`-regular robust graph
`R` on `U`; the proof uses the positive density `min(β/2,1/2)` and the
even order of `U`. Its robust parameter is fixed before the error tolerance.
Delete from `R` the edges of `G[U]` that do not belong to `H`. At most `a`
edges are lost at each vertex. The proved deletion-stability theorem gives
the claimed expansion and minimum degree of the resulting `H'`.

The ambient graph identities account exactly for every removed and
inserted edge. Since the inserted degree is less than the original core
degree, the ambient degree bound follows.

An overfull set in `G'` would have an odd number of vertices and a cut of
size less than `k`. Actual robust core cuts have size greater than `k`
whenever both shores contain at least two core vertices. Thus the set's
intersection with `U`, or its complement in `U`, has at most one vertex.

For the empty set and a singleton, both core edge counts are zero. On
the whole core and the core minus one vertex, the handshaking identities,
regularity of `R`, and minimum degree of `H` show that the replacement
contributes no more induced edges than `H`. The exact ambient induced-edge
identity then contradicts the original overfull inequality.

## Proof map

| Module | Content |
| --- | --- |
| `Overfull/Replacement/Graph.lean` | Actual lifted graphs, exterior disjointness, exact degree and induced-edge identities, and embedded core cut comparison |
| `Overfull/Replacement/SmallShores.lean` | All four small or complementary-small shore comparisons and the overfull preservation argument |
| `Overfull/Replacement/Parameters.lean` | Positive error tolerance and a uniform order threshold for the degree and cut estimates |
| `Overfull/Replacement/Construction.lean` | Actual forbidden-edge deletion, degree loss, and robust expansion |
| `Overfull/Replacement.lean` | Uniform regular realization and full Lemma 3.3 |

The complete theorem passed the strict Lean build and a scoped axiom
audit, with only `propext`, `Classical.choice`, and `Quot.sound`.
Constructing this comparison graph does not provide its later edge
coloring or prove the main theorem.
