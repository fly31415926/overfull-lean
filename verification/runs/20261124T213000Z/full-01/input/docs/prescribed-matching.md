# Retaining prescribed exceptional matching edges

`Overfull.prescribed_exceptional_core_matching` proves Lemma 4.8 of the
recorded manuscript. It returns an actual perfect matching omitting at
most `135720` prescribed edges.

## Exact hypotheses and conclusion

Let `G` be a finite simple graph covered by an exceptional set `Z` and
at most four core cliques, each disjoint from `Z`. Put `t = |Z|`.
Every core has more than `2t+4` vertices, and every exceptional vertex
has more than `2t+4` distinct neighbors outside `Z`. The graph has an
actual perfect matching. Let `M` be a matching whose every edge meets `Z`.

The theorem constructs a perfect matching `N` with

```text
(M.edgeSet \ N.edgeSet).ncard ≤ 135720.
```

This specializes to the manuscript's disjoint core cliques and prescribed
exceptional–core edges. The formal proof also permits overlapping core
cliques and prescribed edges with both endpoints in `Z`. It keeps the
manuscript's hypothesis that the original graph has a perfect matching.
No path, connectivity witness, component correspondence, or completion
feasibility assertion is an extra hypothesis of the public theorem.

## Construction

After deleting at most three vertices, every remaining exceptional
vertex has a surviving core neighbor. A graph on the core labels then
gives an actual connecting path with at most twelve vertices whenever
two cores are connected.

The finite witness construction recursively keeps paths avoiding
forbidden sets of up to three vertices. Across the at most six unordered
core pairs, its vertex set `W` has size at most

```text
6 * 12 * (1 + 12 + 12^2 + 12^3) = 135720.
```

Restrict `M` to the edges avoiding `W`, obtaining `M'`. The proof counts
actual omitted edges and shows that at most `|W|` were lost. It also shows
that `M'` covers at most `t` core vertices. Delete all vertices covered
by `M'` and check Tutte's inequality for every further vertex set `Y`:

- If `|Y| ≤ 3`, the retained paths preserve the core connectivity. Every
  component has a surviving vertex, and the removed matching edges give
  even changes to component orders. The original perfect matching supplies
  the required bound on odd components.
- If `4 ≤ |Y| < t+4`, the core-size and exceptional-degree bounds leave
  every surviving exceptional vertex attached to a core. There are at
  most four components.
- If `|Y| ≥ t+4`, there are at most `t+4` components, since every surviving
  core is a clique and at most `t` exceptional vertices remain.

Mathlib's proved Tutte theorem constructs a perfect matching on the
remaining vertices. Adjoining `M'` gives an actual perfect matching of
`G`, and the set-difference bound transfers to that final matching.

## Proof map

| Module | Content |
| --- | --- |
| `Overfull/ForbiddenSetWitness.lean` | Finite subfamily preserving avoidance of bounded forbidden sets, with exact size bounds |
| `Overfull/PrescribedMatching/ShortPaths.lean` | Actual twelve-vertex paths and the common witness of size at most `135720` |
| `Overfull/PrescribedMatching/Components.lean` | Attachment after deletion, component counts, survival, and actual connectivity preservation |
| `Overfull/PrescribedMatching/Matching.lean` | Matching restriction and union, component parity, induced-deletion identities, and Tutte completion |
| `Overfull/PrescribedMatching/Selection.lean` | The actual retained prescribed matching and all discarded-edge and covered-core bounds |
| `Overfull/PrescribedMatching.lean` | All three Tutte ranges and full Lemma 4.8 |

The strict Lean builds and scoped axiom audits permit only `propext`,
`Classical.choice`, and `Quot.sound`. This lemma does not complete the
subsequent exceptional-boundary reduction or the main theorem.
