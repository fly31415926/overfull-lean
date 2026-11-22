# Lemma 5.12: complete dense link packing

`Overfull.Dense.LinkPacking.exists_tripartite_link_packing` proves the
complete numbered manuscript assertion `dense:link-packing`. The order
threshold is chosen from the fixed real parameters before the order,
vertex types, tripartite graph, and link family. The conclusion supplies
actual pairwise edge-disjoint matchings covering exactly the prescribed
links. Its implementation adds 96 public theorem proofs in ten modules.

This completed one additional numbered result, bringing that checkpoint to
**43 of 69**. The subsequent [robust-partition proof](robust-partition.md)
completed Theorem 2.23 and brought the total to **44 of 69**. The subsequent
[complete proof of Lemma 4.15](four-odd-decomposition.md) brings the current
total to **45 of 69**, with 24 remaining. The main overfull theorem remains
unverified. The earlier
palette and block work consists of supporting results inside unfinished
factorization statements; those supporting results did not increase the
numbered total.

## Exact scope

For real `b ≥ 1` and `0 < λ ≤ 1`, there exists a natural threshold `n₀`
such that the following holds for every `n ≥ n₀`. Let `G` be a simple
tripartite graph with three parts of size `n`, and let `Y₁,…,Yq` satisfy:

| Manuscript hypothesis | Formalized bound |
| --- | --- |
| Number of links | `q ≤ 3 b n` |
| Balanced two-part links | Each `Yi` omits one host part and contains `si` vertices from each remaining part |
| Actual induced minimum degree | `δ(G[Yi]) ≥ si/2 + 81 b λ^(3/2) n` |
| Distinct-link intersections | `|Yi ∩ Yj| ≤ 6 λ² n` for `i ≠ j` |
| Actual vertex incidence | Each vertex belongs to at most `2 b λ n` links |

The theorem returns `M : Fin q → G.toSimpleGraph.Subgraph` with:

- `(M i).IsMatching` for every link index;
- `(M i).verts = Yi` as an equality of actual vertex sets;
- pairwise disjoint `(M i).spanningCoe`, so different matchings share
  no actual graph edge.

A matching with vertex set exactly `Yi` is a perfect matching on the
induced graph `G[Yi]`: every vertex in the link has exactly one incident
matching edge, and both endpoints of every matching edge lie in the link.
The finite family is represented by a function on natural numbers whose
first `q` entries are used. Entries beyond that range impose no conditions.

The manuscript writes `1/n ≪ 1/b, λ ≤ 1`. The formal statement makes
the positive-parameter and joint upper-bound convention explicit as
`b ≥ 1` and `0 < λ ≤ 1`. It introduces no condition `λ ≪ 1/b`.
The underlying estimates in fact hold for every positive `λ`.

## Construction of the matchings

Write

\[
L=\lambda\sqrt\lambda\,n=\lambda^{3/2}n,
\qquad t=\lceil24bL\rceil.
\]

The finite sequential process offers `t` candidates at each round.
Whenever such a family exists, the candidates are actual matchings on
the current link, are pairwise edge-disjoint, and avoid all previously
selected edges. At a history for which they do not exist, the total
process uses empty matchings. This defines the process on every history;
it does not assume that every random history succeeds.

The source randomness is the actual uniform product law on
`Fin q → Fin t`. One candidate is selected in each round. Irrespective
of whether a history succeeds, its selected graphs are matchings, lie
within their corresponding links, and are pairwise edge-disjoint.

For a monitored link `Yi` and vertex `v`, a Boolean indicator records
whether the selected matching has an edge from `v` into `Yi`. The
proof bounds its conditional mean for every fixed preceding history:

- the link's own round contributes at most one;
- a round whose link omits `v` contributes zero;
- every other relevant round contributes at most
  `|Yi ∩ Ys| / t ≤ √λ/(4b)`.

The last inequality counts actual harmful candidates: different
candidates cannot use the same edge from `v`, and their other endpoints
lie in the actual link intersection. The incidence hypothesis therefore
bounds the sum of these conditional means by `L/2 + 1`.

`PredictableBernoulli.upper_tail_of_budget_half_add_one` proves, directly
from finite exponential moments, that the probability of more than `L`
hits is at most `exp(-L/24)` when `L ≥ 8`. The indicators may depend on
the entire previous history; no independence of those indicators is
assumed.

The count-to-graph identity `hits_count_eq_localLoad` identifies this
hit count with the exact number of neighbors of `v` in `Yi` in the
final used-edge graph. Summing the failure probabilities over every
link and every vertex gives

\[
\Pr(\text{some local load exceeds }L)
\le q\,|V(G)|e^{-L/24}
\le (3bn)(3n)e^{-L/24}.
\]

`Parameters.exists_threshold` chooses `n₀` uniformly so that `n > 0`,
`L ≥ 8`, and this last expression is less than one. Thus an actual
complete history with every local load at most `L` exists.

Every prefix uses a subset of the final used edges, so the same local
load bound holds before each selected matching. Dense bipartite Hall
arguments then construct all `t` candidates. The rounding bounds
`t ≤ 25bL` and `L+t ≤ 81bL` fit inside the original degree surplus.
Consequently no fallback occurs along the selected successful history,
and every selected matching covers its entire link.

The final theorem discharges the numerical failure budget, candidate
existence, conditional mean bounds, graph-load bounds, and all
tripartite-to-bipartite conversions. None is an extra hypothesis of the
numbered result.

## Modules and proof responsibilities

| Module | Proved responsibility |
| --- | --- |
| [`Probability/PredictableBernoulli.lean`](../Overfull/Probability/PredictableBernoulli.lean) | Actual finite product law, conditional exponential moments, and dependent-indicator upper tails |
| [`Parameters.lean`](../Overfull/Dense/LinkPacking/Parameters.lean) | Uniform threshold, real-power identity, candidate rounding, and numerical margins |
| [`Candidates.lean`](../Overfull/Dense/LinkPacking/Candidates.lean) | Actual dense bipartite matchings, repeated disjoint candidate construction, and harmful-candidate count |
| [`History.lean`](../Overfull/Dense/LinkPacking/History.lean) | Total sequential selection, including failed histories, with unconditional matching and edge-disjointness invariants |
| [`Feasible.lean`](../Overfull/Dense/LinkPacking/Feasible.lean) | Candidate existence from the actual local used-edge load and the original degree surplus |
| [`LocalProbability.lean`](../Overfull/Dense/LinkPacking/LocalProbability.lean) | Graph-derived conditional means, incidence budget, and actual link-load tail |
| [`Load.lean`](../Overfull/Dense/LinkPacking/Load.lean) | Exact hit-count identity and final-load-to-coverage induction |
| [`Packing.lean`](../Overfull/Dense/LinkPacking/Packing.lean) | Complete union bound, existence of a bounded history, and full finite matching packing |
| [`Tripartite.lean`](../Overfull/Dense/LinkPacking/Tripartite.lean) | Actual three-part geometry, local sides, and exact induced-degree conversion |
| [`Theorem.lean`](../Overfull/Dense/LinkPacking/Theorem.lean) | Uniform public theorem with the manuscript hypotheses and full matching conclusion |

## Statement provenance and verification

The pinned inventory is the November 20 manuscript. The exact Lemma
5.12 statement was compared with lines 4068–4079 of
`Four_Robust_Component_Cases_2026-11-21.tex` and is unchanged. Its
statement SHA256 is
`1d5d07d6cfa237c907e332ee99db407b81dd14a39c99ad0904939c710c8fe2f1`.
The full November 21 manuscript SHA256 is
`ae6adf685e38637f2a1f18f83e63d0c3d92898b77749c9c8da795447c49ce064`.
These are distinct hashes with distinct scopes.

The manuscript cites Lemma 9.1 with `r=3` in Barber, Kühn, Lo, Osthus,
and Taylor, *Clique decompositions of multipartite graphs and completion
of Latin squares*. The
[primary paper](https://babarber.uk/wp-content/uploads/2017/03/completing-latin-squares.pdf)
contains the matching-packing statement and random greedy proof on
pages 23–24. The Lean development proves the needed finite concentration
and graph construction locally; it does not import the paper's lemma
as an axiom.

The canonical validation record is
[`verification/results.json`](../verification/results.json). It records
the strict build, all-module transitive axiom audit, pinned dependencies,
and exact source and verification-input hashes for the published tree.
Only `propext`, `Classical.choice`, and `Quot.sound` are allowed by the
project audit. A declaration tally includes generated and private
declarations and is separate from the 43 complete numbered assertions.

## Remaining scope

Completing this imported matching-packing input does not finish the
dense tripartite decomposition theorem, the robust factorization
theorems, or the main overfull theorem. Those still require their
remaining statements and compositions. The current factorization
obligations are recorded in
[`next-verification-target.md`](next-verification-target.md).
