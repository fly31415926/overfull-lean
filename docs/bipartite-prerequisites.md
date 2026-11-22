# Three prerequisites for bipartite robust-core factorization

This continuation proves three supporting results for the construction in
Section 6: reverse-direction robust expansion, the actual balanced exterior
coloring, and preservation of the ordinary-vertex neighborhood conditions
under a bounded core move. The full factorization Theorem 6.1, its stronger
Proposition 6.2, the robust absorber Theorem 6.3, and the dependent Lemmas 4.2
and 4.14 remain incomplete.

The three results below are complete statements with their displayed
hypotheses. They are not three additional completed numbered manuscript
assertions. The final build, transitive axiom audit, and exact source hashes
are recorded in `verification/results.json`.

## Recovery and scope of this branch

The source workspace from the preceding terminal continuation was absent
when this round began. The published repository contained the earlier
42-assertion checkpoint, and the saved ordinary-core archive supplied a
portable patch for local checkpoint `2fcbfc0b32396c82ef996c27ed3a13e636565a71`.
Applying that patch to its recorded published base
`d31af64653e765888d9024e3ca8c36226184f336` reconstructed the exact source tree
`aab43893d9b1d1e59a87171a33bceaf8a9c601da`. All 316 source hashes and 29
verification-input hashes matched the saved record.

This branch continues that recovered ordinary-core source, whose complete
numbered inventory was **42 of 69**. The later complete proofs of Lemma 5.12
and [Theorem 2.23](robust-partition.md) brought the total to **44 of 69**.
The [complete proof of Lemma 4.15](four-odd-decomposition.md) brings the
current total to **45 of 69**, with 24 remaining.
The later, previously reported
43-assertion terminal checkpoint `eafe3efc18bb66f6ad87f715e79f09e5abfe7798`
was unavailable and is not included in this branch's audit. Its source must
be recovered before the two continuations can be combined and audited
together. The public recovery checkout is preserved separately.

The manuscript read for this continuation is
`Four_Robust_Component_Cases_2026-11-21.tex`; the numbered inventory and
statement hashes remain pinned to the source identified in
`manuscript-source.json`.

## 1. Reverse-direction bipartite robustness

The source is [BipartiteReverse.lean](../Overfull/BipartiteReverse.lean).
Let the two sides have equal order `m`. Suppose

\[
0<\nu\le\tau\le1/4,\qquad 2\le\tau m,
\]

and the actual graph is a bipartite robust `(ν,τ)`-expander in the forward
direction. Then its actual pullback under `Sum.swap` is a bipartite robust
`(ν²/4,2τ)`-expander in the reverse direction. The public theorem is
`Overfull.IsBipartiteRobustExpander.reverse_sq`. The intermediate theorem
`reverse` retains the equivalent parameter `min (ν²) (ντ) / 4`.

This statement requires no separate minimum-degree condition. Its parameter
loss is fixed before the graph. The order condition implies positive side
order and handles the integer rounding in the proof.

### Proof

For a reverse test set `T`, let `Q` be its actual reverse robust
neighborhood and let `S` be the complement of `Q` in the original left
side. Every vertex of `S` has fewer than `μm` neighbors in `T`, where
`μ=min(ν²,ντ)/4`.

For every actual subset `U` of `S`, the proof counts the same crossing
edges in both directions. Forward robust neighbors of `U` lying in `T`
give a lower bound, while the definition of `S` gives the upper bound.
After cancellation this yields

\[
\nu\,|RN_{\nu}(U)\cap T|\le\mu m.
\]

Failure of reverse expansion makes `S` large enough for the lower end of
the forward expansion range. If `S` is also below the upper end, use
`U=S`. Otherwise choose an actual subset of size
`floor((1−τ)m)`. The hypothesis `2≤τm` makes this subset admissible and
absorbs its rounding loss. In each case the forward expansion lower bound
contradicts the displayed incidence inequality. All neighborhood sets and
the subset chosen for the second case are finite sets of vertices of the
given graph.

## 2. The actual balanced exterior coloring

The source is
[Exterior.lean](../Overfull/BipartiteFactorization/Exterior.lean), with
public theorem
`Overfull.BipartiteFactorization.exists_balanced_exterior`.

Let `G` be an even-order loopless `k`-regular multigraph, with `k>0`, and
let `C` be an actual embedded simple bipartite core on disjoint sets
`A,B` of the same order `m`. Each core vertex has core degree at least
`k−a`. The only coloring input is a proper `k`-coloring of the actual
complement of the core copies.

The theorem constructs a proper coloring of that same complement with:

- Every exceptional vertex covered by every color.
- Equal numbers of covered vertices in `A` and `B` for each color.
- Left-side coverage counts differing by at most two between colors.
- At most `2ma/k+4` core vertices covered by any one color.
- Even core footprint for each color.
- Exact vertex load: the number of color footprints containing a core
  vertex equals its degree in the actual core complement, and is at most
  `a`.

### Proof

Every embedded core copy meets each side once. Counting these actual
copies proves equality of the two core degree sums. Subtracting from the
equal regular-host degree sums gives equality of the exterior degree sums.
A core copy never meets an exterior vertex, so the latter retains degree
`k` in the complement. The host is even and the two core sides have equal
order; consequently the exceptional set has even order.

These derived properties supply the hypotheses of the already proved
balanced multigraph coloring theorem. The actual core degree lower bound
gives complementary degree at most `a`, which supplies both the footprint
size estimate and the exact load bound. Parallel copies remain distinct
throughout the construction. The new exterior coloring may interchange
the original color classes; it is not an extension theorem preserving
every initially assigned exterior label.

## 3. Neighborhood conditions after a bounded core move

The source is
[Moves.lean](../Overfull/BipartiteFactorization/Moves.lean). Its public
theorems are `bounded_move_with_ports` and `core_move_with_ports`, in
`Overfull.BipartiteFactorization`.

For a vertex `x` and a target set `X`, `G.edgesTo x X` counts actual edge
copies, whereas `neighborsIn G x X` is the image of those copies under
their other-end map. Thus it counts distinct neighbors. The latter is not
substituted for the incidence count when parallel edges are present.

Let `G` be a loopless `k`-regular multigraph. Put `U=A∪B` and move a set
`Y⊆U` out of the core. Write `t=|Y|` and
`c_x=d_G(x,U)`. Before the move, each ordinary exceptional vertex satisfies
`c_x≥βk` and either

\[
c_x-|N_G(x)\cap U|\le a,
\]

or has at least `βk` distinct neighbors in each side. The bounded special
set `Z₀` is exempt, as in Proposition 6.2.

For a simple core supported on `U`, complementary core degrees at most
`a`, and an actual proper `k`-coloring of its complement, the following
explicit budgets suffice:

\[
\beta\le1,\qquad 3(a+t)<k,\qquad
2at\le\beta k,\qquad2t\le\beta k.
\]

The theorem constructs a coloring of the new complement, proves its
degree bound `a+t` at every retained core vertex, and proves that every
ordinary exceptional vertex after the move satisfies the same two
alternatives with `β/2` and `a+t`. This includes the newly moved vertices.
The new exceptional cardinality is exactly the old one plus `t`. Equal
deletions from equal sides preserve their equal cardinalities.

### Proof

An old exceptional vertex and a core vertex have at most `a` parallel
copies between them: every such copy lies outside the old core and is
counted in the complementary degree at its core endpoint. Therefore
moving `t` core vertices removes at most `at` incidences from an old
exceptional vertex. It removes at most `t` distinct neighbors from either
side.

The repeated-incidence quantity cannot increase when the target set
shrinks. The proof establishes this by partitioning both the actual copy
set and its neighbor image, and observing that every removed neighbor
accounts for at least one removed copy. Thus the first alternative
survives directly; the second survives by the distinct-neighbor loss
bound.

A newly moved core vertex retains at least `k−a−t` incidences into the
remaining core. Simplicity bounds the loss of its core edges by `t` and
charges every repeated incidence to an old complementary copy. It
therefore satisfies the first alternative. The previously proved bounded
core-move theorem supplies the actual coloring and degree bound of the
new complement.

Finally, `exists_move_budgets` fixes a positive density `α`, positive
reserve `β`, and a bound `L` on `t`, and chooses `ε>0` and `n₀` before
the graph. Whenever `m≥n₀`, `k≥αm`, `0≤a≤εm`, and `t≤L`, all three
displayed numerical budgets hold. Hence they can be discharged by the
usual small-error and large-order choices; they are not unexplained
properties of a supplied moved graph.

## Remaining factorization work

Subsequent continuations supply the finite representative, palette,
correction-capacity, and selected-graph coloring steps described in
[bipartite-localization.md](bipartite-localization.md), and the
[two-family construction](bipartite-two-families.md) now constructs both
selected families and their exact remaining exterior coloring from
finite supply conditions. Its total footprint load across all groups
equals the original core degree. The further
[sampling continuation](bipartite-sampling.md) proves the actual
uniform laws, weighted moments, capped means, and nonlinear
graph-score variance for independent samples in disjoint parts. It
constructs simultaneous disjoint palettes from explicit marginal
failure budgets. The full graph-specific score mean, combined
application estimates, and uniform parameter and boundary budgets
remain to be established.

These three results establish concrete prerequisites used in the
preparation and spanning construction of Section 6. The actual bipartite
regularity setup, simultaneous inputs for the localized exterior
families, special path systems, robust absorber, and final decomposition and reconstruction
remain to be formalized.

Once Theorem 6.1 is available, the recovered
`OrdinaryFactorization.exists_uniform_bipartite_reduction` supplies the
actual reduction needed for Lemma 4.2. The proved
`OneCore.even_core_complement` then reduces the one-apex graph in the
boundary argument to an even core with exactly two outside vertices,
allowing Lemma 4.14 to follow directly from Lemma 4.2 and the existing
boundary reconstruction. These later implications still require an
actual coloring of the whole residual.
