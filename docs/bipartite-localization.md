# Finite steps for localized exterior colorings

This continuation proves four finite constructions used in Section 6:
preferred representative edges, the threshold and allowed-color preparation,
correction-edge selection with bounded exceptional degrees, and colorability
of the selected exterior graphs from their inactive residues. They continue
the verified checkpoint `2fb0b6d3fb7ed4e41de90a1d34b5caea3f5993e6`.
The subsequent [one-palette assembly](bipartite-palette-assembly.md)
combines them with actual palette identities and preferred filling.
The [two-family construction](bipartite-two-families.md) now constructs
both selected families and the coloring of their exact remainder from
finite supply conditions, with a total footprint load equal to the
original core degree.

The full factorization assertions remain incomplete. The later
[sampling continuation](bipartite-sampling.md) proves the finite laws,
weighted moments, capped means, and actual nonlinear graph-score
variance, and constructs disjoint palettes from explicit marginal
failure budgets. The later score-mean, simultaneous-selection, and
[uniform-localization](uniform-localization.md) results supply the
application estimates, uniform sampling budgets, rounded palettes,
compatible positions, and boundary-loss bounds. The complete spanning
setup, final boundary construction, and absorber remain to be composed.
This supporting checkpoint had **42 of 69** numbered assertions complete;
the current combined development has **44 of 69** after Lemma 5.12 and
Theorem 2.23. The separate unavailable terminal checkpoint remains outside
this audit; its provenance is recorded in
[bipartite-prerequisites.md](bipartite-prerequisites.md).

The manuscript inspected is `Four_Robust_Component_Cases_2026-11-21.tex`,
in the preferred-side preparation, `old:palettes`, and `old:two-families`
parts of Section 6. The original numbered inventory and statement hashes
remain pinned to the November 20 source in `manuscript-source.json`.

## 1. Preferred sides and representative copies

Source: [Preferred.lean](../Overfull/BipartiteFactorization/Preferred.lean).
The public construction is
`Overfull.BipartiteFactorization.ordinary_preferred_representatives`.

Let `A,B` be disjoint actual vertex sets, let every vertex have degree at
most `k`, and suppose `0≤β≤1`, `10a≤βk`, and the ordinary exceptional
vertices satisfy `OrdinaryPorts`. For such a vertex `x`, put
`c_x=d_G(x,A∪B)`. The preferred side is chosen by comparing the actual
incidence counts, resolving ties in favor of `A`.

The construction returns a finite set of original edge copies from `x`
to its preferred side. Their other endpoints are distinct, and their
other-end image is exactly the full distinct-neighbor set in that side.
The side receives at least `c_x/2` incidences, and the selected set has
size at least `βc_x/4`. The graph may have parallel copies; those copies
are never identified in the graph representation.

Under the first ordinary alternative, repeated incidences in the chosen
side are bounded by the repeated incidences in the whole core. Thus the
chosen side has at least `c_x/2-a≥2c_x/5` distinct neighbors. Under the
second alternative, both sides have at least `βk≥βc_x` distinct neighbors.
The error budget follows from `10a≤βk≤c_x`. Finite surjective-image
selection then chooses one original copy for every chosen neighbor.
No representative set is supplied as an assumption. Equal side sizes,
regularity, and robust expansion are unnecessary for this finite step.

## 2. A bounded special set and the actual allowed colors

Source: [Palettes.lean](../Overfull/BipartiteFactorization/Palettes.lean).
The public construction is
`Overfull.BipartiteFactorization.exists_allowed_palette_data`.

Fix a positive initial threshold `θ₀≤β`, a positive palette size `k`,
and a special set `Z₀⊆Z` of order at most `z`. Assume every vertex of
`Z\Z₀` has at least `βk` core incidences. The theorem uses the fixed
schedule

\[
\theta_j=\theta_0\bigl(65536(z+1)\bigr)^{-j}.
\]

Among the `z+1` disjoint half-open bands, one contains no special
incidence value. The theorem selects `j≤z`, puts `θ=θ_j`, and constructs
the actual low set `L⊆Z₀`. Every low vertex has fewer than `θ_{j+1}k`
core incidences; every vertex of `Z\L` has at least `θk`. The selected
threshold satisfies `0<θ_z≤θ≤θ₀`. Its positive lower bound is fixed
before the graph, although the band index may depend on the graph.

Given the actual proper coloring and two correction pools `P,Q`, a pool
is small exactly when it has fewer than `θk/65536` copies. The excluded
set consists of the actual labels on low core incidences and on both
small pools. Its cardinality is strictly less than `θk/512`. Consequently:

- More than `k-θk/512` labels remain allowed.
- Every active vertex retains at least `511c_x/512` of its core colors.
- No allowed color appears on a low core incidence or in a small pool.

The exclusion bound counts images of actual copies. Properness is used
to prove that the number of core colors at a fixed vertex equals its
core incidence count. The conservative union bound requires no
disjointness of `P,Q`. The theorem constructs the allowed set; it does
not yet select random subpalettes with simultaneous row and pool bounds.

## 3. Correction capacities realized by actual copies

Source: [Capacity.lean](../Overfull/BipartiteFactorization/Capacity.lean).
The generic results lie in `Overfull.BipartiteFactorization.CorrectionCapacity`;
the graph constructors are `exists_graph_correction_subset` and
`exists_graph_correction_subset_after_deletion` in the parent namespace.

For disjoint finite copy pools `F_i` with integer caps `ℓ_i`, the exact
maximum selectable size is `Σ_i min(|F_i|,ℓ_i)`. The proof constructs
every size up to that capacity and proves the converse upper bound.
It first selects a capped subset in each row and then takes a subset of
their disjoint union of the requested size.

For an uncapped internal pool `F₀` and disjoint exceptional rows, the
capacity is

\[
|F_0|+\sum_x\min\{|F_x|,\ell_x\}.
\]

With `0≤ω₁≤ω₂≤1`, the manuscript's weighted score
`ω₂|F₀|+Σ_x min(ω₁|F_x|,ℓ_x)` is at most this actual capacity.
Deleting an arbitrary set `D` lowers the score by at most `ω₂|D|`.
Each deleted copy belongs to at most one row, which supplies the total
loss bound. The deleted set may be chosen adaptively; no independence
assumption is used.

The graph adapter uses `F₀=E(G[B])` and `F_x=E_G(x,B)` for `x∈Z`, with
`B∩Z=∅`. It derives pool disjointness from the actual endpoints. Under
the explicit bound `t≤score(original pools)-ω₂|D|`, it constructs `t`
original copies avoiding `D`, with actual degree at most `ℓ_x` at each
exceptional vertex. The right side is the proved lower bound on the
surviving score. The adapter also proves that the row intersection count
is exactly that exceptional degree in the selected restriction.

The score lower bound remains an explicit input to this finite
construction. Establishing that lower bound simultaneously for the
random blocks is separate unfinished work.

## 4. Coloring a selected graph from its inactive residue

Source: [Coloring.lean](../Overfull/BipartiteFactorization/Coloring.lean).
The public criterion is
`Overfull.BipartiteFactorization.coloring_from_inactive_exterior`.

Let `G` be the actual selected finite loopless multigraph, with core
`U`, active set `Z⁺`, and `a≥0`. Suppose core degrees are at most `a`,
degrees outside the core are at most `k`, `2a<k`, and each active vertex
has more than `2a` copies into `U`. The only coloring input is a proper
`k`-coloring of the actual inactive residue

\[
E(G[U^c])\;\cup\!
\bigcup_{x\in U^c\setminus Z^+}E_G(x,U).
\]

The theorem derives a proper `k`-coloring of all of `G`. To prove it,
choose an actual minimal noncolorable restriction. The proved critical
endpoint-degree inequality excludes its core-core edges. The low-degree
fan lemma excludes its active-to-core edges, using the incidence lower
bounds in `G` before the restriction. Every remaining copy lies in the
initially colorable residue, a contradiction. Regularity of `G` is not
required.

The corollary `exists_balanced_localized_coloring` adds disjoint equal
core sides `A,B`, equal actual side-degree sums, even exterior order,
degree `k` at every exterior vertex, and equal blocks
`Ablock⊆A`, `Bblock⊆B`. Core vertices outside the blocks have degree
zero. It first constructs the whole selected-graph coloring by the
criterion, then balances it. The result has:

- Every exterior vertex covered by every color.
- Equal side coverage in every color and side-coverage spread at most two.
- Every core footprint contained in `Ablock∪Bblock`.
- Even footprints of size at most `2|Ablock|a/k+4`.
- Exact per-vertex footprint load equal to the actual degree, hence at most `a`.

The footprint estimate follows from the actual degree sum supported on
the blocks. The residue labels may be recolored; the theorem asserts
colorability and a new balanced coloring, not preservation of every
initially prescribed label.

## Verification and remaining construction

All four modules are imported by `Overfull.lean`. Their original 54 explicitly
named theorem proofs are registered separately in the coverage catalog
and checked by the transitive axiom audit. Verification uses the pinned
Lean 4.24.0 toolchain, warnings as errors, and only the allowed logical
axioms `propext`, `Classical.choice`, and `Quot.sound`. Exact hashes and
the final audit inventory are in `verification/results.json`.

The subsequent one-palette composition derives the palette row demands
and the correction imbalance identity from the actual balanced exterior
coloring and constructs the selected graph and its localized coloring.
It also strengthens the deletion adapter to charge only the intersection
of the deleted set with the correction pool. The further two-family
composition constructs the mutually disjoint fine and coarse selections,
colors the exact residual, and proves a footprint load bound shared by
all selected and residual colors.

The [sampling continuation](bipartite-sampling.md) proves the weighted
swap bound by finite maximum-weight conditioning and the nonlinear
product bound by variance tensorization. Its graph adapters establish
the actual capped-score variance, and its permutation sampler gives
disjoint palettes from marginal failure estimates. The remaining work
must derive the partition-sample score mean, assemble all required
row, pool, preferred-edge, and score failure bounds, and prove their
combined budget is below one. Uniform parameter choices and boundary
budgets must establish the finite reserve inequalities. The regularity
setup, special path systems, robust absorber, and final factorization
remain substantive additional obligations. Theorem 6.1, Proposition
6.2, Theorem 6.3, and the dependent Lemmas 4.2 and 4.14 remain unverified.
