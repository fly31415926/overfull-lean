# Next verification target: bipartite robust-core factorization

The [complete robust-partition theorem](robust-partition.md) now proves
Theorem 2.23 with uniform constants and all four quantitative clauses.
The preceding [link-packing theorem](dense-link-packing.md) proves Lemma 5.12
with a uniform order threshold and actual disjoint perfect matchings.
The completed numbered total is **44 of 69**. The factorization work below
remains a separate unfinished dependency chain; these results do not
supply its missing regularity or absorber constructions.

The deterministic two-family construction is now proved by
`BipartiteFactorization.exists_colored_two_families`. From original
finite palette, block, and reserve conditions it constructs both
edge-disjoint selected families, their balanced localized colorings,
and the coloring of their exact remaining exterior graph. The total
footprint load across every selected and residual color equals the
original core degree. Coarse reserves charge the fine family's actual
row and correction-pool use, and both correction signs are handled.
See [bipartite-two-families.md](bipartite-two-families.md).

The [sampling continuation](bipartite-sampling.md) now proves weighted
sample moments, capped means, the full weighted swap-variance bound,
nonlinear finite-product tensorization, and its application to the
actual capped graph score in a union of disjoint sampled parts. It
also constructs disjoint samples and actual allowed palettes from
explicit marginal failure bounds whose sum is below one.

The [score-mean continuation](bipartite-score-mean.md) proves actual
pair-inclusion laws, internal-copy expectations, and exceptional-row
moments with variance coefficient one. Their composition gives the full
actual score mean and graph-specific lower tail, and constructs a
supported block with every prescribed part size when the explicit failure
budget is below one.

The [simultaneous-selection continuation](bipartite-simultaneous-selection.md)
now derives every palette-row, pool, ordinary preferred-row, special
preferred-row, and score failure estimate from actual graph data. It compares
the allowed-color fraction with `s/k`, constructs all disjoint palettes
under the explicit total budget, and constructs compatible fine/coarse
blocks from one shared permutation per part. Exact component sizes,
inclusions, disjointness, coarse unions, and full-side coverage are retained.
Neither existence theorem assumes its required probability estimates.
A separate scalar theorem now chooses an error tolerance and order
threshold for every fixed budget `u*m*exp(-r*m) + v*a/m + w/m`, with
`u,v,w ≥ 0` and `r > 0`; the graph-specific coefficient comparisons
remain to be instantiated.

The next finite obligation is **uniform realization from the original
robust-core hypotheses**:

1. Choose positive even palette sizes, labelled fine positions, coarse
   unions, and common fractions satisfying all divisibility, capacity,
   and at-least-two-selected-vertices requirements.
2. Derive the numerical total-budget inequalities using the original
   active-row lower bounds, large-pool threshold, bounded number of special
   vertices and palettes, and actual per-color copy bound.
3. Discharge cap floor errors, boundary exclusions, fine-to-coarse losses,
   and residual coloring reserves, then feed the resulting finite data
   into `exists_colored_two_families`.

The probability estimates and compatible simultaneous choices are now
proved. Their hypotheses still include the exact position families, graph
bounds, cap intervals, a positive correction pool for the block-score
application, and the explicit numerical total budgets. The current result
does not assert that arbitrary robust-core input already supplies all
these data.

The earlier one-palette and finite localization ingredients are recorded
in [bipartite-palette-assembly.md](bipartite-palette-assembly.md) and
[bipartite-localization.md](bipartite-localization.md).

Three Section 6 prerequisites are now proved: reverse bipartite robustness,
the actual balanced exterior coloring, and preservation of the ordinary
neighborhood conditions under a bounded core move. Their statements,
proofs, uniform numerical budgets, and recovery provenance are recorded in
[bipartite-prerequisites.md](bipartite-prerequisites.md). The actual
bipartite regularity setup, uniform realization of the localized exterior
family data, special path systems, robust absorber, and final factorization
remain open.

**Lemma 4.14 remains unverified; the completed assertion count is
44 of 69.** Its full reduction is now constructed by
`Overfull.boundary_extension_reduction`. The remaining factorization to formalize
is an actual factorization of the exact one-apex residual returned by
that theorem. Supplying a coloring as an assumption would not close the
numbered lemma.

Lemma 4.13 is proved by `Overfull.frequent_boundary_patterns`; its exact
residual, complete absorption, and matching-or-star supply are recorded
in `Patterns.FrequentPatternResult`.

The boundary-extension statement is `three:lem:boundary`, lines
3119–3128 of the pinned `Four_Robust_Component_Cases_2026-11-20.tex`.
Its statement SHA256 is
`67baedd4ae2e0451a8842fd27ea0976f50db94c9054eacd2f5dd40ce2cfa21e3`.
This is the statement hash, not the hash of the entire manuscript.
See [the source record](manuscript-source.json),
[the assertion inventory](coverage.json), and
[the detailed boundary-extension notes](boundary-extension.md).
The Lemma 4.2 and Lemma 4.14 statement and proof blocks are unchanged in
the November 21 manuscript inspected during this continuation.

## The completed uniform reduction

For `0 < α ≤ 1`, `0 < γ`, and `0 < ν ≤ τ ≤ α/8`,
[`boundary_extension_reduction`](../Overfull/BoundaryExtension/Reduction.lean)
chooses positive `ε`, `θ`, `σ`, and a threshold `m₀` before every graph,
embedded core, degree, error, and prescribed boundary coloring.
The parameters satisfy `θ ≤ σ ≤ τ` and `σ ≤ min γ 1 / 20`.

The input is a loopless multigraph with a finite edge-copy type, an odd
core `U` of order at least `m₀`, and an embedded simple `(ν,τ)`-robust
graph on `U`. Ambient degrees equal `d` on `U`, the embedded core has
minimum degree at least `d-a`, `α*U.card ≤ d`, and
`0 ≤ a ≤ ε*U.card`. No regularity outside `U` is required.
The actual boundary copies have a proper `Fin d` coloring, every color
has size one or three, and at least `γ*U.card` colors have size one.

The theorem constructs `BoundaryReduction`, whose data include:

- Actual pairwise edge-disjoint completed triple classes, each covering
  every core vertex exactly once and retaining its prescribed boundary
  copies and original color.
- Their exact union `T`, with actual residual `G.restrictEdges Tᶜ`.
- Exact residual degree `h=d-q` on `U` and actual boundary size `h`,
  where `q` is the number of triple colors, with `γ*U.card ≤ h`.
- The actual embedded surviving simple core, of minimum degree `h-a`
  and robust parameters `(θ,σ)`.
- The actual retained-edge contraction on `U ⊕ Unit`, proved
  `h`-regular, of even order, and without any overfull vertex set.
- An `extend` function that takes an actual `h`-coloring of that precise
  contraction and returns a proper coloring of all original edges
  incident with `U`, exactly agreeing with every prescribed boundary
  label.

The construction keeps individual original edge copies. It proves
properness at original exterior endpoints as well as at core vertices.
Its public hypotheses contain no residual coloring or factorization
oracle. The only conditional part of the returned object is `extend`'s
explicit input coloring; existence of that coloring is not asserted.

## Completed supporting components

The earlier contraction, triple completion, and palette-restoration
steps are now proved and assembled by the public reduction.

| Completed obligation | Main module or declaration |
| --- | --- |
| Actual boundary classes, footprints, incidence load, and triple horizon | [BoundaryData.lean](../Overfull/BoundaryExtension/BoundaryData.lean) |
| Uniform fixed-footprint packing with an actual robust residual | [Packing.lean](../Overfull/BoundaryExtension/Packing.lean), `pack_fixed_forbidden_sets` |
| Derive every packing hypothesis from the boundary input | [Triples.lean](../Overfull/BoundaryExtension/Triples.lean), `exists_triple_core_packing` |
| Complete selected classes using actual original core copies | [Assembly.lean](../Overfull/BoundaryExtension/Assembly.lean), `completedColor` |
| Exact deletion degrees and actual surviving core embedding | [Residual.lean](../Overfull/BoundaryExtension/Residual.lean), `remainingAmbient`, `remainingEmbeddedCore` |
| Surviving singleton labels and exact residual boundary size | [SurvivingLabels.lean](../Overfull/BoundaryExtension/SurvivingLabels.lean), `residual_cutSize_eq_sub` |
| Edge-copy-preserving apex graph and exact incidence correspondence | [Contraction.lean](../Overfull/BoundaryExtension/Contraction.lean), `contract`, `contractCore` |
| Derived no-overfullness at the retained density | [OneCore/Cuts.lean](../Overfull/OneCore/Cuts.lean), [ContractionCuts.lean](../Overfull/BoundaryExtension/ContractionCuts.lean) |
| Prescribed singleton palette and proper pullback to original vertices | [Palette.lean](../Overfull/BoundaryExtension/Palette.lean), [Colors.lean](../Overfull/BoundaryExtension/Colors.lean) |
| Reinsert completed classes with exact original labels | [Reassembly.lean](../Overfull/BoundaryExtension/Reassembly.lean), `reassemble_deleted_colors` |
| Uniform public construction and its precise result object | [Reduction.lean](../Overfull/BoundaryExtension/Reduction.lean), [Result.lean](../Overfull/BoundaryExtension/Result.lean) |
| Even-core reduction with two exterior vertices and a colored complement | [OneCore/Complement.lean](../Overfull/OneCore/Complement.lean), `even_core_complement` |

## Shorter route to the missing factorization

The manuscript invokes Corollary 4.6, whose one-core branch uses
Lemma 4.4. The full fixed-pattern proof also uses Fan–Zhang compatible
circuits and Lemma 4.2. None of these unproved factorization inputs is
silently supplied by the boundary reduction.

For this particular one-apex graph, a shorter route is already reduced
to an even ordinary core with at most two exterior vertices:

1. The exceptional complement of the odd core has degree at most `a`
   away from the apex. `one_apex_complement_colorable` uses the proved
   one-high-vertex coloring theorem to color it with `h` colors when
   `2a < h`.
2. Move one vertex `x` from the odd core to the exterior.
   `restrictCore` keeps exactly the original core copies whose endpoints
   survive. `even_core_complement` proves that the new core has even
   order, its exterior is exactly the old apex and `x`, and its
   exceptional complement has an actual `h`-coloring. It also gives
   minimum degree `h-(a+1)` and robustness `(θ/2,2σ)`, under the explicit
   scalar and deletion bounds, including `3(a+1) < h`.
3. A proved ordinary-core Lemma 4.2 with exceptional bound `s=2` would
   factor this actual regular graph. A uniform wrapper must choose the
   parameters and threshold to satisfy that theorem and the preceding
   scalar bounds before the arbitrary input graph.

This route bypasses the full Corollary 4.6/Lemma 4.4/Fan–Zhang chain for
Lemma 4.14. It does not bypass the substantive factorization content of
Lemma 4.2. A one-apex factorization theorem would already cover ordinary
even-order simple regular robust graphs by moving one vertex into an
apex role, so the remaining step is not just palette bookkeeping.

## Completed ordinary-core preprocessing

The ordinary-core route now has a public uniform construction:
`OrdinaryFactorization.exists_uniform_bipartite_reduction`. It constructs
the first group of perfect matchings and the exact residual input for
Theorem 6.1. Its positive crossing parameter is chosen before the
requested final tolerance, and all remaining constants precede the graph.
See [the ordinary-factorization notes](ordinary-factorization.md).

| Input or bridge | Current status and role |
| --- | --- |
| Accurate balanced cut and side-specific reserve sampling | Proved on one actual graph and sample, with the crossing robust parameter chosen before later tolerances. |
| Equitable exterior coloring | Proved from the actual initial coloring; coverage, parity, footprint sizes, and incidence loads are derived. |
| Feasibility with fixed exterior forbidden labels | Proved by permutation counting and greedy repair, using Vizing for the initial simple-graph coloring. This supplies the specialized consequence needed here; the general Kahn theorem remains unformalized. |
| Constrained balancing and near-perfect classes | Proved by actual two-color exchanges and degree/deficit accounting, including palette rounding. |
| Reserve repair | Composed with the proved Lemma 4.1 to construct the actual repaired matching family. |
| Exact first-group deletion and retained degree | Proved on original edge copies, with residual degree `k-h >= 2k/5`. |
| Residual crossing robustness | Derived from actual reserve use, with the factor of two converting full order to side order. |
| Residual complementary coloring | Constructed from the inherited compressed colors by greedy extension; all newly colored copies have both endpoints in the core. |
| Uniform interface for Theorem 6.1 | Constructs an actual embedded crossing core with error at most `η` times the side order and an actual coloring of its complement, for arbitrary requested positive `η` and side-order threshold. |
| Theorem 6.1, `ext:thm:robust` | Still unformalized. It factors the whole residual multigraph through the bipartite robust core. |
| Robust decomposition and Hamilton decomposition infrastructure | The manuscript's inputs to Theorem 6.1, including the cited Granet lemma, still require formalization or a proved sufficient replacement. |

The initial exterior coloring may change during equitization. Its
selected labels are fixed after that step and retained through internal
coloring, balancing, and repair. No stronger preservation of the input
coloring is claimed.

Theorem 6.1's formal interface should use the admissible parameter
`min(ξ/2,4τ)` if needed, and choose the original range small enough that
`4τ` lies below its range threshold. Both choices precede the requested
error tolerance. The host and core vertex sets are unchanged, so an
original bound on the number of exceptional vertices carries directly
to the residual.

## Next proof priority and acceptance gate

Prove Theorem 6.1 (`ext:thm:robust`), or a sufficient specialization for
the actual residuals returned by `exists_uniform_bipartite_reduction`.
The residual ambient graph can have same-side and exceptional edges.
König's theorem cannot factor that whole graph just because it contains
a bipartite robust core.

Then compose the uniform constants to obtain the ordinary-core
factorization of Lemma 4.2, apply its `s=2` case to the even-core
one-apex reduction, and compose the resulting actual coloring with
`boundary_extension_reduction` to prove Lemma 4.14. The full
fixed-pattern/Fan–Zhang chain remains unnecessary for this particular
one-apex route, but remains separate work for the general manuscript.

Do not count Lemma 4.2 or Lemma 4.14 as verified until their actual
factorization conclusions are derived and the strict build, transitive
axiom audit, and semantic review pass. Supporting declarations are
registered separately and do not change the completed assertion tally.
The current count is 44 of 69, and the main theorem remains unverified.

An unfinished formal dependency is not, by itself, a mathematical gap
in the written proof. The manuscript invokes Theorem 6.1; the remaining
work here is to prove and compose that input in Lean.
