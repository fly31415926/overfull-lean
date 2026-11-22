# Remaining factorization targets after Lemma 4.15

This checkpoint completes [Lemma 4.15](four-odd-decomposition.md), bringing
the numbered inventory to **45 of 69**, with **24** remaining. Its direct
proof constructs the required actual joining-edge decomposition from the
original graph hypotheses, using the sufficient ratio bound `1/1000`.
Theorem 2.23 brought the earlier `2eb61f5` checkpoint to 44; the subsequent
109 supporting proofs in 13 modules preserved that earlier count.

The combined tree also preserves the published circuit checkpoint
`54db7b8` and its alternate pattern proof. The [recovery manifest](source-recovery.json)
records the source identity and exact namespace mapping. The recovered
[circuit and forest components](four-odd-circuits.md) remain available.
The new direct proof completes Lemma 4.15 without the general compatible
decomposition theorem, which remains unproved. The second proof of Lemma
4.13 does not add another numbered assertion.

## Newly completed finite constructions

The [uniform-localization continuation](uniform-localization.md) now proves:

- Actual simultaneous palettes with graph-specific error and order
  thresholds, followed by actual positive even rounded palette sizes.
- Actual equal fine positions, exact coarse unions, and actual simultaneous
  vertex blocks constructed from divisible parts of sufficient size.
- Floor-cap intervals, correction-row small-error bounds, and every
  probability budget, all derived internally from the stated graph bounds.
- A preferred-row-only sampling theorem for the no-correction branch.
- The actual normalized boundary weight bound, a light existing cluster,
  and original-copy pool/row loss bounds for any bounded-weight boundary.
- Exact adaptive pool loss, fine-to-coarse reserve accounting, preferred
  supplies, strict coloring reserves, and sampled-to-selection bridges.
- Actual zero-correction selection without any correction-score premise.

The next Section 6 obligation is the **full compatible spanning setup**:

1. Construct and normalize the actual regularity partition and its balanced
   core moves, then connect the proved integer cluster adjustment to it.
2. Choose the absorber parameters and positive even palette targets with
   the exact identities `k₁=2r₃`, `k₂=2r◇` and all required divisibilities.
3. Construct the final forward-copy boundary after insertions and
   equalization, proving both its normalized-weight and cardinality bounds.
4. Assemble the original robust-core hypotheses, allowed colors, both
   correction orientations, samples, reserves, and exact copy accounting
   into one uniform construction of both colored families.
5. Construct the special path systems and robust absorber, then prove the
   factorization of the actual whole residual multigraph.

The finite sampling theorems do not themselves supply regularity or the
absorber. A bipartite core does not make the entire residual host bipartite.

## Separate near-complete deterministic partition reduction

The [critical-partition continuation](critical-partition-consequences.md)
now derives every conclusion of the deterministic argument from the actual
normalized average-degree estimate. The parameters precede the graph,
the low-degree set is the actual manuscript set, and all degree/shore
bounds refer to the actual induced survivor graph and original order.
To complete Proposition 2.24, prove the Cao–Chen criticality-to-average-degree
input and compose its uniform degree threshold. No such theorem is
assumed as an axiom.

## Remaining factorization chain

The boundary-extension reduction for Lemma 4.14 and the ordinary-core
reduction for Lemma 4.2 are already proved. Their remaining input is an
actual factorization of the residual supplied by the Section 6 theorem.
The complete count is **45 of 69**, and the main theorem is unverified.

The detailed boundary statement and manuscript identity remain recorded in
[manuscript-source.json](manuscript-source.json), [coverage.json](coverage.json),
and [boundary-extension.md](boundary-extension.md). The following description
records the already completed reductions and the remaining composition.

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
`boundary_extension_reduction` to prove Lemma 4.14. The general Fan–Zhang
theorem remains unnecessary for this particular one-apex route and for
the new direct proof of Lemma 4.15. Its general formalization is a
separate task.

Do not count Lemma 4.2 or Lemma 4.14 as verified until their actual
factorization conclusions are derived and the strict build, transitive
axiom audit, and semantic review pass. Supporting declarations are
registered separately and do not change the completed assertion tally.
The current count is 45 of 69, and the main theorem remains unverified.

An unfinished formal dependency is not, by itself, a mathematical gap
in the written proof. The manuscript invokes Theorem 6.1; the remaining
work here is to prove and compose that input in Lean.
