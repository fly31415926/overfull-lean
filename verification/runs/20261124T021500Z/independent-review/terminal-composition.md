# Semantic review of terminal native composition and Corollary 4.6

Run: `20261124T021500Z`.

## Result and verification scope

I found no mathematical or statement-level gap in the new native residual
geometry, shore-coloring composition, original-host reconstruction, and the
one/two-core wrapper inspected here. The public declarations
`Overfull.bounded_input_factorization` and
`Overfull.bounded_input_one_factorization` cover both alternatives in the
recorded statement of Corollary 4.6. They do not require a supplied terminal
coloring, reserve, matching representative, or complementary coloring.

This is a source-level semantic review and records observed focused compiler
results. It does not replace the stock full axiom audit or the preservation
checker, and does not claim that either has finished. The reviewer implemented
the shore-host/core transports, shore coloring, terminal numerical budgets,
and `NativeCompletion`; the separate native-geometry, coloring-gluing, pair,
`TwoCore`, and `BoundedInput` modules were independently reviewed from their
authors' sources. Thus independence is asserted for those other authors'
modules, not for every line in the whole continuation.

Observed command receipts:

| Attempt | Command target or purpose | Result |
| --- | --- | --- |
| `native-completion-001` | `lake build --wfail Overfull.NativeTerminal.NativeCompletion` | Exit 0, 3,494 jobs; recorded input hashes unchanged |
| `bounded-input-001` | `lake build --wfail Overfull.NativeTerminal.BoundedInput` | Exit 0; recorded input hashes unchanged |
| `terminal-source-review-001` | Recompute the authorized source statement identity | Exit 0; exact 443-byte statement hash match |

Earlier failed attempts and their genuine diagnostics remain in the run.
In particular, subtype equality-instance transport and four tactic-style
linter warnings were repaired before the warning-free dependency pass. The
proof that changes the decidable-equality instance uses `Subsingleton.elim`;
it does not add a mathematical hypothesis or an axiom.

## Exact source identity and statement match

The reviewed source is the already-authorized exact statement block in
`verification/runs/20261122T235931Z/authorized-manuscript-recovery.md`.
`independent-review/check-bounded-input-source.py` was actually executed by
the current command recorder and produced:

- Statement bytes: **443**.
- SHA-256:
  `86700ed56e6cd9be513339e7c06b5af19d1d8cbe074fed3985ef21e5c9ad6e26`.
- Equality with the pinned Corollary 4.6 statement hash: **true**.

This establishes identity of that statement block. It does not assert that
the entire newer source manuscript equals the pinned November 20 file, nor
does it establish Lean verification by hashing alone.

The source requires an even regular multigraph without an overfull set,
fixed positive linear lower bounds on degree and core orders, sufficiently
small core error, and ordinary robust parameters with sufficiently small
range. Its alternatives are one core with at most three other vertices,
or two cores with at most two other vertices. The new public wrapper gives
the same two alternatives, with the explicit sufficient range
`τ ≤ min α (min β 1) / 16`, error convention `a + 1 ≤ ε * |V|`, and core
minimum degree at least `k - a`. The `SmallCuts.Core` data consist of a
simple graph spanning the actual core vertex set and an injective,
endpoint-preserving map into actual multigraph edge copies. This is the
required robust spanning graph, not a simplification that forgets copies.

The common tolerance is the minimum of the constructed one-core and two-core
tolerances; the common order threshold is their maximum. The degree-density
parameter is weakened to `min α (min β 1)` to apply both engines. This is
derived from the given linear lower bounds. No stronger host hypothesis is
silently introduced. The one-factorization result supplies exactly `k`
pairwise disjoint perfect matchings whose union is all original copies.

The proof of this corollary need not follow the manuscript's invocation of
the broader five-exception corollary. The new direct two-exception proof
establishes the stated conclusion without establishing that broader result.
This review does not promote Lemma 4.4, Corollary 4.5, the five-exception
case, or the main theorem.

## Native external image: both directions checked

`NativeTerminal.externalCopies_eq_joining_exceptional` is proved for an
arbitrary host on the same vertex type as the original representative. It
uses the fixed partition by the two original cores and exceptional set.
An edge is outside both old-core internal sets exactly when it is a joining
copy for the fixed assigned labels or has an exceptional endpoint. In
particular, an exceptional-to-core edge whose assigned labels agree remains
external through the second term of this union. Internal copies of each old
core are excluded even when the host's copy type has changed.

`NativeTerminal.twiceResidualEmbedding` maps a twice-surviving edge to its
original copy by two applications of `Subtype.val`. Its injection and exact
endpoint equation are proved. There is no identification by endpoint pair.

The crucial theorem `NativeTerminal.twiceResidual_external_image` derives
the original-copy image from the final image equality returned by
`NativeCore.exists_uniform_native_unprotected_prefix`. The two image maps
are combined using `Finset.image_image`.

For the forward direction, every surviving external copy belongs to a
selected residual boundary and hence to its original selected boundary.
For the reverse direction, a selected original copy survives the first
deletion by `Q.boundary_disjoint_removed`, using the supplied and already
constructed avoidance of the complete reserve. It therefore defines the
intermediate residual subtype. The prefix's exact image equality then puts
that intermediate copy in the image of the second surviving subtype.
Consequently the argument proves equality of all selected original copies
with the final external image; it does not merely prove containment or
assume that the second deletion avoided them.

The final `NativeCompletion` wrapper obtains this exact image equality from
the constructed prefix and passes it directly into
`NativeTerminal.exists_uniform_native_residual_factorization`. The equality
is not an extra original-host assumption.

## Shore geometry and parity coverage

The selected boundaries are compressed boundaries of perfect matchings
with the same native signature as the representative. The source
`BoundaryPacking.sameSignature`, together with the established compression
identities, proves `NativeTerminal.BoundaryPacking.boundary_assigned_parts`.
Every selected boundary therefore has the same two assigned shores and the
same optional pair component.

The following conclusions are derived, not supplied to the original-host
theorems:

- `boundary_first_cut` identifies a boundary's assigned-shore cut with
  its original old-core crossings.
- `boundary_first_cut_card` gives zero or one crossing according to the
  assigned shore's parity.
- `selected_cuts_disjoint` uses the injectivity of selected reserve indices
  and actual boundary-copy disjointness. `card_biUnion` therefore gives
  exactly `s * (|A_i| % 2)` copies, with all parallel copies counted.
- The two shore cuts agree as finite sets of original copies, and no
  selected copy leaves the optional pair component.
- Every selected incidence at an exception assigned to `U_i` goes into
  `U_i`. This uses the matching property to identify the actual incident
  edge with the assignment witness, rather than merely a common endpoint
  support.

`CopyEmbedding.cut_image_of_external_image` transfers whole-core-shore cuts
from the actual final host to selected original cuts. The assigned shores
contain or avoid each entire old core, so no internal old-core edge can
cross them. Injection makes the transferred cut cardinality exact.
`NativeTerminal.residual_geometry` thus obtains both common cuts, their
parity counts, the closed pair component, and the exceptional star-incidence
condition in the actual final graph.

`exists_uniform_native_image_factorization` proves the assigned shore
parities agree from the original representative's perfect matching and
the equality of its two assigned-shore cuts. It then splits on the first
shore's remainder modulo two. These two cases are exhaustive:

1. Both assigned shores are even, and the actual common cut is empty.
2. Both assigned shores are odd, and the actual common cut has exactly
   the final regular degree `s` copies.

The parity in this split is that of the assigned shore, not necessarily
the smaller old core. The independent-exterior engine accepts either
parity of the old core, so moving exceptions into a shore creates no
unhandled parity case.

## Actual shore hosts, exterior vertices, and color agreement

The even case uses `NativeTerminal.inducedHost`, restricting both vertices
and edge copies to the shore. Empty cut preserves every original degree
at a shore vertex. The graph is not an edge restriction on the old ambient
vertex type with isolated vertices left behind.

The odd case uses `BoundaryExtension.contract G A`, keeping all original
copies with an endpoint in `A`. Every shore degree is preserved; the apex
degree is the actual cut size `s`, so the contraction is `s`-regular.
An odd shore plus the one apex has even order. `contractedCore` embeds the
smaller old core `U ⊆ A`, preserving its degrees and robust expansion
exactly. The exterior contains at most two assigned exceptions and the
apex. The actual star-incidence condition excludes edges between assigned
exceptions and also excludes an exception at the shore endpoint of a
crossing. Thus no edge joins two exterior vertices after contraction.

`NativeTerminal.exists_uniform_shore_coloring_of_star_incidence` invokes
`NativeCore.exists_uniform_independent_exterior_factorization` on these
constructed hosts. No complementary coloring or no-overfull condition on
the contracted graph is required by that theorem. The initial residual's
no-overfull hypothesis is still used by the earlier native prefix stage;
it is not asserted to survive arbitrary matching deletion.

`exists_glued_contracted_shores_coloring` chooses one bijection from the
common original cut-copy set to `Fin s`. The second shore's labels are
transported through equality of the same cut-copy sets. The existing
`BoundaryExtension.exists_singleton_boundary_extension` restores these
labels on both shore colorings. `exists_glued_retained_coloring` checks
properness at each original vertex using a local retained coloring and
proves pointwise agreement on every overlapping original copy. Each shared
crossing is therefore colored once in the original edge type.

The pair component is handled by `retained_pair_colorable`. If it contains
a retained edge, looplessness and the bound of two vertices force every
retained edge to have the same two distinct endpoints. Its copy cardinality
is bounded by one actual degree and can be injected into the palette.
If it contains no edge, the coloring is the empty function. This treats the
empty pair component, arbitrary parallel bundles, and the formally possible
one-vertex component without a positivity shortcut.

Terminal recoloring can change the colors on selected exceptional-star
copies. Only the selected copy union and the shared singleton crossing
labels are preserved here. Corollary 4.6 asks for a factorization and does
not prescribe whole reserve color classes, so this is sufficient. The new
public wrappers do not claim a stronger whole-boundary precoloring extension.

## Parameter order, rounding, and reconstruction

All constants precede the original host and its copy type. In `TwoCore`,
the first robust range is `α/960`. The already proved uniform reserve
completion chooses its positive surviving robust parameter before the
requested surplus tolerance. This avoids a circular choice between that
parameter and the later terminal tolerance.

`NativeCompletion` fixes the later range `α/3840` before prefix completion.
It obtains the prefix's positive expansion parameter, weakens it to its
minimum with that range, and applies the terminal theorem with density
`α/120`. `terminal_robust_range` proves the required inequality between
range and density. The terminal tolerance and threshold are then known,
and `exists_uniform_terminal_parameters` shrinks the error to a positive
minimum and enlarges the order threshold before any host is introduced.

The bound `r ≥ α n/30`, together with `n ≥ 120/α`, gives the exact natural
half-reserve density `(α/120)|U_i| ≤ floor(r/2)` through the already proved
`half_reserve_prefix_room`. Odd reserve size is allowed. The core-size bound
`β n ≤ |U_i|` converts the common host-order error to each terminal core's
order and provides both large-core thresholds. No asymptotic rounding term
is silently discarded.

The nonprotected prefix has exactly `h-r/2` perfect matchings, and its
actual residual is `r/2`-regular. Since `r/2 ≤ r ≤ h`, natural subtraction
gives `(h-r/2)+r/2=h` exactly. `reassembledColoring` shifts the terminal
palette past the prefix indices and uses the original residual-copy
subtypes. The outer reserve construction gives `h+q=k`, so its second
reassembly has exactly `k` colors on the original graph.

The original deficit `a` may be zero. `TwoCore` derives `a ≥ 0` from the
embedded core's degree upper bound and its lower bound `k-a`; it then
uses `a+1` as the positive error required by the reserve selection. The
public hypothesis already controls `a+1`, and the weakened core-degree
bounds are proved before invocation. It does not assume strictly positive
original deficit or discard the zero-deficit case.

The final color-class conversion uses actual host regularity. Exactly
`k` colors on a `k`-regular graph force each class to meet every vertex
once; the proved finite color-class identities give disjointness and
coverage of every original edge copy. Empty-index arithmetic and empty
components are covered by the finite constructions. The large-core and
positive-density hypotheses ensure the nontrivial terminal engine is never
applied without its order and density requirements.

## Review conclusion

The inspected source supplies all previously missing terminal modeling,
common-cut label agreement, and two rounds of original-copy reconstruction
needed by the two-core branch of Corollary 4.6. Together with the existing
one-core branch, the newly compiled public bounded-input wrappers match
the unchanged source statement. Subject to the full unchanged project
audit and the required preservation checks, Corollary 4.6 is eligible for
promotion to a fully verified numbered assertion. The main theorem and
the broader fixed-pattern/five-exception obligations remain outside this
review's claimed completion.
