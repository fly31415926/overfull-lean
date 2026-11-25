# Semantic review of the native two-pair continuation

## Assessment and review provenance

The new declarations prove substantial components of the native construction:
four actual assigned fibers, partner-preserving reserves, residual copy
injections, four-label joining palettes, simultaneous pair completion, and
terminal coloring with two closed pair components. The reviewed statements
do not complete pinned Lemma 4.4, Corollary 4.5, or the full two-pair branch
from its original hypotheses. The numbered inventory remains 51 of 69, with
every original numbered statement and status retained. The main theorem
remains unverified.

The baseline is commit `5679471018d5d087d942c592c72fca3d24e7ea32`, tree
`918663f3827a27a29312835f7b2218d850326a0d`. This review covers the thirteen
new mathematical modules recorded, with their inspected hashes, in
`verification/runs/20261125T023700Z/independent-review.json`.

The `terminal_two_pairs` agent independently read the new modules authored
by the root, `assigned_two_pairs`, and `remote_audit` agents. Its own two
modules, `NativeTerminal/TwoPairs.lean` and
`NativeAssembly/TwoPairBoundary.lean`, were independently inspected by both
the root and `remote_audit`. Those cross-reviews found no semantic issue and
confirmed the closedness, disjointness, exact-copy, and boundary-support
hypotheses described below. No mathematical source was changed during this
review. The review does not substitute for the full kernel and preservation
gate.

## Assumption map

The following distinctions are essential when using the new endpoints.

| Module | What it constructs | Inputs that remain hypotheses |
|---|---|---|
| `AssignedParts/TwoPairs.lean` | Separate endpoint pairs, four assigned labels, exact fiber identities, and the even/even or odd/odd core parity alternative | An original perfect matching, the original disjoint covering core/exceptional partition, and exactly two internal exceptional matching copies |
| `AssignedParts/PartnerSignatures.lean` | A finite code retaining actual exceptional partners; equal codes recover both assigned cores and each pair's parallel-copy supply | Perfect matchings for the semantic interpretation; the original partition for recovery of both assigned cores |
| `AssignedParts/PartnerLabels.lean` | Transport of the representative's explicit pair ordering and identical four-label function through every matching of the same code | Equal full partner codes and the original two-copy enumeration |
| `NativeReserve/PartnerPacking.lean` | A heavy actual representative and a linear family of disjoint compressed boundaries with its full code | For the native existence endpoint: regular degree `k`, no `k`-overfull set, `k >= 201684`, and at most five exceptions |
| `NativeReserve/PartnerResidual.lean` | Exact surviving boundary copies, matching and disjointness, and injective pair-copy selections with retained reserve indices | The deleted copies avoid the entire reserved union; an injective choice of reserve indices |
| `ResidualPalette/FourProtectedGrouping.lean` | Matching-piece grouping with exact protected primary classes and explicit size/load budgets | A disjoint family of actual matching pieces, its incidence bound, chosen primary/protected sets, and the displayed capacity margin |
| `ResidualPalette/FourTwoOddGrouping.lean` | A complete two-odd joining palette, optionally retaining chosen primary pieces as whole classes | An actual four-label two-odd decomposition, bounded joining degrees, and the displayed grouping budget |
| `AssignedParts/TwoPairPalette.lean` | The actual four-fiber parity and a complete unprotected joining palette in a supplied host; no decomposition or palette is supplied | Original matching/partition data, regularity and no-overfull safety of the actual host, bounded joining degree, and numerical grouping budgets |
| `ExceptionalPalette/TwoPairs.lean` | Both pair-pool colorings simultaneously, exact cuts and coverage, and saturation of both pairs in each color | One original joining palette, two distinct size-two fibers with even cut parity, degree equal to the palette size on the pairs, and separately injective free-color seed prescriptions |
| `NativeAssembly/TwoPairBoundary.lean` | Pair seed freedom and the exact joining-plus-two-copies boundary identity | An actual matching boundary containing the specified pair copies; the identity additionally needs pair-only nonjoining support |
| `NativeAssembly/TwoPairs.lean` | Independent seed extensions and exact preservation of all selected boundaries in their protected colors | A joining palette, pair-copy injections, injective protected colors, exact joining traces, and pair-only boundary support |
| `NativeAssembly/TwoPairReserve.lean` | The preceding completion using copies supplied by the actual partner reserve and its residual | Reserve-avoiding deletions, residual regularity, the joining palette and its exact protected traces; pair-only support is assumed or derived by the no-unpaired corollary |
| `NativeTerminal/TwoPairs.lean` | Coloring of two separately closed pair components and uniform factorization of the resulting two-shore terminal geometry | Closed pair cuts, disjoint covering terminal shores, regularity, robust cores, bounded-star incidence, the degree/error inequalities, and the displayed even/odd shore-cut alternatives |

## Pair identity and original-copy preservation

The new assignment starts with the actual two internal copies of an original
perfect matching. Matching disjointness makes their endpoint sets disjoint,
and looplessness makes each endpoint set have size two. The prior assigned
core-part lemmas give disjointness from both cores and coverage of the whole
vertex type. Even total order is derived from the original perfect matching;
the parity of the two assigned cores is then derived from the two even pair
fibers. These are constructed properties, not a supplied four-part partition
or supplied parity alternative.

The pair order is an explicit enumeration of the representative's copies.
No canonical ordering on an arbitrary vertex type is asserted. Equal partner
codes provide actual parallel copies in another matching, and the new
transport theorem aligns the first endpoint pair with its original first
pair. Consequently the label function is unchanged. Parallel copies remain
different elements of the edge type even when their endpoint sets coincide.

`matchingPartner` has a default value for an unmatched vertex, but the
semantic recovery theorems use actual perfect matchings. They therefore do
not mistake that default for a genuine exceptional partner. The code has
`(2+|Z|)^|Z|` possible values, including unrealizable functions. Counting all
of them gives the valid upper bound `7^5 = 16807` for at most five exceptions.

Heavy-code selection ranges over this entire space. It does not presume that
the selected representative has two exceptional pairs. The zero-pair and
one-pair possibilities remain available and still require their own native
assembly. The construction chooses whole compressed boundaries of size at
most six, with one incidence at each exception, rather than independent
numerical supplies for the separate pairs. Its explicit witness
`r = floor(k/100842)` satisfies `r >= k/201684` for `k >= 201684`.
These are sufficient reserve constants, not optimized degree thresholds.

Residual transport is a genuine copy-preserving step. Its edge type is the
subtype of original copies outside the removed union. The avoidance
hypothesis proves that every selected original boundary copy survives.
The image of each residual boundary is exactly the original boundary, and
its selected index is still `q i`. Pair-copy injectivity follows from the
disjoint original boundaries and injectivity of `q`; it is not obtained by
identifying parallel copies. The selected residual edge has exactly the
original specified endpoint pair.

## Joining palettes and protected traces

The generic protected grouping has conflict margin `2*s*D + |Q|` for pieces
of size at most `s`. The additional conflicts prohibit surplus pieces from
using a protected primary's color. The primary colors are injective, so a
protected class is precisely that primary piece. The result retains exact
coverage, matching, copy disjointness, and the whole-class incidence load.

For four-copy pieces, the margin is `8*D + |Q|`, the constructed class bound
is `4*L`, and the support bound is `8*L`. The joining-palette interface stores
these results at capacity `2*L`, so its formal bounds are the weaker
`6*L` and `12*L`. This rescaling is explicit. One must therefore substitute
the interface capacity, rather than the earlier grouping parameter, when
using subsequent `3*L+2` and `6*L+4` bounds.

The two-odd grouping assigns exactly one primary piece to every color.
Every other piece in that color has even fiber cuts, so adding surplus
preserves the primary's exact cut parity. The protected theorem preserves
chosen members of the primary family; it does not assert that an arbitrary
native boundary trace is a primary piece, nor does it supply an arbitrary
previously fixed protected-color map.

The actual-host endpoint in `TwoPairPalette.lean` first derives the four
fiber parities from the original matching, then constructs the appropriate
decomposition in the actual regular, non-overfull host. Its assumptions
include the actual joining-degree bound `D`, `0 < L`, `8*D < h`, and
`n*D <= 2*L*(h-8*D)`. It supplies an unprotected joining palette. The theorem
does not construct a reserve-avoiding residual with these properties, and
the native selected boundaries are not arguments to this endpoint. Exact
protected joining traces must still be established in the native proof.

## Simultaneous completion and whole-boundary identities

Both single-pair completions are applied to the same original joining
palette. The first completed family is never treated as another joining
palette. Their union counts that common joining class only once.

The two inserted internal pools have disjoint vertex support. Consequently
the pair copies belonging to one reserved boundary may receive the same
protected color. Injectivity is required separately within each pair pool;
disjoint color ranges across the two pools would be an incorrect extra
requirement and are not imposed. The combined family covers exactly the
joining copies and the two full internal pools, is a disjoint family of
matchings, saturates both pairs in every color, and preserves each fiber cut
as an exact set of copies. Each outside footprint is unchanged, not merely
bounded anew. At joining-palette capacity `L`, the resulting bounds are
`3*L+2` copies, `6*L+4` support vertices, and outside load at most `D`.

The seed maps in `NativeAssembly/TwoPairs.lean` are constructed from the
actual pair-copy injections using `Function.extend`. A default map is
obtained from the pair-pool/free-color equicardinality, so no unjustified
inhabitant of `Fin h` is selected when `h = 0`. The exact same protected color
is retained in both pair prescriptions.

For exact whole-boundary preservation, the boundary identity needs all
nonjoining copies to meet the two pair fibers. A matching containing the
two pair copies can then contain no other copy incident with those vertices,
and its entire nonjoining portion is precisely those two copies. The separate
`reserved_pairFiber_free` theorem has no such support restriction and remains
valid when an additional nonjoining star copy is present.

`exists_partner_two_pair_completion` derives the actual injections from the
partner reserve and its residual transport before applying that identity.
The no-unpaired corollary also derives the support restriction when the
exceptional set is exactly the union of the two endpoint pairs and the old
cores have distinct constant labels. It still assumes a joining palette,
residual regularity, reserve-avoiding deletions, and exact protected traces.
It does not complete the native branch from the original source hypotheses.

## Terminal factorization

The two pair components are colored separately with the same degree palette.
Closedness places every incidence of a retained pair copy in its own shore;
disjointness then rules out cross-component conflicts. This argument permits
four pair vertices in total and retains every original parallel copy.

The uniform terminal theorem keeps the original robust-shore constants and
all geometric assumptions. Even shores are colored as components. Odd
shores are contracted at their common cut and aligned on the same original
crossing copies before gluing. No coloring of a pair union of size four is
obtained by applying a size-two theorem directly to that union. Closed pair
cuts and the required residual shore/star geometry remain inputs to this
terminal endpoint.

## Remaining obligations

1. **Construct a suitable native residual.** The regularity, no-overfull
   safety, degree margins, reserve avoidance, and high internal degree of
   the selected exceptional pairs must hold simultaneously in the residual
   used for palette construction. A linear number of retained parallel
   copies by itself does not imply the required small joining-degree bound.
2. **Construct the protected joining traces.** The selected whole native
   boundaries must be placed in one joining palette with the same protected
   labels and exact traces. The new unprotected palette theorem and protected
   primary grouping do not, by themselves, establish this alignment.
3. **Assemble the possible fifth exception.** Exactly two pairs can leave
   one unpaired exception when `|Z| <= 5`. Its assigned-core star must be
   completed together with the pairs while preserving whole boundaries,
   cuts, saturation, and degree/weight budgets. The pair-only boundary
   equality does not include an extra internal star copy.
4. **Complete the other partner-code branches.** Zero pairs can leave five
   unpaired exceptions, and one pair can leave three. The old native
   external/unpaired assembler still assumes `Z.card <= 2`; the old native
   single-star theorem assumes all of `Z` is one singleton; and the existing
   weighted native grouping permits at most two star resources. The new
   general protected grouping is not a multi-star assembly theorem. The
   corresponding larger star systems and same-label internal bundles remain
   to be constructed and counted.
5. **Connect the assembled classes to terminal geometry and the pinned
   source statements.** Terminal cut and star-incidence hypotheses must be
   derived from the native construction, after which the original-copy
   reassembly must be completed. Only then can the exact pinned statements
   be reconsidered for promotion. Other outstanding global, critical-case,
   mixed/bipartite, packing, absorption, padding, and source-identity tasks
   are unaffected by this continuation.

## Verification evidence and preservation

Each of the thirteen reviewed modules has a genuine successful focused
check with `lake env lean -DwarningAsError=true`; the command receipts and
all successful and failed outputs are retained under the run's `focused/`
directory. The inspected source hashes and the successful receipt paths
are recorded in `independent-review.json`. Module builds also succeeded.
These focused results do not establish the full project audit.

The new run infrastructure pins the baseline and allows only the registered
additive root imports and verifier registrations. It checks every previous
nonroot mathematical source, the stock `Audit.lean`, the original 14,830
audited declarations with their modules and axiom sets, the 2,844 previous
completed-result mappings, every old declaration map, and all 69 numbered
records. It also checks that all new mathematical modules are exactly those
listed in the new source manifest and that every added audited declaration
is present in the new complete map. The allowed axioms remain `propext`,
`Classical.choice`, and `Quot.sound`.

The wrapper freezes and archives its actual inputs and controls, executes
the stock verifier, retains real output, and compares the frozen bytes
afterward. Final verification is established only by a successful
`full-*/terminal.json` and its `preservation.json` in this run. Public
publication is established separately by the remote objects and both-branch
readbacks. This semantic review makes neither claim in their absence.
