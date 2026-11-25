# Native two-pair continuation

## Scope and baseline

This continuation starts from public commit
`5679471018d5d087d942c592c72fca3d24e7ea32`, tree
`918663f3827a27a29312835f7b2218d850326a0d`. Both requested branches were read
at that commit before editing. The baseline contains the complete published
ordinary-core checkpoint and its publication receipts.

The new work supplies native ingredients for the two-core construction with
up to five exceptional vertices. It does not complete pinned Lemma 4.4 or
Corollary 4.5. All 69 numbered records, their statement identities, and the
51 completed statuses remain unchanged. The main theorem remains unverified.

The exact module inventory and public theorem locations are in
`two-pair-native-source.json`. The full verifier creates the complete map of
public, private, and generated proof declarations in
`verification/two-pair-native-declarations.json`. A focused compilation alone
does not establish that the full project audit passed; read the actual
`full-*/terminal.json` and `preservation.json` under
`verification/runs/20261125T023700Z`.

## The obstruction addressed

With at most two exceptions, an internal exceptional matching copy uses the
entire exceptional set. The former code could therefore record only whether
such a pair existed, or otherwise record each exception's assigned core.
For five exceptions that code loses essential information: there can be two
different internal pairs, or a pair together with unpaired exceptions.

The new construction retains the separate pair identities. It works with
actual multigraph edge copies throughout. A change from one parallel copy to
another may preserve its endpoints and assignment code; it does not identify
the two copies in a matching, reserve, residual, or coloring.

## Actual four-part assignment

`AssignedParts/TwoPairs.lean` uses an explicit enumeration of the original
perfect matching's two internal exceptional copies. Their endpoint sets are
two disjoint sets of size two. They are also disjoint from both assigned core
parts, and these four parts cover the original vertex type.

The assigned cores receive labels 0 and 1 and the pair parts labels 2 and 3.
The total order is even because the original host has a perfect matching.
Since both pair parts have even order, the two core-part parities agree. The
four fibers are therefore all even or exactly the first two are odd. The
endpoint `exists_two_pair_assigned_labels` obtains the two-copy enumeration
from the actual internal-copy count; it does not assume a four-part partition
as a supplied conclusion.

Two additional counting facts retain the original exceptional bound: a
matching has at most two internal copies when the exceptional set has size
at most five, and exactly two such copies leave at most one unpaired exception.
No step changes the five-exception statement to a two-exception statement.

## Partner codes and native reserves

`AssignedParts/PartnerSignatures.lean` assigns to every exceptional vertex
either its matched core or its actual exceptional partner. Its finite code
type is `Z -> (Fin 2 + Z)`. Matching uniqueness makes the selected opposite
endpoint independent of any choice of a matching edge. For perfect matchings,
the code recovers the first assigned core, the full paired support, and hence
the second assigned core.

For each internal copy of one representative, every matching with the same
code contains an actual parallel copy. `AssignedParts/PartnerLabels.lean`
applies this to both pairs. It proves that the two chosen copies exhaust the
other matching's internal exceptional copies and give the same four labels.
The representative's explicit ordering of the pairs is transported through
their endpoint sets. No canonical ordering of arbitrary vertex types is
asserted.

The complete code space has cardinality `(2+|Z|)^|Z|`, at most `7^5=16807`
when `|Z|<=5`. `NativeReserve/PartnerPacking.lean` applies the existing native
perfect-matching distribution and weighted selection theorem to that entire
space. A heavy actual representative has scaled code weight at least
`k/16807`. Its compressed boundaries have at most `|Z|+1<=6` original copies.
Whole boundaries, rather than independent pair pools, are selected disjointly.

The endpoint `exists_linear_partner_boundary_reserve` gives an actual reserve
with `r>=k/201684` when `k>=201684`; its construction chooses
`r=floor(k/100842)`. These are sufficient
constants for this reserve step and are not claimed to be optimal. Selection
does not assume that the heavy representative has two pairs: it also permits
the zero-pair and one-pair patterns. Every exceptional vertex is covered once
in each selected boundary. Each original exceptional pair receives distinct
actual parallel copies at the different reserve indices.

`NativeReserve/PartnerResidual.lean` transports these boundaries into the
actual residual edge subtype when the deleted copies avoid the reserved
union. Matching, disjointness, membership, and the selected reserve indices
are retained. The resulting pair injections refer to the surviving original
copies; no fractional decomposition of the residual is assumed by this
transport step.

## Four-label palettes

The already proved compatible-circuit construction gives matching pieces of
size at most four for four assigned labels. The new protected grouping extends
the corresponding bounded-size argument to protected primary pieces. A
protected primary color receives no surplus piece. For four-copy pieces the
endpoint-conflict allowance is `8D`; with `q` protected primaries it is
`8D+q`. The class and support bounds are `4L` and `8L`.

`ResidualPalette/FourTwoOddGrouping.lean` groups the two-odd decomposition
with exactly one primary per color and even-cut surplus pieces. It preserves
the actual cut parity and every protected primary piece. Its result uses the
existing `JoiningPalette` interface at capacity `2L`, which explicitly allows
the weaker bounds `6L` and `12L`.

`AssignedParts/TwoPairPalette.lean` combines the actual four-part parity with
the all-even and two-odd four-label constructions. It constructs an
unprotected joining palette in a supplied regular non-overfull host from
the joining-degree and numerical grouping budgets. This removes a supplied
palette from that endpoint, but it does not construct a safe residual or
establish those degree budgets in the full fixed-pattern argument. Nor does
the protected grouping by itself align selected native reserve traces with
protected primary pieces.

## Simultaneous pair completion and exact boundaries

`ExceptionalPalette/TwoPairs.lean` constructs the two single-pair completions
relative to the same original joining palette. It then combines their color
classes. It does not apply the single-pair theorem to a family that no longer
satisfies the `JoiningPalette` definition.

The pair supports are disjoint. Therefore the two reserve copies from one
boundary may use the same protected color. The completed classes remain
matchings, use disjoint actual copies across colors, and cover exactly the
original joining copies and both complete internal pair pools. Every color
saturates both pairs, every assigned-fiber cut is unchanged, and support
outside the two pair parts is unchanged. At capacity `L`, the bounds are
`3L+2` copies, `6L+4` support vertices, and outside load at most `D`.

`NativeAssembly/TwoPairBoundary.lean` proves that a matching boundary with
its two internal pair copies is exactly its joining trace plus those copies,
provided all its other copies are joining copies. The joining trace is free
at all four pair vertices. A separate freedom theorem allows additional
nonjoining copies, including an assigned-core star.

`NativeAssembly/TwoPairs.lean` constructs both injective seed prescriptions
and proves exact whole-boundary preservation when those pair-only support
and joining-trace hypotheses hold. It handles an empty palette without an
extra positive-degree assumption. `NativeAssembly/TwoPairReserve.lean`
derives the actual pair injections and matching boundaries from the native
reserve and its residual transport before applying this completion.
When the two endpoint pairs exhaust the exceptional set and the old cores
have distinct constant labels, its no-unpaired corollary also derives the
pair-only boundary containment from the compressed boundaries themselves.
The exact protected joining traces remain explicit inputs.

An extra internal assigned-core star copy is not part of the two-copy
boundary identity. The two-pair-plus-one-unpaired-exception case still needs
that star to be assembled while retaining its whole protected boundary.

## Terminal coloring

`NativeTerminal/TwoPairs.lean` colors two separately closed components of
order at most two with the same degree palette. It then glues those colorings
on the retained original edge types. The union is not assumed to have order
at most two.

The uniform endpoint combines this pair coloring with the existing two robust
assigned-shore factorization. It retains the even/odd shore alternatives,
regularity, bounded-star incidence, cut equality, expansion, and degree
hypotheses. In the odd case the shore colorings are aligned on the same
original crossing copies. The constants are chosen before the host, as in
the existing shore theorem. This is a terminal theorem under its geometric
inputs, not a construction of those inputs from the original five-exception
host.

## What remains

The full native construction must construct a safe residual, establish the
joining and star budgets, and align actual native reserve traces with the
protected joining palette. It must then assemble the possible extra star
in the two-pair branch. The one-pair branch can have three unpaired exceptions
and the zero-pair branch five; their multi-star assembly and same-label bundle
bookkeeping also remain unfinished. The current two-star and two-resource
native endpoints cannot silently be used for those larger counts.

The new general protected grouping, partner reserve, simultaneous pair
completion, and terminal gluing are proved components available for this
work. Neither the 51/69 inventory nor the main-theorem status is promoted.
The critical average-degree, critical-case, mixed and bipartite, dense
integral packing and absorption, padding, and older source-identity tasks
remain separate obligations.

## Verification and evidence

The run uses the pinned Lean 4.24.0 and pinned dependency revisions. The
restored compiler binary has the same SHA-256 as the preceding verified run.
All focused attempts retain genuine compiler output and command receipts;
failed attempts are preserved with the successful repairs.

The full gate freezes all mathematical and verification inputs and the run
controls, executes the stock verifier with additive module registration,
then compares the frozen bytes and the entire previous audit. It requires
every old nonroot mathematical source, the stock axiom audit, each prior
declaration with its module and axiom set, every old completed-result mapping,
and every prior declaration map to remain unchanged. New declarations must
belong exactly to the new registered modules and map to their actual source
hashes. The only permitted axioms remain `propext`, `Classical.choice`, and
`Quot.sound`. Publication is established separately by actual remote object
and both-branch readbacks.
