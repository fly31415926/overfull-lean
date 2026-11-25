# Continuation handoff: native two-pair construction

## Authoritative starting state

Both `main` and `verified-bipartite-continuation-2026-11-21` were fetched and
read at `5679471018d5d087d942c592c72fca3d24e7ea32`, tree
`918663f3827a27a29312835f7b2218d850326a0d`, before this run. That public commit
contains the complete ordinary-core checkpoint and publication evidence.
No source reconstruction was needed.

The baseline full verifier records 14,830 audited declarations and 51 of 69
numbered manuscript assertions. The main theorem is unverified. The preceding
current-source ordinary-core coloring theorem is separately identified from
the older pinned Theorem 1.2 and remains preserved in full.

## New proved components

This continuation introduces 13 modules and 82 public theorem proofs. Read
`docs/two-pair-native-source.json`, `docs/two-pair-native-verification.md`, and
`docs/two-pair-native-semantic-review.md` for exact statements, hashes, source
locations, assumptions and review provenance.

1. `AssignedParts/TwoPairs.lean` constructs the four actual fibers from an
   original perfect matching with two internal exceptional copies. It proves
   the pair sizes, disjointness, covering and core-parity alternatives. It also
   proves that five exceptions allow at most two pairs, and two pairs leave
   at most one unpaired exception.
2. `PartnerSignatures.lean` and `PartnerLabels.lean` retain every exceptional
   partner and assigned core. Equal codes give the same four labels after
   actual parallel representatives are aligned. No arbitrary vertex order or
   canonical ordering is asserted.
3. `NativeReserve/PartnerPacking.lean` constructs actual disjoint compressed
   boundaries for any exceptional set of size at most five. The heavy code is
   chosen from the whole `(2+|Z|)^|Z|<=7^5` space, so it is not assumed to have
   two pairs. For `k>=201684` the construction uses `r=floor(k/100842)` and
   proves `r>=k/201684`. These constants have not been optimized.
4. `NativeReserve/PartnerResidual.lean` transports the whole reserve and the
   actual parallel pair copies into a reserve-avoiding residual, retaining
   exact reserve indices, endpoints, matching and disjointness.
5. `ResidualPalette/FourProtectedGrouping.lean` and `FourTwoOddGrouping.lean`
   construct protected grouping for bounded-size pieces and four-label
   two-odd palettes. The four-copy margin is `8D+|Q|<h`. At capacity `2L`,
   the existing `JoiningPalette` interface accommodates the true `4L`/`8L`
   grouping bounds. `AssignedParts/TwoPairPalette.lean` constructs the actual
   unprotected four-fiber palette from a regular non-overfull host and its
   explicit joining-degree and numerical budgets.
6. `ExceptionalPalette/TwoPairs.lean` completes both pairs relative to the
   same original joining palette. Independent injective seeds may share the
   protected color of one boundary. Exact fiber cuts, copy coverage, matching,
   disjointness, and outside support are preserved.
7. `NativeAssembly/TwoPairBoundary.lean`, `TwoPairs.lean` and
   `TwoPairReserve.lean` prove exact whole-boundary preservation from actual
   reserve injections and protected joining traces. When the pairs exhaust
   the exceptional set, the pair-only support condition is derived from
   distinct constant labels on the old cores. The joining traces still need
   construction in the full native argument.
8. `NativeTerminal/TwoPairs.lean` factors the terminal host with two robust
   assigned shores and two separately closed pair components, retaining the
   original even/odd alternatives and bounded-star incidence hypotheses.

## Verification and preservation

The actual run is `verification/runs/20261125T023700Z`. All focused attempts,
including failures and their source snapshots, are retained. The restored
Lean 4.24.0 executable has the same binary hash as the preceding verified run.

Read the actual `full-*/terminal.json` and `preservation.json` to determine
full success. The full gate runs `python3 scripts/verify.py`; only additive
source registration and result-map entries were made to that verifier. The
stock `Audit.lean` is unchanged. All inputs and run controls are frozen and
compared after execution. The audit permits only `propext`, `Classical.choice`
and `Quot.sound` and maps every new public, private and generated proof.

The preservation gate requires every previous nonroot mathematical source,
every old declaration with its module and axioms, every old result mapping,
every old declaration map, and all 69 numbered records to remain unchanged.
New declarations and imported modules must match the new manifest exactly.
Publication is established only by actual remote object and both-branch
readbacks in `publication/`; do not infer publication from a local commit.

## Concrete remaining work

Do not repeat the now-proved pair code, reserve selection, pair completion,
or closed-pair terminal gluing unless an actual failed gate identifies a defect.

The next connection is to construct protected native joining traces for the
four-label palette, rather than supply them. In the no-unpaired two-pair case,
the compressed boundary is the two internal pair copies plus zero or one
old-core crossing. Thus the trace is empty in the even case and is an actual
reserved singleton crossing in the odd case. Generalize the existing forced
reserved-primary construction from three labels to the proved four-label
circuit interface, preserving the actual residual copy and reserve index;
then apply the new protected grouping. Empty protected classes in the even
case also need an actual supply and injective color assignment.

The native reserve-avoiding matching removals must still produce a safe
regular residual with the required joining and star degree budgets. The new
linear reserve theorem is not a residual-safety theorem. Partner codes must
replace coarse codes in any weighted pool/small-cut bookkeeping used here.

For two pairs plus one unpaired exception, assemble the remaining assigned-core
star while retaining the whole protected boundary. The old single-star theorem
assumes all exceptions form a singleton and cannot directly be applied to
this five-exception host. Pair-only whole-boundary equality excludes an extra
internal star copy; only the pair-free-on-joining-trace lemma allows it.

The zero-pair and one-pair branches can leave five and three unpaired
exceptions respectively. They require native multi-star assembly and
same-label-bundle bookkeeping. Existing generic weighted extension and terminal
star interfaces do not themselves construct those native inputs.

Accordingly, pinned Lemma 4.4, Corollary 4.5, and all other unfinished numbered
records remain unfinished: the inventory is still 51/69. The critical
average-degree input, critical-case compositions, mixed and bipartite cases,
dense integral packing and absorption, padding, and the main theorem remain
separate obligations. Exact recovery of the older Theorem 1.2 and Corollary 3.2
statements is also still a separate source-identity task.
