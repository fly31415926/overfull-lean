# Continuation handoff: protected traces and complete two-pair external assembly

## Authoritative starting state

The continuation starts from public commit
`f2510d10c114bcf3d0003b5e2e4e35cb0400167d`, tree
`58fe77f4afaba4b0ab6cf77956afb1c23608cd35`. The baseline contains the preceding
native partner reserve and two-pair construction, including its full-verifier
and publication evidence. The working branch is
`continuation-protected-traces-20261125T121903Z`; the current run is
[`verification/runs/20261125T121903Z`](../verification/runs/20261125T121903Z/).

The numbered inventory remains **51 of 69**. The main theorem is unverified.
The separately recorded current-source ordinary-core coloring endpoint and
all earlier verified declarations remain within the preservation obligation.
No numbered statement is promoted by the new supporting constructions.

## What this continuation proves

There are **16 new modules and 75 public theorem proofs**. The exact inventory,
statements and semantic scope are recorded in the
[source manifest](protected-trace-source.json),
[proof map](protected-trace-verification.md), and
[semantic review](protected-trace-semantic-review.md).

The new modules form the following chain:

| Modules | New construction |
| --- | --- |
| `NativeReserve/PartnerTraces.lean`, `PartnerGeneralTraces.lean` | Actual residual joining traces of the native compressed boundaries are empty or singleton. Unpaired exceptional incidences remain internal to their assigned core; the general result does not assume that the two pairs exhaust `Z`. |
| `ResidualPalette/FourReservedPrimary.lean`, `FourProtectedPalette.lean` | Force actual reserved singleton crossings into four-label primaries and preserve their full protected classes; construct injectively assigned empty protected classes in the even case. |
| `NativeAssembly/TwoPairProtected.lean`, `TwoPairBounds.lean`, `TwoPairGeneralProtected.lean` | Derive protected native palettes, pair completion and actual joining-degree bounds from the reserve and retained-core degrees. |
| `WeightedPalette/FourGrouping.lean`, `NativeWeighted/FourJoining.lean`, `TwoPairNative.lean` | Construct protected four-label palettes with the needed `h/8` star weights from actual copy incidences and core deficit. |
| `AssignedParts/TwoPairOneStar.lean` | Derive the zero-or-one-unpaired-vertex alternative and the exact assigned-core fiber of a possible fifth exception. |
| `NativeAssembly/TwoPairStarBase.lean`, `TwoPairStar.lean`, `TwoPairStarReserve.lean` | Complete both pairs and the remaining assigned-core star while retaining the entire actual protected boundary, including its star copy. |
| `NativeCore/TwoPairParity.lean`, `TwoPairExternal.lean` | Transfer assigned-fiber cut parity to the original cores and construct the complete native external family, including its actual total core loads. |

The weighted grouping works on the full `h`-color palette. Its conflict count
is at most `8*D` for shared endpoints and `32*D` for at most two weight
resources, yielding the explicit `h-t-40*D` capacity margin. The construction
proves the actual class weights at most `h/8`; it does not require a separate
product bound of the form `12*L*b <= h/8`. Such a bound would be too strong
when both `L` and the bundle bound grow linearly with graph order.

## Exact native endpoint

The strongest new endpoint is
`Overfull.NativeCore.exists_native_two_pair_external_palette` in
[`Overfull/NativeCore/TwoPairExternal.lean`](../Overfull/NativeCore/TwoPairExternal.lean).

Its original objects and hypotheses are:

- An original multigraph, two disjoint old cores `U₀`, `U₁`, an exceptional
  set `Z` disjoint from them, and a partition of all vertices by these sets.
- An original perfect matching `M` with exactly two distinct internal
  exceptional copies `e₀`, `e₁`, and `Z.card <= 5`.
- An actual `PartnerBoundaryPacking Q` of size `r`, a deletion family `N/T`
  avoiding every reserve boundary, and the actual residual subtype
  `H = residualGraph G N T`.
- `H` is `h`-regular and has no `h`-overfull vertex set. The embedded cores
  on the original shores have degree at least `h-D`.
- An injective choice `q : Fin t -> Fin r` of protected reserve indices,
  `h <= r+D`, and the following numerical hypotheses:

```text
0 < h
128*D <= h
2*t <= h
0 < L
|V|*D <= 2*L*(h-t-40*D).
```

The parameters in these budgets are natural numbers, including truncated
subtraction. The retained-core degree inequalities in the Lean statement
are cast to real numbers. The theorem derives the actual joining-degree
bound and its two-pair/no-star or two-pair/one-star branch internally.

It constructs an injective map `f : Fin t -> Fin h` and actual residual
copy classes `F : Fin h -> Finset E_residual` with all of the following
properties:

- Every class is a matching and distinct classes are edge-disjoint.
- `F (f i)` equals the entire `Q.residualBoundary N T (q i)`.
- Every class saturates every vertex in `Z`.
- The union is exactly `joiningCopies H label` together with all
  `exceptionalCopies H univ Z`.
- Every assigned-fiber cut has the correct cardinality parity, and each
  original core has an even number of uncovered vertices in every class.
- Each class has at most `6*L+3` copies and `12*L+6` support vertices.
- Every class is disjoint from both embedded old-core edge sets, and each
  old-core vertex belongs to the support of at most `D` classes.

The inputs do not include a joining palette, its protected traces, any
star-weight inequality, a pair completion, a supplied exceptional case split,
or a free-color/cardinality balance. Those objects and identities are proved
from the inputs above. Both possible assignments of the fifth vertex to an
old core are handled. Original parallel copies, the residual subtype and
selected reserve indices remain distinct.

This endpoint is conditional external assembly. It does not construct the
safe residual, complete the classes inside the robust cores, or factor the
terminal remainder. Its union statement does not claim to cover old-core
internal edges.

## Verification and independent review

All final new modules have genuine successful strict focused compiler
receipts in the current run, with `-DwarningAsError=true`, the corresponding
source snapshots and output hashes. All failed development attempts remain
in the run. In particular, the final endpoint has the retained receipt
[`two-pair-external-04/command.json`](../verification/runs/20261125T121903Z/focused/two-pair-external-04/command.json);
its successful source hash is
`e39608d92ccb73cc0f144866fa74eb1ae7f1355bc68b2272d3ea5e5aa2b954d5`.
The final parity module has the retained receipt
[`two-pair-core-parity-01/command.json`](../verification/runs/20261125T121903Z/focused/two-pair-core-parity-01/command.json).

The independent cross-review of the weighted and native modules is retained
in [`pair-star-independent-review.json`](../verification/runs/20261125T121903Z/pair-star-independent-review.json).
Its bytes are preserved; the final parity and external modules are assessed
in a separate
[`pair-star-independent-review-addendum.json`](../verification/runs/20261125T121903Z/pair-star-independent-review-addendum.json).
The three pair-star modules authored by that reviewer are assessed by the
other reviewer in the consolidated run review.

At preparation of this checkpoint text, the full build, declaration/axiom
audit and preservation gate were pending. Read the actual
`full-*/terminal.json` and `preservation.json` in the current run for their
subsequent outcome. A successful focused check is not a full-project pass.
The full gate must run the actual verifier, retain its output, freeze and
compare its inputs, and audit all public, private and generated declarations.
The allowed axioms remain `propext`, `Classical.choice` and `Quot.sound`.

The preservation check must compare every prior nonroot mathematical source,
all old declaration/module/axiom records and result mappings, the old
declaration maps, all 69 numbered records, `Audit.lean`, and the toolchain
pins against the baseline. New imports and result entries must correspond
to the exact new-source inventory. Publication is established only by actual
remote object and both-branch readbacks in the run's publication receipts;
local source, focused checks and a local commit do not establish publication.

## Concrete remaining work

Do not repeat the protected-trace construction, four-label reserved primaries,
two-pair-plus-one-star assembly or old-core parity transport unless a genuine
failed gate identifies a defect.

The next mathematical target is a safe residual built from the original
hypotheses while preserving the whole partner reserve. The detailed
[source-based plan](partner-safe-residual-next-step.md) identifies an
obstruction in the old aggregate exceptional-pair pool: two different
exceptional pairs can cross a whole shore differently. Simply changing the
old signature type or replacing `Z.card <= 2` by `Z.card <= 5` does not repair
cut uniformity or greedy realization.

Add unordered exceptional-pair-specific pools and prove full-partner
compressed-boundary usage, disjointness, coverage, capacity and whole-cut
accounting. The existing arbitrary-`Z` parity and generic `WeightedSafety`
interfaces can then be reused with these actual counts. The old greedy,
rounding and rejection constants must be recomputed for the larger template
sizes and code space before deriving the residual's degree and palette
budgets. The detailed note distinguishes proposed lemmas from proved inputs;
it is not itself a theorem or residual-safety certificate.

The heavy representative is selected from the entire partner-code space;
its number of exceptional pairs cannot be assumed to be two. The zero-pair
and one-pair cases may leave five and three unpaired exceptions and still
require native simultaneous multi-star assembly with enough weight resources.
For the two-pair branch, robust-core completion and terminal factorization
must still be connected from the original hypotheses after safe residual
construction.

Pinned Lemma 4.4 and Corollary 4.5 therefore remain unfinished. The critical
average-degree input, critical-case compositions, mixed and bipartite cases,
dense integral packing and absorption, padding, and the main theorem remain
separate obligations. Recovery of the exact older Theorem 1.2 and Corollary
3.2 statements is also still a separate source-identity task.
