# Semantic review: actual assigned parts and joining composition

## Review boundary and provenance

This review concerns the recreated modules under `Overfull/AssignedParts/`.
The earlier isolated drafts did not survive the workspace replacement. The
current files therefore require fresh checks; they are not described as a
byte-for-byte recovery of those unpublished drafts.

The reviewer authored `Basic.lean` in this recreation. The independent part
of this review covers `PairFiberParity.lean`, `ThreePartLabels.lean`,
`MatchedCuts.lean`, and `JoiningConstruction.lean`. The agent responsible for `MatchedCuts` separately reviewed `Basic.lean`
with SHA256 `033a7aebbe8903f2ad647f32d3d8e85dea58a3ddbf5fad12c7b91140fe446d12`
and found no semantic defect: the support handshake, retained matching
witnesses, exact partition and derived parity have the stated scope. This review
does not replace Lean compilation or the complete stock axiom audit.

The source review and compiler evidence are separate. Fresh strict checks of
all five assigned-part modules have passed, as recorded below. Historical
chat reports are not substituted for missing compiler logs. This document is
frozen before the complete repository verification; it makes no claim that
the full audit has already run.

## Original-copy assignment

The input is a specified matching `M : Finset E` in a loopless multigraph
`G : Multigraph V E`, together with original core sets `U₀`, `U₁` and an
exceptional set `Z`. The partition hypotheses are explicit: the three sets
are pairwise disjoint and every original vertex belongs to one of them.
The covering and parity interfaces require that this same `M` is perfect.

An exceptional vertex belongs to `assignedExceptions G M Z U` precisely
when an actual selected copy of `M` joins it to the original core `U`.
The enlarged core is `corePart G M Z U`; `pairPart G M Z` consists of the
endpoints of the copies of `M` internal to `Z`. No endpoint-pair image is
used in place of the original copy type `E`.

Matching uniqueness prevents a vertex from being assigned to two disjoint
cores. It also prevents an assigned exception from simultaneously belonging
to an internal exceptional pair: the two incident selected witnesses must
be the same copy, whose other endpoint would then lie in both a core and
`Z`. Perfect-matching coverage ensures that every remaining exceptional
vertex has a selected neighbor in one core or inside `Z`. These facts give
disjointness and coverage of the actual assigned parts.

The specified representative is retained throughout. The construction does
not replace it with an unrelated existential perfect matching. That matters
when the eventual source-level proof applies the interface to a selected
heavy-pattern representative.

## Exact fibers and the exception bound

`labelOfThreeParts` labels the first part by zero, the second by one, and
the remaining vertices by two. The zero-fiber equality holds directly;
the one-fiber equality uses disjointness of the first two parts; the
two-fiber equality uses disjointness from the third part and full coverage.
The supplied hypotheses give exact equalities of finite sets, not merely
inclusions or cardinality comparisons.

The matching support identity is

```lean
(G.edgeSupport M).card = 2 * M.card
```

It is obtained from the actual selected-degree sum and matching incidence
one at every support vertex. Applied to the internal exceptional copies,
it gives the pair support cardinality as twice the number of those copies.
The support lies in `Z`. Consequently `Z.card ≤ 2` implies at most one
internal selected copy and third-fiber cardinality zero or two.

The bound `Z.card ≤ 2` is explicit in
`exists_two_core_assigned_labels`. Several generic helper statements and
the joining composition do not need it: they may aggregate several internal
exceptional pairs into one even third fiber. That broader statement does
not prove a decomposition with a separate part for each pair, and it must
not be presented as completing the larger exceptional cases of the
manuscript. The single optional pair interpretation uses the displayed
two-exception bound.

## Parity is derived

Perfect-matching support equals the full vertex set, so the matching support
identity proves even total vertex cardinality. Internal matching support
also has even cardinality. The three exact fibers sum to the total order;
the generic arithmetic bridge therefore proves equal parity for the first
two fibers. Splitting their common remainder modulo two gives exactly the
all-even or the two-odd profile accepted by the joining theorem.

No desired fiber parity is assumed in `assignedLabel_parity`. Its inputs
are the actual perfect matching and the original vertex partition.

## Exact selected cuts

The `MatchedCuts` argument first fixes a selected copy `e ∈ M`. If an
endpoint belongs to an enlarged core through an existential matching
witness, matching uniqueness identifies that witness with `e` itself.
Thus its membership can be expressed using the two endpoints of that same
original copy.

A small isolated propositional lemma classifies the two endpoints among
the original cores and `Z`. It proves that crossing an enlarged core is
equivalent to crossing both original core shores. Hence the exact identity
is an equality of copy sets:

```lean
G.cutOn M (corePart G M Z U₀) = G.cutOn M U₀ ∩ G.cutOn M U₁
```

Both enlarged core cuts equal this same set. Every selected copy touching
the pair support remains inside it, so its selected cut is empty. The
perfect-matching degree sum then identifies each assigned core's cardinal
parity with the cardinality of the actual old-core crossing-copy set.

These are native multigraph arguments. No simple-host or uniqueness assumption for copies between two endpoints is used. The resulting crossing count has not been
identified with a separately defined heavy-pattern code merely by giving
the quantities the same name.

## Joining composition and remaining scope

`assignedLabel_joining_decomposition` applies the recovered joining-stage
theorems to the actual constructed label map. It branches on the derived
parity alternative. Regularity and absence of overfull sets are explicit
host hypotheses; quotient admissibility, quotient even degrees and a
compatible circuit partition are not additional supplied inputs.

The new `assignedLabel_joining_decomposition_in_host` interface separates
the graph containing the representative from the graph being decomposed.
It constructs the labels from `G` and its perfect matching `M`, then applies
the joining theorem to `H : Multigraph V F` on the same vertex type. The
output preserves the actual copies of `F`. It does not require the selected
representative to remain a matching in `H`, which is useful after that
representative has been removed with a reserve. Regularity and absence of
overfull sets for `H` remain explicit stage hypotheses; the theorem does
not prove those properties of a particular residual graph or assert a
relationship between the two copy types.

In the even case the output is an exact partition of all joining copies
into disjoint nonempty host matchings of size at most three. In the odd
case the checked `TwoOddJoiningDecomposition` structure supplies exactly
`h` primary matchings, surplus matchings, and the full original-copy
coverage and cut-footprint properties. The host remains a multigraph.

The original heavy-pattern selection, reserved family and degree estimates,
preservation of residual non-overfull hypotheses, palette grouping, robust
perfect-matching completion, regular auxiliary graphs and final factorization
remain separate obligations. Existing simple-graph pattern and reserve APIs
do not establish those native multigraph steps. Full Corollary 4.6 and the
main theorem remain unfinished, and this supporting construction adds no
complete numbered manuscript assertion.

## Current verification evidence

The actual run directory is `verification/runs/20261123T042619Z/`. The following
results were read from its retained command metadata and compiler logs.

| Fresh command | Result | Retained record |
| --- | --- | --- |
| `lake build --wfail Overfull.AssignedParts.Basic` | Exit 0; 3,148 jobs; finished `2026-11-23T04:34:24.949751+00:00` | `assigned-basic-01.json`, `assigned-basic-01.log` and source snapshot |
| `lake build --wfail Overfull.AssignedParts.MatchedCuts` | Exit 0; 3,149 jobs; finished `2026-11-23T04:37:20.888398+00:00` | `matched-cuts-03.json`, `matched-cuts-03.log` and source snapshot |
| `lake build --wfail Overfull.AssignedParts.JoiningConstruction` | Exit 0; 3,168 jobs; finished `2026-11-23T04:43:10.508223+00:00` | `joining-construction-01.json`, `joining-construction-01.log` and source snapshot |
| `lake env lean verification/runs/20261123T042619Z/public-name-check.lean` | Exit 0; 118 mapped public names resolved; finished `2026-11-23T04:43:18.588033+00:00` | `public-name-check.json`, `public-name-check.log` and checked Lean file |

The Basic check freshly compiled both generic helper modules and Basic. The
MatchedCuts check passed on unchanged source after two preserved failures:
the first exhausted the heartbeat allowance in a propositional `tauto` step
and reported a deprecated finite-set lemma; the second reported an unused
`simp` argument. Replacing the propositional search by the nine explicit
endpoint-part cases and fixing the warning left all eight public statements
unchanged. Both failure logs and corresponding source snapshots remain in
the run directory.

The joining composition check includes the new separate-host interface. All
three command records confirm that their target source stayed unchanged
during the check. The reviewed final source identities are:

| Module under `Overfull/AssignedParts/` | SHA256 |
| --- | --- |
| `Basic.lean` | `033a7aebbe8903f2ad647f32d3d8e85dea58a3ddbf5fad12c7b91140fe446d12` |
| `PairFiberParity.lean` | `b3ff00c53a3f30c5ae8cd6d451f937b4a9318ca05c02ccf9ce427e5b26ff4686` |
| `ThreePartLabels.lean` | `3044f55c9fb8a86e797ece4487996e7b57ca41a7bd67284312b5080c9292a8f0` |
| `MatchedCuts.lean` | `500175e757628c5d53393f6a199db06050188374294ea58ee43d04d903ddc766` |
| `JoiningConstruction.lean` | `dd070d578403598115b359cf4649fa2f8a786cd8e189eee43123d9ceace54ed1` |

The public-name check covers the 75 recovered joining proofs and 43 recreated
or new assigned-part proofs. It records both source-manifest hashes and the
checked Lean file's hash. Name resolution is a separate inventory check; it
does not replace the complete declaration and axiom audit.

These targeted checks do not constitute the complete repository audit. The
complete repository result belongs in `verification/results.json` only after
the unchanged full verifier passes. Its fresh run metadata, frozen input
hashes, full logs and final run report provide that separate evidence.
