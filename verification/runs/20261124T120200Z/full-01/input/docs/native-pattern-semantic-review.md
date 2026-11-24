# Semantic review of the native two-core boundary stage

## Review boundary and verification evidence

This review concerns the new native multigraph compression, assignment
signature and weighted-copy constructions based on checkpoint `ec25857`.
The reviewer independently read the source statements and proofs in
`BoundaryCompression`, `NativeWeights`, `Signatures`, `SignaturePools`,
`HeavySignature`, `ExactPoolWeights` and `NativePatternConstruction`, together with the
previously checked assigned-part interfaces and the recovered statements
of Lemma 4.4 and Corollaries 4.5
and 4.6. The reviewer subsequently authored `CompressionCuts`; that file
is included in the mathematical assessment below but is not claimed as
an independent review of another author's implementation.

This is a statement and proof-scope review. The actual compiler attempts,
strict build, stock transitive axiom audit and exact final source hashes
are recorded separately under
[`verification/runs/20261123T113235Z`](../verification/runs/20261123T113235Z/)
and in [`verification/results.json`](../verification/results.json).
The presence of this review or a source manifest is not verification
evidence by itself.

## Native edge copies and distribution weights

All new graph-dependent weighted statements use
`MultigraphMatchingProbability.Distribution G k S`, whose matchings are
finite sets of the actual edge-copy type `E`. Scaling each sample weight
by `k` gives total weight `k` and, when `k > 0`, marginal exactly one
for every individual copy. The pool identity sums these marginals over
an arbitrary finite set of copies. Selecting a submatching changes that
identity to the correctly directed capacity inequality.

The only reused `CircuitPatterns` results are finite aggregation and
numerical maximum-weight arguments, whose hypotheses have no graph
type. No simple-host distribution or simple-edge internal-pair theorem
is applied to a native multigraph.

`aggregateWeight_le_pool` includes the necessary usage premise: every
sample with the specified code must contain a copy from the pool. Its
conclusion bounds that code's weight by the cardinality of the whole
copy pool. A pair of exceptional endpoints can therefore have weight
larger than one when it has several parallel copies. None of the new
statements excludes such a pair or merges those copies into one edge.

## Assignment signatures and the supplied representative

`AssignmentSignature Z` is `Option (↥Z → Fin 2)`. For an actual perfect
matching, `none` records the presence of a selected internal exceptional
copy. Otherwise `some σ` records the original core assigned to each
exceptional vertex. The encoding is attached to that same matching.

The conclusions about the optional pair explicitly require
`Z.card ≤ 2`. Looplessness and matching uniqueness then imply that a
selected internal exceptional copy uses all of `Z`, which has exactly
two vertices. Its endpoint set is independent of the chosen parallel
copy. Without the size restriction, a single `none` code could forget
which exceptions are paired; no such broader assertion is made.

Equal signatures give equal first assigned core parts and equal pair
parts. Perfect-matching coverage and disjointness then give equality of
the second assigned core parts. Thus the actual `Fin 3` vertex labels
agree. The previously checked matching-cut identity yields equality
of the old-core crossing counts **modulo two**. The source correctly
does not claim equality of their full counts or their selected copies.

The type has `2 ^ Z.card + 1 ≤ 5` elements. Unrealizable signatures do
not invalidate the upper bound. Nonnegative weights summing to `k`
therefore give a code of weight at least `k/5`, and its positive weight
gives a positive-weight sample with that exact code.

## Pool supplies from the actual graph hypotheses

The pool witnesses are correctly matched to the signature:

- The paired code uses an actual copy internal to `Z`.
- Every unpaired exception uses an actual copy to the original core
  recorded by its code.
- If one representative has odd old-core crossing count, all samples
  with its code have odd crossing count and use the original cross-core
  pool.

The native capacity theorem consequently gives at least `k/5` copies
in each required pool for one heavy representative.
`exists_assignment_matching_with_linear_pools` constructs the distribution
from positive regular degree and absence of overfull sets; it assumes
neither a heavy signature nor the desired pool supplies.

These bounds concern the original host. They do not assert that all
pools admit simultaneously disjoint selections, that they contain
`k/5` distinct neighbors, or that a reserve survives later deletions.
Parallel copies make the distinction between copy counts and distinct
neighbors essential for any later use of a simple-host absorption API.

The independently reviewed `ExactPoolWeights` strengthens the count for
a fixed exceptional vertex and either original core: the total weight
of signatures assigning that vertex to that core equals the cardinality
of the whole actual-copy pool. A matching uses at most one copy incident
with that vertex, and its code records the usage exactly. The explicit
bound `|Z| ≤ 2` is correctly retained when proving that the `none` code
assigns the exceptional vertex to neither old core. This exact identity
supports later reserve arithmetic but still describes the original host.

## Compression and exact uncovered parity

`compressedBoundary` retains every selected copy touching `Z`. From the
old-core crossing set it retains no copy when the cardinality is even,
and one of that set's own copies when the cardinality is odd. The
result is a subset of the original matching, has at most `|Z| + 1`
copies and at most `2(|Z| + 1)` incident vertices, and preserves every
exceptional assignment and internal exceptional copy exactly.

For a disjoint covering triple `U₀,U₁,Z`, every old-core cut splits into
its exceptional-incident cut and its copies to the other old core.
These two sets are disjoint. The compressed cut replaces only the
second set by its parity selection, so its cardinality has the same
parity as the original cut. Compression leaves no copy internal to
either old core; the statement for the other core also follows by the
proved symmetry of compression.

The general native matching identity counts covered vertices by their
selected degree sum. Together with the actual-copy handshake, it gives
the equivalence between even uncovered shore order and the shore/cut
parity equality. Applying the perfect-matching shore parity proves
even uncovered order in both original cores. This compression argument
does not need a bound on `|Z|`; its specialization to at most two
exceptions has at most three retained copies. It does not assume a
perfect completion of the compressed matching.

## Relation to the manuscript and remaining obligations

The original statements and their pinned hashes are unchanged. Full
Corollary 4.6 still has its original small-error, large-order and
positive linear density requirements. The present stage is finite
combinatorial reasoning and needs no chosen robustness or error
parameters; it therefore introduces no reversed uniform quantifiers.
Full Corollary 4.5 still allows five exceptional vertices, beyond the
five-signature theorem reviewed here.

The independently reviewed integration in `NativePatternConstruction`
uses the same actual representative for all pool bounds and its retained
boundary. It proves that compression preserves the code, that the
retained old-core crossing count equals the original crossing parity,
and that this retained count is constant on a common signature. The
final construction includes both even uncovered-core orders and every
original-copy pool bound without a new reserve or completion premise.

The coarse signature alone should not be silently equated with the
previous simple-graph `Encodes` relation or the manuscript's full
boundary pattern. The optional native crossing statistic is now
identified by the integration just described. A later use of the
separate full source encoding relation still needs its own precise
bridge; no existing simple-host encoding theorem has been imported as
a native multigraph result.

The next source obligations are simultaneous reserve realization,
the residual degree and exceptional outside-incidence bounds, and
absence of overfull sets in every required residual. A perfect-matching
deletion decreases every degree by one but can remove several copies
from an odd cut, so residual no-overfull safety does not follow from
regularity alone. Subsequent palette grouping, robust core completions,
regular auxiliary graphs and reconstruction of the whole
one-factorization also remain to be proved.

This supporting stage does not complete a numbered manuscript
assertion. The inventory remains **47 of 69**, and full Corollary 4.6
and the main theorem remain incomplete.
