# Foreign-edge reduction: the complete actual process

This development proves Proposition 4.10, `three:prop:foreign`, of the
recorded manuscript. Its public declarations are
`Overfull.foreign_edge_reduction` and
`Overfull.foreign_edge_reduction_with_small_error`. The inventory contains
42 of 69 complete numbered assertions, including the subsequent bounded
absorption proposition and frequent-pattern lemma. The main theorem remains unverified.

The proof constructs the assignments, matching classes, refinement cuts,
changed core vertex sets, marks, fixed packing rules, and both local and
ambient matching transcripts. Its inner induction constructs each
interrupted or completed epoch. Its outer induction combines those epochs
with at most three actual refinements and returns one perfect-matching
sequence in the original graph, together with its exact residual.

## Fresh assignments and color classes

[`Assignment.lean`](../Overfull/ForeignEdges/Assignment.lean) proves
`ForeignAssignment.exists_assignment_color_classes_of_cores`. Given at most
four pairwise disjoint actual cores, each unmarked exceptional vertex is
assigned to a same-cluster core containing the most of its neighbors.
The existence of a represented same-cluster core is an explicit hypothesis;
the refinement construction below proves that hypothesis after marking.

For an exceptional vertex, let `T` be its number of same-cluster core
neighbors, `D` the number in its assigned core, and `F` its foreign degree.
The proof derives `T = D+F`, `T ≤ 4D`, and `T ≤ d_G(v)`, hence
`4F ≤ 3d_G(v)`. At a core vertex, the actual exterior degree is bounded by
the error of its embedded core. Under the theorem's explicit hypothesis
`4*error ≤ 3*h₀`, the actual foreign graph is bipartite with maximum degree
at most `floor(3h₀/4)`. Its edge set is partitioned into that many actual
matching subgraphs.

With the assignment fixed, `foreignGraph_subgraph_eq` and
`foreignEdges_surviving` prove that passing from the phase-start host `G`
to `R ≤ G` retains exactly the old foreign edges still in `R`.

[`PhaseConclusion.lean`](../Overfull/ForeignEdges/PhaseConclusion.lean)
packages fresh assignment and class data before the later deletion
sequence. Its current classes are actual matchings in each current host;
each edge is exceptional-incident and has both endpoints in the same
cluster. The conclusion for a completed phase is conditional on constructing
the actual sequence with the stated per-class loss. `Epoch.lean` constructs
that sequence; `Reduction.lean` obtains the final completed epoch through
the actual outer induction.

## One actual refinement

[`SmallCutRefinement.lean`](../Overfull/ForeignEdges/SmallCutRefinement.lean)
proves `ForeignRefinement.exists_small_cut_refinement`. A supplied actual
small cut separates the majority shores of two cores in one old group.
The proved robust small-cut theorem supplies the minority bound. The result
constructs:

- At most one actual core vertex to move into the exceptional set.
- Surviving core graphs on the actual surviving vertex sets, embedded in
  the same ambient graph, with degree error increased by at most one.
- The actual heavy exceptional set to mark.
- New vertex and core labels in `Fin 4`, preserving the equality relation
  of the refined labels on all unmarked vertices.
- A strictly larger number of occupied core groups, with every new group
  refining an old group.
- A same-cluster core for every unmarked vertex, and the required current
  intercluster-degree bound for every unmarked exceptional vertex.

[`Refinement.lean`](../Overfull/ForeignEdges/Refinement.lean) proves the
three-refinement bound from strict occupied-group growth. Its canonical
shore-history labels make every current intercluster edge cross a recorded
cut. If there are at most three recorded cuts, each of size at most `2k₀`,
and the current graph is contained in each recorded graph, the actual
intercluster edge count is at most `6k₀`. The handshaking calculation bounds
the actual heavy set by `12/θ` when its threshold is `θk₀`.

[`RefinementCore.lean`](../Overfull/ForeignEdges/RefinementCore.lean) proves
the actual vertex-deletion degree and robustness bounds. The restart
corollary starts with range `τ/2` and returns to range `τ`; its order
condition allows the deletion of at most one vertex. These are one-step
and history-accounting results. `RefinementHistory.lean` instantiates the
history along the constructed process. Its append constructor stores the
actual current host and shore, preserves every old cut, and derives the
new pre-mark crossing bound before applying the heavy-mark estimate.

## The incidence budget comes from exterior edges

[`Incidence.lean`](../Overfull/ForeignEdges/Incidence.lean) defines a core
footprint as the vertices covered by an actual partial ambient matching.
It proves that the number of footprint appearances of a core vertex is
the degree of the union of those partial matchings. Edge disjointness and
the absence of internal core edges give

```text
footprint appearances at v + d_H(v) ≤ d_G(v).
```

Regularity and the initial core error therefore provide the adaptive
incidence budget. The current partial matching is included before its
completion exists. Only earlier partial matchings are required to have
already been completed. This avoids a circular use of the current
completion to justify its own forbidden input.

The exact whole-core identity is also proved:

```text
d_(unused core)(v) + number of rounds
  = d_(initial core)(v) + footprint appearances at v.
```

The unused core includes its unused reserve edges. The module proves its
actual embedding in the ambient residual, derives pairwise disjointness
from sequential deletion, and proves the exact ambient residual degree.

[`Adaptive.lean`](../Overfull/ForeignEdges/Adaptive.lean) combines parity,
actual footprint size, and the proved exterior-incidence budget into the
precise `OrdinaryPackingStrategy.Allowed` predicate.

## A fixed rule supplies each core completion

[`Transcript.lean`](../Overfull/ForeignEdges/Transcript.lean) proves that a
finite transcript following a fixed rule is exactly the online execution
on its own inputs. `adaptive_ordinary_packing_transcript` derives the full
finite-prefix packing certificate from the previously proved packing
theorem, without imposing any condition on future inputs.

[`RuleStep.lean`](../Overfull/ForeignEdges/RuleStep.lean) obtains the next
matching from that certificate. Updating the current transcript entry
preserves every earlier entry. The next rule output is an actual matching
perfect outside the presented set, belongs to the whole unused core, is
disjoint from all earlier outputs, and leaves the exact next unused graph
robust with the same certificate parameters.

[`SafePrescription/Adaptive.lean`](../Overfull/SafePrescription/Adaptive.lean)
proves `Overfull.prepare_safe_prescription`. Its footprint tolerance is
chosen by the caller before the graph. It constructs the bounded partial
matching, including exceptional coverage, core parity, absence of internal
core edges, and prescribed-edge retention. Its safety clause applies to
any compatible completion with actual robust residual cores.

[`Completion.lean`](../Overfull/ForeignEdges/Completion.lean) assembles
actual local core matchings into an ambient perfect matching and proves
the exact induced matching in every core. Its uniform public theorem is
`Overfull.safe_prescription_of_core_matchings`.

[`RuleCompletion.lean`](../Overfull/ForeignEdges/RuleCompletion.lean)
constructs these local matchings from the certified fixed-rule outputs.
`safe_complete_from_certificates` applies exactly the safety clause
provided by `prepare_safe_prescription`. It returns an actual ambient
perfect matching, the prescribed-edge loss, no overfull set in the
residual, and the exact unchanged-parameter robust core remainders.
The prepared safety clause is an explicit input to this composition,
and the preceding uniform theorem supplies it.

This completes the local connection needed to avoid invoking the
one-step completion repeatedly with a new robustness loss at each deletion.
`EpochState.lean` maintains the actual ambient and local transcripts
through the full phase. Admissibility is derived from the stored partial
matchings; it is not an assumed field of the state.

## Parameters fixed before the graph

[`PackingSchedule.lean`](../Overfull/ForeignEdges/PackingSchedule.lean)
chooses the restart schedule from the proved adaptive theorem. Every
stage has output range `τ/2`, its output robust parameter is at most
`τ/2`, and half that output parameter is the next input. The schedule is
fixed before any graph or transcript. Its first four entries are the
ones needed in Proposition 4.10.

[`EpochParameters.lean`](../Overfull/ForeignEdges/EpochParameters.lean)
chooses one positive original error and one order threshold after four
positive tolerances and four order thresholds have been fixed. These
choices are uniform in the eventual exceptional order. They allow up to
three moved core vertices, error increase at most three, and exceptional
order increase at most three, while retaining the footprint and size
bounds at every stage. It also proves the exact floor-valued phase
horizon and the strict `k₀/1024 < h` safe-prescription reserve.

## Actual phase and final counts

[`Phase.lean`](../Overfull/ForeignEdges/Phase.lean) uses fixed phase-start
host-edge copies. Restricting a class to the current graph, rehosting it,
and deleting its completed matching gives an exact cardinality identity.
A loss of at most `c₁` for each of `d` processed classes leaves at most
`c₁d` edges of the phase's initial foreign graph. Later deletions cannot
increase any earlier class's remainder.

The integer arithmetic proves that a phase of at most `floor(3h₀/4)`
rounds retains degree at least `h₀/4`. Four such phases retain at least
`k₀/256`, with all rounding effects included.

[`FinalCount.lean`](../Overfull/ForeignEdges/FinalCount.lean) counts all
actual exceptional-to-nonassigned-core edges. Each has exactly one
exceptional endpoint, so the edge count equals the relevant incidence
sum. Its three contributions are the final unmarked same-cluster foreign
edges, the actual intercluster edges, and incidences at marked vertices.
The actual final completed phase has at most `c₁k₀` foreign edges, and the
proved final bound is

```text
total exceptional incidence outside assigned cores
  ≤ (c₁ + 6 + t₀) k₀
  ≤ 256 (c₁ + 6 + t₀) h.
```

This coefficient is smaller than the manuscript's allowance containing
`4c₁`. It uses the final completed phase's fresh assignment. A changed
assignment can make an edge newly foreign, so the complete current foreign
graph must be rebuilt and recolored after a refinement. No containment
claim about the previous phase's unprocessed classes is used.

## The actual inner induction

[`EpochState.lean`](../Overfull/ForeignEdges/EpochState.lean) defines the
actual transcript: original-host ambient matchings, their partial matchings,
and each initial core's local transcript. Its `Valid` predicate stores
perfectness, current-host membership, partial-matching containment, absence
of internal core edges, footprint size and parity, agreement with the fixed
rules, exact induced core edges, prescribed-edge loss, and the actual
no-overfull conclusion.

`Allowed` is not a field of this record. `Valid.allowed` derives every
previous input's admissibility from the actual exterior edges.
`Valid.allowed_next` includes the current prepared partial matching before
its completion exists. The current core is exactly the whole unused
initial core; its embedding, degree bounds, and certified robustness are
proved from the actual transcript.

[`Epoch.lean`](../Overfull/ForeignEdges/Epoch.lean) proves
`Setup.extend_no_trigger`. Negating the existence of an actual triggering
cut supplies the universal same-group majority condition needed by safe
preparation. The theorem prepares the current class, derives its inputs'
admissibility, obtains the certified rule outputs, constructs the actual
ambient completion, and updates both kinds of transcript.

`Setup.finish_from_valid` is the finite induction on the number of remaining
classes. `Setup.exists_stopping_transcript` starts with empty transcripts
and returns an actual prefix of at most `floor(3h₀/4)` matchings, together
with either completion of all classes or an actual triggering shore.
No per-round completion or admissibility oracle is an input.

## The actual outer induction

[`RefinementHistory.lean`](../Overfull/ForeignEdges/RefinementHistory.lean)
stores the actual graph and shore of every recorded cut. On unmarked
vertices, equality of encoded labels is equivalent to equality of all
recorded shore bits. Graph deletion preserves this invariant. Appending an
actual refinement transports the new labels, proves strict occupied-group
growth, derives the crossing-edge bound, and then proves the actual
marked-set increment. This establishes both the `6k₀` crossing bound and
the marked-set bound throughout the process.

[`ProcessState.lean`](../Overfull/ForeignEdges/ProcessState.lean) defines
`Entry`. Besides the current graph, degree, cores, exceptional and marked
sets, and labels, it contains an actual matching prefix in the original
graph and the exact residual identity. Its quantitative fields retain
`k₀ ≤ 4^j*h`, core order loss at most `j`, exceptional growth at most `j`,
core error at most `a₀+j`, and the scheduled input robustness.

`Entry.initial` constructs the original constant-label, empty-mark,
empty-history, zero-deletion state. `Entry.advance` consumes an actual
interrupted prefix and concrete refinement, appends the matchings to the
original-host sequence, changes the actual core types, and proves every
invariant for the next entry.

[`ProcessRefinement.lean`](../Overfull/ForeignEdges/ProcessRefinement.lean)
proves `Entry.refine_from_prefix`. It derives all required scalar bounds,
constructs the refinement from the actual small cut, and invokes the
actual state update. It does not assume existence of a next entry.

[`ConfiguredEpoch.lean`](../Overfull/ForeignEdges/ConfiguredEpoch.lean)
constructs each epoch setup from the current entry. Its fresh assignment
and entire foreign graph are reconstructed after every refinement. Its
fixed core rules are obtained from the proved packing theorem before any
new transcript is supplied.

[`Reduction.lean`](../Overfull/ForeignEdges/Reduction.lean) proves
`ForeignProcess.reduce_from_entry` by finite induction on the number of
possible further refinements. If an epoch finishes, it constructs the
final result. If it stops at an actual cut, it constructs the next entry
and continues. At index three, the history forces four occupied groups
among at most four cores. The core-label map is injective, so equal labels
cannot have different majority shores. Thus this last epoch cannot stop
at a trigger and must finish.

[`Concatenation.lean`](../Overfull/ForeignEdges/Concatenation.lean) rehosts
and concatenates actual prefixes. It proves the exact residual identity
at every intermediate local prefix, preserves perfectness and current-host
membership, and derives edge disjointness in the original graph. The
bound `k₀ ≤ 4^(j+1)*(h-s)` holds throughout epoch `j`, so the reserve needed
before every safe-prescription call is established at that prefix.

## Uniform parameter choices and public conclusion

Let `0 < α ≤ 1`, `0 < ν₀ ≤ τ`, and `τ ≤ (α/256)/1000`. These explicit
small-range bounds are one sufficient choice for the manuscript's fixed
parameter hierarchy. The degree and core-order density used throughout
all four epochs is `α/256`.

[`GlobalParameters.lean`](../Overfull/ForeignEdges/GlobalParameters.lean)
chooses all four packing and safe-preparation certificates before the graph.
The marking threshold is `1/1024000`, the absolute marked-set bound is
`t₀ = 3*(1+12*1024000)`, the boundary limit is `q₀ = 4096*(t₀+6)`, and the
class loss is `c₁ = 2*q₀+4*135720`. These constants are not optimized.

Within epoch `j`, the safe-preparation robust parameter is the minimum of
the scheduled input and output parameters. Refinement uses the certified
output parameter and range `τ/2`, giving exactly the next scheduled input
parameter and range `τ`. The certificate at prefix zero includes an
immediate refinement. Every rule restarts after every refinement.

[`ProcessParameters.lean`](../Overfull/ForeignEdges/ProcessParameters.lean)
chooses one positive original error and one order threshold, before all
graph data and the actual exceptional order. Every actual entry and every
allowed prefix receives the required safe-preparation tolerance, packing
tolerance, order bounds, small-cut allowance, robust order inequality,
core density, and degree reserve. These conclusions follow from the
original smallness condition and the proved cardinality losses.

The public theorem `Overfull.foreign_edge_reduction` applies these choices
to a regular simple graph of degree `k₀ ≥ αn`, partitioned into an
exceptional set and at most four disjoint robust cores of order at least
`αn`. The core graphs are actual subgraphs, with minimum degree at least
`k₀-a₀`; the original smallness condition is
`a₀ + |Zinit| + 1 ≤ εn`. No overfull set is allowed at the original degree.
The formal theorem allows any nonempty core index type of size at most
four, so it includes the manuscript's three-core and four-core cases.

Its `ReductionResult` contains one actual perfect-matching deletion
sequence, its exact final regular graph of degree `h`, no overfull set at
`h`, and `k₀ ≤ 256h`. It also contains the actual surviving core sets and
graphs, the actual enlarged exceptional set and assignment, and the
incidence bound above. At most three vertices leave the original core
union. Each core has minimum degree at least `h-(a₀+3)` and retains fixed
positive robust parameters.

[`ReductionError.lean`](../Overfull/ForeignEdges/ReductionError.lean)
proves `Overfull.foreign_edge_reduction_with_small_error`. The positive
output robust parameter is fixed before the requested error tolerance.
For every positive tolerance, the theorem chooses the original error and
order threshold before the graph and obtains the requested small final
error relative to `h`. This makes the final phrase of Proposition 4.10
explicit rather than leaving it as an informal parameter choice.

## Verification scope and next manuscript target

Proposition 4.10 is a complete numbered result. Proposition 4.12 now also
constructs the repeated forcing and bounded exceptional-set absorption;
[`exceptional-absorption.md`](exceptional-absorption.md) records that proof.
Lemma 4.13 now also constructs the actual boundary patterns, weighted
rounding, realization, complete absorption, and residual forest supply;
[`frequent-patterns.md`](frequent-patterns.md) records that proof. The next
scoped target is Lemma 4.14. The full ordinary-core coloring argument, the other
coloring cases, and the structural exclusion remain separate outstanding
assertions. The main theorem is not verified.

The provenance stays tied to the recorded 20 November manuscript and its
exact SHA256. Later presentation changes do not silently change the
numbered-assertion inventory or the statement being verified.
