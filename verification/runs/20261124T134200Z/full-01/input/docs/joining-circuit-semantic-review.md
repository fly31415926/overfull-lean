# Semantic review of the joining-circuit continuation

Review recorded for run `20261123T010829Z` on 2026-11-23 UTC. This review
examines `QuotientCuts`, `JoiningPartitions`, `TwoOddQuotient`, and the
completed `TwoOddDecomposition`, independently of their implementation,
using the checked `PairAugmentation` interface. The reviewer implemented
that augmentation interface, so this document does not describe its
review as independent of its author.

## Conclusion and precise scope

The reviewed composition proves a supporting joining-copy decomposition
from an actual label assignment into at most three labels. The principal
host inputs are finiteness, looplessness as built into `Multigraph`,
`h`-regularity, absence of an `h`-overfull vertex set, and the stated fiber
parities. The all-even result requires every label fiber to be even. The
two-odd result specifies distinct labels `a,b`, requires their fibers to
be odd, and requires every other fiber to be even.

Under those inputs, the existence theorems construct their compatible
circuit partition internally. They do not assume a selector, a partition,
or an unproved admissibility predicate. No mathematical defect or hidden
extra joining-degree assumption was found in these principal results.
They do not complete the original Corollary 4.6: the label assignment and
the subsequent factorization construction remain separate obligations.

## Exact transport from the original host

`joiningCopies G label` is a subtype of the original edge-copy type.
Its map to the host is `Subtype.val`, which is injective. Parallel copies
retain their individual identities throughout the quotient and lift.
There is no passage to endpoint pairs or to a simple graph that could
collapse copies.

`joiningQuotient_cutOn_image` and `joiningQuotient_cutOn_card` identify a
quotient cut with the corresponding original-host cut of a union of
label fibers. Every host edge crossing that shore is a joining copy,
which justifies exact coverage rather than only an inclusion.
`joiningQuotient_degreeOn_eq_cut` supplies the same exact correspondence
for a selected set of joining copies and a single fiber.

For an original vertex `v` and quotient label `i`,
`joiningQuotient_classCutOn_card` gives the endpoint-class cut size as

```lean
if label v = i then
  G.degreeOn (G.cutOn univ (labelShore label A)) v
else 0
```

The class is the actual original endpoint, not merely its quotient
label. Class-cut definitions filter by incidence, so arbitrary values of
the class function on nonincident pairs have no effect. The exact
identity supports both the individual class bound by `G.degree v` and
the even-shore half-cut bound.

The parity lemmas count the actual finite fibers. For all-even fibers,
every union of fibers is even. With exactly two odd fibers, a union is
odd exactly when its shore separates `a` and `b`. Empty unused fibers
are included in these statements. The singleton-fiber obstruction is
also checked: admissibility of the original joining quotient and a fiber
equal to `{v}` force `G.degree v = 0`. This prevents treating the old
unaugmented admissibility obstruction as resolved by an unsupported
assumption.

## All-even construction and lifting

`joiningQuotient_admissible_of_even_fibers` applies the already checked
original-host even-shore cut inequality. Every original endpoint class
satisfies twice its cut size at most the total cut size. Quotient degree
parity follows from host regularity and the even fiber cardinalities.
The at-most-three-label circuit theorem then constructs the quotient
partition used by
`exists_joining_matching_partition_of_even_fibers`.

Endpoint-class compatibility becomes the host matching property. The
whole-partition lift preserves nonemptiness, cardinalities of individual
parts, pairwise copy disjointness, and exact coverage of all original
joining copies. Injection of the subtype map also prevents distinct
parts from being merged by finite-set image. This covers the joining
edge set, not the internal edges of every fiber or the complete host.

The separately named
`exists_joining_matching_partition_of_even_degree_bound` wrapper assumes
an even regular degree and an explicit bound `D` on individual joining
degrees with `2 * D ≤ h`. That is an openly stronger sufficient wrapper.
Neither principal all-even nor principal two-odd result uses it, and it
is not a proof of the original manuscript assertion under its original
hypotheses.

## Two odd fibers: deriving admissibility and parity

The augmentation retains original copies in the left summand and adds
exactly `h` distinct virtual copies, indexed by `Fin h`, between `a` and
`b`. All virtual incidences use one fresh class in `V ⊕ Unit`, distinct
from every original endpoint class.

For a shore not separating `a,b`, the corresponding original host shore
is even. The existing even-shore inequality therefore supplies the
original half-cut inequalities, and no virtual copy crosses. For a
separating shore, the original shore is odd. The no-overfull-set input
gives at least `h` original crossing copies. Each original class has at
most `h` copies by host regularity; adding the `h` virtual crossing
copies supplies at least `2*h` total copies. This proves the inequality
for every original class and for the fresh virtual class.

The original quotient degree has parity `h % 2` at `a,b` and even parity
elsewhere. Adding `h` at exactly those two labels makes every augmented
degree even. Consequently
`exists_twoOddJoining_circuitPartition` follows from the proved
at-most-three theorem, without assuming the desired partition or its
cut bounds.

## Exact primary and surplus host data

Compatibility allows at most one virtual copy in a circuit. A compatible
circuit cannot consist only of virtual copies, so every original-copy
restriction is nonempty. Distinct restrictions are disjoint; together
with nonemptiness, this makes the restriction map injective on the
partition. The subsequent subtype projection is injective as well.

These facts justify the exact primary count in
`TwoOddJoiningDecomposition`. The `h` virtual copies belong to exactly
`h` distinct circuit parts, and their host restrictions remain `h`
distinct nonempty primary matchings. Each has at most two original
copies. All remaining parts are nonempty surplus matchings with at most
three original copies. The two families are disjoint, all their distinct
parts are edge-disjoint, and their union covers exactly every original
joining copy. No copy or partition index disappears through finite-set
deduplication.

`joiningQuotient_degreeOn_eq_cut` transports the circuit restriction
profiles to the actual original-host quantities
`(G.cutOn M (labelShore label {i})).card`. Every primary part has exactly
one crossing copy at each of `a,b`, with odd cut size exactly at those
labels. Every surplus part has even cut size at every label.

A zero-virtual restriction remains a circuit in the **unaugmented
joining quotient**. Its projection in the original host is a matching;
this review does not identify that host matching with a host circuit.
The one-virtual restriction has a proved size bound and degree profile.
No separate formal connected-path object for that case is claimed.

## Boundary cases and statement preservation

There is no hidden assumption `h > 0`, no inhabited class type, and no
requirement that every available label is used. Empty joining sets give
empty partition families as appropriate. For `h = 0`, the virtual family
and primary family are empty; the proof does not divide by `h` or choose
a virtual element. The explicitly odd fibers are nonempty as a
consequence of their parity, not an extra hypothesis.

The final decomposition theorem explicitly retains `a ≠ b`. During
development, Lean's section-variable inclusion initially omitted that
proof parameter from the final theorem because it does not appear in
the output structure's type. `include hab in` correctly retains the
intended distinct-label input already required by the augmentation.
This is not an added assumption on the host. Other resolved compiler
issues normalized proof-irrelevant decidable-equality instances or
removed an unused finiteness instance; they did not weaken a statement.

## Relation to the manuscript and unfinished work

The [authorized manuscript recovery record](../verification/runs/20261122T235931Z/authorized-manuscript-recovery.md)
contains the hash-matched statements of 4.4, 4.5 and 4.6 and relevant
construction excerpts. Matching those statements does not establish that
the entire later manuscript or its adjoining proof text is byte-for-byte
the pinned original source.

The inspected two-core construction for 4.6 uses at most three assigned
parts: two core parts and at most one additional exceptional pair. This
round supplies the circuit and original matching stage once such a
label assignment and its parities are available. The preceding reserves
and assigned-part construction, palette grouping, the required
exceptional coverage in each round, robust completion inputs, regular
auxiliary graphs, and the final original-host one-factorization remain
to be proved. General four-label branches of 4.4/4.5 are not supplied by
an at-most-three-label theorem. This review certifies no additional
complete numbered manuscript assertion; the recorded coverage remains
47 of 69.

## Compiler evidence and audit boundary

All five new modules have completed targeted strict builds with exit
code zero under the pinned Lean 4.24.0 toolchain:

| Module | Genuine successful log | Reported build jobs |
| --- | --- | ---: |
| `QuotientCuts` | `quotient-cuts-02.log` | 3145 |
| `PairAugmentation` | `pair-augmentation-strict-build.log` | 3103 |
| `JoiningPartitions` | `joining-parts-03.log` | 3156 |
| `TwoOddQuotient` | `two-odd-quotient-03.log` | 3158 |
| `TwoOddDecomposition` | `two-odd-decomposition-03.log` | 3159 |

These logs and their command/status JSON records are under
`verification/runs/20261123T010829Z/`. Failed development checks are
retained separately and are not counted as passes. No `sorry`, admitted
proof, or newly declared axiom was introduced in the reviewed source.

This source-level semantic review and the targeted module checks do not
replace `python3 scripts/verify.py`, its complete strict build, or the
unchanged complete `Audit.lean`. Exact final source hashes, declaration
counts, and allowed-axiom audit results belong to the final verification
outputs and run logs. This document does not assert a fresh whole-tree
audit result before that verification has completed.
