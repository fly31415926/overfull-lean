# Lean formalization of the overfull manuscript

## Current continuation: uniform three-core terminal factorization

The three-core terminal construction now reaches original-host coloring and
one-factorization theorems:

- `Overfull.three_core_terminal_factorization`
- `Overfull.three_core_terminal_one_factorization`

For fixed positive degree and part-size density and robust expansion parameters,
one common positive error tolerance and order threshold are chosen before the
host. An even-order regular simple graph with no overfull set and three disjoint
covering robust core parts then has exactly the degree number of disjoint
perfect matchings covering every original edge copy. The theorem constructs the
joining palettes, completed prefix, residual cores, central and leaf colorings,
and final restoration. No decomposition or residual coloring is assumed.

The all-even residual is factored as closed components. With exactly two odd
parts, their simultaneous contraction gives a central graph with one robust
core and two apices. The surviving joining matchings prove its no-overfull
condition. Complete bounded-input Corollary 4.6 supplies its coloring, and
singleton boundary extension aligns both odd leaves on the same original copies.

**Coverage remains 48 of 69 numbered assertions.** This is the three-core
subcase of Proposition 4.16; the four-core cases and full proposition remain
incomplete. There are still 21 unfinished assertions, including the main theorem.
Every preceding numbered assertion record and statement hash is unchanged.

The [source inventory](docs/three-core-terminal-source.json),
[proof map](docs/three-core-terminal-verification.md),
[semantic review](docs/three-core-terminal-semantic-review.md), and
[handoff](docs/continuation-handoff.md) give the exact scope. The
[current run](verification/runs/20261124T032118Z/) retains genuine successful
and failed development checks. Its complete frozen verifier, unchanged axiom
audit and supplementary preservation report establish the actual full-project
result; focused checks alone do not.

The exact published baseline is `0cf1c68c4daaeec9b879a03f1871eb64a0fa9640`,
with tree `5d031253d02d0d0878422f8fbc367f04b812450c`. Both `main` and
`verified-bipartite-continuation-2026-11-21` were independently read back at
that commit before this round. It has the identical tree of the authorized
local checkpoint `a7b16ddfcda8ba4247900795d1c9406036a2a9ef`, including its
sources, mappings, snapshots and genuine logs. The new round's publication
requires its own exact-tree and branch readbacks.

The sections below retain earlier checkpoint scope and verification history.

## Previous continuation: complete bounded-input Corollary 4.6

**48 of the manuscript's 69 numbered assertions are complete.** The new
`Overfull.bounded_input_one_factorization` proves the complete Corollary 4.6:
an even-order regular multigraph with no overfull set has an exact
one-factorization when it has either one robust core and at most three
exceptional vertices, or two robust cores and at most two exceptional vertices,
under the stated fixed linear density bounds and sufficiently small core error.
One common error tolerance and order threshold are chosen before the host.

The new two-core theorem constructs the native reserve, completes the
nonprotected colors, colors the protected residual through its actual assigned
shores, and reassembles both perfect-matching prefixes. Even shores are factored
as components. Odd shores are contracted to an apex and their colorings are
aligned on the same original crossing copies. The optional exceptional pair is
colored as a separate component. Every parallel copy remains distinct.

The principal original-host declarations are:

- `Overfull.two_core_two_exception_factorization`
- `Overfull.two_core_two_exception_one_factorization`
- `Overfull.bounded_input_factorization`
- `Overfull.bounded_input_one_factorization`

The exact source statement and its SHA-256 are unchanged. The other 68 assertion
records remain unchanged. **21 assertions remain incomplete, including the main
theorem.** The general fixed-pattern lemma, the five-exception corollary, terminal
three-core work, and the remaining global factorization inputs are not claimed
by this result. Whole protected boundaries need not retain their previous
colors during terminal factorization.

The [source inventory](docs/native-terminal-source.json),
[proof map](docs/native-terminal-verification.md),
[semantic review](docs/native-terminal-semantic-review.md), and
[continuation handoff](docs/continuation-handoff.md) describe the exact scope.
The [current run](verification/runs/20261124T021500Z/) retains every genuine
focused failure and success, the immutable full build/audit inputs and outputs,
and strict preservation evidence. The final frozen verifier and supplementary
report establish full-project verification; a focused pass alone does not.

The preceding verified local chain `af8dca2 → d2e7b12 → f557ae0` was published
with exactly identical Git trees as `a4b34a8 → 498d737 → 0f168ca`. Both public
branches were independently read back at `0f168ca` before this continuation's
full verification. Publication of the new continuation has its own separate
commit/tree/branch readbacks.

The historical checkpoint sections below retain the mathematical scope and
verification status recorded at their respective dates.

## Latest continuation: native weighted assembly and bounded core completion

The native construction now supplies weighted odd/even joining palettes with
exact half-reserve prescriptions, constructs every paired/unpaired exceptional
case, and covers precisely all joining and exceptional edge copies. It derives
old-core parity, small support and actual whole-family core loads from the
embedded near-regular cores. The constants and natural quotient capacity are
proved uniformly from the native numerical hypotheses. Supporting robust core
completion and nonprotected-color selection now produce all `h-r/2` nonprotected
perfect matchings under constants fixed before the host. The remaining graph is
exactly `r/2`-regular, retains two robust cores, and has exactly the selected
reserve copies as its external edges. An independent-exterior one-core theorem
supplies a further ingredient for the terminal problem.

Native weighted odd/even joining palettes derived from actual residual cores; complete paired and unpaired exceptional-copy assembly with exact selected reserve classes; original-core parity and whole-family load bounds; uniform completion of every nonprotected color, leaving a robust r/2-regular residual whose external copies are exactly the selected native reserve; and independent-exterior one-core factorization. These are supporting constructions; final protected-residual factorization and reassembly, full two-core Corollary 4.6, and the main theorem remain unproved.

**Coverage remains 47/69. Full two-core Corollary 4.6 and the main theorem are
unproved.** The [source inventory](docs/native-integration-source.json),
[public proof map](docs/native-integration-verification.md),
[semantic review](docs/native-integration-semantic-review.md) and
[current-run evidence](verification/runs/20261124T010000Z/) record the exact scope.
The final frozen verifier and preservation reports determine the actual full
verification state. Focused checks and source inventories alone do not certify
the full project.


[Repository](https://github.com/fly31415926/overfull-lean) · [Verification workflow](https://github.com/fly31415926/overfull-lean/actions)

**47 of the manuscript's 69 numbered assertions are complete.** Full ordinary-core Lemma 4.2 is proved by `Overfull.ordinary_core_factorization` and `Overfull.ordinary_core_one_factorization`. **22 assertions, including the main theorem, remain incomplete.** The continuation also proves the one-core branch of Corollary 4.6; the distinct two-core branch remains open.

The source manuscript is *An Asymptotically Sharp Form of the Overfull Conjecture*, version `Four_Robust_Component_Cases_2026-11-20.tex`. Its exact filename and SHA256 are recorded in [`docs/manuscript-source.json`](docs/manuscript-source.json).

## Latest continuation: native reserve-star balance and actual star insertion

The native unpaired reserve now supplies distinct surviving actual copies in
each assigned old-core star. Joining incidences, that star pool, and the
same-label exceptional bundle form a disjoint partition of the residual
degree. The resulting **combined** joining-plus-bundle bound is derived from
the native reserve and regularity; no old-core multiplicity estimate is
incorrectly imposed on the exceptional-to-exception bundle.

The construction derives common colors for the internal bundle and the
exact remaining-star/free-color balance after selected reserve prescriptions.
Hall's theorem then assigns actual star copies to available colors from
concrete endpoint loads and whole-class blocked-copy weights. Colored-star
accounting proves the bounds needed for the second star. The sequential
extension retains original copies and unavailable colors, derives matching
and disjointness, covers both added star pools, and adds at most two copies
and four support vertices per class.

The Hall row count is restricted to the **available** colors. Protected
reserve classes outside that set do not consume the row budget. The generic
global-load versions are retained as consequences of this stronger form.

These are supporting constructions. The complete native weighted odd/even
seed wrappers and the final composition of all reserve prescriptions, parity,
and robustness hypotheses remain to be supplied. **Coverage remains 47/69;
full two-core Corollary 4.6 and the main theorem remain unproved.**

See the [exact public proof inventory](docs/native-star-source.json),
[verification map](docs/native-star-verification.md),
[semantic review](docs/native-star-semantic-review.md),
[continuation handoff](docs/continuation-handoff.md), and
[genuine current-run evidence](verification/runs/20261123T235203Z/).
The complete frozen verifier and preservation reports in that run are the
authority for full verification; focused checks alone are not a full audit.

## Previous continuation: weighted palettes and actual star-copy bounds

Five new modules prove dynamic weighted palette extension and apply it to
actual matching pieces, with **41 public theorem proofs**. The weights count
original exceptional-to-core copies blocked at their old-core endpoints,
retaining every parallel copy. The construction bounds the actual blocked
copies of each complete grouped color class by `h/8`, simultaneously for
at most two specified exceptional resources.

The principal theorem is
`Overfull.WeightedPalette.exists_star_weighted_matching_grouping`.
Under its explicit seed certificates, multiplicity and incidence bounds,
`b<=D`, `128D<=h`, protected-color budget and piece capacity, it preserves
prescribed seed colors and protected seed unions, properness, exact union
of the original pieces, matching and disjointness. Each class has at most
`3L` copies and `6L` support vertices, and each vertex has color load at most
`D`. The asymmetric Hall theorem permits different conflict bounds on the
two sides and includes the equality and empty-side cases.

This checkpoint left actual remaining-star balance and sequential star
insertion open; the new stage above supplies their supporting constructions.
Native weighted parity/reserve wrappers, robust completion and the final
factorization remain separate obligations. **Coverage remains 47/69; full
Corollary 4.6 and the main theorem remain unproved.**

See the [proof map and exact public inventory](docs/weighted-palette-verification.md),
[source manifest](docs/weighted-palette-source.json),
[semantic review](docs/weighted-palette-semantic-review.md),
[continuation handoff](docs/continuation-handoff.md), and
[current run records](verification/runs/20261123T230808Z/).
All five focused strict target builds passed. The actual full-command,
frozen-input, audit and preservation reports in that run determine global
verification status; no new global audit count is inferred from those
focused checks.

The complete weighted checkpoint `af8dca22ef67d66d0de3f6d89954d31f06a4d2fa` is the verified local baseline,
with exact tree `5ddefa9b77dfaf2d1cf09df1d7e2d4b541346a85` and all 2,507 files. Publication was blocked by automatic approval review at
this continuation's input freeze; later public commits and branch updates
are established by separate publication receipts. Its 3,734-job strict build
and unchanged audit of 12,811 proof
declarations, including all complete private/generated maps and genuine logs,
are retained in its run. The public parent `c28cec4` preserves `89678bc`, and
that parent's predecessor `8c974c8` preserves `1b5663a`.

## Previous continuation: internal pair coloring and reserve palette extensions

The new stage derives the common free palette of an actual exceptional pair
and colors every parallel copy while preserving valid prescribed reserve
colors. It also constructs all-even joining palettes with prescribed empty
colors, and extends protected joining classes to full surviving original
reserve boundaries with exact copy accounting and cut parity.

These are concrete missing construction steps in the two-core argument.
Exceptional vertices assigned to old cores still require their internal
coloring construction, followed by the full robust completions and final
factorization. **Coverage remains 47/69; the main theorem is unverified.**

See the [proof map](docs/exceptional-palette-verification.md),
[source manifest](docs/exceptional-palette-source.json),
[semantic review](docs/exceptional-palette-semantic-review.md), and
[current run records](verification/runs/20261123T221916Z/).
The exact full build, unchanged axiom audit and preservation report determine
local verification status. This stage and its preceding complete verified
candidate have now been published as the exact source trees recorded above.
The earlier blocked attempts remain preserved as genuine historical records;
both public verified branches subsequently advanced to `c28cec4` and were
independently read back.

## Previous continuation: actual residual joining palettes

The continuation now derives the actual residual joining-degree bounds and
constructs bounded matching color classes covering every joining copy, with
whole-class parity, footprint, and vertex-load certificates. The retained
robustness parameter is chosen before the later error tolerance. In the
odd assigned-part case, a selected half of the surviving reserve crossings
can be forced into singleton primary pieces and protected through grouping.
Explicit uniform numeric bounds keep the complete palette footprints small.

The principal interfaces are
`exists_uniform_native_reserve_completion_with_small_joining`,
`AssignedParts.exists_assigned_joiningPalette_in_host`, and
`exists_native_protected_joiningPalette`. The resulting uncovered-order certificates
refer to assigned fibers. Internal exceptional completion, old-core robust
completion, the full residual factorization and reconstruction remain open.
**Coverage remains 47/69, with 22 incomplete assertions.**

See the [proof map](docs/residual-palette-verification.md),
[source manifest](docs/residual-palette-source.json),
[semantic review](docs/residual-palette-semantic-review.md), and
[current run records](verification/runs/20261123T210325Z/).
The exact current strict build and complete axiom audit determine verified
status. Prior source, mapping and historical evidence are preserved.

## Previous continuation: native reserve completion and actual residual safety

The native two-core stage now constructs an actual linear reserve of disjoint
compressed boundaries and completes the accepted boundary family to disjoint
perfect matchings inside the original embedded robust cores. All constants
are chosen before the host. The completions avoid the reserved original
copies, and the actual residual is regular, has no overfull set, and retains
robust embedded cores on both old core vertex sets.

The final interface is
`Overfull.NativeReserve.exists_native_reserve_completion_parameters`.
It gives `k/30≤r≤h`, `h+q=k`, and `h-r≤δn`. Every parallel copy remains
distinct. Rounding and protected-cut tests use the original matching
weights, and exact copy accounting connects selection to the actual residual.

This is supporting progress toward the two-core branch of Corollary 4.6.
Palette grouping and the remaining factorization still require proofs.
The numbered count remains **47/69**, with **22** incomplete assertions,
including the main theorem.

See the [proof map](docs/native-reserve-verification.md),
[source manifest](docs/native-reserve-source.json),
[semantic review](docs/native-reserve-semantic-review.md),
[continuation handoff](docs/continuation-handoff.md), and
[current run records](verification/runs/20261123T201422Z/).
Current compiler and audit records determine verification status. The run
recovered one original source byte-for-byte and reconstructed the remaining
continuation after an interrupted publication; its
[provenance](verification/runs/20261123T201422Z/recovery-provenance.md)
distinguishes those sources from historical observed checks.

## Previous continuation: native multigraph assignment patterns

The native two-core construction now selects an actual perfect-matching
representative from a signature of scaled weight at least `k/5`. With at most
two exceptional vertices there are at most five signatures. Every original
copy remains distinct, including parallel copies in an exceptional pair.
The construction derives linear original-copy supplies for the pair, each
assigned exception, and the old-core crossing pool when its parity is odd.
Exact marginal identities also recover each exceptional-to-core pool size
from the total weight of the signatures assigning that exception there.

A compression of this same representative retains every exceptional-incident
matching copy and at most one old-core crossing copy. It contains at most
`|Z|+1` edges, preserves the exact internal exceptional pair and all assigned
vertex parts, and leaves even uncovered order in both original cores. The
retained crossing count is proved equal to the original crossing parity.

These eight modules add supporting proofs toward the two-core branch of
Corollary 4.6. Actual disjoint reserve selection, residual non-overfull safety,
palette grouping, robust completion and the final factorization remain open.
The numbered count remains **47/69**, with **22** unfinished assertions.

See the [proof map](docs/native-pattern-verification.md),
[source manifest](docs/native-pattern-source.json),
[semantic review](docs/native-pattern-semantic-review.md), and
[current run records](verification/runs/20261123T113235Z/).

## Previous continuation: actual assigned parts and exact matching cuts

The assigned parts are now constructed from a specified actual perfect
matching and the two-core/exceptional vertex partition. The explicit
`Fin 3` labels retain both original cores, assign unpaired exceptions to
their matched core, and keep an internal exceptional pair together. With
at most two exceptions, that third fiber is empty or has two vertices.
The proof derives all-even or exactly-two-odd fiber parity and proves
that both assigned cores have exactly the selected original copies
between the two old cores as their matching cut.

This composes with the joining theorem below. A new separate-host
interface uses the original representative's assignment in another
regular non-overfull host on the same vertices, without requiring the
representative to survive reserve deletion. The latter host conditions
remain explicit stage inputs. Reserve selection, residual safety,
palette grouping, robust completion and full Corollary 4.6 remain open;
the numbered count stays **47/69**.

See the [proof map](docs/assigned-part-verification.md),
[source manifest](docs/assigned-part-source.json),
[semantic review](docs/assigned-part-semantic-review.md), and
[current run records](verification/runs/20261123T042619Z/).
The joining sources were recovered byte-for-byte from the published
recovery checkpoint. Unpublished assigned-part drafts were lost with a
workspace replacement and have been recreated for fresh checking;
the run does not claim the lost draft bytes or invent their old logs.

## Recovered continuation: original-host joining decompositions

For an actual assignment of the original vertices to at most three parts,
the original regularity, absence of overfull sets, and part parities now
produce the complete joining-edge circuit and matching stage. When all
parts are even, the proof partitions every joining copy into nonempty
matchings of size at most three. When exactly two parts are odd, it
constructs exactly `h` primary matchings of size at most two and surplus
matchings of size at most three. The families are disjoint and cover every
original joining copy exactly; their cut footprints have the required
odd/even parity at every part. Parallel copies remain distinct.

All quotient half-cut inequalities and degree parities are derived from
the original host. Neither a circuit partition nor a bound on individual
joining degrees is assumed in these two parity cases. The construction
reuses the complete at-most-three-vertex circuit theorem from the previous
round. See the [proof map](docs/joining-circuit-verification.md),
[source manifest](docs/joining-circuit-source.json), and
[semantic review](docs/joining-circuit-semantic-review.md).

This is a supporting stage toward the two-core branch of Corollary 4.6.
The actual assigned partition, reserve selection, palette grouping,
robust completion, and final factorization still need construction from
that full statement. The numbered count remains **47/69**. Complete
verification evidence is recorded in [verification/results.json](verification/results.json)
and the [timestamped run directory](verification/runs/20261123T010829Z/).
The [handoff](docs/continuation-handoff.md) specifies the next proof target.

## Previous continuation: complete compatible circuits on at most three vertices

The original even-degree and half-cut hypotheses now suffice for an exact
partition of every selected original edge copy into compatible circuits on
at most three vertices. The proof constructs a safely removable parallel
pair or triangle, preserves every class-cut inequality, and performs the
complete induction with exact disjoint coverage. Arbitrary parallel
multiplicities and incidence-class types are allowed; no circuit-selector
assumption remains in the final theorem.

The [proof and scope](docs/three-label-circuit-verification.md),
[source mapping](docs/three-label-circuit-source.json), and
[independent semantic review](docs/three-label-circuit-semantic-review.md)
explain the construction. The latest [run records](verification/runs/) and
[continuation handoff](docs/continuation-handoff.md) identify the next target.
This supporting theorem adds no numbered manuscript assertion: the count
remains **47/69**, and the general four-label compatible-circuit theorem,
full two-core branch of Corollary 4.6, terminal Proposition 4.16, and main
theorem remain incomplete.

## Previous checkpoint: recreated ordinary-core closure and recovered continuation

The original local checkpoint `cb05ef5` was not available as a complete checkout
or archive. At the user's request, eleven missing Lean modules were recreated
and checked with a fresh strict build and the unchanged full axiom audit. Nine
recovered original modules, including the public ordinary-factorization wrapper
and all six continuation modules, retain their original bytes. This is a new
checkpoint; it does not claim the original commit or tree hash.

The full ordinary-core theorem constructs a coloring and an exact partition of
all original multigraph copies into perfect matchings. Its inputs are the
original even regular host, sufficiently large even robust core, bounded exterior,
small core deficit, and a coloring of the actual core complement. Every uniform
parameter precedes the host. A direct bounded-exterior cleanup closes the
previously missing factorization of the actual residual graph.

The recovered continuation constructs the complete one-core branch with at most
three exceptional vertices, terminal one-core factorizations under the recorded
incidence hypotheses, and the exact safe circuit-deletion criterion on at most
three labels. These supporting results add no further complete numbered item.

The [reconstruction provenance](docs/checkpoint-reconstruction.md),
[ordinary proof map](docs/ordinary-factorization-full.md),
[ordinary source manifest](docs/ordinary-factorization-full-source.json),
[continuation notes](docs/few-exception-continuation.md), and
[fresh verification report](verification/results.json) record the scope and
current source hashes. Recovered historical evidence is preserved separately in
[recovery/cb05ef5](recovery/cb05ef5).

## Historical checkpoint: complete Lemma 4.14

[`Overfull.boundary_extension`](Overfull/BoundaryExtension/Full.lean)
extends the prescribed singleton/triple coloring of the boundary of an odd
robust core to every original edge copy incident with that core. **Every
prescribed boundary label is retained exactly**, including properness at
original exterior endpoints. Its positive error tolerance and order
threshold precede the graph, core, regular degree, and prescribed coloring.

The proof completes and removes the triple colors, contracts the remaining
exterior ends to one apex, and constructs a factorization of that actual
regular multigraph. The new direct route moves one ordinary core vertex
outside, chooses a prescribed pairing and first-group palette that preserve
its incidence supply on both shores, and proves the resulting two-apex
factorization. Selected colors are constructed by the multigraph fan
criterion and balanced-coloring theorem, completed by robust bipartite
packing, and joined to a genuinely bipartite remainder colored by König.
The final reconstruction restores the original singleton and triple labels.

This completes **one additional numbered assertion**, raising the inventory
from **45/69 to 46/69** at that historical checkpoint. General ordinary-core
Lemma 4.2 was subsequently completed by the bounded-exterior route above. Full
Corollary 4.6, bipartite-core Theorem 6.1, and terminal Proposition 4.16
remain incomplete. The direct one-apex proof supplies the particular
factorization needed for Lemma 4.14; it does not assume those broader
statements.

The [statement and proof map](docs/boundary-extension.md),
[source mapping](docs/boundary-extension-full-source.json), and
[semantic review](docs/boundary-extension-full-semantic-review.md) record
the exact scope. The [verification report](verification/results.json)
records the strict build, complete transitive axiom audit, and exact source
and input hashes for the recorded checkpoint.

## Historical continuation: coupled parameters and the exact reserved remainder

**That continuation retained 45 of 69 completed numbered assertions.** It
added **99 public theorem proofs in eight modules** for the
Section 6 factorization chain. It constructs the coupled absorber integers,
positive even palettes, source palette bounds and divisibilities, with
uniform choices in the required order. It also completes the actual
packing-to-remainder stage on original multigraph edge copies.

The public theorem
`Overfull.BipartiteFactorization.exists_uniform_reserved_remainder` in
[`ReservedRemainder.lean`](Overfull/BipartiteFactorization/ReservedRemainder.lean)
starts with the original regular host and an explicit reserved-copy set.
It derives the retained core and its robustness and error bounds, completes
all `k-2*s` colors of the supplied balanced remaining exterior, and proves
that every surviving copy belongs to an actual simple `2*r`-regular
bipartite core. It constructs an orientation of that core with indegree and
outdegree exactly `r` at every vertex. All errors and order thresholds
precede the graph and reserved set.

The actual reserved set and compressed balanced exterior coloring remain
explicit stage inputs. The full spanning bi-setup, special path systems,
robust absorber, and final reconstruction of the whole host factorization
still require proof for the general Section 6 route. That continuation
did not complete Theorem 6.1 or Lemmas 4.2 and 4.14 and added no numbered
assertion. The later direct one-apex construction above now completes
Lemma 4.14 independently of the full Section 6 factorization.

The [construction and proof](docs/residual-factorization.md),
[source and public declaration mapping](docs/residual-factorization-source.json),
[semantic review](docs/residual-factorization-semantic-review.md), and
[complete new declaration mapping](verification/residual-factorization-declarations.json)
record the scope. Strict build logs, transitive axiom logs and exact hashes
are in [verification/results.json](verification/results.json).

## Historical checkpoint: complete Lemma 4.15

**That checkpoint completed 45 of 69 numbered assertions.** It proved
[Lemma 4.15](docs/four-odd-decomposition.md), the decomposition of all joining
edges of four odd parts. At that checkpoint the main theorem and **24**
numbered assertions remained incomplete.

The public theorem is
`Overfull.FourOdd.four_odd_parts_decomposition` in
[`Overfull/FourOdd/Theorem.lean`](Overfull/FourOdd/Theorem.lean). From the
original regular graph, absence of overfull sets, four odd parts, actual
boundary degrees, and prescribed matching-or-star supplies, it constructs
an exact partition into actual matchings. Exactly `h` pieces project to
perfect matchings or three-edge stars; every surplus piece projects to a
circuit of exact length two. The fixed sufficient bound is **1/1000** for
both manuscript error ratios. The undivided variants also cover `h = 0`.

The proof uses König coloring, equitable balancing, minority-class
contraction and Hall pairing. All quotient cut conditions, selections,
endpoint constraints and exact counts are derived in the 17 new `FourOdd`
modules. The general Fan–Zhang compatible-circuit theorem remains unproved
and is not an input to this construction.

The [source manifest](docs/four-odd-source.json),
[clause mapping and proof](docs/four-odd-decomposition.md),
[semantic review](docs/four-odd-semantic-review.md), and
[complete new declaration mapping](verification/four-odd-declarations.json)
record the exact scope. The strict build, complete transitive axiom log,
source hashes and verification-input hashes are recorded in
[verification/results.json](verification/results.json).

## Previous continuation: uniform localization and critical-partition reduction

That continuation added **109 public theorem proofs across 13 modules** to
the published `2eb61f5` checkpoint and preserved its **44 of 69** count.
The subsequent Lemma 4.15 proof added the forty-fifth complete assertion;
the subsequent Lemma 4.14 proof adds the forty-sixth.

The [uniform-localization results](docs/uniform-localization.md) construct
actual positive even allowed palettes and actual compatible fine/coarse
blocks, with error tolerances and order thresholds fixed before the graph.
The proofs derive the actual sampling budgets and floor-cap intervals,
handle the preferred-row-only case, construct light-cluster boundary
weights, and connect sampled estimates and adaptive copy losses to actual
selected graphs and their balanced localized colorings.

The [critical-partition reduction](docs/critical-partition-consequences.md)
constructs the exact low-degree deletion and proves every five-case,
degree-exception, and shore-size conclusion from the actual average-degree
estimate. Proposition 2.24 still requires the unformalized Cao–Chen
criticality-to-average-degree input. Section 6 still requires the full
spanning setup, absorber-compatible parameters, final boundary assembly,
special paths, robust absorber, and factorization. The new supporting
theorems are not counted as full proofs of those numbered statements.

The strict build, transitive-axiom inventory, and exact source and input
hashes are recorded in [verification/results.json](verification/results.json).

### Reunited published proof histories

This tree combines the continuation at `2eb61f5` with the separate published
`main` checkpoint `54db7b8`. The latter contained the compatible-circuit
work and an alternate proof of Lemma 4.13. All ten circuit modules are
retained unchanged. The alternate pattern construction is preserved in
27 `CircuitPatterns` modules, alongside the continuation's `Patterns`
implementation. Its public theorem is
`Overfull.circuit_frequent_boundary_pattern`.

The [source recovery manifest](docs/source-recovery.json) records both
parents, every restored source hash, the namespace changes, and 1,214
historical proof-declaration mappings. The verification script requires
every mapped proof in the new combined axiom audit. These recovered
declarations include generated support proofs and are separate from the
109 new public theorem proofs described above.

The [four-odd circuit components](docs/four-odd-circuits.md) preserve the
earlier partial progress on Lemma 4.15: actual circuit copies, finite
compatible cases, Hall pairing, matching forests, surplus circuits,
virtual-family counts, and incidence loads. The general compatible
decomposition remains unproved. The separate direct construction above
now completes the full lemma. The two proofs of Lemma 4.13 still count as
one numbered assertion; source recovery itself added no numbered assertion.

### Previous continuation: complete Theorem 2.23

The [robust-partition theorem](docs/robust-partition.md) completes
**Theorem 2.23**, increasing verified numbered coverage to **44 of 69**.
`Overfull.robust_partition` chooses its positive tolerance and order
threshold before every finite graph. From the actual minimum and maximum
degree bounds it constructs a partition into induced robust expanders
and ordered almost bipartite pieces, with every size, balance, edge-error,
internal-degree, and weighted floor bound stated in the manuscript.

The proof uses actual incidence counts and a finite refinement whose
shore count strictly increases until all ordinary pieces expand. It
requires only positivity of the prescribed error function on `(0,1)` and
permits the order threshold `n₀ = 1`. The implementation adds **71 public
theorem proofs across nine modules**. These establish one complete
numbered theorem; the broader published robust-partition conditions
are not separately claimed.

At that checkpoint the main theorem and **25** numbered assertions remained
unverified. The current total is **47 of 69**, with **22** remaining. The
exact build, axiom inventory, and source hashes appear in
[verification/results.json](verification/results.json).

### Previous continuation: complete Lemma 5.12

The [dense link-packing theorem](docs/dense-link-packing.md) completes
**Lemma 5.12**, which raised that checkpoint to **43 of 69**.
For every fixed `b ≥ 1` and `0 < λ ≤ 1`, the proof chooses an order
threshold before the graph and link family. It constructs actual
pairwise edge-disjoint perfect matchings under the manuscript's original
degree, intersection, and incidence bounds, retaining the constants
`81`, `6`, `3`, and `2`.

The public theorem is
`Overfull.Dense.LinkPacking.exists_tripartite_link_packing` in
[`Theorem.lean`](Overfull/Dense/LinkPacking/Theorem.lean). The proof derives
its finite probability estimates and matching candidates from the graph,
and proves that one complete selection covers every link. No matching
family, probability estimate, or numerical failure budget is assumed in
the final statement. The implementation adds **96 public theorem proofs
across ten modules**; these together establish one complete numbered lemma.

The main theorem remains unverified. The exact strict build, transitive
axiom audit, and source hashes for this checkpoint are recorded in
[verification/results.json](verification/results.json).

### Previous continuation: simultaneous actual palettes and blocks

[The simultaneous-selection continuation](docs/bipartite-simultaneous-selection.md)
adds **75 public theorem proofs in ten modules**. It derives active
palette-row, correction-pool, ordinary preferred-row, special
preferred-row, and capped-score failure estimates from the actual graph.
It constructs all disjoint palettes when their explicit budgets sum to less
than one. It also constructs actual fine and coarse blocks from compatible
position sets, retaining every prescribed size, inclusion, disjointness,
coarse union, and coverage relation. One shared permutation per vertex part
handles overlapping labels without an independence assumption between them.

These results complete the finite simultaneous-selection stage under the
stated graph, size, and numerical hypotheses. Uniform realization from the
original robust-core assumptions, the spanning regularity setup, special
path systems, the robust absorber, and full factorization remain open.
That supporting checkpoint left the numbered assertion count at
**42 of 69**. Lemma 5.12 added the forty-third full statement;
Theorem 2.23 added the forty-fourth, Lemma 4.15 the forty-fifth,
Lemma 4.14 the forty-sixth, and full Lemma 4.2 the forty-seventh.

## The main theorem

The formal target is `Overfull.MainTheorem` in [`Overfull/Specifications.lean`](Overfull/Specifications.lean). For every fixed real `ε > 0`, it asserts that all sufficiently large finite simple graphs satisfying

```text
Δ(G) ≥ (1/4 + ε) * |V(G)|
```

have a proper edge coloring with `Δ(G)` colors if and only if they have no overfull vertex set at that maximum degree. The order threshold may depend on `ε`. A set `X` is overfull at `Δ(G)` when its actual number of internal edges exceeds `Δ(G) * floor(|X|/2)`.

The definition is not an axiom. No unconditional theorem of this type is proved in this project.

[`Overfull/OverfullSubgraphs.lean`](Overfull/OverfullSubgraphs.lean) proves that the vertex-set predicate is equivalent to the absence of an intrinsically overfull subgraph with maximum degree exactly `Δ(G)`. Thus the formal target uses the same obstruction as the manuscript, including arbitrary vertex and edge deletions.

### The reduction that is proved

[`Overfull/MainReduction.lean`](Overfull/MainReduction.lean) extracts an edge-minimal counterexample, removes its isolated vertices, and proves that the no-overfull property is inherited. Vizing's bound supplies equality of the maximum degrees. The proof transports the resulting graph to `Fin m` and checks both order bounds, the density inequality, and the threshold transfer used in the manuscript.

Vizing's bound is proved in [`Overfull/Vizing/Theorem.lean`](Overfull/Vizing/Theorem.lean), using the compiled Misra–Gries formalization and adapters to the project's graph and coloring definitions. This gives the checked implication

```lean
Overfull.mainTheorem_of_criticalExclusion
    (h : Overfull.LargeCriticalExclusion) :
    Overfull.MainTheorem
```

`LargeCriticalExclusion` is the remaining structural assertion: sufficiently large edge-minimal counterexamples above the stated density threshold cannot have no overfull set. Its proof still requires the critical-graph application of the now-proved robust partition and the five coloring cases. It is a transparent proposition definition, not an assumed axiom. The implication above does not constitute a verification of the main theorem.

[`docs/main-theorem.md`](docs/main-theorem.md) records the formal statement, the checked reduction, and the outstanding work.

## Complete numbered manuscript results

| Manuscript result | Lean declaration | Scope |
| --- | --- | --- |
| Lemma 2.2: concentration | `Overfull.IndependentBernoulli.chernoff_of_independent_indicators` and `Overfull.Hypergeometric.chernoff` | Both distributional cases, including unequal indicator probabilities, with the actual means; formulated as finite probability laws |
| Theorem 2.3: Hall's theorem | `Overfull.bipartite_hall_iff` | Full equivalence for actual bipartite matching subgraphs, with arbitrary side sizes |
| Corollary 2.4: Hall's deficiency form | `Overfull.bipartite_hall_defect` | At most `h` uncovered left vertices under the stated deficiency inequalities |
| Theorem 2.5: the Tutte–Berge formula | `Overfull.TutteBerge.tutte_berge_integer_maximum` | The exact attained maximum of `o(G−X)−\|X\|`, using integer differences and actual maximum matchings |
| Lemma 2.6: fan consequences | `Overfull.Multigraph.IsKMinimal.endpoint_degree_sum` and `fan_low_degree_set_real` | Both the endpoint-degree inequality and the exclusion of edges to the low-degree set, with parallel edge copies |
| Lemma 2.7: the first fan argument | `Overfull.Multigraph.first_fan` | No internal core edge, exclusion of the specified exceptional-to-core edges, and the resulting degree bounds |
| Lemma 2.8: moving a bounded set out of the core | `Overfull.Multigraph.bounded_core_move_full` | An actual coloring after the move and the stated degree bound, including an empty core |
| Theorem 2.9: the matching polytope | `Overfull.Multigraph.matching_polytope` | Both directions for all finite loopless multigraphs, retaining parallel edge copies |
| Lemma 2.10: balanced color classes | `Overfull.Multigraph.balanced_edgeColoring` | Exceptional coverage, equal side coverage, spread at most two, exact vertex incidence, and both footprint bounds |
| Lemma 2.11: one high-degree vertex | `Overfull.Multigraph.edgeColoring_one_high` | A proper coloring of every edge copy under the strict `2s < k` bound |
| Lemma 2.12: sparse vertex deletion | `Overfull.Multigraph.edgeColoring_sparse_vertex_deletion_real` | The full coloring conclusion, including real error bounds and parallel edge copies |
| Lemma 2.13: bipartite robust expansion after deletions | `Overfull.IsBipartiteRobustExpander.after_edge_deletion_of_degree_bound` and `after_vertex_deletion` | Both assertions, with graph degrees, actual induced graphs, and side normalization |
| Lemma 2.14: an independent random reserve | `Overfull.RandomReserve.bipartite_random_reserve` | The actual sampled subgraph satisfies the robust-expansion probability bound; the failure estimate is stronger by a factor of two |
| Lemma 2.15: a short augmenting path | `Overfull.bipartite_robust_augmenting_path` | A simple alternating path avoiding the prescribed set, with at most `ceil(2/θ)+1` matching edges |
| Theorem 2.16: adaptive bipartite packing | `Overfull.adaptive_bipartite_packing` | Uniform constants, one rule for every admissible adaptive input sequence, actual edge-disjoint matchings perfect outside the presented sets, and robust expansion after every prefix |
| Lemma 2.17: reducing the robust range | `Overfull.robust_range_reduction` | Every allowed smaller range; actual neighbor counts |
| Lemma 2.18: small cuts through robust cores | `Overfull.SmallCuts.small_cut_lemma` | Real degree and error bounds, a uniform order threshold, and an actual union of whole cores differing by at most one vertex |
| Lemma 2.19: a robust cut splitting prescribed pairs | `Overfull.PairedCut.paired_cut` | A balanced cut splitting every pair, crossing minimum degree at least `αn/3`, and bipartite robust expansion with constants chosen before the graph and pairing |
| Lemma 2.20: adaptive ordinary packing | `Overfull.adaptive_ordinary_packing` | Uniform constants, one rule for every admissible adaptive input sequence, actual edge-disjoint matchings perfect outside the presented sets, and ordinary robust expansion after every prefix |
| Lemma 2.21: balanced robust realization | `Overfull.balanced_robust_realization` | Exact prescribed labelled degrees, a simple robust expander, and constants chosen before the order and degree sequence |
| Lemma 2.22: robust auxiliary completion | `Overfull.robust_auxiliary_completion` | The least auxiliary order, even regular completion, original edge copies retained, simple added edges, a robust auxiliary core, and no overfull set |
| Theorem 2.23: the robust partition | `Overfull.robust_partition` | Uniform constants before the graph; actual induced expanders and ordered almost bipartite parts; all size, edge-error, exceptional-degree, and `q+2ℓ` floor bounds |
| Lemma 2.25: balanced-core extraction | `Overfull.BalancedCore.balanced_core_of_bipartite_outcome` | From the stated bipartite outcome, actual equal retained sides of size at least `n/3`, at most `6√ρn` deleted vertices, and crossing degrees between `Δ−8√ρn` and `Δ` |
| Lemma 3.3: replacing a dense core | `Overfull.robust_core_replacement` | An actual robust replacement on the prescribed even vertex set, retaining the exterior and preserving the maximum-degree bound and every overfull-set inequality, with uniform constants |
| Lemma 4.1: reserve repair | `Overfull.MatchingRepair.reserve_repair` | Uniform constants, actual disjoint repaired matchings perfect outside the prescribed sets, and degree at most `μm` in both the used-reserve and released-original-edge unions |
| Lemma 4.2: ordinary-core factorization | `Overfull.ordinary_core_factorization`, `Overfull.ordinary_core_one_factorization` | Uniform constants before the host; bounded exterior and actual complementary coloring; exact partition of all original multigraph copies into perfect matchings |
| Lemma 4.7: matching-deletion probabilities | `Overfull.MatchingProbability.Distribution.odd_failure_probability`, `even_toggles_failure_probability`, and `family_failure_probability` | All three probability bounds, with the actual residual graph identified; also generalized to loopless multigraphs |
| Lemma 4.8: retaining prescribed exceptional edges | `Overfull.prescribed_exceptional_core_matching` | An actual perfect matching omitting at most `135720` prescribed matching edges, with all path, connectivity, parity, and Tutte conditions proved from the graph |
| Lemma 4.9: preserving prescribed exceptional edges | `Overfull.safe_prescription` | An actual perfect matching retaining all but `c₁ = 2q₀ + 4c₀` prescribed edges, fixing the sampled boundary and leaving no overfull set, with uniform constants |
| Proposition 4.10: reducing foreign exceptional incidence | `Overfull.foreign_edge_reduction` and `Overfull.foreign_edge_reduction_with_small_error` | An actual original-host sequence of perfect matchings, final degree at least `k₀/256`, no overfull set, actual surviving robust cores, and bounded total exceptional incidence outside assigned cores; fixed output robustness precedes any requested final error tolerance |
| Lemma 4.11: forcing an exceptional star | `Overfull.force_exceptional_star` | For each exceptional-centered star of more than `11*2^(t+4)` edges, an actual perfect matching meeting that star, obtained from a compressed matching with a proved forest projection; its deletion leaves no overfull set |
| Proposition 4.12: bounded exceptional-set absorption | `Overfull.bounded_exceptional_absorption` | An actual sequence of safe perfect-matching deletions and two actual core enlargements, retaining at least three quarters of the degree, fixed positive robustness, at most a uniform number of exceptional vertices, and core error bounded by an arbitrary positive function of the actual final exceptional cardinality |
| Lemma 4.13: frequent boundary patterns | `Overfull.frequent_boundary_patterns` | Actual safe perfect-matching deletions and complete exceptional absorption, degree and integer reserve at least `k/(3*b4(t))`, arbitrarily small relative core error, and actual matching-or-star pair and cut supply in the four-odd-part case; fixed output robustness precedes the error request |
| Lemma 4.14: prescribed boundary extension | `Overfull.boundary_extension` | A proper `d`-coloring of every original edge copy incident with the odd robust core, agreeing exactly with the prescribed singleton/triple boundary labels; all error tolerances and order thresholds precede the graph and coloring |
| Lemma 4.15: four odd parts | `Overfull.FourOdd.four_odd_parts_decomposition` | An exact partition of every original joining-edge copy into exactly `h` actual matchings projecting to perfect matchings or three-edge stars, with all remaining pieces actual matchings projecting to circuits of length two; the explicit error constant is `1/1000` |
| Lemma 5.3: encoding a precoloring by triangles | `Overfull.dense_encoding` | Local balance, exact deficit identities, and both directions of the extension/decomposition equivalence |
| Lemma 5.4: the explicit cycle absorber | `Overfull.Dense.CycleAbsorber.in_host` | Every positive cycle length; both triangle decompositions and the exact counts |
| Lemma 5.5: the finite absorber | `Overfull.Dense.FiniteAbsorber.finite_absorber_subgraph` | One actual absorber for every allowed balanced remainder, with simultaneous placement and total size at most `4h²2^(h²)` |
| Lemma 5.6: a bounded signed flow | `Overfull.dense_signed_flow` | Prescribed row and column sums with edge weights bounded by `d/λ` |
| Lemma 5.7: a fractional triangle decomposition | `Overfull.dense_fractional_triangles` | Actual triangle weights with incidence one at each edge and the exact bounds `1/(2k)` and `3/(2k)` |
| Lemma 5.9: a signed flow with unequal sides | `Overfull.dense_unequal_flow` | The stated bound `3θ/(2c−1)`, with the stronger bound `2θ/(2c−1)` also proved |
| Lemma 5.10: balancing six directed pairs | `Overfull.dense_reserve` | Positive edge probabilities, exact balance at every vertex, and explicit constants depending only on `c` |
| Lemma 5.11: integer balance repair | `Overfull.dense_balance_repair` | Actual deleted edges, an exactly locally balanced residual, and deleted degree at most `5√ξn`, with uniform constants |
| Lemma 5.12: dense link packing | `Overfull.Dense.LinkPacking.exists_tripartite_link_packing` | A uniform order threshold and actual pairwise edge-disjoint perfect matchings on all balanced two-part links, with the original `81`, `6`, `3`, and `2` constants |
| Lemma 6.4: reducing the bipartite robust range | `Overfull.bipartite_robust_range_reduction` | The smaller range `σ` and the exact new parameter `min(ν,ασ/4)` |
| Proposition 7.1: the sharpness family | `Overfull.sharpness_family` | Connectivity, order, maximum degree, class 2, edge count, and no overfull set |
| Corollary 7.2: arbitrarily large examples below one quarter | `Overfull.arbitrarily_large_class_two_graphs` | Every real coefficient below `1/4` and every order threshold |

These are 47 of the manuscript's 69 numbered assertions. The remaining 22, including Theorem 1.1, have no complete proof here. Checked components of other assertions are listed separately in [`docs/coverage.json`](docs/coverage.json). The count records complete numbered statements, not the relative size or difficulty of the remaining work.

## Further checked inputs

### Finite sampling for palettes and correction scores

The sampling continuation proves exact uniform marginals for images
of disjoint position sets under one random permutation, weighted
sample moments, capped-mean lower bounds, and the weighted
swap-variance estimate

\[
\operatorname{Var}f\le4(s/n)\sum_x\omega(x)^2.
\]

The swap proof uses finite conditioning on a maximum-weight member
and an exact add-one coupling. Nonlinear variance tensorization then
extends it to independent samples in arbitrarily many finite parts.
The graph adapters derive the exchange bound from actual original
edge copies and prove the correction-score variance bound
`8p₀ω₂²a|P|` for the union of samples in disjoint parts. The capped-mean
argument proves the manuscript's `7/4` numerical margin, and the
finite lower-tail adapter proves the `2²¹` Chebyshev constant from
explicit mean and variance bounds.

Actual allowed-color palettes are sampled from the allowed-label
subtype, with denominator equal to the number of allowed colors.
Their weighted demand is exactly the count of original copies in
the selected palette and pool. The permutation construction produces
simultaneously good disjoint palettes whenever the marginal failure
bounds sum to less than one; no independence between those palettes
is required.

The preceding sampling continuation added 128 named theorem proofs
across seven modules; see [bipartite-sampling.md](docs/bipartite-sampling.md).
The subsequent [score-mean continuation](docs/bipartite-score-mean.md) adds
31 public proofs of actual pair-inclusion laws, row moments, the full
score mean, its graph-specific lower tail, and supported block existence.
The [simultaneous-selection continuation](docs/bipartite-simultaneous-selection.md)
now derives the application estimates and explicit failure budgets, compares
the actual allowed population with the palette fractions, and selects the
palette and block families under those budgets. The latest
[uniform-localization continuation](docs/uniform-localization.md) supplies
uniform sampling choices, rounded integer palettes, compatible positions,
and boundary-weight and adaptive-loss estimates. The full spanning setup,
absorber-specific identities, final boundary construction, absorber, and
factorization remain open.
These factorization components do not themselves complete a numbered assertion.

### Two selected families and the exact remaining exterior

`Overfull.BipartiteFactorization.exists_colored_two_families` constructs
the fine and coarse selected graphs from original finite palette and
block conditions, their balanced localized colorings, and the coloring
of the exact complementary exterior graph. The coarse supplies reserve
the fine family's actual row and correction-pool costs before any fine
copies are chosen. Both correction signs are supported, and disjoint
palettes together with disjoint blocks within each scale give an actual
pairwise edge-disjoint family.

The remaining exceptional degree is exactly the original degree minus
the sum of the selected palette sizes. Its inactive coloring is derived
from the unused original labels. Across both selected families and the
remainder, the total footprint incidence at every core vertex equals
the original exterior degree, hence is at most `a`. Selected footprints
also avoid any boundary set whose original incident copies are deleted.

That continuation added 46 named theorem proofs across five modules.
See [bipartite-two-families.md](docs/bipartite-two-families.md) for the
exact hypotheses and conclusions. The subsequent
[sampling continuation](docs/bipartite-sampling.md) proves the finite
laws, moment bounds, and actual nonlinear score variance. The
[simultaneous-selection results](docs/bipartite-simultaneous-selection.md)
now establish the application bounds and simultaneous families under explicit
numerical budgets and prescribed positions. The latest uniform-localization
results derive those budgets and construct rounded palettes and compatible
positions. The complete spanning setup, final boundary, composition into
both colored families, and absorber remain open.

### One-palette construction and localized coloring

`Overfull.BipartiteFactorization.exists_localized_palette` now constructs
one actual selected palette graph and its balanced localized coloring.
The input is the actual exterior coloring, a palette, two blocks, a
deleted set, and explicit finite bounds on the surviving correction score
and unused preferred copies. The proof derives the actual row demands,
the signed correction imbalance, exact exceptional degrees, equal core
side-degree sums, block support, and exact correction-pool usage.

The construction inherits its initial coloring from the exceptional
palette base. No selected graph or selected-graph coloring is supplied
as an assumption. Its footprints are even, lie in the selected blocks,
have size at most `2|Ablock|a/|I|+4`, and have exact per-vertex load equal
to the selected degree. The deletion estimate charges only copies
inside the relevant correction pool while avoiding all deleted copies.

See [bipartite-palette-assembly.md](docs/bipartite-palette-assembly.md)
for the exact hypotheses, orientation, and remaining obligations.
That continuation added 40 named theorem proofs. The subsequent
two-family construction composes these results with exact union,
deletion, and residual-coloring arguments. The subsequent sampling
results supply the analytic ingredients. The
[simultaneous-selection results](docs/bipartite-simultaneous-selection.md)
instantiate the graph estimates and select both kinds of family under explicit
numerical budgets and prescribed positions. The remaining uniform realization
from the robust-core hypotheses is recorded in the next-target document.

### Finite localization constructions

The preceding continuation proves preferred representative edge selection,
threshold separation and actual allowed-color preparation, capped
correction-edge selection after arbitrary deletions, and a fan criterion
that colors each selected graph from its inactive residue. The latter
also gives balanced localized classes with footprint bound
`2|Ablock|a/k+4`. See [bipartite-localization.md](docs/bipartite-localization.md)
for the hypotheses and scope of all four constructions.

These results construct actual copy sets and colorings, now composed
into both selected families and their exact remainder under finite
supply conditions. The [sampling results](docs/bipartite-sampling.md)
now provide the weighted moments, capped means, and actual graph-score
variance. The simultaneous-selection continuation subsequently completed
the application estimates and actual simultaneous choices under explicit
finite budgets. The latest uniform-localization results construct the
sampling parameters, integer palettes, and compatible positions, and prove
the boundary-weight and loss bounds. The full regularity setup, final
boundary construction, and absorber remain unformalized.

### Three bipartite factorization prerequisites

The continuation in [bipartite-prerequisites.md](docs/bipartite-prerequisites.md)
proves reverse-direction bipartite robustness with parameters `(ν²/4,2τ)`,
constructs the balanced coloring of the actual complement of an embedded
bipartite core, and preserves the ordinary exceptional-vertex neighborhood
conditions and complementary coloring under bounded core moves. The
numerical move budgets are chosen uniformly before the graph.

These remain supporting results for the incomplete Theorem 6.1 and
Proposition 6.2. Full Lemma 4.2 is now proved by the bounded-exterior route;
Lemma 4.14 is proved by the direct one-apex route above. Historically, this
branch continued the exactly recovered ordinary-core tree `aab43893d9b1`;
its complete numbered coverage was 42 of 69 before the link-packing result.
The later terminal
checkpoint `eafe3efc18bb` was unavailable after the source workspace reset
and is outside this audit. It is distinct from the published circuit
checkpoint `54db7b8`, whose source is now included through the recovery
described above. The linked note records the original recovery and the
precise scope of the three prerequisite results.

### Vizing's theorem

`Overfull.vizing_finite` proves the upper bound `Δ(G) + 1` for arbitrary finite simple graphs with the project's proper edge-coloring definition. The adapter uses actual adjacency and unordered edges; a partial upstream coloring is accepted only after the upstream completeness theorem proves that every graph edge is colored.

The upstream source is Arohee Bhoja's [Vizing formalization](https://github.com/aroheebhoja/vizing), pinned to commit `c4fc77be6af1a48a44351234120898ad3cf6b545`. The project fetches that version and applies a recorded compatibility patch. The exact file hashes and source provenance are in [`docs/vizing-source.json`](docs/vizing-source.json). The complete upstream source is not redistributed in this archive.

### König's theorem

[`Overfull/Konig.lean`](Overfull/Konig.lean) proves that a finite loopless bipartite multigraph has a proper `k`-edge-coloring if and only if every degree is at most `k`. Its coloring assigns a value to every actual edge copy. The proof uses a matching covering every maximum-degree vertex, deletes those copies, and inducts on the degree bound. It includes `k = 0` and arbitrary parallel multiplicities.

### Matchings, the matching polytope, and their probabilities

[`Overfull/BipartiteMatching.lean`](Overfull/BipartiteMatching.lean) proves the Hall inequalities and constructs a perfect matching in a balanced bipartite robust expander with the stated minimum crossing degrees.

[`Overfull/TutteBerge.lean`](Overfull/TutteBerge.lean) proves that a maximum matching leaves exactly `max_X (o(G−X)−|X|)` vertices uncovered. It uses the actual odd components of the graph after vertex deletion and counts actual unordered matching edges. The proof adds universal vertices, applies mathlib's proved Tutte theorem, and restricts the resulting perfect matching. It proves both the upper bound for every integer difference and attainment by a vertex set, as well as the existence of a maximum matching. The empty graph is included.

[`Overfull/FractionalMatching.lean`](Overfull/FractionalMatching.lean) proves that every positive `k`-regular simple graph with no `k`-overfull set admits a finite probability distribution on perfect matchings in which each edge has marginal `1/k`. It proves the degree and odd-cut hypotheses of the perfect-matching polytope theorem and identifies its integral points with mathlib perfect-matching subgraphs.

[`Overfull/MatchingPolytope.lean`](Overfull/MatchingPolytope.lean) proves the full matching-polytope theorem for loopless multigraphs. It doubles the graph, adds one edge between the two copies of each vertex, and proves all required odd-cut inequalities before applying the perfect-matching polytope theorem. Projection gives a convex combination of actual matchings. The converse, the degree inequalities, and the exact interpretation of zero–one vectors as matchings are proved as well.

It also constructs uniform-marginal distributions for nonregular multigraphs with maximum degree at most `k` and no `k`-overfull set. Every matching of positive weight covers every degree-`k` vertex. For a regular multigraph, removing zero-weight indices gives a distribution on actual perfect matchings. The edge type distinguishes parallel copies throughout.

The underlying perfect `b`-matching proof is adapted from [Shengtong Zhang's repository](https://github.com/shengtongz/lovasz-opus). Its mathematical proof compiles unchanged with the required mathlib imports. The source commit, license, and adaptation are recorded in [`docs/bmatching-source.json`](docs/bmatching-source.json), [`THIRD_PARTY_NOTICES.txt`](THIRD_PARTY_NOTICES.txt), and [`LICENSE_BMATCHING.txt`](LICENSE_BMATCHING.txt).

[`Overfull/MatchingProbability.lean`](Overfull/MatchingProbability.lean) then proves the failure bounds `<1/k`, `≤10/k`, and `≤11ℓ/k`. The proof derives the cut parity, toggle identities, expectations, and finite union and Markov bounds. It also proves that its failure event is precisely the odd-cut failure in the actual graph obtained by deleting the matching, and that the residual graph is `(k−1)`-regular.

[`Overfull/MultigraphMatchingProbability.lean`](Overfull/MultigraphMatchingProbability.lean) proves all three bounds for loopless multigraphs. Its residual multigraph has exactly the remaining edge copies; the cut and degree identities are proved for that graph. This covers the multiplicities appearing in the completion arguments.

### Robust cores and signed flows

The augmenting-path theorem permits the supplied matching to lie outside `G`. Its conclusion records the two injective vertex sequences, actual alternating edges, avoidance of the forbidden set, and the quantitative length bound. Separate theorems establish distinctness of the matching edges and that the forward graph edges do not belong to the matching.

The small-cut theorem represents each simple core by an injective, endpoint-preserving map into the multigraph edge copies. It proves that distinct cores contribute disjoint edge sets. The explicit sufficient order condition is `3 < ν²c²n`; the public theorem chooses a uniform order threshold before quantifying the graph, the real degree and error bounds, or the cut.

The signed-flow proofs derive all cut inequalities from actual crossing degrees. The resulting weights vanish on nonedges and have the prescribed sums. The finite circulation proof is included with its pinned source and compatibility changes in [`docs/circulation-source.json`](docs/circulation-source.json) and [`CIRCULATION_NOTICE.txt`](CIRCULATION_NOTICE.txt). Both flow statements include empty vertex classes.

The bipartite range lemma proves the exact neighborhood-expansion conclusion. At positive order, its hypotheses also imply the usual admissibility of the new robust parameter. The empty-graph branch proves the expansion inequality without asserting that additional parameter bound.

### Balanced and sparse multigraph colorings

[`Overfull/CriticalMultigraph.lean`](Overfull/CriticalMultigraph.lean) constructs minimal noncolorable restrictions of the actual edge copies and proves the missing-color counts. [`Overfull/MultigraphFan.lean`](Overfull/MultigraphFan.lean) proves the two-edge fan property by an actual recoloring, then derives both conclusions of Lemma 2.6. [`Overfull/MultigraphFanApplications.lean`](Overfull/MultigraphFanApplications.lean) proves the first-fan and bounded-core-move lemmas. The host may have parallel edges; only the distinguished core must be simple in the bounded-move argument. Its full wrapper includes the empty-core case without an extra assumption that the exterior degree bound is nonnegative.

[`Overfull/BalancedColoring.lean`](Overfull/BalancedColoring.lean) proves the balanced-coloring lemma from a supplied proper coloring. It constructs actual switches on unions of two-color components and proves their effects on vertex coverage. Two finite minimizations give equal side coverage and spread at most two. The component argument retains parallel copies in its degree and endpoint counts; connectedness alone uses the underlying simple graph. The exceptional vertices are covered in every color, and both footprint estimates follow from the actual incidence counts.

[`Overfull/MultigraphGreedy.lean`](Overfull/MultigraphGreedy.lean) first colors the star at the distinguished high-degree vertex injectively and extends the coloring across the remaining edge copies. [`Overfull/SparseColoring.lean`](Overfull/SparseColoring.lean) proves the sparse-deletion lemma by coloring the core and the two-star subgraph, then using Hall's theorem to assign distinct available colors to the two-star classes. The central parallel edges receive the remaining colors. The actual vertex deletion and all degree comparisons are proved.

### Random reserves and degree control

[`Overfull/Probability/Bernoulli.lean`](Overfull/Probability/Bernoulli.lean) defines the finite independent sampling distribution and proves its normalization and joint coordinate probabilities. [`Overfull/RandomReserve.lean`](Overfull/RandomReserve.lean) then proves Lemma 2.14 for the actual sampled graph. Its failure bound is

```text
4^m * exp(-p * ν^2 * m^2 / 24).
```

This is stronger than the manuscript's bound with leading factor two. The proof constructs the vertex-set witnesses to failed robust expansion and bounds their actual sampled crossing-edge counts.

[`Overfull/Probability/Concentration.lean`](Overfull/Probability/Concentration.lean) proves the two-sided Chernoff estimate with constant `1/3` for the common-probability finite Bernoulli model, along with the additive bound used for degrees. [`Overfull/Probability/IndependentBernoulli.lean`](Overfull/Probability/IndependentBernoulli.lean) allows a different success probability at every coordinate and transfers the estimate to any finite probability law with the independent joint distribution. [`Overfull/Probability/Hypergeometric.lean`](Overfull/Probability/Hypergeometric.lean) proves the same estimate for actual uniform sampling without replacement. Both modules prove the stated mean and derive the exponential-moment estimate; neither assumes a concentration conclusion. This completes the two distributional cases of Lemma 2.2 in finite-law form. There is no separate interface to `Mathlib.iIndepFun` on an arbitrary underlying measure space.

[`Overfull/RandomReserveDegrees.lean`](Overfull/RandomReserveDegrees.lean) combines the expansion and degree estimates in one sample. It proves a uniform order threshold before quantifying the graph and obtains an actual contained bipartite reserve with all degree deviations from `p*Δ` strictly below `2εm`. This supplies the reserve-selection input in Step 1 of the complete adaptive packing proof.

[`Overfull/MatchingExtension.lean`](Overfull/MatchingExtension.lean) proves that a maximum matching can retain every vertex covered by a prescribed matching. It also constructs a matching covering any set `Z` when each vertex of `Z` has degree greater than `2|Z|`, then extends its coverage to a maximum matching. These are actual matching subgraphs, and maximality compares their actual edge counts. They supply the coverage-preserving selection used in Step 2 of adaptive packing.

[`Overfull/BipartitePackingDeficiency.lean`](Overfull/BipartitePackingDeficiency.lean) derives an actual Hall witness from maximum matching size and counts the graph edges between the witness and its neighborhood. Under ordinary degree bounds `d−a ≤ d_G(v) ≤ d+a+u(v)`, nonnegative load of total at most `t`, and side orders at most `m`, it proves that the number missed on the left is at most `(2am+t)/d`. Equal side orders imply equal uncovered counts. The ambient `m` may exceed the actual side order, as required after deleting the prescribed vertices.

[`Overfull/BipartitePackingStep.lean`](Overfull/BipartitePackingStep.lean) combines these results into the matching-selection conclusion and proves the manuscript bound `h ≤ (16+2c₀)εm/γ`. A separate variant derives the saturated set directly from a positive capacity and the total load. [`Overfull/BipartitePackingWorking.lean`](Overfull/BipartitePackingWorking.lean) applies this to the actual graph obtained by deleting the reserve, previously used edges, and the current forbidden vertices. Its degree and load bounds are derived from that graph.

### Adaptive bipartite packing

[`Overfull/BipartitePacking.lean`](Overfull/BipartitePacking.lean) proves Theorem 2.16. It chooses `ε` and `m₀` before the graph, and then chooses one fixed rule before any adaptive input sequence. The rule receives only the earlier sets and matchings and the current forbidden set. Every output is an actual subgraph of `G`, is a matching with vertex set exactly the complement of the current forbidden set, and has no edge in an earlier matching.

The proof constructs vertex-disjoint alternating paths in the unused reserve and performs the simultaneous switches needed to complete each matching. Its capacity and total-load bounds count actual reserve edges in the union of the chosen matchings. The one-round recurrence proves that a matching preserving the geometric load bound always exists, and the fixed rule maintains this bound throughout all `max(0, floor(Δ−γm))` rounds. After every prefix, the remaining graph is a bipartite robust `(pν/4, τ)`-expander.

[`Overfull/BipartitePackingCorollaries.lean`](Overfull/BipartitePackingCorollaries.lean) gives direct statements for a prescribed sequence of forbidden sets and for the case in which every set is empty. The latter produces actual pairwise edge-disjoint perfect matchings. Both statements give the robust-expansion conclusion after removing any subfamily, hence after every prefix. The prescribed-sequence theorem assumes the manuscript's total incidence bound explicitly. The adaptive theorem uses the weaker bound on past incidences at each round.

[`docs/adaptive-packing.md`](docs/adaptive-packing.md) records the statement, the proof components, and the correspondence with the manuscript. The packing theorem is one supporting result; it does not establish the remaining structural and coloring arguments for the main theorem.

### Adaptive ordinary packing

[`Overfull/OrdinaryRandomReserve.lean`](Overfull/OrdinaryRandomReserve.lean) samples each unordered edge once and proves ordinary robust expansion with parameter `pν/4`. Its failure bound is `4^n exp(−pν²n²/48)`. The counting proof permits the two witness vertex sets to overlap. [`Overfull/OrdinaryRandomReserveDegrees.lean`](Overfull/OrdinaryRandomReserveDegrees.lean) chooses one actual contained reserve satisfying both expansion and all degree bounds, with a threshold uniform over the graph.

[`Overfull/OrdinaryPackingDeficiency.lean`](Overfull/OrdinaryPackingDeficiency.lean) uses the proved Tutte–Berge formula and actual component boundary counts to obtain

```text
h ≤ (m + 2am + t)/(d − a + 1)
```

under the specified degree and total-load bounds. It derives the manuscript estimate `h ≤ (30/γ)(εm+t/m)` and constructs a maximum matching covering the saturated vertices. [`Overfull/OrdinaryPackingWorking.lean`](Overfull/OrdinaryPackingWorking.lean) applies this to the actual graph after deleting the reserve, prior matching edges, and the forbidden vertices. The resulting ambient matching has even uncovered count and the required edge avoidance and coverage properties.

[`Overfull/OrdinaryRobustStability.lean`](Overfull/OrdinaryRobustStability.lean) proves robust expansion after simultaneous bounded edge and vertex deletion. It also applies the actual reserve-load identities to the unused reserve and residual graph. [`Overfull/OrdinaryPackingInitial.lean`](Overfull/OrdinaryPackingInitial.lean) first reduces the robust range of the original graph, then chooses one actual reserve with the required minimum degree and degree deviations. Its order threshold is uniform over the graph and nominal degree.

[`Overfull/MatchingPairing.lean`](Overfull/MatchingPairing.lean) extends an actual matching on an even vertex set to a partition into pairs. [`Overfull/OrdinaryMatchingCompletion.lean`](Overfull/OrdinaryMatchingCompletion.lean) completes a matching through a supplied actual balanced robust cut, using the proved bipartite augmenting-path construction. The result is an ambient matching perfect outside the forbidden set. It uses only original matching edges and unused reserve edges, uses no reserve edge at a protected vertex, and bounds the total reserve degree by `ℓh`, where `h` is the total uncovered count.

[`Overfull/OrdinaryPackingBounds.lean`](Overfull/OrdinaryPackingBounds.lean) proves the reserve-load recurrence and the bound with `c₀ = exp(120ℓ/γ)−1`, together with the numerical budget for the protected vertices and augmenting paths. [`Overfull/OrdinaryPackingParameters.lean`](Overfull/OrdinaryPackingParameters.lean) chooses the positive reserve, error, and capacity constants in the required order. [`Overfull/PairedCut/Matching.lean`](Overfull/PairedCut/Matching.lean) constructs the actual robust cut crossing a given matching.

[`Overfull/OrdinaryPackingRound.lean`](Overfull/OrdinaryPackingRound.lean) proves that a new matching satisfying the capacity and total-load bounds exists at every admissible step. [`Overfull/OrdinaryPackingStrategy.lean`](Overfull/OrdinaryPackingStrategy.lean) chooses one fixed rule and proves its invariant for every adaptive forbidden-set policy. [`Overfull/OrdinaryPacking.lean`](Overfull/OrdinaryPacking.lean) assembles these results into full Lemma 2.20. The positive error, retained robust parameter, and order threshold precede the graph; the rule precedes the adaptive input. Every output is an actual matching perfect outside its current forbidden set, the matchings are edge-disjoint, and the remaining graph retains the prescribed robust range after every prefix.

[`Overfull/OrdinaryPackingPrefix.lean`](Overfull/OrdinaryPackingPrefix.lean) strengthens the strategy interface for an interrupted phase. One fixed rule gives an actual packing and a robust unused graph after every prefix whose inputs satisfy the size, parity, and incidence conditions up to that point. The rule is chosen before both the adaptive input and the stopping index. No condition is imposed on later inputs; the constants retain the quantifier order of Lemma 2.20.

### A cut splitting prescribed pairs

[`Overfull/PairedCut/Full.lean`](Overfull/PairedCut/Full.lean) proves Lemma 2.19. For fixed `α > 0` and `0 < ν ≤ τ ≤ 1/8`, it chooses `ξ > 0` and an order threshold before the graph and prescribed pairing. The resulting equal bipartition splits every pair, has crossing minimum degree at least `αn/3`, and is a bipartite robust `(ξ,4τ)`-expander.

The proof constructs an equitable regularity partition using mathlib's proved regularity theorem. [`Overfull/PairedCut/Regularity.lean`](Overfull/PairedCut/Regularity.lean) bounds the total degree lost on discarded edges, proves robust expansion in the actual reduced graph, and trims the parts to equal clusters with a small exceptional set. [`Overfull/PairedCut/Labels.lean`](Overfull/PairedCut/Labels.lean) orients the prescribed pairs to balance these clusters and preserve crossing degrees. [`Overfull/PairedCut/Lifting.lean`](Overfull/PairedCut/Lifting.lean) derives expansion of the cut from lower bounds on actual cluster edge counts. Its last step uses the side size in both the neighborhood threshold and expansion surplus. The required ordinary regularity and inheritance statements are proved within the project; the general directed regularity statements cited in the manuscript are not claimed separately.

### Balanced robust realization and auxiliary graphs

[`Overfull/RobustRealization.lean`](Overfull/RobustRealization.lean) proves Lemma 2.21 on the prescribed labels. It constructs the exact degree multiset from cycle powers and disjoint added or deleted pairs, proves robustness using consecutive blocks, and permutes the vertices to match the required sequence. The positive robust parameter and order threshold depend only on the fixed density and robust range, and precede the order and sequence. All parity cases and the complete graph are included.

[`Overfull/AuxiliaryCompletion.lean`](Overfull/AuxiliaryCompletion.lean) proves full Lemma 2.22. Its constants precede the original multigraph, and it uses the least allowed auxiliary order. The completion is even-order and regular, retains every original edge copy, has multiplicity one at each added edge, and induces the required simple robust graph on the new vertices. Balanced neighbor sets give each new vertex at most one neighbor of original deficiency one. This supplies the estimate for an odd set containing exactly one new vertex; the other odd sets are controlled by the original inequalities and the auxiliary cuts. The proof establishes that the actual completion has no overfull set. [`docs/auxiliary-completion.md`](docs/auxiliary-completion.md) records its construction and proof map.

### Balanced-core extraction

[`Overfull/BalancedCore.lean`](Overfull/BalancedCore.lean) proves Lemma 2.25 from the precise bipartite outcome properties supplied by Lemma 2.24. It defines the vertices with too few neighbors across the original partition, deletes this actual set, and trims the larger surviving side. The retained sides have the same size, at least `n/3`; at most `6√ρn` vertices are lost, and every degree in the actual crossing graph lies between `Δ−8√ρn` and `Δ`. The construction includes the zero-error case. The preceding existence and classification assertion in Lemma 2.24 remains unproved.

### Replacing a dense core

[`Overfull/Replacement.lean`](Overfull/Replacement.lean) proves full Lemma 3.3. For fixed `β > 0` and `0 < τ ≤ min(β/16,1/4)`, it chooses positive `μ`, `ξ`, and an order threshold before the graph and its even core vertex set. The output is an actual robust `(μ,τ)`-expander on that set, with minimum degree at least `k−2a−1`. Its edges avoid the retained exterior, and the ambient replacement has maximum degree at most `k` and no `k`-overfull set.

The proof constructs a regular robust graph using Lemma 2.21 and deletes its forbidden exterior edges. Exact graph identities control the degrees and induced edge counts. Actual robust core cuts reduce a possible overfull set to the four small or complementary-small core intersections; regular degree counts handle each case. [`docs/replacement.md`](docs/replacement.md) gives the statement and proof map. The subsequent coloring of the comparison graph remains a separate task.

### Repairing a family of matchings

[`Overfull/MatchingRepair.lean`](Overfull/MatchingRepair.lean) proves full Lemma 4.1. For every sufficiently small positive `μ`, it chooses a positive error and an order threshold before the reserve graph and matching family. The resulting matchings are perfect outside the prescribed forbidden sets, use only their own original edges and reserve edges, and are pairwise edge-disjoint. Both the actual used-reserve union and the actual released-original-edge union have degree at most `μm` at every vertex.

The proof constructs each repair in the unused reserve. [`Overfull/MatchingRepairStep.lean`](Overfull/MatchingRepairStep.lean) constructs the required robust cut and completes a matching while protecting specified covered vertices. [`Overfull/MatchingRepairLoad.lean`](Overfull/MatchingRepairLoad.lean) separates internal reserve incidence from incidence at the original uncovered vertices and preserves the integer internal capacity through each update. [`Overfull/MatchingRepairFamily.lean`](Overfull/MatchingRepairFamily.lean) proves disjointness of the updated family, and [`Overfull/MatchingRepairAccounting.lean`](Overfull/MatchingRepairAccounting.lean) bounds released-edge degree by used-reserve degree. All parameter choices and the finite-family induction are proved. [`docs/matching-repair.md`](docs/matching-repair.md) records the hypotheses, numerical choices, and proof map.

### Retaining prescribed exceptional edges

[`Overfull/PrescribedMatching.lean`](Overfull/PrescribedMatching.lean) proves full Lemma 4.8. In a graph with at most four large core cliques and an exceptional set, an actual perfect matching retains all but at most `135720` edges of the prescribed matching. The hypotheses include the existence of an initial perfect matching, as in the manuscript. The formal theorem also permits overlapping core cliques and prescribed edges with both endpoints exceptional.

The proof constructs paths with at most twelve vertices and a bounded set preserving core connectivity after any deletion of at most three vertices. It discards only prescribed matching edges meeting that set, proves actual component and parity comparisons, checks all three ranges of Tutte deletion sets, and completes the retained matching. No path, witness, or Tutte feasibility statement is assumed in the public theorem. [`docs/prescribed-matching.md`](docs/prescribed-matching.md) records the exact hypotheses and the six proof modules.

### Preserving prescribed edges and odd-set inequalities

[`Overfull/SafePrescription.lean`](Overfull/SafePrescription.lean) proves Lemma 4.9. For the stated regular graph, robust cores, cluster groups, and prescribed exceptional matching, it constructs a perfect matching whose deletion leaves no overfull set and which omits at most `c₁ = 2q₀ + 4c₀` prescribed edges. Here `q₀ = 4096(t₀+6)` and `c₀ = 135720`. The marked-set bound `t₀` is fixed before the error tolerance and order threshold. Both constants precede the graph and the actual exceptional order, which may grow with `n` subject to `a + |Z| + 1 ≤ εn`.

The proof samples an actual perfect matching preserving the tested cuts and constructs its exact boundary submatching, consisting of edges meeting the marked set or joining different clusters. The finite Markov estimate bounds this submatching by `q₀` edges. After its vertices are removed, one application of Lemma 4.8 across all surviving cores, followed by compression, gives an actual retained partial matching `F`. This proves the stronger intermediate loss bound `2q₀ + c₀`. Every retained edge belongs to the original graph, and completion inside the actual robust cores preserves `F`.

The proof derives the small-cut classification from the group condition and actual core expansion. Fixing the boundary transfers the tested odd-cut inequalities on whole-cluster unions and their one-vertex changes. The residual core bounds then exclude every overfull set after the perfect matching is deleted. This proves one safe-prescription step. The iterative refinement in Proposition 4.10 and the repeated forcing and absorption in Proposition 4.12 are proved below.

### Forcing an exceptional star

[`Overfull/ForceMatching.lean`](Overfull/ForceMatching.lean) proves Lemma 4.11. In the stated `h`-regular graph with no `h`-overfull set, at most four disjoint robust cores, and at most `t` exceptional vertices, every star of more than `11*2^(t+4)` edges centered at an exceptional vertex is met by a perfect matching whose deletion leaves no overfull set at degree `h−1`. The robust range and positive error tolerance are fixed before `t`; only the lower bound on the graph order may depend on `t`.

The proof constructs all three actual matchings: the sampled perfect matching, its compressed submatching, and the perfect completion inside the cores. [`Overfull/Compression/Matching.lean`](Overfull/Compression/Matching.lean) retains every exceptional-incident edge and at most three joining edges whose projected labels form a forest, and proves even uncovered order in every core. The probability argument counts the actual tested family and uses the exact star probability `|S|/h`. Completion preserves the whole-union cut-edge sets of the compressed matching. The parity of perfect-matching cuts controls every one-vertex toggle, and the small-cut theorem then excludes every overfull set in the actual residual graph.

[`Overfull/ForceMatching/Adaptive.lean`](Overfull/ForceMatching/Adaptive.lean) also prepares the compressed partial matching before its core completion is chosen. Its safety clause applies to every compatible completion with the stated residual robust cores. Proposition 4.12 uses this preparation with one fixed certified rule per core throughout its forcing phase.

### Foreign-edge reduction with actual refinements

[`Overfull/ForeignEdges/Reduction.lean`](Overfull/ForeignEdges/Reduction.lean) proves Proposition 4.10. It constructs fresh maximizing core assignments, actual foreign matching classes, actual small-cut refinements with surviving robust cores, and Fin-4 labels. Recorded-cut accounting bounds the actual intercluster edge count and the number of heavy marked vertices. The incidence budget for adaptive packing is derived from distinct actual exterior edges, including the current partial matching before its completion exists.

The preparation theorem in [`Overfull/SafePrescription/Adaptive.lean`](Overfull/SafePrescription/Adaptive.lean) separates the bounded exceptional partial matching from its core completion. Fixed-rule transcript, next-step, and completion theorems then construct the actual local and ambient matchings, retaining the exact whole unused cores and their fixed robust parameters. The restart schedule and one original error and order threshold are chosen before the graph.

The inner induction constructs an actual interrupted or completed epoch. The outer induction carries the original-host matching sequence, exact residual graph, actual cut history, changed core sets, and all quantitative bounds. Every refinement strictly increases the number of occupied core groups; after three refinements the core labels are injective and no triggering shore exists. Every prefix satisfies the required degree reserve. The full current foreign graph is rebuilt and recolored at each restart.

The final completed epoch supplies the actual incidence bound `256*(c₁+6+t₀)*h`, with `k₀ ≤ 256*h`. This improves the manuscript allowance containing `4c₁`. The result contains one sequence of actual perfect matchings in the original graph, its exact final residual, and surviving core error at most `a+3`. [`Overfull/ForeignEdges/ReductionError.lean`](Overfull/ForeignEdges/ReductionError.lean) fixes the positive output robustness parameter before an arbitrary requested final error tolerance, then chooses the original error and order threshold. [`docs/foreign-edge-reduction.md`](docs/foreign-edge-reduction.md) records the quantified statement and the two constructed inductions. This completes one more numbered assertion; the main theorem remains unverified.

### Bounded exceptional-set absorption

[`Overfull/Absorption/Bounded.lean`](Overfull/Absorption/Bounded.lean) proves Proposition 4.12. Its positive output robustness is fixed before an arbitrary positive function `f`. The exceptional bound, original error tolerance, and order threshold are then chosen before the graph. The actual result contains a sequence of perfect matchings in the original host, its exact residual of degree at least `3h/4`, no overfull set, and enlarged robust cores covering all but at most the uniform bound of exceptional vertices. The final core error is at most `f(|Z_final|) * h_final`, with no monotonicity assumption on `f`.

The proof selects a light band from the original foreign-neighbor counts and absorbs the vertices below that band into their assigned cores. One fixed certified rule per enlarged core supplies every completion during the forcing phase. The actual potential counts all neighbors outside each selected vertex's assigned enlarged core, including remaining exceptional neighbors, and decreases whenever the corresponding star is forced. Its initial bound is strictly below `h/4`. A second actual enlargement absorbs the selected band; the terminal outside-degree bound supplies the final error without a second exceptional-order term. [`docs/exceptional-absorption.md`](docs/exceptional-absorption.md) records the parameter order, graph constructions, and complete proof map.

### Frequent boundary patterns

[`Overfull/Patterns/Frequent.lean`](Overfull/Patterns/Frequent.lean) proves Lemma 4.13. The positive surviving robust parameter is fixed before an arbitrary requested final error. The proof groups an actual scaled perfect-matching distribution into common fixed-label patterns, rounds one common proposal, realizes the accepted copies as actual edge-disjoint boundary matchings, and completes them with one certified rule per core. Exact cut accounting and the small-cut theorem prove that every deletion prefix has no overfull set.

The distinguished pattern retains an integer reserve `r >= k/(3*b4(t))`. Its actual residual edges supply distinct neighbors for absorbing every exceptional vertex. The final enlarged cores partition all vertices, have the requested relative degree error, and retain fixed robustness. Their parity is the parity of the distinguished joining forest; four odd parts force a perfect matching or three-edge star, with at least `r` actual joining edges for each forest pair and the required supply on every union of parts. See [`docs/frequent-patterns.md`](docs/frequent-patterns.md) for the construction and parameter order. The next subsection records the completed extension for Lemma 4.14. The terminal factorization of Proposition 4.16 and the main theorem remain unverified.

### Complete prescribed boundary extension

[`Overfull.boundary_extension`](Overfull/BoundaryExtension/Full.lean) proves the full Lemma 4.14. It colors all original copies with an endpoint in the odd robust core and preserves every prescribed boundary label. Its input only requires ambient degree `d` on the core, an embedded simple robust core of minimum degree at least `d-a`, sufficiently small relative error, sufficiently large core order, and the stated proper singleton/triple boundary coloring with a linear singleton reserve. The ambient host need not be regular outside the core.

The earlier `Overfull.boundary_extension_reduction` constructs actual completed triple classes, their exact deletion, the surviving singleton labels, and an even regular contraction with one exterior apex. The new `Overfull.OneCore.exists_uniform_one_apex_factorization` supplies an actual coloring of that contraction. A prescribed neighbor pairing and an actual two-row label choice preserve the moved core vertex's supply into both shores after the first completed matchings. `Overfull.TwoApexFactorization.exists_uniform_two_apex_factorization` then constructs selected exceptional colors, completes them by robust bipartite packing, and colors the actual bipartite remainder with König. Palette restoration and reassembly retain every original prescribed singleton and triple label, with properness at the original exterior vertices.

All errors and order thresholds precede the input graph and coloring. The proof uses no general Lemma 4.2, Corollary 4.6, Theorem 6.1, spanning bi-setup, or robust absorber. Full Lemma 4.2 is now proved separately; the broader bipartite and two-core factorization assertions remain open. The current count is **47 of 69**, with **22** remaining, including the main theorem. See [the full statement and proof map](docs/boundary-extension.md).

### Ordinary-core reduction to a bipartite robust core

`Overfull.OrdinaryFactorization.exists_uniform_bipartite_reduction` constructs the ordinary-core preprocessing in Lemma 4.2. Its crossing robustness constant precedes an arbitrary requested final error tolerance. All subsequent reserve, repair, coloring, and order parameters precede the graph, embedded core, and initial exterior coloring. It constructs a first family of actual perfect matchings, retaining at least two fifths of the original regular degree in the exact residual graph. The residual has an actual embedded balanced bipartite robust core, arbitrarily small side-normalized degree error, and an actual coloring of the complement of that core. It also provides reconstruction from an explicit coloring of the whole residual graph.

The specialized list constraint is proved by finite permutation counting and greedy repair, using the proved Vizing theorem for the initial simple-graph coloring. For every fixed positive slack `δ`, the uniform theorem produces a proper coloring with `Δ+1+ceil(δn)` colors avoiding a sufficiently small forbidden set on each edge. Constrained alternating-component exchanges balance its classes while retaining the fixed exterior labels, and the proved reserve-repair theorem constructs their completions. This supplies the consequence needed in Lemma 4.2 without assuming Kahn's general list-coloring theorem; that general theorem is not claimed as formalized.

The new bounded-footprint reduction and reserved-color cleanup factor the actual residual for every bounded exterior permitted by Lemma 4.2. They construct a common exterior split, preserve a linear original-color reserve, complete the selected colors, and leave a genuinely bipartite whole remainder. [The full ordinary-factorization notes](docs/ordinary-factorization-full.md) explain that completed construction. General Theorem 6.1 remains a separate obligation.

### The coloring encoding and balanced reserve

[`Overfull/Dense/Encoding.lean`](Overfull/Dense/Encoding.lean) models the simple part by an injective map into the host edge copies. The prescribed coloring remains fixed on every complementary copy, including parallel edges. Its missing colors define the other two parts of the encoded tripartite graph. The proof establishes local balance, all stated deficit identities, and an exact equivalence between full coloring extensions and actual triangle decompositions.

[`Overfull/Dense/Reserve.lean`](Overfull/Dense/Reserve.lean) proves the six-pair reserve lemma from actual directed degrees and pair edge counts. The common vertex demands are derived from the graph, and the unequal-side flow theorem corrects the initial constant edge weights. The explicit choices are `c₁ = 12/(2c−1)` and `θ₀ = min(1/4, 1/(4c₁))`. The resulting probabilities lie strictly between zero and one on every edge and have equal incoming and outgoing sums at every vertex. This is the expected-balance conclusion; subsequent sampling and integral decomposition remain separate steps.

### Fractional triangle decomposition

[`Overfull/Dense/FractionalTriangles.lean`](Overfull/Dense/FractionalTriangles.lean) proves Lemma 5.7 from its graph hypotheses. The tripartite model has a corresponding simple graph, actual triangle coordinates, and an incidence map that sums triangle weights at each actual edge. The conclusion gives incidence exactly one and weights between `1/(2k)` and `3/(2k)`.

The proof first solves signed flows in the actual link graphs, then distributes the remaining weights on the first two parts across their triangles. It proves a contraction of the residual and sums the resulting correction series. The sufficient choice is `ε₀ = min(η, 1/(32(2+10/η)))`, depending only on `η`; it is quantified before every graph and part type. The empty-side case is included. No flow, correction, contraction, or convergence conclusion is assumed in the final theorem.

This verifies the fractional decomposition. The subsequent approximate integral packing and the full dense extension remain unproved.

### Integer balance repair

[`Overfull/Dense/BalanceRepair.lean`](Overfull/Dense/BalanceRepair.lean) proves full Lemma 5.11. From the prescribed tripartite sizes, pair densities, and actual cyclic degree imbalances, it constructs a deleted subgraph and a locally balanced residual. Their simple graphs satisfy the exact deletion identity, and the deleted graph has degree at most `5√ξn` at every vertex.

The constants are `c₀ = min(η,1)/1000`, `c₁ = 5`, and `ξ₀ = (c₀/100)²`; the order threshold is chosen after fixing `0 < ξ ≤ ξ₀`. [`Overfull/Dense/BalanceRepair/Routing.lean`](Overfull/Dense/BalanceRepair/Routing.lean) constructs the required paths in all nine ordered endpoint-part cases. [`Overfull/Dense/BalanceRepair/Cancellation.lean`](Overfull/Dense/BalanceRepair/Cancellation.lean) proves finite cancellation with bounded internal incidence. The graph identities and numerical estimates prove that every residual graph meets the routing hypotheses. The public theorem assumes no routing or balance-repair existence statement. This proves integer balance repair; the full dense extension remains unproved.

### Cycle absorbers and the finite absorber

[`Overfull/Dense/CycleAbsorber.lean`](Overfull/Dense/CycleAbsorber.lean) defines the listed absorber edges for every positive length `ℓ`. An injective placement in a host graph, together with the presence of those edges, gives both triangle decompositions, edge-disjointness from the cycle, exactly `9ℓ` absorber edges, and exactly `2ℓ+1` support vertices outside the cycle. Each absorber edge meets a vertex outside the cycle.

[`Overfull/Dense/FiniteAbsorber.lean`](Overfull/Dense/FiniteAbsorber.lean) proves the subsequent finite absorber lemma from the actual dense-host hypotheses. It enumerates every locally balanced remainder on `U`, proves its decomposition into simple directed cycles, and places separate gadgets with pairwise disjoint auxiliary vertices. The resulting single absorber has both its default decomposition and a decomposition after adjoining any allowed remainder. Its edges avoid `G[Z]`, and its support outside `U` avoids `Z`.

[`Overfull/Dense/FiniteAbsorberSubgraph.lean`](Overfull/Dense/FiniteAbsorberSubgraph.lean) returns a literal mathlib subgraph whose vertex set is exactly its support, with the same actual edges and decompositions.

The complete edge-plus-auxiliary-vertex budget is `4h²2^(h²)`. The order threshold depends only on `h`, `η`, and `γ`, and is chosen before the graph, `ε`, `U`, or `Z`. The condition involving `ε` is expressed as `16hε ≤ γ`, which also includes `h = 0`. This proves the bounded finite absorber; the approximate integral packing and iterative absorption needed for the full dense extension remain unproved.

## The sharpness conclusion

For every odd integer `Δ ≥ 3`, Lean proves the existence of a connected simple graph satisfying

```text
|V(G)| = 4Δ + 5
Δ(G) = Δ
χ′(G) = Δ + 1
|E(G)| = 2Δ(Δ + 1),
```

with no `Δ`-overfull vertex set. The class-2 conclusion consists of a proof that no `Δ`-coloring exists and an explicit proper `(Δ+1)`-coloring. The no-overfull statement quantifies over every vertex subset.

For every real `c < 1/4` and natural `N`, the development constructs such a graph of order `n ≥ N` with `Δ(G) ≥ c*n`. The ratio `Δ/(4Δ+5)` approaches `1/4` from below. Thus a coefficient below `1/4` cannot support the proposed general coloring conclusion. These examples leave the exact boundary `Δ ≥ n/4` open.

[`docs/sharpness.md`](docs/sharpness.md) explains the complete checked construction and its proof modules.

## Reproducing the verification

The project pins Lean to `leanprover/lean4:v4.24.0`, mathlib to commit `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`, and all transitive dependencies in `lake-manifest.json`.

With Lean's version manager, Python 3, Git, and the standard `patch` command installed, run from the project root:

```sh
python3 scripts/setup_vizing.py
lake exe cache get Mathlib.Combinatorics.SimpleGraph.Matching Mathlib.Combinatorics.SimpleGraph.Coloring Mathlib.Combinatorics.SimpleGraph.Tutte Mathlib.Tactic Mathlib.Data.Real.Archimedean Mathlib.Data.Nat.Choose.Basic Mathlib.Analysis.Convex.Combination Mathlib.Analysis.Normed.Operator.Banach Mathlib.Analysis.Normed.Module.FiniteDimension Mathlib.Combinatorics.Hall.Finite
python3 scripts/verify.py
```

The first command fetches and verifies the pinned Vizing source. It can instead use a pristine local copy with `--source /path/to/upstream`. Once the prepared source is present, it verifies the local files without downloading them. Do not run `lake update` to reproduce the recorded versions; the committed manifest already supplies them.

The verification script checks the source pins, performs a strict build with `lake build --wfail`, and audits the transitive axioms of the proved declarations. It also checks that every project module is imported and that every assertion marked complete has an audited proof declaration.

The only permitted logical axioms are

```text
propext
Classical.choice
Quot.sound
```

The audit rejects any added axiom, `sorryAx`, or the additional axiom used by `native_decide`. Generated and private support theorems are included. The declaration count is therefore not a count of independently proved manuscript results.

[`verification/results.json`](verification/results.json) records the exact proof-source hashes, imported modules, proof declarations, dependency revisions, and axioms. Build and audit logs are in the same directory. A failed check removes any previous success report. The GitHub Actions workflow is configured to run the same commands; a local success report does not claim a remote Actions run or GitHub publication.
