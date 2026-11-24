# Complete bounded-input Corollary 4.6: semantic review

## Source statement and scope

The public theorem `Overfull.bounded_input_one_factorization` proves both
alternatives in the pinned source statement 4.6. The exact 443-byte statement
in the authorized source excerpt was independently rehashed during this run;
its SHA-256 remains
`86700ed56e6cd9be513339e7c06b5af19d1d8cbe074fed3985ef21e5c9ad6e26`.
The excerpt is retained in
`verification/runs/20261122T235931Z/authorized-manuscript-recovery.md`.

The source requires a sufficiently large even-order regular multigraph with
no overfull set, fixed positive linear lower bounds on degree and core orders,
sufficiently small ordinary robust range, and sufficiently small core error.
Its alternatives are one robust core with at most three exterior vertices,
or two disjoint robust cores with at most two other vertices. The conclusion
is an exact partition of every original edge copy into perfect matchings.
The new combined theorem has exactly these alternatives and conclusion.

The theorem uses independent fixed densities `α,β`, normalizes with
`γ=min α (min β 1)`, and specifies `τ≤γ/16` as the sufficiently small
range. One positive error tolerance and order threshold are selected before
all host types, graphs, cores, degrees and deficits. The source convention
`a+1≤εn` accommodates zero deficit and a positive reserve tolerance.
The statement hash, labels and source identities are not weakened or replaced
by a supporting assertion. This completes one new numbered assertion: 48/69.
The main theorem and 20 other assertions remain incomplete.

## Construction rather than a supplied factorization

`two_core_two_exception_factorization` starts from the original regular,
non-overfull graph and its embedded cores. It assumes no representative,
reserve, boundary palette, complementary coloring or residual factorization.
The native reserve theorem constructs the representative, the actual disjoint
boundary reserve, the first perfect-matching prefix, and the regular
non-overfull residual retaining both robust cores.

The chosen uniform reserve interface fixes its surviving expansion parameter
before the requested final surplus tolerance. This avoids a quantifier cycle:
the later prefix and terminal error tolerances depend on that parameter.
The proof uses
`exists_uniform_native_reserve_completion_with_small_joining`, not the older
interface that returns expansion only after the tolerance has been chosen.

`exists_uniform_native_remaining_factorization` constructs the external
palette, completes every nonprotected color in the old cores, factors the
actual protected residual, and restores that prefix. The original-host
theorem then restores the first prefix. `Reassembly.lean` proves exact
prefix and residual color-class identities on original copies. The previously
proved one-core factorization supplies the other branch. Thus neither branch
of the combined public statement has an unproved target-coloring input.

## Actual residual geometry

`PrefixGeometry.lean` constructs an injective endpoint-preserving map from
the twice-residual edge subtype to the original edge type. The last image
identity returned by the previous native prefix yields precisely the
selected reserve union as the image of all external residual copies.
The reverse direction uses the first-prefix avoidance and the second-prefix
remainder equality, so every selected original copy is shown to survive both
deletions. It is not simply assumed to survive.

The common native signature preserves each compressed boundary's assigned
parts. At an assigned exception, its unique retained incidence enters its
assigned old core. The optional exceptional pair is a separate part with at
most two vertices. Each boundary has exactly the assigned-shore parity number
of crossings, zero or one. Selected boundaries are pairwise copy-disjoint,
so their cut cardinalities add. The residual assigned-shore cuts are empty
when even and have exactly the residual degree when odd. The two cuts are
the same actual copy set, a stronger fact than equal cardinality.

Both assigned shore parities follow from the original perfect matching and
its cut identities. The smaller old core is permitted either parity. All
assigned exterior vertices are independent, and all shore crossings have
their shore endpoints in the old core. The optional exceptional pair is closed.
These properties are derived from the actual residual image in
`NativeGeometry.lean`, rather than reassumed in the concrete theorem.

## Shore models and gluing

For an even shore, `inducedHost` restricts the vertex type to the actual
shore and keeps its original internal copies. Empty cut proves that all its
incidences and degrees are preserved. Its old core is embedded as its actual
image vertex subset, preserving the simple graph, degrees and expansion.

For an odd shore, the outside is contracted to one apex while retaining every
original incident copy. Exact cut size gives the apex the regular degree,
and the shore vertices retain their degrees. The order is even. The new
core transport handles an old core properly contained in its assigned shore;
it does not accidentally apply the existing whole-shore-core embedding.
The exterior is independent: assigned exceptions meet their core only,
and no crossing can connect an assigned exception to the apex.

The independent-exterior one-core theorem constructs these shore colorings.
In the odd case, the same bijection from the common crossing-copy set to
the palette supplies both prescribed boundary labelings. The existing
singleton-boundary theorem restores these labels by a palette permutation.
`ColoringGlue.lean` proves properness at each original incidence vertex
by taking a shore that contains it and using overlap agreement on actual
copies. Closed pair copies cannot overlap another disjoint shore.
`PairColoring.lean` assigns distinct labels to every parallel copy in the
optional closed component, using its actual degree bound, and covers the
empty case.

The resulting ordinary factorization may recolor selected reserve stars.
Only the common singleton crossing labels are restored. No theorem here
claims that all originally protected whole boundaries keep their old colors;
Corollary 4.6 does not require that stronger assertion.

## Quantitative composition

The outer reserve uses range `α/960`, below its own `α/300` requirement
and the subsequent prefix's `α/240` requirement. The terminal range
`α/3840` is fixed before the host. The prefix's retained expansion is
reduced to its minimum with this range. Terminal density is `α/120`.

The degree is the natural quotient `r/2`, including odd reserve sizes.
The proved bounds `r≥αn/30` and `n≥120/α` yield
`(α/120)|U|≤r/2` for either old core. The range satisfies
`α/3840≤min(α/120,1)/16` under `α≤1`; the combined wrapper ensures this
normalization via `γ`.

Shrinking the host tolerance below `ε_terminal*β` gives both old-core
error bounds. Explicit ceiling thresholds give the requisite core orders.
Every constant precedes all graph data. Actual regularity and a nonempty
embedded core imply `a≥0`; using `a+1` supplies strict reserve positivity
without excluding the zero-deficit case.

## Independent checks and verification boundary

The complete new dependency chain passed the strict focused command
`lake build --wfail Overfull.NativeTerminal.BoundedInput`, with genuine
exit zero and unchanged inputs. Independent reviews are retained under
the current run's `independent-review/` directory. They cover source
strength, quantifier order, actual copy survival, graph transport, gluing
and both parity cases. The complete project verifier and unchanged full
axiom audit remain the authority for global counts and checkpoint status.

Every genuine failed and successful development attempt is preserved. The
source manifest enumerates public proofs; the full audit also enumerates
private/generated declarations and binds them to exact source hashes.
The preservation checker permits only the reviewed 4.6 promotion and its
appended component, preserves all 69 source statement identities, all 68
other assertion records, every old source, declaration owner/axiom set and
completed-result mapping, and retains every historical verification record.

The full verifier replaces the old 4.6 incompleteness guard with an explicit
positive statement-hash and theorem-name gate. It retains all other
incompleteness guards. Only `propext`, `Classical.choice` and `Quot.sound`
are permitted logical axioms.

The broader fixed-pattern Lemma 4.4, five-exception Corollary 4.5, general
four-label compatible-circuit result, terminal Proposition 4.16, remaining
dense and bipartite factorizations, critical average-degree input and main
theorem remain outside this completed assertion.
