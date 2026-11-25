# Independent semantic review: native protected traces and two-pair external assembly

## Scope and review provenance

This continuation constructs the external matching family in the branch with
two exceptional matching pairs and at most five exceptional vertices. It
derives the protected joining traces, joining and parallel-copy bounds, the
weighted palette, the possible fifth vertex and its assigned-core star, and
the final external family from explicit native residual data. The remaining
safe-residual construction, completion inside the two cores, terminal
factorization, and other exceptional-pair branches remain separate obligations.

The baseline is commit
`f2510d10c114bcf3d0003b5e2e4e35cb0400167d`, tree
`58fe77f4afaba4b0ab6cf77956afb1c23608cd35`. Its audit contains 742 nonroot
mathematical modules, 14,994 proof declarations, 2,926 completed-result
mappings, and 23 declaration maps. The preservation gate requires every
previous nonroot mathematical source byte, declaration owner and axiom list,
result mapping, and declaration-map byte to remain unchanged; root imports and
verifier registrations must be exactly the registered additive edits.
All 69 numbered assertion records
retain their existing statuses: 51 complete, with no promotion of the main
theorem, Lemma 4.4, or Corollary 4.5.

The machine-readable review is
[`independent-review.json`](../verification/runs/20261125T121903Z/independent-review.json).
It records each final source hash, its primary author and a different
independent reviewer, the inspected claims and retained assumptions, and the
exact successful strict compiler receipt. Each receipt is checked against its
archived source bytes, output log, and recorder. The review covers the whole
new source inventory; a changed or unreviewed module blocks preflight.

Agent `/root/proof_target_review` inspected all modules authored by the root,
the boundary agent, and the star-assembly agent. The three modules authored
by that reviewer—`FourReservedPrimary`, `FourGrouping`, and `FourJoining`—were
independently inspected by `/root/pair_star_assembly`; the root also separately
reviewed `FourReservedPrimary`. The other agent's findings and genuine
compiler evidence are retained in
[`pair-star-independent-review.json`](../verification/runs/20261125T121903Z/pair-star-independent-review.json).
This semantic review is distinct from the full build and complete kernel
axiom audit, whose actual results are recorded by the frozen verifier run.

## Four-label protected pieces and palettes

### Prescribed actual crossings

[`FourReservedPrimary.lean`](../Overfull/ResidualPalette/FourReservedPrimary.lean)
generalizes the reserved-primary construction to at most four labels. It
does not merge the two pair fibers, identify parallel copies, or replace an
actual selected crossing with an abstract endpoint pair. For every prescribed
joining copy it removes that original copy together with one distinct virtual
parallel copy, applies the smaller construction, and restores the two-copy
circuit.

The induction preserves the actual cut inequalities. Closed cuts cross neither
member of a selected two-circuit, so their original cut is unchanged. A
separating cut loses one original copy while the virtual budget decreases by
one. The
original-incidence margin is unchanged when both the budget and selected-copy
count decrease by one. Compatibility and even degree are checked at every
step. The base uses the previously proved complete compatible-circuit theorem
for at most four labels.

The host-level endpoint derives its cut inequalities from regularity and the
absence of overfull vertex sets. Its conclusion gives a four-label two-odd
decomposition in which every prescribed original crossing is a singleton
primary piece. The explicit sufficient condition `D ≤ h - A.card` remains an
input. It is not a theorem constructing a reserve-safe residual.

[`FourProtectedPalette.lean`](../Overfull/ResidualPalette/FourProtectedPalette.lean)
then handles the two parity cases. In the all-even case it first groups on a
smaller palette and embeds those colors into the full palette with genuinely
empty reserved colors. In the two-odd case the prescribed singleton primaries
remain whole protected classes; distinct original copies imply distinct
protected colors. This unweighted construction retains its `8*D+t<h` margin
and returns `JoiningPalette` capacity `2*L`. It does not itself prove the
star-weight estimate needed for the fifth-vertex extension.

## Exact traces of the actual partner reserve

[`PartnerTraces.lean`](../Overfull/NativeReserve/PartnerTraces.lean) first proves
the no-unpaired specialization. Every selected exceptional copy lies inside
one of the actual pair fibers, and the boundary's joining trace is exactly
its parity-selected old-core crossing. The surviving-copy subtype and reserve
avoidance preserve this equality after deletion. Odd traces give an injective
family of actual singleton crossing copies indexed by the original reserve.

[`PartnerGeneralTraces.lean`](../Overfull/NativeReserve/PartnerGeneralTraces.lean)
removes the no-unpaired hypothesis from the trace statements. A selected
matching copy incident with an unpaired exception is internal to the core
fiber to which that exception is assigned. The proof establishes the common
core membership of its endpoints through the matched-cut information and
establishes pair membership through uniqueness in the original matching.
The full partner signature transports those facts to every reserved parent
matching.

Consequently, even with unpaired exceptions, the only possible joining copy
in a compressed boundary is the parity-selected core crossing. Its cardinality
is the parity of the **assigned** core `corePart G M Z U₀`, including assigned
exceptions. Substituting the parity of the old core alone would be wrong in
the fifth-vertex branch; these statements do not make that substitution.
The residual singleton injection preserves reserve indices and distinct
parallel copies, rather than merely remembering endpoint pairs.

[`TwoPairProtected.lean`](../Overfull/NativeAssembly/TwoPairProtected.lean)
constructs the unweighted palette, its protected-color injection, and complete
pair-only boundary preservation. Its pair-only completion retains the exact
pair-exhaustion hypothesis on `Z`.
[`TwoPairGeneralProtected.lean`](../Overfull/NativeAssembly/TwoPairGeneralProtected.lean)
constructs the palette and traces without that hypothesis. These are actual
constructions from the reserve, not interfaces assuming the desired trace
alignment as an additional certificate.

## Joining degree and parallel-copy estimates

[`TwoPairBounds.lean`](../Overfull/NativeAssembly/TwoPairBounds.lean) counts
exactly `r` reserved incidences at every exceptional vertex: each boundary is
a matching covering that vertex, and the boundaries are pairwise disjoint.
Reserve avoidance leaves all these copies present in the residual. In the
appropriate assigned fibers they are internal copies, so exceptional joining
degree is at most `h-r`.

The generalized version in `TwoPairGeneralProtected.lean` proves the same
estimate for paired and unpaired exceptions using their exact internal-label
property. Old-core vertices have joining degree at most `D` because their
retained embedded simple core has degree at least `h-D`. Together with
`h ≤ r+D`, this bounds the actual joining degree at every vertex by `D`.

[`TwoPairNative.lean`](../Overfull/NativeWeighted/TwoPairNative.lean) also derives
every exceptional-to-old-core parallel multiplicity bound from the same core
deficit. Those copies lie outside the embedded simple core, so they consume
part of the at-most-`D` residual incidence deficit at their old-core endpoint.
This uses actual multigraph copies; it does not assume the whole multigraph
is simple or suppress multiplicity.

These arguments require the supplied residual to be regular and to contain
the stated retained cores. They do not establish that a deletion family with
those properties exists.

## Weighted grouping with four-copy pieces

[`FourGrouping.lean`](../Overfull/WeightedPalette/FourGrouping.lean) extends the
existing weighted grouping proof to pieces of at most four actual copies.
A piece meets at most eight vertices, so its weight against a star resource
is at most `8*b` when each relevant parallel bundle has at most `b` copies.
The total resource weight is bounded by actual incidence double counting,
using the degree load `D` and the center's degree bound `h`.

The integer inequality

\[
  h < 16\bigl(\lfloor h/8\rfloor-8b+1\bigr)
\]

follows from `b ≤ D` and `128*D ≤ h`, with natural subtraction handled in the
proof. It bounds overloaded colors by `16*D` for each resource. At most two
resources contribute at most `32*D` forbidden colors, and endpoint conflicts
contribute at most `8*D`. Thus the construction uses the quantitative margin
`h-Q.card-40*D`.

The weight target is `h/8` for the full palette throughout. In particular,
the weighted all-even construction does not obtain a smaller-palette weight
bound and silently reuse it as a full-palette assertion. The generic grouping
preserves seed colors, exact protected seed unions, matchingness, original
copy disjointness and coverage, and the original per-vertex load.

[`FourJoining.lean`](../Overfull/NativeWeighted/FourJoining.lean) supplies the
seeds required by that generic construction. The all-even case has empty
seeds and any prescribed protected empty colors. The two-odd case puts one
primary in each color by an injection; a primary has at most three copies,
giving seed weight at most `6*b ≤ h/8`. Other pieces have even fiber cuts, so
the unique primary determines each class's exact odd-cut parity. Protected
primary colors receive no surplus pieces.

Piece cardinality is derived from the actual incidence budget
`|V|*D ≤ 2*L*(h-Q.card-40*D)`. The constructed copy and support bounds are
`4*L` and `8*L`, conservatively stored as `JoiningPalette` capacity `2*L`.
The directly proved whole-class star-weight bound remains `h/8`.

The native weighted endpoint in `TwoPairNative.lean` composes these results
with the actual reserve traces and retained-core estimates. It constructs
both parity branches, an injective protected-color map, and all requested
star weights for at most two exceptional centers. It assumes no supplied
weighted palette, protected trace certificate, or star-weight certificate.
Its retained numerical inputs include `h>0`, `128*D≤h`, `2*t≤h`, `L>0`, and
`|V|*D≤2*L*(h-t-40*D)`.

## Completing two pairs and the possible fifth vertex

[`TwoPairStarBase.lean`](../Overfull/NativeAssembly/TwoPairStarBase.lean) first
completes the two pair pools while retaining whole protected boundaries that
may contain an additional star copy. It restricts each boundary only for the
intermediate pair completion, then reunites it with the full protected
boundary. The resulting protected classes are exactly those full boundaries.
Cross-family disjointness uses pair saturation and matching uniqueness; it
is not inferred merely from within-family disjointness.

[`TwoPairStar.lean`](../Overfull/NativeAssembly/TwoPairStar.lean) proves the
remaining-star balance from actual incidence counts. The exact fiber identity
`labelShore label {label z} = insert z U` partitions the center's incident
copies into joining copies and copies in its assigned-core star. Regularity,
coverage by the protected boundaries, and pairwise disjointness then equate
the number of remaining star copies with the number of available colors.
This balance is derived, not assumed.

The pair additions are disjoint from the fifth center and its old core, so
they preserve the joining palette's available-color vertex loads and actual
star weights. The Hall extension then supplies exactly one star copy in each
remaining color. The generic endpoint still displays its fiber and weight
hypotheses; the native modules discharge them.

[`TwoPairStarReserve.lean`](../Overfull/NativeAssembly/TwoPairStarReserve.lean)
derives the pair injections, boundary matching/disjointness/cardinality, and
center coverage from `PartnerBoundaryPacking`. Its coverage theorem proves
that the joining copies, the two pair pools, and the one assigned-core star
are exactly the joining and exceptional copies in this geometry.

[`TwoPairOneStar.lean`](../Overfull/AssignedParts/TwoPairOneStar.lean) obtains that
geometry from the original perfect matching and `Z.card ≤ 5`. Two distinct
internal matching copies have four distinct exceptional endpoints. There is
therefore either no leftover vertex or one actual vertex. In the latter case
the proof derives its assignment to one of the two old cores, the exact insert
fiber, and the fact that the other assigned core is unchanged. Both assignment
alternatives are retained.

[`TwoPairExternal.lean`](../Overfull/NativeCore/TwoPairExternal.lean) composes the
zero-star and one-star alternatives. Its endpoint constructs `h` pairwise
copy-disjoint matchings whose union is exactly all joining and exceptional
copies. Every exceptional vertex is covered in every color. The selected
whole residual boundaries occur at an injective family of colors with their
original reserve indices. Each class has at most `6*L+3` copies and at most
`12*L+6` support vertices.

[`TwoPairParity.lean`](../Overfull/NativeCore/TwoPairParity.lean) transfers the
actual four-fiber cut parity to even uncovered sets in each original core,
using complete saturation of `Z`. The final external endpoint also derives
disjointness from both embedded old cores and at most `D` external class
incidences at every old-core vertex. These are the estimates needed by later
core-completion machinery. The external matchings themselves are not asserted
to be perfect matchings of the whole residual.

## Remaining obligations and verification boundary

The new native endpoint retains the original disjoint old-core/exceptional
partition, an original perfect matching with exactly two internal exceptional
copies, and an actual `PartnerBoundaryPacking`. It additionally requires an
actual reserve-avoiding residual that is regular and non-overfull, retained
core degree at least `h-D`, enough surviving reserve incidences
(`h≤r+D`), and the explicit grouping and star budgets described above.

The following work is not established by this continuation:

1. Construct that regular, non-overfull, reserve-avoiding residual and retained
   cores with the required numerical parameters from the original theorem's
   hypotheses.
2. Complete the constructed external classes to perfect matchings inside the
   two robust cores, then establish the terminal geometry, factor the remainder,
   and reassemble the original copies in the full theorem.
3. Complete the zero-pair and one-pair branches, which can have respectively
   five and three unpaired exceptional vertices.
4. Close any additional pinned numbered assertion or the main theorem.

No mathematical semantic defect, hidden conclusion-as-assumption, weakening
of a preserved baseline theorem, or loss of original-copy identity was found
in the reviewed additions. The machine-readable review binds that assessment
to exact source hashes. Strict focused checks support those hashes; the full
frozen build, exhaustive declaration/axiom audit, and baseline-preservation
checks provide their own separate execution evidence. Genuine failed focused
attempts remain in the run history alongside the corrected successful checks.
