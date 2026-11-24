# Semantic review: complete four-label compatible-circuit theorem

## Statement fidelity

The main endpoint accepts an arbitrary loopless four-label multigraph,
arbitrary incidence classes, and a finite selected copy set. Its only
mathematical assumptions are even selected degrees and the original global
half-cut inequalities. The arbitrary-label wrapper assumes only that the
finite vertex type has cardinality at most four. Parallel copies remain
distinct throughout; the ambient edge type need not be finite.

The exact endpoint does not assume a compatible partition, safe selection,
regularity, connectedness, a bounded degree, a bounded bundle, strict
nonlocal inequalities or a fixed low-degree label. Intermediate structures
are constructed before they are consumed by the final theorem.

## Strict branch

Strict nonlocal inequalities apply precisely when both shores contain a
vertex different from the tested class vertex. This definition includes
zero-cut shores; the alternative branch explicitly handles tight zero cuts.
A nonempty selected copy set provides a class value for the nonempty-class
instance used by local coarsening.

Tight local coarsening preserves weak global admissibility and strict
nonlocal inequalities. The complement-class calculation uses the original
class on the toggled shore; the toggle preserves nonlocality. A compatible
coarse pair at a vertex meets every original tight local class.

Absence of a compatible parallel pair makes every nonempty bundle
monochromatic at one endpoint. The support-degree arguments and kernel
finite classification reduce to square, diamond or complete support.
The square with no pair contradicts a strict neighboring singleton bound.
The diamond and complete cases are excluded by the original local and
nonlocal class counts. All bundle counts are unrestricted natural numbers.
Consequently a genuine compatible pair or triangle is constructed.

The safe-deletion theorem uses the exact existing short-circuit criterion.
Strict nonlocal cuts cannot be tight; every remaining crossed tight cut
isolates the tested class vertex. Coarse compatibility meets its tight
class. Deletion therefore preserves original admissibility and even
degrees. Strictness is deliberately not asserted for the residual. The
strong induction may return to either branch.

## Tight branch

Complementation normalizes a tight nonlocal shore to a nonempty set of
one or two labels avoiding its class vertex. The original class counts,
not a weaker local surrogate, are retained.

The inside graph collapses only the exterior. Each interior label remains
distinct, and every original copy touching the shore survives. Incidences
are tagged with the original endpoint and class. The designated tight
class at the apex is then coarsened against its complement. The proved
three-label theorem supplies the inside partition. Its original-copy
pieces are compatible at all original vertices, even at interior vertices,
and have zero boundary or one designated-class copy and one complementary
copy.

The outside graph contracts the entire shore into the designated outside
vertex. Every surviving copy retains its own identity. The special class
bound is derived from the original cut of a disjoint test shore united
with the tight shore. The exact cut identity counts copies between the
two shores twice. Other class bounds are inherited. Parity follows from
fiber cut parity. The outside support has at most three vertices, so its
partition is also constructed by the existing three-label theorem.

Restoration selects the unique inside piece containing each surviving
redirected copy, while exterior copies select their original singletons.
The common anchor class prevents two distinct shore pieces from appearing
in one compatible outside part. Exact exterior degree and class identities,
internal evenness, and original piece compatibility prove that each
expanded part is compatible and even. Ordinary four-label decomposition
then produces genuine connected circuits; no unproved path-connectivity
claim is used.

Pieces with no surviving outside copy are saved. All their exterior
incidences are at the anchor, whose degree is zero or two. They too are
compatible and even and receive ordinary circuit partitions. These saved
pieces are disjoint from all selected blocks. Their union with the blocks
covers the entire original copy set, including anchor-returning copies
that become loops and are removed by the outside contraction.

## Applications and limits

The new joining wrappers invoke the unrestricted theorem on the actual
quotient and then the previously verified injective original-copy lifts.
The even-fiber and two-odd-fiber wrappers retain all regular-host and
no-overfull assumptions. The even-degree wrapper additionally retains the
per-vertex half-joining-degree bound. Primary/surplus counts, nonemptiness,
matching conditions, footprints and exact cover are the existing complete
decomposition structures, not weakened replacements.

These results finish the circuit stage for the remaining parity branches.
They do not supply the subsequent four-core robust packing, palette
construction, residual factorization or uniform full Proposition 4.16.
The 69 assertion identities and 49 complete numbered assertions therefore
remain unchanged. The main theorem remains unverified.

Independent reviews and genuine command receipts in the current run give
the executed status. The final frozen verifier checks all sources and the
transitive axiom dependencies rather than trusting this semantic review.
