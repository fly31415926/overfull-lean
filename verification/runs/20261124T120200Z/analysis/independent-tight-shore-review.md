# UNVERIFIED research review: tight shores and the four-label selector

Reviewer: `/root/four_degree_two`.

This is an independent mathematical reading of proposed future constructions.
It is not a Lean proof, a kernel certificate, a full source audit, or a claim
that the general four-label theorem is proved. No Lean source, frozen input,
verification control, existing review or index was changed. The only new
artifact from this review is this research note.

Reviewed notes:

- `tight-shore-suppression.md`, SHA-256
  `feebb006e51727c6449b1e8eeee85a0c5e1800c3c0a223456e414ad503496971`.
- `four-label-selector-route.md`, SHA-256
  `640681b9011315b41d8226d876d2c7194f4af31db67d073b4b0fcedd8a22d6ab`.

## Assessment

I found no counterexample or missing mathematical hypothesis in the tight-shore
construction as stated. The two graph constructions, both sets of half-cut
identities, and the proposed exact lift are consistent. The support-case
argument also appears sound under its stated no-pair, no-triangle and strict
positive nonlocal-cut hypotheses. These findings concern the paper argument;
the actual finite constructions and their formal interfaces still have to be
implemented and checked.

## First contraction and its classes

The first auxiliary graph must use only selected copies internal to `X` or
crossing its boundary. Keeping copies with both ends outside `X` and mapping
both ends to the apex would create loops. The note correctly discards these
copies from this first graph; they are retained separately for the second.

For `Y subset X`, its cut contains exactly the original selected copies in
the original cut at `Y`. Interior incidence classes are unchanged. The apex
class `A` has count `A_Y`, inherited from the original class `(w,p)`. For the
other apex class, tightness on `X` gives
`A_Y + A_Z = B_Y + B_Z`; the original bound on `Z = X \ Y` gives
`A_Z - B_Z <= s`, hence `B_Y - A_Y <= s`. This is precisely its required
half-cut inequality. The cases `Y=empty` and `Z=empty` are included in the
same equalities.

A clean total class map uses a tagged sum: original class values for
interior labels, and two new tags for the apex classes `A,B`. This requires
no inhabitant of the original class type. Values on nonincident pairs can
be assigned by the same total map without affecting compatibility.

The at-most-three-label theorem produces actual finite parts. A part through
the apex has exactly two apex incidences; compatibility with its two coarse
classes forces one `A` copy and one `B` copy. Such a part yields a path using
one or two distinct labels of `X`. Different paths need only be edge-disjoint;
their interior vertex sets need not be disjoint. Shared interior vertices
across different final circuits cause no difficulty.

## Second graph and saved returns to w

The virtual-copy type should be indexed by first-part identities whose `B`
outside endpoint differs from `w`. This keeps distinct paths distinct even
when they have the same outside endpoint. Original outside copies and these
virtual copies should be in separate summands of the edge type.

A path returning to `w` is saved as an original circuit. Its `B` incidence
at `w` cannot have class `p`: such a boundary copy would belong to `A`,
contrary to its membership in `B`. Thus the saved circuit is compatible at
`w`, in addition to the interior compatibility supplied by the first graph.

Every outside degree except `w`'s is unchanged. At `w`, each saved returning
path removes exactly two incidences; the other paths replace one original
`A` incidence by one virtual incidence. The asserted drop by twice the
number of saved returns is therefore correct.

For a shore `T` of outside vertices excluding `w`, the original cut at `T`
has `d+b` copies, exactly as the second graph does. For classes other than
`(w,p)`, inherited endpoint classes give the same count, with actual copies
related by the appropriate identity or virtual-copy correspondence.

For `(w,p)`, the new class count is `c+b`. The original cut at `T union X`
has total `d+2r-b` and class count `c+r`. Its inequality gives
`2c <= d-b`, equivalently `2(c+b) <= d+b`. A saved returning path has `B`
outside endpoint `w`, which is not in `T`, so it does not contribute to
`b`. The count remains valid when such saved paths occur.

The second graph can use the original class type: the already specified
`p` is available for irrelevant default values, and each virtual incidence
at its other endpoint inherits the actual original `B` class.

## Empty boundary and exact lift

The case `r=0` does not need exclusion. Both `A` and `B` are empty, and the
first apex is isolated. No first part can use it. All first parts are
internal original circuits. The second graph consists solely of the old
outside copies, and all displayed degree and cut formulas remain valid.
This also covers disconnected input separated by `X`.

Every virtual copy in the second graph is incident with `w` in class `p`.
Therefore a compatible second part contains at most one virtual copy.
Replacing that copy by its first-part path introduces only vertices of `X`,
whereas all other vertices of the second circuit are outside `X`. The
replacement consequently has no repeated interior label. Compatibility at
`w` and at the other boundary endpoint follows from the two inherited
virtual classes; interior compatibility comes from the first part.

With `|X|<=2`, the first graph and the outside graph each have at most three
labels. A first apex part is a parallel pair or triangle. Its restored
piece is respectively a two-edge or three-edge path, or a saved two-edge
or three-edge circuit when both outside ends are `w`. Lifting a second
part gives an original circuit of at most four copies. Thus the proposed
lift avoids the known failure of arbitrary partwise splitting: each second
part expands at most one path through the deleted shore.

Exact coverage must still be formalized. First parts partition all internal
and boundary copies; nonreturning path IDs each occur once in the second
partition; old outside copies occur once there; saved returning parts and
first internal parts are then appended. These categories are disjoint in
actual copies. No assumption of vertex-disjoint paths or of a bijection
between endpoint pairs and paths is justified or needed.

## Strictness transfer can avoid a connectedness prerequisite

For a locally tight class `P` at `v`, the complementary-class slack across
`X` equals the original `P`-class slack across
`Y = V \ (X union {v})`. Here `X,Y` should both be nonempty when applying
the statement to nonlocal constraints.

There is a useful way to handle a potentially zero cut at `Y` without first
proving connected support. Suppose the original cut at `X` is positive and
all original positive nonlocal constraints are strict. If the cut at `Y`
were empty, every incidence of `v` would go to `X`, and there would be no
edge from `X` to `Y`. Local tightness would then imply
`2|P intersect cut(X)| = d(v) = |cut(X)|`, an original positive nonlocal
tight constraint. This is a contradiction. Hence the cut at `Y` is positive,
and the complementary-slack identity transfers its strictness. This is an
additional proof detail to encode, not a new hypothesis on the input.

## Remaining selector argument

The subsequent support classification is consistent with the hypotheses:

- A support-degree-one vertex contradicts a local or nonlocal half-cut
  inequality, depending on the monochromatic endpoint of its only bundle.
- At support degree two, strictness at the singleton cut excludes a larger
  bundle being monochromatic at the opposite endpoint. The local bound then
  forces equal bundle sizes. Both bundles are constant in different classes
  at the degree-two support vertex.
- Four active labels and minimum support degree two leave exactly `C4`,
  `K4-e`, and `K4`. A disconnected support would have a two-vertex component
  and a support-degree-one vertex.
- In the diamond, the two degree-three vertices must block different
  triangles, giving `z+x<=y` and `z+y<=x`, impossible for `z>0`.
- In `K4`, a vertex cannot block two triangles. The blocker assignment is
  therefore bijective, and its omitted-neighbor map is a derangement. A
  four-cycle derangement contradicts positivity of the two diagonals after
  summing local bounds. Two transpositions force the displayed positive
  two-versus-two cut to be tight, contradicting strictness.
- In the remaining `C4`, equality of bundle sizes and distinct constant
  corner classes give the stated partition by four chosen bijections.

For a selected compatible pair or triangle, every crossed cut loses exactly
two copies. A positive nonlocal slack is even and at least two, while local
tight classes are met by the selected coarse-compatible incidence pair.
Thus the proposed exact-deletion induction is compatible with the previously
proved correction criterion. Its graph-level selectors, strictness transfer,
support classification, uniform-cycle construction and induction composition
remain separate formal obligations.

No promotion of the general four-label theorem or a numbered manuscript
assertion follows from this research review.
