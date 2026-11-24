# General tight nonlocal shore reduction: proof plan

This document records mathematical reasoning for a future Lean construction.
It is not an executed Lean proof and does not change numbered coverage.

Let a selected Eulerian loopless multigraph on at most four labels satisfy
all original class-cut inequalities. Fix a class `p` at a label `w` and a
nonempty shore `X` not containing `w`, with `|X| <= 2`, on which that class is
tight. Set `A = classCut(C,w,p,X)` and `B = cut(C,X) \ A`.
Then `|A|=|B|=r`; every edge of `A` has outside endpoint `w`.

## First graph: find the actual paths through X

Collapse all labels outside `X` to one apex. Retain every internal edge of
`X` and every crossing copy, with its individual identity. Discard all edges
whose two endpoints are outside `X`. At interior labels retain the original
classes; at the apex use just two classes, `A` and `B`.

The graph has at most three vertices. Interior degrees are unchanged and
the apex has degree `2r`, so it is Eulerian. To verify admissibility, it
suffices by cut complementation to test a shore `Y subset X`.

Write `Z=X\Y`, let `s` be the number of original edges between `Y` and `Z`,
and let `A_Y,B_Y,A_Z,B_Z` count the corresponding boundary copies.
The new cut at `Y` has exactly the original cut size `s+A_Y+B_Y`. Every
class at an interior label has its original class-cut count. The apex
class `A` has count `A_Y`, so its bound is the original `(w,p,Y)` inequality.
For the other apex class, the original `(w,p,Z)` inequality says
`2 A_Z <= s+A_Z+B_Z`. Since `A_Y+A_Z=B_Y+B_Z`, this is equivalent to
`2 B_Y <= s+A_Y+B_Y`. Thus the first graph is admissible.

Apply the already proved at-most-three-label compatible-circuit theorem.
A circuit through the apex uses exactly one `A` copy and one `B` copy.
Removing the apex from such a circuit gives an actual path through `X`
with those two boundary copies. Its interior labels are distinct, and all
incidences at those labels remain compatible. Parts avoiding the apex are
already original compatible circuits inside `X`.

## Second graph: suppress these paths

For each path whose `B` copy has outside endpoint `z != w`, introduce a
distinct virtual copy `w-z`. Give it class `p` at `w` and its original
`B`-copy class at `z`. If instead the `B` outside endpoint is `w`, the path
already gives an original circuit through `w`: the `B`-copy class at `w`
differs from `p` because that copy belongs to `B`. Save these circuits.
Retain all original copies with both endpoints outside `X`.

The second graph has at most three labels. Every degree except that of
`w` is unchanged. The degree at `w` drops by twice the number of saved
paths closing at `w`; hence all degrees are even.

To verify admissibility, test a shore `T` of the remaining labels with
`w` outside. Let `d` count retained old copies crossing `T`, and let `b`
count original `B` copies whose outside endpoint belongs to `T`.
The new cut size is `d+b`. For every class other than `(w,p)`, the class
count and total cut count are the same as in the original shore `T`,
where every label of `X` lies outside. This includes original classes at
endpoints of virtual copies, because their `B` classes were inherited.

Let `c` count the retained crossing copies in class `(w,p)`. Its new count
is `c+b`. The original shore `T union X` has cut size `d+2r-b` and class
count `c+r`. Its inequality gives
`2(c+r) <= d+2r-b`, exactly equivalent to `2(c+b) <= d+b`.
Thus the second graph is admissible too.

Apply the at-most-three-label theorem again. All virtual copies share
class `p` at `w`, so each compatible circuit contains at most one of them.
Replace that copy by its original path through `X`. This introduces each
interior label of that path once, while every other label of the circuit
is outside `X`. Compatibility is retained at the real boundary endpoints
and every interior label. Append the saved circuits through `w` and the
first graph's internal circuits.

Both decompositions are partitions of actual copies. Their path pieces
partition `A union B`; the remaining pieces partition the internal and
external old copies separately. Consequently the final lifted parts
partition every original selected copy, without identifying parallel
copies or leaving auxiliary copies in the conclusion.

## Consequence for the unresolved four-label case

Once formalized, this reduction will settle every input with a tight
nonlocal singleton cut or a tight two-versus-two cut. After excluding
those cases, all tight inequalities are local singleton inequalities.
Every other nonzero slack is even and at least two. A compatible pair
or triangle meeting all local tight classes is then safely removable.
Four-circuit deletion still needs the exact slack-two check on the
opposite-pair shore. This last selector is not proved here.

## Global validity of local tight-class coarsening

There is a useful companion identity. Suppose an original class `P` at
`v` is locally tight, `|P|=d(v)/2`. Merge all other classes at `v` into
one complementary class. This preserves every class-cut inequality,
not just the local degree inequality.

For a shore `X` excluding `v`, put `Y=V\(X union {v})`. Let `c` count
edges from `v` to `X`, and `q` count edges between `X` and `Y`.
Write `P_X,P_Y` for the two portions of `P`; then
`P_X+P_Y=d(v)/2`. The complementary class across `X` has size
`c-P_X=c-d(v)/2+P_Y`. The original inequality across `Y` gives
`2 P_Y <= d(v)-c+q`; substitution gives
`2(c-P_X) <= c+q`, the required new bound across `X`.

If both `X` and `Y` are nonempty, strictness of the old nonlocal bound
across `Y` yields strictness of the new bound across `X`. Original
classes that are left unchanged retain all bounds. Thus the existing
local coarsening construction can be upgraded to preserve global
admissibility and the absence of tight nonlocal constraints.
