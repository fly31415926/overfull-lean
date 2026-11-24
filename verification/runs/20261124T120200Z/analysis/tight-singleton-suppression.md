# Arbitrary-degree tight-singleton reduction: mathematical construction

This is a proof plan, not a Lean-verified theorem or a new completed assertion.
The current Lean implementation specializes suppression to a vertex of degree
two. The argument below identifies a wider arbitrary-degree branch without
assuming a compatible partition of the original graph.

Let `Q` be a finite loopless multigraph on at most four labels with selected
actual copies `C`, even degrees, and the original class-cut admissibility.
Suppose `u != w` and a class `p` at `w` is tight on the singleton cut at `u`.
Write `A` for the selected `u-w` copies with class `p` at `w`, and write `B`
for all other copies incident with `u`. Then `|A|=|B|=r`.

## Pairing the actual copies

Pair `A` bijectively with `B`, forbidding a pair whose members have the same
original class at `u`. This bipartite graph satisfies Hall. A subset of `A`
meeting two different `u`-classes has all of `B` as its neighborhood. A subset
inside one class `q` has neighborhood `B` outside `q`; the original local
half-degree inequality gives
`|A_q|+|B_q| <= r`, hence `|A_q| <= |B \ B_q|`.

Every pair is thus a compatible two-edge path at `u`. If its `B` edge also
ends at `w`, it is a compatible two-edge circuit: its `w`-class differs from
`p` by the definition of `B`. Save these circuits and remove their copies.
For each remaining pair, with `B` endpoint `z != w`, replace its two original
copies by one distinct virtual `w-z` copy. Its class at `w` is `p`; its class
at `z` is inherited from the `B` copy. Retain all copies not incident with
`u`, and remove `u` from the vertex type. No virtual copy collapses another.

## Exact admissibility calculation

Fix a shore `X` of the remaining labels and take its complement if needed so
that `w` is outside `X`. Let `d` be the number of retained old crossing copies,
and let `b` be the number of `B` copies whose other endpoint lies in `X`.
The new crossing count is exactly `d+b`.

For every original class except `(w,p)`, testing the old shore `X` with `u`
outside gives the same class count and the same total crossing count as the
new graph. In particular, a `B` copy into `X` simply becomes its paired
virtual copy and retains its class at its endpoint in `X`. The paired circuits
whose other endpoint is `w` do not cross this shore.

For `(w,p)`, let `c` be the number of retained crossing copies of that class.
The new class count is `c+b`. In the old shore `X union {u}`, all `r` copies
of `A` cross, while precisely `r-b` copies of `B` cross. Its total crossing
count is `d+2r-b`, and its `(w,p)` class count is `c+r`. Old admissibility
therefore yields `2(c+r) <= d+2r-b`, equivalently
`2(c+b) <= d+b`, exactly the new inequality. This computation is independent
of the chosen Hall pairing.

All remaining-label degrees stay even. At labels other than `w`, the degree
is unchanged. At `w`, each saved two-edge circuit lowers its degree by two;
all other paired paths preserve its degree. Thus the already verified
at-most-three-label theorem supplies a compatible circuit partition of the
new graph.

## Lifting and exact original-copy coverage

All virtual copies are incident with `w` in the same class `p`. Compatibility
therefore allows at most one virtual copy in each new circuit. Replacing that
copy by its paired original two-edge path introduces `u` exactly once. The
lifted circuit is compatible at `u` by the Hall pairing, at `w` by the copied
class `p`, and at its other endpoint by the inherited class. Original old
incidences are unchanged. Circuits without virtual copies are unchanged.

The paired original paths are disjoint and partition the incidences at `u`;
the saved two-edge circuits use precisely the pairs with second endpoint `w`.
Consequently the lifted partition, together with those saved circuits, covers
every selected original copy exactly once.

## Remaining scope

This establishes a sound reduction for any positive even degree at a label
with a tight nonlocal singleton class. Formalization still requires the Hall
pairing, replacement graph, class/cut identities, and partition lift. It does
not settle inputs with no tight nonlocal singleton constraint, or general
tight two-versus-two cuts. No general four-label existence theorem follows
from the degree-two implementation alone.
