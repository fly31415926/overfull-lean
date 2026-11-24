# Four-label compatible-circuit theorem: complete proposed proof route

Status: mathematical argument, not yet a complete Lean formalization. The
degree-two and cut-accounting implementations do not by themselves certify
this whole argument. This note records the construction and isolates its
remaining implementation obligations.

All graphs below retain actual finite edge copies. A bundle `uv` consists of
all copies with endpoints `u,v`; its size is denoted `m_uv`. Compatibility
means two used incidences at a label have distinct class values.

## Reduction and induction framework

Induct on the number of selected copies. An empty set has the empty partition.
If some label has degree zero, use the established at-most-three-label theorem.
If a class at `w` is tight on a shore of size one or two excluding `w`, use
the two successive at-most-three-label constructions in
`tight-shore-suppression.md`; they partition the whole original graph.

It remains to consider a selected graph with all four labels active and no
tight nonlocal constraint: every positive cut at a singleton other than the
class vertex, or at a two-versus-two shore, has strictly positive class slack.
Every such slack is even, because all graph degrees are even.

At each label apply the existing local coarsening. If no class is locally
tight, retain the original classes. Otherwise retain one locally tight class
and merge its complement into one other class. The last section of
`tight-shore-suppression.md` proves that this coarsening preserves global
admissibility. When both shores away from the tested class vertex are nonempty,
it transfers strict nonlocal inequalities to strict inequalities as well.
The cases below in fact force connected support, so their nontrivial cuts
are positive. Alternatively, disconnected support is handled componentwise.

Distinct coarse classes imply distinct original classes. The existing local
coarsening theorem also says that a coarse-compatible pair of incidences
meets every original locally tight class.

If there is a coarse-compatible two-copy parallel circuit or a compatible
triangle, delete it. Every cut meets such a circuit in zero or two copies.
The local tight constraints are met, and every nonlocal slack is at least
two. The exact deletion identity therefore preserves all original class-cut
inequalities. Degrees remain even and the copy count drops. Induction gives
the residual partition, and reinserting the selected circuit gives the
original partition.

The remaining task is therefore to classify an admissible coarsened graph
with no compatible parallel pair and no compatible triangle.

## Lemma 1: each bundle is monochromatic at one endpoint

On a nonempty bundle `uv`, regard the two endpoint class maps as two
coordinates of every actual copy. If each coordinate is nonconstant, the
existing two-coordinate selector gives two copies on which both coordinates
differ. These form a compatible parallel pair. Thus, in its absence, one of
the two endpoint class maps is constant on the entire bundle.

Choose one such monochromatic endpoint for each nonempty bundle. This choice
does not replace or identify any copies; it is used only in the argument.

## Lemma 2: a triangle without a compatible triple has a blocked corner

Assume the three bundles `ab,ac,bc` are nonempty and each is monochromatic at
at least one endpoint. If no compatible choice of one copy from each bundle
exists, some vertex has the same constant class on both its triangle bundles.
Call that vertex a blocker of this triangle.

Orient each of the three bundles toward a chosen monochromatic endpoint.
Up to relabeling there are two orientation types.

**Cyclic type.** Suppose `ab` is constant at `a`, `bc` at `b`, and `ac` at `c`.
To avoid a blocker at `a`, choose an `ac` copy whose class at `a` differs from
the fixed `ab` class. To avoid a blocker at `b`, choose an `ab` copy whose
class at `b` differs from the fixed `bc` class. To avoid a blocker at `c`,
choose a `bc` copy whose class at `c` differs from the fixed `ac` class.
These three choices are independent. Their constant-endpoint values do not
change, so they give the required compatible triangle.

**Transitive type.** Suppose `ab` and `ac` are constant at `a`, and `bc` is
constant at `b`. If the two fixed values at `a` agree, `a` is a blocker.
Otherwise compatibility at `a` is automatic. If every `ab` copy has at `b`
the fixed `bc` value, `b` is a blocker. Otherwise choose an `ab` copy avoiding
that value. Finally, if some `ac` copy and some `bc` copy have different
values at `c`, choose them. If no such pair exists, nonemptiness of both
bundles implies that both bundles have one common constant value at `c`,
so `c` is a blocker. The choices at the two nonconstant endpoints are
independent, which proves the claim.

## Lemma 3: support vertices of degree one or two

Here "support degree" counts distinct neighbors, while graph degree counts
all actual copies.

A support-degree-one vertex `v`, with bundle size `m>0`, is impossible.
If that bundle is monochromatic at `v`, its local class bound fails.
If it is monochromatic at its other endpoint, the nonlocal singleton
inequality at `{v}` fails. Lemma 1 supplies one of these alternatives.

Suppose `v` has exactly two neighbors and its bundle sizes are `x>=y>0`.
The larger bundle cannot be monochromatic at its other endpoint: strict
nonlocal admissibility at `{v}` would give `2x<x+y`, contradicting `x>=y`.
It is therefore monochromatic at `v`, and the local class bound gives
`2x<=x+y`. Hence `x=y`. The same strict nonlocal argument shows that the
other bundle must also be monochromatic at `v`. The two constant values
are different, since equality would put all `2x` incidences in one class.

Thus a support-degree-two vertex has equal incident bundle sizes, and any
choice of one copy from each of them is compatible there.

## Exhaustive underlying support cases

There are four active labels. With no support-degree-one vertex, their
underlying simple graph is one of `C4`, the diamond `K4-e`, or `K4`.
A support on three labels is already covered by the established theorem;
directly, Lemma 3 would make its triangle compatible. Disconnected support
on four active labels would have a two-vertex component and hence a
support-degree-one vertex, so it is impossible here.

### The diamond is impossible

Let `a,b` be the two degree-three support vertices, joined by a nonempty
bundle of size `z`. Let `c,d` be the degree-two vertices. Lemma 3 gives
`m_ac=m_bc=x>0` and `m_ad=m_bd=y>0`, with distinct neighbor classes at
`c,d`. Thus the triangles `abc` and `abd` cannot be blocked at `c,d`.

Neither `a` nor `b` can block both triangles. Doing so makes all three of
its incident bundles the same class, violating its local half-degree bound.
Therefore, after exchanging `c,d` if needed, `a` blocks `abc` and `b`
blocks `abd`. Their local class bounds give respectively
`z+x<=y` and `z+y<=x`. Adding yields `2z<=0`, contradicting `z>0`.

### The complete support K4 is impossible

Each of the four triangles has a blocker by Lemma 2. Each vertex blocks
at most one triangle, because any two of its three triangle corners share
a bundle; their two constant class values must then agree, making all
three bundles one class. Thus the four blockers are distinct.

For each vertex `v`, let `f(v)` be the unique neighbor omitted from the
triangle blocked at `v`. Its two other incident bundles form one class.
The four omitted labels are distinct because the four blocked triangles
are distinct. Hence `f` is a permutation without fixed points. The local
class bound gives
`m_vf(v) >= sum of the other two incident bundle sizes`.

There are two derangement types.

* If `f` is the four-cycle `a->b->c->d->a`, add the four inequalities.
  The left side is `m_ab+m_bc+m_cd+m_da`. The right side is that same
  sum plus `2(m_ac+m_bd)`. This contradicts positivity of both diagonals.
* Otherwise relabel so that `f` consists of `a<->b` and `c<->d`.
  Put `A=m_ac+m_ad` and `B=m_bc+m_bd`. Local bounds at `a,b` give
  `m_ab>=A` and `m_ab>=B`. By Lemma 1 the bundle `ab` is monochromatic
  at at least one endpoint; suppose it is monochromatic at `a`.
  Its constant class differs from the class covering `ac` and `ad`,
  since otherwise every incidence at `a` has that class. The local
  bound on the `ab` class gives `m_ab<=A`, so `m_ab=A`.
  The nonlocal cut `X={c,d}` contains exactly `A+B` copies. The class
  at `a` covering `ac,ad` contributes exactly `A` of them. Its half-cut
  inequality gives `A<=B`, while `B<=m_ab=A` was already proved.
  Therefore `A=B`, and this nonlocal class-cut is tight. Its cut is
  positive. This contradicts the standing strict nonlocal hypothesis.
  If `ab` is monochromatic only at `b`, interchange `a,b` in the argument.

### The remaining C4 support has an explicit partition

Every support vertex has degree two. Lemma 3 propagates one common positive
bundle size `m` around the four-cycle. At each vertex its two bundles have
different constant classes. Choose bijections from `Fin m` to each of the
four actual bundles. For each index, take the four corresponding copies.
They form a circuit and are compatible at every label. The bijections
give pairwise disjointness and exact coverage of all original copies.
There is no residual admissibility obligation in this final branch.

## Formal obligations still open

The argument uses no existence theorem beyond the already proved
at-most-three-label partition and finite elementary selection. Completing
it in Lean still requires:

1. Full tight-shore suppression with two actual-copy graph constructions,
   exact degree/cut/class identities, and both partition lifts.
2. Global coarsening and strictness transfer in a precise finite API.
3. The triangle-bundle lemma, support classification, blocker assignment,
   and the two finite derangement cases.
4. The explicit uniform-C4 partition and the final safe-deletion induction.

Each item must be proved and compiled before the general four-label result
or any dependent numbered manuscript assertion is promoted.

## Focused implementation update

During this continuation, `FourGlobalCoarsening.lean` passed the strict
focused command `global-coarsening-01`, proving global admissibility of
the local coarsenings on arbitrary vertex types. `FourTriangleSelection.lean`
passed `four-triangle-selection-01`, proving Lemmas 1 and 2 above as elementary
finite-bundle statements, with cyclic/transitive proofs covering all eight
endpoint orientations. The full degree-two branch also passed `d2-final-02`.

These focused passes do not establish the proposed general theorem or
replace the complete project's frozen build and axiom audit. Strictness
transfer for the graph-level nonlocal hypotheses, tight-shore construction
and restoration, support classification, explicit uniform-C4 partition,
and the final safe-deletion induction remain unformalized in this route.
