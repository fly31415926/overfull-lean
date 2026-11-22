# A direct proof of the four-odd-parts decomposition

## Status and scope

**The complete public theorem has passed its strict Lean check and independent
semantic review.** The new source checkpoint records **45 of 69** complete
numbered assertions, with **24 remaining**. The full project build and transitive
axiom audit for this continuation are still pending. Until that run finishes,
the preceding verification report must not be read as evidence for the new
source.

The complete statement is
`Overfull.FourOdd.four_odd_parts_decomposition` in
[Theorem.lean](../Overfull/FourOdd/Theorem.lean). It supplies a direct proof of
manuscript **Lemma 4.15**, label `three:lem:four-odd`, with the explicit sufficient
constant

\[
\delta=\frac1{1000}
\]

for both small ratios. The conclusion is an exact partition of the original
joining-edge copies into exactly \(h\) actual matchings projecting to perfect
matchings or three-edge stars, together with actual matching pairs whose
projections are two-edge circuits. The surplus conclusion is stronger than the
manuscript's bound of four.

The proof uses the already proved finite multigraph König theorem, equitable
edge-coloring theorem, and finite Hall arguments. It does not use a general
compatible-circuit decomposition theorem. The preserved general circuit work
is documented separately in [four-odd-circuits.md](four-odd-circuits.md).

The source statement is the existing assertion in the pinned manuscript
inventory, `Four_Robust_Component_Cases_2026-11-20.tex`. Its statement environment
also matches the recovered November 21 manuscript exactly; no weakened or newly
numbered assertion is substituted for Lemma 4.15.

## Original graphs, joining copies, and quotient labels

The formalization works for finite loopless multigraphs, so it also applies to
finite simple graphs. An element of the edge type denotes one actual copy.
Different copies are never identified merely because their endpoints or their
part labels agree.

A map `label : V → Fin 4` represents the partition. Labels `0,1,2,3` correspond
to the manuscript's four parts. Each fiber is required to have odd cardinality.
The graph's regularity and absence of an overfull vertex set are hypotheses
about the original graph, including its internal edges.

`joiningCopies G label` is the finite set of copies whose endpoints have
different labels. `joiningGraph G label` restricts the edge type to the subtype
of those copies while keeping the original vertex type and original endpoints.
The subtype projection back to the original edge type is injective.
`joiningQuotient G label` then replaces the endpoints by their four labels and
retains this same joining-copy type. Thus a matching in the joining graph is an
actual original-vertex matching, even when its projection is a star or a
parallel pair. These definitions and their cut/degree transport lemmas are in
[OriginalGraph.lean](../Overfull/FourOdd/OriginalGraph.lean).

The output structure `FourOdd.Decomposition` in
[Basic.lean](../Overfull/FourOdd/Basic.lean) records:

- a finite family of nonempty copy sets and a designated primary subfamily;
- exactly \(h\) distinct primary members;
- the original-graph matching property for every member;
- an injective pair-label projection and an allowed perfect-matching or star
  shape for every primary member;
- two distinct copies with the same projected pair for every surplus member;
- pairwise edge disjointness and the exact union of all supplied copies.

Consequently the count cannot be increased by repeating a piece or inserting
empty pieces. The circuit predicate used for the surplus pieces is the existing
connected, degree-two multigraph predicate, which permits two distinct parallel
copies. `Decomposition.surplus_circuit` proves both the exact size two and the
required size bound four.

## Cut information derived from the original hypotheses

Let \(G\) be \(h\)-regular. The handshake identity for a shore \(U\) is

\[
h|U|=2e_G(U)+|\partial_G U|.
\]

If \(|U|\) is odd, absence of an \(h\)-overfull set gives
\(|\partial_G U|\ge h\). Its cut cardinality is congruent to \(h\) modulo two.
Applying these facts to the four odd parts gives the quotient bounds

\[
d_Q(i)\ge h,\qquad d_Q(i)\equiv h\pmod2.
\]

A union of two odd parts has even cardinality. Its cut has an even number
\(M\) of copies. For any original vertex \(v\), toggling \(v\) changes that
shore to an odd shore and gives

\[
|\partial_G(U\mathbin{\triangle}\{v\})|
 = M+h-2d_{\partial_G U}(v).
\]

The odd-cut lower bound therefore implies
\(2d_{\partial_G U}(v)\le M\). This is a bound on the original vertex's actual
incident copies, not just on a quotient degree. The statements are proved in
[CutBounds.lean](../Overfull/FourOdd/CutBounds.lean) and transported to joining
subtypes and quotient cuts in `OriginalGraph.lean`. No cut parity or half-degree
condition remains an extra input to the final original-graph theorem.

## An actual singleton-and-pair construction

The reusable result in
[PairPools.lean](../Overfull/FourOdd/PairPools.lean) starts with a finite actual
bipartite pool of \(n\) copies. Given a quota \(q\) such that

\[
0\le q\le n,\qquad q\equiv n\pmod2,\qquad
\Delta\le\frac{n+q}{2},
\]

König coloring with \((n+q)/2\) colors, followed by equitable balancing,
produces exactly \(q\) singleton color classes and \((n-q)/2\) two-copy
matching classes. The construction returns the actual singleton subset and an
exact partition of its complement into actual matchings. The quota's parity and
degree conditions are proved before this theorem is used.

For a fixed pair of part labels, each two-copy matching projects to a genuine
parallel circuit. The ambient-pool versions of the theorem return finite sets
in the original copy type, so no later identity or coverage argument relies on
informal identification of subtypes.

## Safe cap truncation and the explicit constants

For an integer boundary-degree bound \(D\), use

\[
B=2D+(h-r_0)_+,
\]

where the positive part is natural-number subtraction in Lean. Prescribed
forest pools remain unchanged. Each other pair pool is retained in full if it
has at most \(B+1\) copies; otherwise its singleton quota is \(B\) or \(B+1\),
chosen with the same parity as its original cardinality. Every removed copy is
placed in an actual parallel matching pair by the preceding construction.

Thus each changed pool retains at least \(B\), every off-forest pool has at most
\(B+1\) retained copies, and every pool keeps its original parity. The record
`CappedPools` also contains the actual discarded decompositions and their exact
coverage. Its existence is proved in
[Capping.lean](../Overfull/FourOdd/Capping.lean).

All quotient singleton lower bounds survive. If no pool incident with a label
changed, that label's whole degree is unchanged. If an incident pool changed,
its at least \(B\) retained copies supplement an unchanged prescribed forest
pool with at least \(r_0\) copies. Such a prescribed incident pool exists for
each label of a perfect matching or star, and
\(r_0+B\ge h\). The changed and prescribed pools are distinct, so their
cardinalities add. Parity preservation follows by summing the disjoint incident
pools.

The proof takes

\[
1000D\le h,\qquad 999h\le1000r_0.
\]

For \(h>0\), an odd part and the odd-cut lower bound force a joining edge;
hence any valid integer boundary bound satisfies \(D\ge1\). This positivity
absorbs the cap's possible extra one copy. The checked arithmetic provides, in
particular,

\[
8(B+1)+4D\le h,
\qquad 3(B+1)+12D<h.
\]

The first is more than sufficient for the matching-case allocations; the
second gives the two Hall pairings in the star case their strict reserve.

## Prescribed matching: minority contraction and exact savings

Relabel the prescribed perfect matching as \(\{01,23\}\). The retained
off-matching copies form a bipartite graph across \(\{0,1\}\mid\{2,3\}\).
Write its cardinality as \(M=2k\). There are four pools, so
\(M\le4(B+1)\).

This residual graph has actual maximum degree at most \(M/2\). If no crossing
pool was changed, this is the original even-cut bound. If a crossing pool was
changed, the residual graph contains at least \(B\ge2D\) copies, while each
original vertex still has degree at most \(D\). Its even cardinality follows
from the preserved pool parities. These facts are constructed in
[MatchingPreprocessing.lean](../Overfull/FourOdd/MatchingPreprocessing.lean).

Let \(x_0,x_1\) be the row totals, and \(y_2,y_3\) the column totals.
Contract every original vertex in a smaller row class to one new vertex, and
do the same for a smaller column class. Keep all other vertices individually
and retain every edge copy. A contracted minority vertex has degree at most
\(M/2\); an uncontracted vertex retains its original degree bound. The two
sides remain distinct, so the new graph is loopless and bipartite.

König coloring followed by equitable balancing with \(k=M/2\) colors gives
exactly two copies in every color class. A matching after contraction is still
a matching in the original graph. Moreover, two copies from the same minority
class cannot occur together, because they would meet the contracted vertex.
Each minority edge therefore has a partner in the other refinement label on
that side. This construction, including the case \(M=0\), is
`exists_minorityPairing` in
[MinorityPairing.lean](../Overfull/FourOdd/MinorityPairing.lean).

The pairs have four possible projected shapes:

| Row labels | Column labels | Count | Piece used in the decomposition |
| --- | --- | --- | --- |
| Different | Different | \(P\) | Already a primary perfect matching |
| Equal | Different | \(R\) | Add one unused `01` singleton to form a primary star |
| Different | Equal | \(C\) | Add one unused `23` singleton to form a primary star |
| Equal | Equal | \(T\) | A surplus parallel two-edge matching |

Every mixed-row pair contains exactly one minority-row edge, and every
minority-row edge belongs to exactly one such pair. The same holds for columns.
The formal bijection counts actual copies and proves

\[
P+C=\min(x_0,x_1),\qquad
P+R=\min(y_2,y_3),\qquad
P+R+C+T=k.
\]

Select singleton quotas

\[
q_{01}=h-\min(x_0,x_1),\qquad
q_{23}=h-\min(y_2,y_3)
\]

from the prescribed pools. The retained singleton-label lower bounds prove
these quotas do not exceed the available pool cardinalities; their parities
follow from the preserved quotient-degree parities. The numerical reserve
also verifies the degree condition for the singleton-and-pair construction.
All remaining prescribed-pool copies become surplus parallel pairs.

An actual two-edge matching has at most four original endpoints. At most
\(4D\) candidate singleton copies can meet these endpoints. A finite Hall
selection therefore allocates distinct compatible singleton copies to all
\(R\) shared-row pairs and all \(C\) shared-column pairs. The inequalities
\(2k+4D\le h\) and \(\min(x_0,x_1),\min(y_2,y_3)\le k\) provide the required
pool sizes. This allocation is proved in
[Allocation.lean](../Overfull/FourOdd/Allocation.lean), and its actual matching
and shape consequences are assembled in
[Matching.lean](../Overfull/FourOdd/Matching.lean).

Put \(p=P+R+C\). After those augmentations, the `01` and `23` singleton pools
both have exactly \(h-p\) unused copies. Pair them bijectively. Their part
labels are disjoint, so each resulting pair is automatically an actual
matching and projects to \(\{01,23\}\). There are now exactly
\(p+(h-p)=h\) primary pieces. Every residual cross copy, every selected
singleton, every unselected prescribed-pool copy, and every capped-off copy is
accounted for by disjoint finite-set union identities.

## Prescribed star: three singleton quotas and two Hall pairings

Relabel the prescribed star to have center `0`. Let \(O_i\) be the retained
off-star pool opposite arm \(0i\), and let
\(N=|O_1|+|O_2|+|O_3|\). There are three off-star pools, so
\(N\le3(B+1)\). Set \(q=h-N\); the numerical bound gives \(q>12D\).

For arm \(0i\), choose exactly \(q+|O_i|\) singleton copies. This is the same
quota as \(h\) minus the retained off-star incidence at leaf \(i\). The leaf
cut lower bound and parity prove its capacity and parity requirements, and the
degree bound proves the coloring requirement.

Pair \(|O_i|\) of these singletons with all copies in \(O_i\). The opposite
part pairs are disjoint, so these are actual perfect matchings. Exactly \(q\)
singletons remain in each of the three arms. Two Hall pairings join these
three equally sized families into \(q\) actual matching triples. The original
endpoint loads are bounded by \(D\), and \(q>12D\) supplies the required
strict Hall margin. Each triple projects to the three distinct star arms.

There are exactly \(N\) primary perfect matchings and \(q\) primary stars,
so their total is \(N+q=h\). Every other copy is in one of the actual parallel
matching pairs produced by the pool constructions. The full canonical result
is `exists_star_decomposition` in
[Star.lean](../Overfull/FourOdd/Star.lean), with actual family assembly in
[StarAssembly.lean](../Overfull/FourOdd/StarAssembly.lean).

## Relabeling, real bounds, and the zero-degree case

A finite permutation of the four labels sends every allowed prescribed forest
to one of the two canonical cases. The permutation is selected inside the
proof. Pair supplies, cuts, quotient degrees, parity, and the output shapes are
transported explicitly, and the final decomposition is returned to the
original labels. Actual vertices and edge copies are unchanged. See
[Relabeling.lean](../Overfull/FourOdd/Relabeling.lean) and
[RelabelGraph.lean](../Overfull/FourOdd/RelabelGraph.lean).

For a nonnegative real boundary bound \(a\), take \(D=\lfloor a\rfloor\).
An integer actual degree at most \(a\) is at most this natural floor. The
condition \(a/h\le1/1000\), for \(h>0\), gives \(1000D\le h\), and
\((h-r_0)/h\le1/1000\) gives \(999h\le1000r_0\). No rounding error is added
to the degree bound. These conversions are in
[Quantitative.lean](../Overfull/FourOdd/Quantitative.lean).

`four_odd_parts_decomposition` uses \(h>0\), as required to interpret the two
ratios. The integer and multiplication-form real theorems also cover \(h=0\):
a zero-regular loopless graph has no edge copies, so the empty decomposition
has exactly zero primary pieces. The real-bound theorem states \(a\ge0\);
this also follows from the original boundary-bound hypothesis and the existence
of a vertex in an odd part. A positive-degree instance forces the integer
boundary bound \(D\) to be positive before either canonical construction is
invoked.

## Source-to-Lean clause map

All declarations below are in namespace `Overfull.FourOdd` unless a different
namespace is displayed. The public source theorem is in `Theorem.lean`.

| Manuscript clause | Formal representation and proof connection |
| --- | --- |
| An \(h\)-regular graph | `G : Multigraph V E`, `hregular : ∀ v, G.degree v = h`; the multigraph statement specializes to simple graphs |
| No \(h\)-overfull set | `hno : ∀ X : Finset V, ¬ G.IsOverfull h X` on the original graph |
| Four odd parts | `label : V → Fin 4`; `hodd` requires every label fiber to have odd cardinality |
| Boundary degree at most \(a\) | `hdegree` bounds `G.degreeOn (joiningCopies G label) v`, cast to the reals |
| Prescribed perfect matching or three-edge star | `hF0 : CircuitPatterns.LabelForestShape F0`; `exists_canonical_relabeling` selects and transports a canonical case |
| Forest-cut supply | `_hforestSupply` in `four_odd_parts_decomposition`; retained as a source hypothesis, although the direct proof proves a stronger theorem using only the pair supplies |
| At least \(r_0\) copies in each prescribed pair | `hsupply` bounds `pairPool (joiningQuotient G label) p` for each `p ∈ F0` |
| Both ratios sufficiently small | Both are at most the absolute constant `1 / 1000`; `ratio_boundary_small` and `ratio_supply_nearly` give the integer construction bounds |
| Derived quotient cut/parity information | `joiningQuotient_degree_lower`, `joiningQuotient_degree_parity`, `joiningCut_pair_parity`, `joiningCut_pair_degree_le_half` |
| Exactly \(h\) primary matchings | `Decomposition.primary_card`; `exists_matching_decomposition` or `exists_star_decomposition`, then `exists_joining_decomposition` and `four_odd_decomposition_nat` |
| Matchings of actual joining edges | `Decomposition.matching` in `joiningGraph G label`, with original vertices and original endpoint incidences |
| Primary projections have the prescribed kinds of shape | `Decomposition.primary_shape` contains `IsPrimary`, including injectivity of the pair-label projection and `LabelForestShape` |
| Surplus projections are circuits of length at most four | `Decomposition.surplus_circuit`: an actual quotient circuit with exact cardinality two, hence cardinality at most four |
| A decomposition of all joining edges | `Decomposition.disjoint`, `Decomposition.nonempty`, and `Decomposition.cover`; the covered set is `univ` in the actual joining-copy subtype |

## What this completion does and does not prove

The new argument proves the full existing Lemma 4.15 from its original graph
hypotheses with an explicit absolute smallness constant. It retains the
forest-cut supply in the public statement but establishes that this additional
supply hypothesis is unnecessary for the stronger direct construction.

The general Fan–Zhang theorem for compatible circuit decompositions remains
unproved in this repository. The old virtual-edge, admissibility, finite
template, and local circuit-lifting components are preserved. They are useful
independent results, but the new proof does not need their missing general
existence step. Completing Lemma 4.15 therefore does not complete that general
theorem, Lemma 4.14, the later factorization chain, or the manuscript's main
theorem.

After the full verification run succeeds, the authoritative declaration audit,
source/input hashes, assertion coverage, and allowed axioms are recorded in
`verification/results.json`, `verification/axioms.log`, and
`docs/coverage.json`. The status paragraph above will be updated only after
that evidence is available.
