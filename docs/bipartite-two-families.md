# Two selected families and the exact remaining exterior

This continuation extends the verified one-palette construction at commit
`3dccee2161518e8cfa1581eda49fe2046a41627c`. The public theorem
`Overfull.BipartiteFactorization.exists_colored_two_families` constructs
two families of pairwise edge-disjoint selected graphs, their balanced
localized colorings, and a balanced coloring of the exact remaining
exterior graph. It also proves that the total footprint load across
both families and the remainder equals the original core degree.

The construction starts from finite conditions on the original exterior
coloring, palettes, blocks, and deletion budgets. The simultaneous
existence of data satisfying all those quantitative conditions remains
to be proved. The subsequent [sampling continuation](bipartite-sampling.md)
supplies weighted moments, capped means, actual graph-score variance,
and a disjoint-palette constructor from marginal failure budgets.
The current completed numbered assertion count is **45 of 69**, with 24
remaining, after the [complete proof of Lemma 4.15](four-odd-decomposition.md).
The full factorization theorem is still unverified.

The manuscript reference is the selection of the fine and coarse
families and the coloring of their remainder in Section 6,
`old:two-families`, of
`Four_Robust_Component_Cases_2026-11-21.tex`. The one-palette interfaces
and their precise scope are recorded in
[bipartite-palette-assembly.md](bipartite-palette-assembly.md).
Earlier recovery provenance remains in
[bipartite-prerequisites.md](bipartite-prerequisites.md).

## Sources and public interfaces

| Component | Source and principal declarations |
| --- | --- |
| Either correction orientation, in the original side order | [Oriented.lean](../Overfull/BipartiteFactorization/Oriented.lean): `OrientedPalette`, `exists_oriented_palette`, `LocalizedColoring` |
| One-scale family construction and exact union counts | [Families.lean](../Overfull/BipartiteFactorization/Families.lean): `exists_oriented_palette_family`, `familyCopies_degree`, `OrientedPalette.family_base`, `OrientedPalette.family_rows_palette_union` |
| Actual complementary graph and its inherited inactive colors | [Remaining.lean](../Overfull/BipartiteFactorization/Remaining.lean): `remaining_exceptional_degree`, `remaining_inactive_colorable`, `exists_balanced_remaining_coloring` |
| Coloring the selected family and remainder with a shared load bound | [FamilyColoring.lean](../Overfull/BipartiteFactorization/FamilyColoring.lean): `localized_family_load`, `exists_family_and_remaining_colorings` |
| Reserving coarse supplies and constructing both families | [TwoFamilies.lean](../Overfull/BipartiteFactorization/TwoFamilies.lean): `ReservedPaletteConditions`, `TwoFamilyConditions`, `exists_two_palette_families`, `exists_colored_two_families` |

## 1. Original exterior data and either correction sign

Let `G` be the actual exterior multigraph with a proper original
`Fin k` coloring `c`. Write `U=A∪B` for its core and `Z=Uᶜ` for the
exceptional set. In the manuscript application, `G` is `R_ext`, after
the embedded core copies have been removed from the regular host.
The degree bound on core vertices is a bound in this exterior graph.

All sets in the construction contain original edge copies. Parallel
copies retain distinct identities. The core sides `A,B` are disjoint,
and `Z_A,Z_B` are disjoint active sets outside `U`. They specify the
preferred sides. The correction pools are

\[
P_+=E(G[B])\cup\bigcup_{x\in Z_A}E_G(x,B),\qquad
P_-=E(G[A])\cup\bigcup_{x\in Z_B}E_G(x,A).
\]

For a palette `L`, let

\[
F_L=\{e:c(e)\in L\},\quad
r_L(x)=|F_L\cap E_G(x,U)|,\quad
e_{L,\sigma}=|F_L\cap P_\sigma|.
\]

`OrientedPalette` retains the original ordered sides and blocks even
when the one-palette selection is carried out after swapping them. Its
two pool-count fields prove

\[
|S_L\cap P_+|=(e_{L,+}-e_{L,-})_+,\qquad
|S_L\cap P_-|=(e_{L,-}-e_{L,+})_+,
\]

where `n_+` denotes the nonnegative part; the implementation uses
natural-number subtraction for these two quantities. At most one pool
is used by a particular palette. The earlier signed imbalance identity
continues to use integer subtraction.

The public constructor accepts either the original
`PaletteSelectionConditions` or the same conditions with the sides,
blocks, and active classes swapped. Thus each palette may have its own
correction sign. Its other fields are the exact exceptional base, the
original palette row counts, degree `|L|` at each exceptional vertex,
equal core side-degree sums, block support, and avoidance of the stated
deleted set.

## 2. One-scale families are constructed with disjoint copies

The fine palettes are `I_i`, indexed by a finite type `ι`, and their
block pairs are `Af_i,Bf_i`. The coarse palettes are `J_j`, indexed by
a finite type `κ`, with block pairs `Ac_j,Bc_j`. Family sizes are
arbitrary finite values in the theorem. The manuscript's `q` fine
graphs and seven coarse graphs are an instantiation of these indices.

`exists_oriented_palette_family` constructs every member from its
original finite one-palette conditions. Pairwise disjoint palettes and
pairwise disjoint block unions within that scale imply pairwise
disjoint selected copy sets.

### Argument for disjointness

Suppose a copy belonged to two selected graphs. If it had an endpoint
in `U`, positive degree at that endpoint and the support conclusions
would put the endpoint in both block unions, contradicting their
disjointness. Otherwise both endpoints would be exceptional. The
exact base identities would put its original color in both palettes,
contradicting their disjointness. This argument applies to each actual
copy, including any parallel copy.

For `T=familyCopies (fun i => S_i.copies)`, which is the actual finite
union, the module proves exact addition of degrees and of intersections
with any fixed copy set. In particular,

\[
d_{G[T]}(x)=\sum_i |I_i|\quad(x\in Z),\qquad
|T\cap E_G(x,U)|=\sum_i r_{I_i}(x).
\]

The exceptional base is exactly the base for the union of the original
palettes. Side-degree balance is preserved by the union. Pool use is
exactly the sum of the corresponding nonnegative differences, even
when different members use different correction signs.

## 3. Coarse supplies reserved before fine copies are selected

`TwoFamilyConditions` contains only original data. It assumes the fine
one-palette conditions, stronger coarse reserve conditions, pairwise
disjoint palettes within each scale, and disjoint palettes between the
two scales. Block unions must be disjoint within each scale. Fine and
coarse blocks may overlap.

The fine palettes determine the following costs before any fine copies
are selected:

\[
b_x=\sum_i r_{I_i}(x),\qquad
B_+=\sum_i(e_{I_i,+}-e_{I_i,-})_+,\qquad
B_-=\sum_i(e_{I_i,-}-e_{I_i,+})_+.
\]

These are `familyRowDemand` and the two orientations of
`familyCorrectionDemand`. Exact family accounting proves that the
constructed fine union has these row and pool counts.

Let `D` be the original deleted set. For a coarse palette using the
positive correction orientation, the reserve conditions require

\[
r_{J_j}(x)+b_x
\le |E_G(x,\text{preferred block of }j)\setminus D|
\]

at every active exceptional vertex. Write

\[
P_{+,j}=E(G[Bc_j])\cup\bigcup_{x\in Z_A}E_G(x,Bc_j).
\]

The coarse correction reserve is the explicit inequality

\[
\begin{aligned}
(e_{J_j,+}-e_{J_j,-})_+\le{}&
\omega_{c,2}|E(G[Bc_j])|\\
&+\sum_{x\in Z_A}
\min\{\omega_{c,1}|E_G(x,Bc_j)|,r_{J_j}(x)\}\\
&-\omega_{c,2}\bigl(|D\cap P_{+,j}|+B_+\bigr),
\end{aligned}
\]

with `0≤ωc,1≤ωc,2≤1`. For the negative orientation, the sides and
active classes are swapped and `B_-` is charged. The inherited
one-palette conditions also retain the original balance, full
exceptional degrees, low-row exclusion, base avoidance, and block
containment assumptions.

### Argument for the enlarged deletion set

Construct the fine family and let `T_f` be its union. Every coarse
selection is then made avoiding `D∪T_f`. The generic row-deletion lemma
deducts at most `b_x` from the unused preferred row, leaving at least
the requested coarse demand. For the positive correction pool,

\[
|(D\cup T_f)\cap P_{+,j}|
\le |D\cap P_{+,j}|+|T_f\cap P_+|
=|D\cap P_{+,j}|+B_+.
\]

The negative version uses `B_-`. The original deletion is charged
locally, and the fine family is charged once through its actual use of
the relevant global correction pool. Preferred fine copies do not
consume either correction pool. The reserve transfer imposes no
independence condition on the chosen fine copies.

A coarse exceptional base avoids the fine union because its palette
is disjoint from every fine palette: a shared base copy would also be
in a fine exceptional base, where its original label belongs to the
fine palette. This uses the exact base identity, and needs no
disjointness between fine and coarse blocks.

`exists_two_palette_families` consequently constructs both families on
the combined index `ι⊕κ`. Coarse members avoid the whole fine union;
members within each scale are disjoint by their blocks and palettes.
The resulting combined family is pairwise edge-disjoint and every
member avoids `D`.

## 4. The exact remaining graph

Let `K` be the union of all fine and coarse original palettes, let

\[
s=|K|=\sum_i|I_i|+\sum_j|J_j|,
\]

and let `T` be the actual union of both selected families. The remaining
graph is exactly `G.restrictEdges Tᶜ`. It retains every original copy
not selected in either family. Together with the selected graphs it
partitions all exterior copies; the original deleted set `D` is an
avoidance constraint for the selected graphs, not an additional
deletion from this remaining graph.

At every exceptional vertex, the remaining degree is exactly `k-s`.
Its core side-degree sums are equal, because the original exterior and
the selected union both have equal side-degree sums. The selected and
remaining copies partition each actual exceptional-to-core row, so

\[
d_{G[T^c]}(x,U)\ge d_G(x,U)-s\quad(x\in Z).
\]

`remaining_inactive_color_mem` proves that every copy in the actual
inactive residue of this remainder has an original label outside `K`.
An exceptional-internal copy with a label in `K` would belong to the
selected base and hence could not remain. A low-to-core copy cannot
have a label in `K`, by the original palette exclusion. This claim is
restricted to the inactive residue; remaining active copies can still
carry original labels from `K`.

The original coloring on the inactive residue is compressed to
`Fin (k-s)`. The fan criterion constructs a coloring of the entire
remaining graph, and the balancing theorem gives the final residual
coloring. No coloring of the remaining graph is assumed.

## 5. Coloring both families and bounding their total load

The final public constructor adds the following conditions to the
finite selection data:

- `a≥0`, equal core side orders, and even exceptional order.
- Original degree `k` at every exceptional vertex, equal original
  core side-degree sums, and exterior core degrees at most `a`.
- Every selected palette has more than `2a` labels, and every active
  vertex has more than `2a` actual core copies in each selected palette.
- The two blocks of each selected graph have equal cardinality.
- `k-s>2a`, and `d_G(x,U)-s>2a` at every active exceptional vertex.

The selected graph colorings are constructed from their inherited
exceptional bases. The residual coloring is constructed from its
unused original labels on the inactive residue. `LocalizedColoring`
records the resulting proper coloring and all the following facts:

- Every color covers the entire exceptional set.
- Every color has equal core coverage on the two sides.
- The side coverage of two colors differs by at most two.
- Every selected footprint is supported in its own block pair.
- Each footprint has even size.
- A selected palette `L` with left block `W` has footprint bound
  `2|W|a/|L|+4`; the residual bound is `2|A|a/(k-s)+4`.
- At each core vertex, the footprint incidence count for a particular
  graph equals its actual degree in that graph.

`LocalizedColoring.footprint_avoids` also proves the boundary exclusion
from actual copy avoidance. If every original copy incident with a
vertex in `W` belongs to `D`, a selected graph avoiding `D` has every
footprint disjoint from `W`. The proof uses the actual incident copy
witness in the footprint. Choosing such a boundary set with the
manuscript's budgets remains separate work.

The exact incidence property gives a shared bound across all groups. If `d_i`
ranges over both fine and coarse colorings and `dRest` is the residual
coloring, then for every `v∈U`,

\[
\sum_{i\in\iota\sqcup\kappa}
\bigl|\{\gamma:v\in\operatorname{footprint}(d_i,\gamma)\}\bigr|
+\bigl|\{\gamma:v\in\operatorname{footprint}(d_{\mathrm{Rest}},\gamma)\}\bigr|
=d_G(v)\le a.
\]

`localized_family_load` proves the equality from exact disjoint-union
degree addition and the complementary degree identity. Thus the bound
applies to all selected colors and residual colors together. It is not
obtained by summing separate upper bounds of `a` for each group.

The construction may recolor inherited labels during the fan and
balancing steps. It retains the original edge copies and their exact
partition; it does not claim that the final colors agree with every
original label.

## Scope and remaining obligations

This result completes the deterministic two-family selection and
coloring composition under explicit finite supplies and degree bounds.
Its hypotheses contain no selected-family witness or residual-coloring
oracle. All choices of selected copies and all final colorings are
constructed in the proof.

The [sampling continuation](bipartite-sampling.md) proves the finite
disjoint-sampling laws, weighted moments, capped means, and actual
nonlinear score variance for unions of independent samples in
disjoint parts. Its disjoint-palette existence theorem applies once
the marginal failure bounds sum to less than one. The remaining
application must establish the full partition-sample score mean and
all simultaneous row, pool, preferred-edge, and score failure budgets.
The conversion from the allowed-color denominator to the manuscript's
palette fractions, uniform parameter hierarchy, boundary-set
construction, and quantitative reserves must still be derived from
the robust-core input. The theorem gives the exact residual degree
`k-s`; it does not establish the manuscript's additional numerical
estimate `k-s≥k/2` from those unformalized parameter choices.

The special path systems, robust absorber, and final factorization also
remain to be constructed. Theorem 6.1, Proposition 6.2, Theorem 6.3,
and the dependent Lemmas 4.2 and 4.14 remain unverified as full numbered
assertions. This continuation extends their proved finite supporting
components without changing the completed assertion count.
