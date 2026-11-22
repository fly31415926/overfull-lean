# Deterministic assembly of one localized palette

This continuation composes the finite selection and coloring constructions
from the verified checkpoint `9f2dd24a26c94568904b75c4fe3bcd9ae985ca1f`.
The public theorem
`Overfull.BipartiteFactorization.exists_localized_palette` constructs an
actual selected palette graph and its balanced localized coloring from
conditions on the original exterior coloring, one palette, two blocks,
and the unused edge supplies. No selected graph, correction set, or
coloring of the selected graph is supplied as an assumption.

The current completed numbered inventory is **44 of 69**. The subsequent
[two-family construction](bipartite-two-families.md) now assembles the
fine and coarse families and colors their exact remaining exterior from
finite input conditions. The later
[sampling continuation](bipartite-sampling.md) proves the probability
ingredients and constructs disjoint palettes from marginal failure
bounds. The subsequent [uniform-localization](uniform-localization.md)
results derive uniform sampling budgets and connect sampled supplies to
actual palette selection and coloring. The full spanning setup, final
boundary construction, and robust-core factorization remain open. Earlier
recovery provenance, including the unavailable
later checkpoint, is recorded in
[bipartite-prerequisites.md](bipartite-prerequisites.md).

The manuscript reference is Section 6, `old:two-families`, in
`Four_Robust_Component_Cases_2026-11-21.tex`, particularly the imbalance
identity `old:fac:imbalance` and the selection and coloring of an
individual palette graph. The numbered inventory and statement hashes
remain pinned to the source recorded in `manuscript-source.json`.

## Sources and public interfaces

| Component | Source and principal declarations |
| --- | --- |
| Actual palette copies, row demands, inherited colors, and degree sums | [PaletteRows.lean](../Overfull/BipartiteFactorization/PaletteRows.lean): `palette_row_eq`, `palette_low_core_empty`, `palette_side_degree_eq`, `compressedPaletteColoring` |
| Signed correction accounting | [Imbalance.lean](../Overfull/BipartiteFactorization/Imbalance.lean): `correction_imbalance_identity`, `balanced_correction_imbalance`, `selected_degree_balance` |
| Filling demands with unused preferred copies | [Selection.lean](../Overfull/BipartiteFactorization/Selection.lean): `PreferredSelection.exists_filled_exterior`, `exists_preferred_selected_graph` |
| Capacity after deletions from the relevant pool | [Capacity.lean](../Overfull/BipartiteFactorization/Capacity.lean): `exists_graph_correction_subset_after_pool_deletion` |
| Constructed palette graph and coloring | [Assembly.lean](../Overfull/BipartiteFactorization/Assembly.lean): `PaletteSelectionConditions`, `SelectedPalette`, `exists_selected_palette`, `SelectedPalette.exists_localized_coloring`, `exists_localized_palette` |

## 1. Original copies and palette demands

Let `G` be a finite loopless multigraph with a proper `Fin k` coloring
`c`. In the manuscript application, `G` is the exterior graph
`R_ext`, whose core vertices have small degree. It is not the dense
regular host before its embedded bipartite core is removed. Every
original edge copy has its own element of the edge type; parallel
copies remain distinct throughout the construction.

Write `U=A∪B`, where `A` and `B` are disjoint actual vertex sets, and
let `I` be a finite set of original color labels. Define

\[
F_I=\{e:c(e)\in I\},\qquad
R_I^0=F_I\cap E(G[U^c]),\qquad
r_x=|F_I\cap E_G(x,U)|.
\]

The Lean definitions are `paletteEdges c I` and `paletteBase c U I`.
At every exceptional vertex `x∉U` of original degree `k`, the proofs
give

\[
d_{G[F_I]}(x)=|I|,\qquad
d_{G[R_I^0]}(x)+r_x=|I|.
\]

Consequently the natural-number demand
`I.card - (G.restrictEdges (paletteBase c U I)).degree x` equals the
actual palette-to-core copy count `r_x`. Properness supplies one
incidence for each selected label at a full-degree vertex; the base
and the core incidences partition those copies.

Every subset of `F_I` inherits a proper coloring with `|I|` labels.
`paletteEquiv` gives an equivalence between the selected original labels
and `Fin I.card`; `compressedPaletteColoring_restore` proves that
inverting this equivalence recovers the original label. In particular,
the exceptional base has an actual proper coloring with `|I|` colors.

If `I` is contained in the allowed colors from the earlier palette
preparation, `palette_low_core_empty` proves that a low vertex has no
palette-to-core copy. This conclusion follows from the actual excluded
labels, not from an assumed zero demand. Finally,
`palette_side_degree_eq` derives equality of the two actual side-degree
sums whenever every color in `I` is balanced on `A,B`.

## 2. The signed correction identity

Let `Z_A,Z_B` be disjoint active sets outside `U`. Their labels specify
the preferred side used in this construction. The earlier preferred-side
theorems can supply that choice; the present finite theorem needs only
the stated side supplies. Define the actual correction pools

\[
P_+=E(G[B])\cup\bigcup_{x\in Z_A}E_G(x,B),\qquad
P_-=E(G[A])\cup\bigcup_{x\in Z_B}E_G(x,A).
\]

In Lean these are `correctionPool G B ZA` and
`correctionPool G A ZB`. For any actual retained set `F` with no core
copies at exceptional vertices outside `Z_A∪Z_B`, put
`r_F(x)=|F∩E_G(x,U)|`. The general identity is

\[
\begin{aligned}
\sum_{v\in A}d_{G[F]}(v)-\sum_{v\in B}d_{G[F]}(v)
={}&\sum_{x\in Z_A}r_F(x)-\sum_{x\in Z_B}r_F(x)\\
&-2\bigl(|F\cap P_+|-|F\cap P_-|\bigr).
\end{aligned}
\]

All signed quantities in this theorem are integers. No natural-number
subtraction is used to represent a potentially negative imbalance.
For the balanced actual palette graph, this specializes to

\[
\sum_{x\in Z_A}r_x-\sum_{x\in Z_B}r_x
=2(e_{I,+}-e_{I,-}),\qquad e_{I,\pm}=|F_I\cap P_\pm|.
\]

### Argument

`restricted_degree_sum` expresses an actual side-degree sum as the sum
of endpoint contributions over the retained copies. The endpoint cases
are in `A`, `B`, `Z_A`, `Z_B`, or outside all four sets. Empty inactive
core rows exclude a core-to-inactive edge. The contribution identity is
proved for each remaining endpoint case and summed over `F`.
Distinct exceptional vertices have disjoint rows into the core, so the
union counts equal the sums of the actual row counts. This argument
counts each parallel copy separately and also covers edges between the
two core sides: their signed contributions cancel.

## 3. Exact finite input conditions

`PaletteSelectionConditions` supplies conditions before any correction
set or selected graph is chosen. Besides the proper original coloring,
it requires:

- Disjoint core sides; disjoint active sets `Z_A,Z_B` outside the core;
  and blocks `Ablock⊆A`, `Bblock⊆B`.
- Original degree `k` at every exceptional vertex, balance of each
  selected original color, and empty palette core rows at inactive
  exceptional vertices.
- An arbitrary deleted set of original copies `D`, with
  `R_I^0∩D=∅`.
- The orientation `e_{I,-}≤e_{I,+}`.
- At least `r_x` unused preferred copies into `Ablock` for every
  `x∈Z_A`, and at least `r_x` into `Bblock` for every `x∈Z_B`.
- Weights `0≤ω₁≤ω₂≤1` and the correction-score inequality below.

Set `t=e_{I,+}-e_{I,-}`. The orientation makes this natural-number
difference equal to its signed integer counterpart. The correction pool
restricted to the chosen block is

\[
P_{+,\mathrm{block}}=E(G[B_{\mathrm{block}}])\cup
\bigcup_{x\in Z_A}E_G(x,B_{\mathrm{block}}).
\]

The exact score condition is

\[
\begin{aligned}
t\le{}&\omega_2|E(G[B_{\mathrm{block}}])|\\
&+\sum_{x\in Z_A}
  \min\{\omega_1|E_G(x,B_{\mathrm{block}})|,r_x\}\\
&-\omega_2|D\cap P_{+,\mathrm{block}}|.
\end{aligned}
\]

This is the original weighted score minus its proved deletion-loss
bound. It is an explicit sufficient lower bound on surviving capacity;
the theorem does not assume merely that an unspecified surviving score
is large enough. Only deleted copies belonging to this correction pool
are charged. The selected corrections nevertheless avoid all of `D`.
The deleted set may depend on earlier choices; independence is not
required.

The score uses the actual row cap `r_x`. The manuscript obtains its
capacity estimate using auxiliary caps `ℓ_x^0≤r_x`; monotonicity of the
minimum makes that estimate sufficient for the condition above. This
construction guarantees the cap `r_x`, and does not assert the stronger
auxiliary `ℓ_x^0` cap.

The public preferred supply condition asks for the full row `r_x` at a
left active vertex. After the correction set is chosen, only
`r_x-d_C(x)` copies are needed. This sufficient condition can be checked
before choosing `C`, and the manuscript supplies it through its bound
on available preferred copies and `r_x≤2λc_x`.

The theorem is stated with the positive orientation. For the opposite
inequality the same construction is applied with `A,B`, their blocks,
and `Z_A,Z_B` interchanged. No symmetry of the two individual pool sizes
is assumed.

## 4. Constructing the selected graph

The strengthened capacity theorem selects an actual set
`C⊆P_{+,block}` with `|C|=t`, disjoint from `D`, and
`d_C(x)≤r_x` for every `x∈Z_A`. Each active vertex then receives an
actual subset of its unused preferred row, of size
`r_x-d_C(x)`. Corrections have no incidence at `Z_B`, so those vertices
receive `r_x` preferred copies.

Distinct preferred rows are disjoint because each such copy has one
exceptional endpoint and one core endpoint. The proof also derives
disjointness from the correction set and from the exceptional-internal
base. The resulting set is

\[
F=R_I^0\cup C\cup\bigcup_{x\in Z_A\cup Z_B}M_x.
\]

The specialized selection theorem proves the exact pool intersections

\[
F\cap P_+=C,\qquad F\cap P_-=\varnothing.
\]

In particular, preferred copies consume no correction-pool capacity.
These identities also make later deletion accounting depend on the
number of correction copies, rather than the size of the entire
selected graph.

`exists_selected_palette` returns a `SelectedPalette` whose original
copy set `F` satisfies:

- `F∩D=∅` and `F∩E(G[Uᶜ])=R_I^0`.
- `|F∩E_G(x,U)|=r_x` for every exceptional vertex.
- Degree `|I|` at every exceptional vertex, including the inactive ones.
- Equal actual side-degree sums on `A` and `B`.
- Degree zero at every core vertex outside `Ablock∪Bblock`.
- Exactly `t` copies in `P_+` and none in `P_-`.

The side-degree equality is a conclusion: substitute the constructed
row counts and correction-pool intersections into the general signed
identity. Its right side is `2t-2t=0`. The selected copy set is a finite
subset of the original edge type; no abstract replacement edges or
identification of parallel copies are introduced.

## 5. Constructing the localized coloring

`exists_localized_palette` combines that selection with a coloring
construction. Its additional inputs are

\[
a\ge0,\quad 2a<|I|,\quad |A|=|B|,\quad
|U^c|\text{ even},\quad |A_{\mathrm{block}}|=|B_{\mathrm{block}}|,
\]

an ambient exterior degree bound `d_G(v)≤a` for every `v∈U`, and
`r_x>2a` at every active exceptional vertex. These are conditions on the
original exterior graph and its palette rows. The selected graph's core
degree bound follows because its copies form a subset of the original
copies.

The actual inactive residue of the selected graph is contained in
`R_I^0`: inactive exceptional vertices have no selected core copies,
and the exceptional-internal restriction is exactly the inherited base.
`color_inactive_from_base` transports the compressed original coloring
to that precise residue. The previously proved fan criterion then
constructs a proper coloring of the whole selected graph. The balancing
theorem produces a coloring `d` with `|I|` colors having all of the
following properties:

- Every color covers every exceptional vertex.
- Every color covers equally many core vertices in `A` and `B`.
- The numbers of vertices covered in `A` by any two colors differ by
  at most two.
- Every core footprint is contained in `Ablock∪Bblock`.
- Every footprint has even cardinality and size at most
  `2|Ablock|a/|I|+4`.
- At each core vertex, the number of color footprints containing it
  equals its actual selected degree, and is therefore at most `a`.

The final coloring may recolor the base during the fan and balancing
steps. The reversible compression result describes the inherited
starting coloring; it does not assert preservation of those labels in
the final balanced coloring.

## Remaining obligations

This result constructs one selected palette graph from the stated
finite inputs. The subsequent
[two-family construction](bipartite-two-families.md) proves mutual
disjointness of both selected families, exact aggregate row and pool
counts, coloring of the actual remaining exterior, and the footprint
load bound shared by all groups.

The [sampling continuation](bipartite-sampling.md) proves exact
uniform marginals for disjoint samples, weighted moments, capped
means, and the actual capped graph-score variance under independent
sampling in disjoint parts. Its simultaneous disjoint-palette
constructor keeps the marginal failure bounds explicit. The remaining
application must establish the actual partition-sample score mean,
derive every row, pool, preferred-edge, and score estimate, and prove
their combined failure budget is below one. The allowed-color
denominator conversion, uniform parameter choices, and boundary
budgets must still establish all finite supply and reserve inequalities
from the original robust-core hypotheses.

The regularity setup, special path systems, robust absorber, and final
factorization also remain substantive obligations. Theorem 6.1,
Proposition 6.2, Theorem 6.3, and the dependent Lemmas 4.2 and 4.14 remain
unverified as full numbered assertions. The construction recorded here
extends the checked finite components without increasing their numbered
assertion count.
