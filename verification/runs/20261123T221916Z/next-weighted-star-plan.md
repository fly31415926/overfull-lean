# Next-target assessment: weighted joining palettes and unpaired exceptional stars

**Status:** read-only mathematical plan. No new Lean proof, compiler check, or verification claim is attached to this assessment. Frozen sources and verification inputs were not changed.

## Assessment

The proposed weighted grouping refinement appears sufficient to color the unpaired exceptions, including two exceptions assigned to the same core and the prescribed half-reserve colors. It needs a stronger palette theorem with weighted whole-class bounds. The current unweighted palette theorem alone remains insufficient.

A clean sufficient regime is

- residual degree `h>0`;
- at most two unpaired exceptions;
- `b=floor(a) <= D`, `h-r <= D`, and `128D <= h`;
- `s=r/2 <= h/2` selected protected colors;
- target weighted class load `W=floor(h/8)`.

These are sufficient constants, not optimized constants. The original uniform native construction permits the requested surplus error to be made this small before the host is chosen.

## 1. Define weights at the old-core endpoint only

For an unpaired exception `z`, let `U_z` be its assigned original core and let
`S_z = exceptionCorePool H z U_z` be its actual residual star-copy pool.
For a joining piece `P`, define

`w_z(P) = sum_{v in U_z intersect support(P)} mu_H(z,v)`.

Equivalently, count copies in `S_z` whose **old-core endpoint** belongs to `support(P)`. Do not count an edge merely because its exceptional endpoint `z` lies in `support(P)`: that incorrect definition could give the whole star degree and would invalidate the `6b` bound.

Every old-core vertex has actual complementary degree at most `a`, so each multiplicity `mu_H(z,v)` is at most `b=floor(a)`. A joining piece has at most six support vertices, giving `w_z(P)<=6b`.

The joining pieces are edge-disjoint, and at most `D` pieces meet any fixed vertex. Double-counting by the old-core endpoint gives

`sum_P w_z(P) <= D*|S_z| <= D*h`.

The sum of the weights of the pieces placed in one color bounds the actual star copies blocked by that entire joining class. This is a whole-class weighted bound; it does not replace multiplicity by a vertex count.

## 2. Weighted finite greedy grouping

At a greedy insertion, forbid:

1. Colors with an endpoint conflict with the new piece: at most `6D`.
2. All protected labels: `s`.
3. For each exception `z`, colors whose current weight exceeds `W-6b`.

A color in the third set has weight at least `W-6b+1`. Since its total available weight is at most `Dh`, the number of such colors is at most `13D`. Indeed, `128D<=h` and `b<=D` imply `6b<=W` and

`64*(W-6b+1) > 5h`.

Thus a nonempty overloaded set has cardinality strictly less than `64D/5`, which is certainly at most `13D`. If `D=0`, its total weight is zero and the overloaded set is empty.

With at most two exceptional resources, the forbidden-color bound is therefore

`B = s + 6D + 2*(13D) = s + 32D`.

It leaves a gap `g=h-s-32D >= h/4 > 0`. Let `N` be the number of joining pieces and choose

`L=(nD/2)/(h-s-32D)+1`

with natural division. The existing incidence argument gives `N<=floor(nD/2)`, hence `N<=L*g`. The existing finite palette-capacity argument can then choose a color outside the above forbidden sets and below `L` pieces. Its new weight is at most `(W-6b)+6b=W`.

The odd case already has one prescribed primary piece in each color. Each primary has at most two copies, so its initial weight is at most `4b<=W`, and its initial piece count is at most one. Protected singleton primaries receive no surplus. The all-even case starts with no prescribed pieces and leaves its protected colors empty. Thus the seed data satisfy the new induction invariants without assuming a weighted coloring of the surplus pieces.

This needs a new dynamic weighted extension lemma; the existing static conflict relation does not by itself express weighted fullness.

## 3. Prescribed reserve edges do not cause an extra Hall obstruction

Use the original joining palette as the starting palette. For each selected protected label, the existing native insertion results identify its exact full reserve boundary. In the unpaired signature, that boundary contains one actual `z`-to-`U_z` copy at each exception. Its whole matching certificate also proves that these prescribed core endpoints avoid the protected joining crossing and one another.

Insert those boundaries, then exclude **all** protected labels from every remaining star palette. Consequently their prescribed old-core endpoints create no additional compatibility condition in any remaining color. The selected star copies are deleted from the remaining star pools, and all prescribed labels and copy identities remain fixed.

Do not feed `ReserveExtension.classes` directly to a theorem requiring a joining-only `JoiningPalette`. Maintain the original palette and the explicitly inserted copies as separate input data, then prove properties of their actual unions.

## 4. Handle a shared internal exceptional bundle first

If `z1,z2` are assigned to different cores, their mutual copies are joining copies and have already been colored. There is no additional internal exceptional bundle.

If they are assigned to the same core, let `t` be the number of their actual mutual copies. Let `j_z` be the joining degree at `z`. The original reserve supplies `r` distinct surviving copies from `z` to its assigned old core. Therefore the **combined** off-assigned-core incidence satisfies

`j_z+t <= h-r <= D`.

This stronger combined count must be derived, rather than separately subtracting two bounds of size `D`.

Color the `t` actual mutual copies injectively using labels outside the protected set and outside both joining-used palettes. There are at least `h-s-j_z1-j_z2` such colors, and

`t+j_z1+j_z2 <= 2D <= h-s`.

The bundle therefore has enough common free labels. Its copies have only the two exceptional endpoints, so this step has no old-core endpoint cost. It is internal to one assigned fiber, so it preserves every assigned-fiber cut. Distinct copies receive distinct labels and no protected label is touched.

## 5. Exact star/free-palette balance and sequential Hall

After the protected boundaries and any shared bundle have been colored, let `F_z` be the colors still free at `z`, and let `A_z` be the remaining actual star copies to `U_z`. Exact regularity and disjoint-copy accounting give

`|A_z| = |F_z| = m_z = h-s-j_z-t >= h-s-D >= h/2-D`.

For the first exception, relate a star copy `(z,v)` to a free color precisely when its old-core endpoint `v` is unoccupied in that color. A copy has at most `D` forbidden colors, while a free color blocks at most `W` star copies by the weighted grouping certificate.

For the second exception, the first star never touches the second exceptional vertex, so the second free-palette cardinality is unchanged. Its effect is confined to old-core endpoints:

- At a fixed old-core vertex `v`, the first star occupies at most `mu_H(z1,v)<=b` colors. Thus a second-star copy has at most `D+b` forbidden colors.
- A given color contains at most one newly added first-star copy, with one old-core endpoint `v_j`. This blocks at most `mu_H(z2,v_j)<=b` second-star copies. Thus a free color blocks at most `W+b` copies.

If the exceptions have different assigned cores, the additional endpoint obstruction is zero; the same bounds still apply.

The two sufficient half-degree inequalities are

`2(D+b) <= m_z` and `2(W+b) <= m_z`.

They follow with ample room from `b<=D`, `128D<=h`, `s<=h/2`, `W<=h/8`, and `m_z>=h-s-D`. In particular it is enough that `s+5D<=h` and `s+3D+h/4<=h`.

Apply an actual dense bipartite Hall bijection separately to each star. Its domain consists of distinct original edge copies and its codomain of the exact current free colors. The second bijection is constructed after the first and avoids its occupied old-core endpoints. No compatibility of two independently chosen star colorings is assumed.

## 6. Intended assembled conclusion

After these steps, every exceptional vertex is covered exactly once in every color. All joining copies and all copies incident with the exceptional set are colored, with protected reserve prescriptions unchanged. The color classes remain actual edge-disjoint matchings.

Every added copy is internal to its assigned fiber. Hence the assigned-fiber cuts retain their original parity. Since all exceptions assigned to a core are now covered, the uncovered assigned fiber is exactly the uncovered original core; this gives even uncovered old-core order for every color.

A color gains at most two copies and four support vertices, so bounds `3L+2` and `6L+4` are available. At each old-core vertex, the entire colored boundary lies in the actual complement of the embedded simple core. Its color load is therefore at most `a` (or `b` naturally), rather than a product involving the palette support size.

This is the input needed for the next robust completion stage. It is not itself the final factorization or reconstruction theorem.

## 7. Uniform parameter order

The existing residual satisfies `h>=alpha*n/30` and `D<=delta*n`. Choosing

`delta <= alpha/3840`

ensures `128D<=h`. Since the new grouping gap is at least `h/4>=alpha*n/120`,

`6L <= (360*delta/alpha)*n + 6`.

Thus `delta<=epsilon*alpha/720` and `n>=12/epsilon` give `6L<=epsilon*n` for the **joining palette before adding star copies**.

For the final enlarged classes, retain the additive four vertices: the same delta inequality together with `n>=20/epsilon` gives `6L+4<=epsilon*n`. Alternatively use `epsilon/2` for the joining palette and a larger order threshold. A core-relative error requires the existing lower bound `|U_i|>=c*n` and the corresponding tolerance `c*epsilon_core`.

Retained robustness is already chosen before the requested surplus error. Choosing delta as the minimum of these positive requirements is compatible with the existing order of uniform quantifiers; no extra hypothesis needs to be imposed on the original theorem's arbitrary host.

## Existing APIs and remaining proof tasks

Available:

- `OneCore.complement_degree_le_error`: actual complementary degree at an old-core vertex, hence parallel multiplicity bound.
- `AssignedParts.signature_some_uses_exceptionCorePool`, `coarseSignature_eq_some_iff`, `exceptionCorePool_matching_card_le_one`, and `exceptionCorePool_usage_eq_assignment`: one actual assigned-core incidence per parent matching in the unpaired signature.
- `BoundaryPacking.sameSignature`, compression retention, `reserved_exceptional_degree`, `residualBoundary_image`, and survival/disjointness lemmas: preserve and count those original reserve incidences.
- `Multigraph.family_support_load_le_degreeOn`: the piece-support multiplicity bound needed for total resource weight.
- `NativeReserve.pieceConflict_card_le`, `exists_available_palette`, and `exists_bounded_palette_extension`: existing finite endpoint/capacity arguments to strengthen by weighted invariants.
- The protected-primary and all-even circuit constructions: retain exact coverage and per-piece parity while changing only the grouping argument.
- `DenseLinkPacking.dense_bipartite_bijection` in `Overfull/Dense/LinkPacking/Candidates.lean`: a finite relation with balanced sides and both degrees at least half the common order yields an actual adjacency-respecting equivalence.
- `IsMatching.uncovered_even_iff_cut_parity` and `assignedLabel_fibers`: final passage from exact cut parity and exceptional saturation to uncovered old-core parity.

Still to prove and formally integrate:

1. Actual residual star-pool partition and the stronger combined `j_z+t<=h-r` count; the current joining-degree theorem alone does not state this stronger conclusion.
2. Actual-copy weighted support definitions, per-piece and total-weight bounds, and the dynamic two-resource grouping theorem preserving primary/reserve labels.
3. Common-free-color selection for the internal exceptional bundle.
4. Exact remaining star/free-palette equality with all prescribed copies removed.
5. The two Hall relations and exact assembly/preservation of every original copy.
6. Full native wrapper and quantitative final footprint/load/parity interfaces.

No remaining finite combinatorial obstruction was found under the explicit sufficient regime above. These six tasks remain prospective proof work; the current frozen checkpoint does not claim them.
