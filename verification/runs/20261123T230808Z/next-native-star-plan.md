# Next native step: weighted joining palettes and unpaired exceptional stars

**Status:** prospective read-only proof plan. This document adds no Lean theorem, compiler run, or verification claim. The five `Overfull/WeightedPalette/` source modules are frozen. Their existing contracts supply the weighted grouping and abstract Hall steps described below; native instantiation and the actual remaining-star assembly are still to be proved.

## 1. Current proved interface and intended next boundary

`Overfull.WeightedPalette.exists_star_weighted_matching_grouping` now groups actual edge-disjoint matching pieces of at most three copies. For at most two specified vertex/core resources it derives the local bound `6*b`, the total bound `D*h`, and the overloaded-color bound `13*D`; it retains the original `h` labels and bounds every whole grouped star weight by `h/8`. It preserves explicit seed certificates and makes each protected class exactly its prescribed seed union.

The theorem does not yet select the native circuit decomposition or prove its seed certificates, joining-cut parity, native reserve correspondence, or remaining-star/free-color balance. Those are the next concrete interfaces. The existing unweighted native palette theorems cannot simply be decorated with the new weight bounds: their existential colorings were not chosen by the weighted construction. Reuse their decomposition and reserve-selection arguments, with the new grouping theorem at the coloring choice.

Suggested implementation sequence, with each name below understood as a proposed module rather than an existing result:

1. **Weighted joining wrappers:** instantiate odd primary seeds and even empty seeds, prove their budgets, and construct actual `JoiningPalette` objects with accompanying star-weight bounds.
2. **Native weighted reserve wrappers:** select the actual surviving protected crossings or empty colors, retain the reserve indices, and apply the existing `reserveExtension` constructor.
3. **Actual exceptional incidence partition:** identify the residual star pools and any internal same-core exceptional bundle, prove the combined reserve bound, and establish exact free-color/remaining-copy balance.
4. **Sequential actual star coloring:** color the internal bundle, then apply the checked asymmetric Hall theorem to each remaining star in sequence and prove the resulting copy-level union certificates.

The first two steps produce a useful independently checkable milestone before the final star assembly.

## 2. Keep the original native objects and palette order

Use the following notation throughout a new native wrapper:

- `G` is the original host, `M` its original perfect-matching representative, and `R` its `BoundaryPacking G U₀ U₁ Z M r`.
- `H := residualGraph G N T` is the actual surviving host. Its edge type is the surviving-copy subtype; every new star, bundle, piece, and color class is a finset in this same type.
- `label := AssignedParts.assignedLabel G M U₀ U₁ Z` remains the original representative's assignment. Do not interpret `M` as a matching in `H`.
- For the unpaired branch, assume and retain an explicit `σ : Z → Fin 2` with `coarseSignature G M U₀ Z = some σ`.
- Use resource type `κ := Z`, with `z ↦ z.val` and `U_z := if σ z = 0 then U₀ else U₁`. Thus `Fintype.card κ = Z.card ≤ 2`, including the empty and one-exception cases without introducing dummy vertices.
- Let `h` be the actual residual regular degree, `s := r/2`, `b := ⌊a⌋₊`, and `D := ⌊max a ((h : ℝ)-r)⌋₊`.
- The weighted load target is always `W := h/8`, and the protected-label set `Q : Finset (Fin h)` has cardinality `s`.

The native quantitative regime is

```text
0 < h,  r ≤ h,  b ≤ D,  h-r ≤ D,  128*D ≤ h,
2*Q.card ≤ h,  Q.card = r/2.
```

No replacement of `h` by `h-s` is made in the weight target or total weight budget. Protected labels are forbidden only for surplus pieces. This permits primary seeds in protected colors in the odd case, and leaves them empty in the even case.

### Actual multiplicity input

The native residual already has retained cores of degree at least `h-a` and is `h`-regular. Use:

- `NativeReserve.poolCopies_disjoint_core`;
- `NativeReserve.pool_core_incidence_le_error`;
- `OneCore.complement_degree_le_error`;
- `WeightedPalette.exceptionCorePool_eq_edgesTo`;
- `Multigraph.mem_parallelEdges`, `parallelEdges_card_le_degree`, and `restrictEdges_edgesTo_card` as needed for the final count.

Every `z` lies outside both original cores. Every actual `z`-to-`v` copy with `v ∈ U_z` is therefore outside the embedded core. Its multiplicity is at most the actual complementary incidence at `v`, hence at most `a` as a real number and at most `b` naturally. Floor monotonicity gives `b ≤ D`. Since `r ≤ h`, the integral surplus `h-r` is also at most `D`. These are new wrapper derivations, not additional assumptions to impose on the original theorem's arbitrary host.

## 3. Derive one common capacity before the coloring

Write `n := Fintype.card V`, let `I` index all actual joining pieces, and set

```text
g := h - Q.card - 32*D
L := (n*D/2)/g + 1.
```

The checked `NativeReserve.weighted_palette_protected_margin` gives `Q.card + 32*D < h`, so `0 < g`. The checked `weighted_palette_protected_gap` gives `h ≤ 4*g`.

For both decompositions, the actual pieces are nonempty, pairwise edge-disjoint, and contained in `joiningCopies H label`. The native joining-degree estimate supplies `H.degreeOn (joiningCopies H label) v ≤ D`. Apply the existing

```lean
NativeReserve.twice_piece_count_le_order_mul_degree
```

to obtain `2*Fintype.card I ≤ n*D`, and hence `Fintype.card I ≤ n*D/2`. The existing generic division lemma

```lean
NativeReserve.natural_palette_capacity (n*D/2) g hg
```

gives `0 < L` and `n*D/2 ≤ L*g`. Consequently the exact capacity hypothesis of `exists_star_weighted_matching_grouping` holds. This route uses the actual piece count; it does not infer a whole-class bound from the size of each piece alone.

The old `uniform_protected_palette_budget` and the old native palette wrappers have the smaller exclusion term `6*D+s`. Their conclusions should remain unchanged. A new weighted budget wrapper should use the same integer-division proof pattern with `32*D+s`, or call `natural_palette_capacity` as above. The old capacity formula is not itself the new weighted capacity formula.

## 4. Odd assigned-core parity: injective primary seeds

The construction in `Overfull/ResidualPalette/NativeProtectedPalette.lean` already isolates the required native inputs.

1. Use `BoundaryPacking.exists_half_residual_crossing_reserve` to select a finset `A` of `r/2` actual surviving joining copies. It records each copy's membership in the original reserve and its quotient endpoints `s(0,1)`.
2. Use `exists_twoOddJoining_decomposition_with_reserved_primary` to construct a `FourOdd.TwoOddJoiningDecomposition H label 0 1 h` in which every selected crossing is a singleton primary piece. The hypotheses `A.card ≤ h` and `D ≤ h-A.card` follow from `A.card=s`, `2*s≤h`, and `128*D≤h`; the existing `half_reserve_palette_room` is also available once `6*D<h` is derived.
3. Index the total piece family by `I := P.primary ∪ P.surplus`, with each index carrying its original finset of copies. Let `Pseed` be the subtype-index finset of primary pieces. Then `Pseed.card = h`.
4. Set `c₀ := NativeReserve.primarySeed Pseed hP hh`. Use `primarySeed_injective` for injectivity on the seed set.
5. Let `Bseed ⊆ Pseed` be the indices of the selected singleton crossings, and set `Q := Bseed.image c₀`. Both the singleton-copy map and the seed color map are injective on their relevant sets, so `Q.card = Bseed.card = A.card = s`.

All explicit seed hypotheses of the new grouping theorem can now be derived:

- **Properness:** `pieceConflict` contains inequality of indices, so seed injectivity implies properness.
- **Count:** each color has at most one seed, and `1 ≤ L`.
- **Resource weight:** `P.primary_card_le` bounds each primary by two actual copies. `WeightedPalette.starWeight_le_four_mul` bounds each primary's resource weight by `4*b`. An injective seed color fiber has at most one member, so its sum is at most `4*b ≤ 6*b ≤ h/8`, using `NativeReserve.weighted_palette_item_bound`.

Apply `exists_star_weighted_matching_grouping` with these derived certificates and the actual residual resource weights. Its protected-color conclusion gives the exact seed union in each `j ∈ Q`. Since there is exactly one primary in each seed color, the color of a selected singleton crossing is exactly that singleton; no surplus piece has entered it.

### Recover joining-cut parity

Use `primarySeed_extension_unique` with the returned equality on seeds. Every color contains exactly one primary, while every other piece in that color belongs to `P.surplus`. Then use:

- `NativeReserve.cutOn_biUnion_mod_two_of_one_primary`;
- `P.primary_odd_cut_iff`;
- `P.surplus_even_cut`;
- the returned edge-disjointness and exact copy coverage.

These are the same parity facts used in `TwoOddJoiningDecomposition.exists_palette` and `.exists_protected_palette`. They remain valid after changing the greedy coloring because the weighted theorem preserves the seeds and only regroups the even-cut surplus pieces.

Construct a `NativeReserve.JoiningPalette H label h D L` with parity `if i=0 ∨ i=1 then 1 else 0`, and retain the additional conclusion

```text
∀ z ∈ Z, ∀ j : Fin h,
  starWeight H z U_z (C.classes j) ≤ h/8.
```

The star-weight certificate can accompany the existing structure; no change to the frozen `JoiningPalette` definition is necessary.

## 5. Even assigned-core parity: empty seeds and prescribed empty labels

Reuse the selection pattern in `Overfull/ExceptionalPalette/EvenNative.lean`:

1. Choose injective `q : Fin s → Fin r` and `f : Fin s → Fin h`, using `s=r/2≤h/2<h` when `h>0`.
2. Let `Q := univ.image f`, so `Q.card=s`.
3. Construct `FourOdd.EvenJoiningDecomposition H label` using `exists_evenJoining_decomposition` and the native all-even assigned-fiber parity.
4. Index `P.parts` directly, take `Pseed=∅`, and use any default `c₀ : I → Fin h` supplied by `hh`.

Seed properness, count, and resource weight are vacuous or zero; `paletteWeight_empty` gives the last certificate. Apply the same actual grouping theorem on all `h` labels with `Q` forbidden for every piece. The exact protected seed-union conclusion becomes `C.classes j=∅` for `j∈Q`.

Use `NativeReserve.cutOn_biUnion_even` and `P.even_cut` to recover even parity in every assigned-fiber cut. All matching, disjointness, cover, footprint, vertex-load, and whole-class star-weight conclusions come from the actual grouping theorem and `P.cover`.

This is a direct weighted all-even construction. It avoids transporting a theorem on `h-s` colors whose numeric target might otherwise be confused with `(h-s)/8`.

## 6. Insert the actual protected reserve without losing the weighted certificate

For odd parity, use the selected crossing's original-reserve membership to recover injective reserve indices `q`. The correspondence proof in `exists_native_reserved_palette` can be reused with the newly constructed weighted `C`; its only grouping-specific input is the exact protected singleton equality.

For even parity, retain the explicit `q` and `f` above. Use these existing trace theorems:

- `BoundaryPacking.residualBoundary_joining_singleton` in the odd case;
- `BoundaryPacking.residualBoundary_joining_empty` in the even case;
- `BoundaryPacking.residualBoundary_matching`;
- `BoundaryPacking.residualBoundary_disjoint`;
- `BoundaryPacking.residualBoundary_card_le`;
- `BoundaryPacking.residualBoundary_covers_exceptional`.

Apply the existing `NativeReserve.reserveExtension` to obtain a `ReserveExtension C B f (Z.card+1)`. It already provides exact prescribed classes, unchanged other classes, matching, disjointness, exact coverage, exact joining trace, and exact assigned-fiber cut equality.

Keep the original joining palette `C` and the reserve extension as separate objects. Its extended family contains internal reserve copies and is not itself a `JoiningPalette`. No weighted bound on all extended protected classes is needed for Hall: every protected label will be excluded from all remaining star palettes. For `j∉Q`, `ReserveExtension.unchanged` identifies the extended class with `C.classes j`, preserving the checked whole-class star bound there.

In the unpaired branch, each selected reserve boundary has exactly one actual assigned-core star copy at every exception. To establish this, use `BoundaryPacking.sameSignature`, `AssignedParts.signature_some_uses_exceptionCorePool`, `exceptionCorePool_usage_eq_assignment`, and `compressedBoundary_retains_exceptional`. Matching gives the corresponding upper bound of one. Transport the copies to `H` with `residualBoundary_image` and the survival/disjointness certificates.

The helper `compressed_inter_exception_pool` in `NativeReserve/RoundedPools.lean` is private and should not be treated as a public API. Either prove a small public equality from `compressedBoundary_retains_exceptional`, or use the public `compressedBoundary_pool_usage` when its distribution/sample context is already available.

## 7. The exact incidence partition still needed

For an unpaired exception `z`, define in the residual copy type:

```text
J   := joiningCopies H label
S_z := AssignedParts.exceptionCorePool H z U_z
B   := H.internalOn univ Z \ J
```

Here `B` is precisely the internal exceptional bundle whose endpoints have the same assigned label. If the two exceptions are assigned to different cores, all their mutual copies lie in `J`, so `B=∅`. With zero or one exception, `B=∅` by looplessness. With two distinct exceptions assigned to the same core, every copy in `B` has those two endpoints, and each is counted once at each exception.

Prove the following actual set identity, with pairwise-disjoint terms:

```text
H.incidenceEdges z =
  (H.incidenceEdges z ∩ J) ∪ S_z ∪ (H.incidenceEdges z ∩ B).
```

Useful APIs include `AssignedParts.assignedLabel_fibers`, `coarseSignature_eq_some_iff`, `pairPart_eq_empty_of_internal_eq_empty`, `WeightedPalette.exceptionCorePool_eq_edgesTo`, `Multigraph.edge_eq_otherEnd`, and `NativeReserve.pairFiberCopies_incident`. A general preliminary lemma identifying nonjoining incidence with copies into the vertex's label fiber would simplify the proof:

```text
H.incidenceEdges z \ joiningCopies H label =
  H.edgesTo z (labelShore label {label z}).
```

This displayed identity is a proposed new lemma. The existing `pairFiberCopies_eq_nonjoining_incidence` assumes an entire two-vertex label fiber, so it does not apply to a fiber containing an old core.

Let `j_z := H.degreeOn J z` and `t_z := H.degreeOn B z`. Regularity and the disjoint partition give

```text
j_z + S_z.card + t_z = h.
```

All `r` reserve boundaries survive, are edge-disjoint, and, in the unpaired branch, each supplies one distinct member of `S_z`. Hence `r ≤ S_z.card`, and therefore

```text
j_z + t_z ≤ h-r ≤ D.
```

This combined bound is essential. `BoundaryPacking.residual_exceptional_joining_degree` currently proves only `j_z≤h-r`; it does not supply the combined statement by itself. Two separate bounds of size `D` must not be silently substituted for this exact incidence count.

In particular, **the bound `t_z≤b` does not follow from the old-core multiplicity bound**: both endpoints of a bundle copy are exceptions. The preferred route is the actual reserve/partition argument above, which proves `j_z+t_z≤h-r≤D` without any bound on exception-to-exception multiplicity by `b`. That route remains a new Lean obligation; no currently checked theorem is being cited as already giving the combined inequality.

The public `NativeReserve.poolCopies_pairwiseDisjoint` and `poolCopies_specialEnds` give useful separation facts: the assigned star pools are distinct actual-copy pools, and a star copy has precisely its named exceptional endpoint in `Z`.

## 8. Color the same-core exceptional bundle first

Only the case of two exceptions assigned to the same core has a new internal bundle. Write its size as `t`; then `t_z=t` at both endpoints.

The original joining palette has exactly `j_z` used colors at `z`, by `JoiningPalette.usedColors_card`. Its protected odd classes are old-core crossings and its protected even classes are empty, so all protected labels are free at every exception before reserve insertion. Select distinct colors for the `t` actual bundle copies outside:

```text
Q ∪ joiningUsedColors(z₁) ∪ joiningUsedColors(z₂).
```

The two combined incidence inequalities give

```text
t + j_z₁ + j_z₂ ≤ 2*D ≤ h-s.
```

Thus the common available set has at least `t` colors. A finite injection assigns the distinct actual parallel copies to distinct colors. The existing `pairColorClass_card_le_one`, `pairColorClass_isMatching`, `pairColorClass_support_subset`, `pairColorClass_disjoint`, and `pairColorClass_cover` can be reused after identifying `B` with the appropriate pair-copy pool. The existing `JoiningPalette.exists_pair_bijection` requires a genuine two-vertex label fiber and should not be applied to a core-containing assigned fiber.

Each added bundle copy touches only the two exceptions. Selected colors were free at both, no protected class changes, and no old-core endpoint obstruction is introduced. The bundle is internal to one assigned fiber, so every assigned-fiber cut is unchanged exactly.

## 9. Establish remaining-star/free-color balance by a generic family identity

A useful next lemma should apply to any family `F : Fin h → Finset E` of pairwise edge-disjoint actual matchings in an `h`-regular host. Define its free colors at `z` by absence of `z` from the class support. Then prove

```text
freeColors(F,z).card =
  (H.incidenceEdges z \ univ.biUnion F).card.
```

The proof is already modeled by `JoiningPalette.usedColors_card` and `freeColors_card_add_degree`: use `removed_degreeOn`, the 0/1 incidence of a matching at a vertex, exact edge-disjointness, and the regular degree. This generalization applies after reserve and bundle insertion; the current `JoiningPalette` free-color API applies only to the original joining family.

Let `F₀` be the family after protected reserve and full internal bundle insertion. Let `P_z` be the selected reserve-star copies at `z`. Their cardinality is exactly `s`, using the injective selected reserve indices and one star copy per boundary. Prove the actual set equality

```text
H.incidenceEdges z \ univ.biUnion F₀ = S_z \ P_z.
```

The two sides then have equal cardinality automatically. Call the remaining copy set `A_z` and the exact free-color set `F_z`. The partition additionally gives

```text
|A_z| = |F_z| = h-s-j_z-t_z ≥ h-s-D.
```

All protected colors, joining-used colors, and bundle-used colors removed in this formula must be shown pairwise disjoint at the relevant exception. The reserve and bundle constructions above provide these facts. The exact set identity is preferable to assuming or merely estimating this balance.

## 10. Sequential Hall uses the checked asymmetric bound

For `e : A_z` and `j : F_z`, use the relation that the old-core endpoint `H.otherEnd z e` is unoccupied in the current class at `j`. The exceptional endpoint is already free by membership in `F_z`.

For the first star:

- An actual copy has at most `D` forbidden colors, by the original joining palette's vertex-load bound.
- A free color blocks at most `W=h/8` actual star copies, by the new weighted joining certificate and restriction to `A_z`.

The protected labels are absent from `F_z`; the bundle uses no old-core endpoints and is absent at colors free at `z`. Thus these bounds genuinely refer to the unchanged original joining classes on the relevant colors.

After coloring the first star bijectively, construct the second star relation using the updated actual family:

- `poolCopies_specialEnds` shows that the first star does not touch the other exception, so that exception's free-color set and its cardinality remain unchanged.
- At a fixed old-core endpoint `v`, the first star uses at most `(H.parallelEdges z₁ v).card` colors, hence at most `b` when both exceptions have the same assigned core. With different assigned cores the extra obstruction is zero.
- One color receives at most one first-star copy. Its old-core endpoint blocks at most `b` copies of the second star.

Therefore the second relation has row obstruction at most `D+b` and column obstruction at most `W+b`. These are actual-copy bounds, not bounds obtained by replacing multiplicity with a vertex count.

For the last column estimate, prove explicitly that the support of one first-star copy meets the second old core in at most one vertex: its exceptional endpoint lies outside both cores. Then `starWeight_le_inter_support_mul` gives `b`. Applying only the generic two-endpoint support estimate would give `2*b` and would lose this sharper certificate.

The checked theorem

```lean
Overfull.CircuitPatterns.exists_star_equiv_of_conflict_bounds
```

already gives the required bijection once the exact sets, balance, lower bound, and two conflict counts are proved. Its underlying `exists_equiv_of_asymmetric_conflicts` needs only the non-strict condition `a+b≤m`. In the current regime, `star_hall_margin` proves

```text
(D+b) + (h/8+b) ≤ h-s-D ≤ m.
```

There is no need to impose the stronger pair of separate half-degree inequalities or introduce real-number half-degree casts. The checked constants are sufficient; no optimization of `128` or `13` is asserted here.

### Conditional fallback if a weaker bundle bound is proved first

The preferred native route above gives the stronger lower bound `m≥h-s-D`. If a future intermediate lemma instead proves only `t_z≤D`, then combining it with the existing `j_z≤D` gives only `m≥h-s-2*D`. If the additional, stronger hypothesis `t_z≤b` were independently proved in a special case, it would give `m≥h-s-D-b`. Neither bundle bound is presently supplied by old-core multiplicity alone.

Both weaker bounds still have enough numerical room under the current regime. With `W=h/8`, `b≤D`, `2*s≤h`, and `128*D≤h`, one has `s+5*D+W≤h`. Consequently

```text
(D+b)+(W+b) ≤ h-s-2*D
(D+b)+(W+b) ≤ h-s-D-b.
```

For example, `s≤h/2`, `5*D≤5*h/128`, and `W≤h/8` bound their sufficient left-hand budget by `85*h/128≤h`. These are prospective arithmetic derivations, not additional checked lemmas. Such a fallback would apply the already checked general `exists_equiv_of_asymmetric_conflicts` after proving the new arithmetic and actual size bound. It must not apply `exists_star_equiv_of_conflict_bounds` without that theorem's explicit stronger hypothesis `h-s-D≤m`. No frozen source needs changing for this conditional route.

After each bijection, prove actual matching unions, copy disjointness across colors, exact newly colored sets, and preserved protected classes. The second bijection must be constructed after the first, rather than choosing two independent star colorings and assuming compatibility.

## 11. Final interface and uniform parameter order

Once both stars have been assembled, every exceptional vertex is covered exactly once in every color, and every actual joining or exceptional-incident copy is colored. The protected reserve assignments remain exact. All newly added copies are internal to their assigned fibers, so the original cut sets, and therefore their parity, remain unchanged. Use `Multigraph.IsMatching.uncovered_even_iff_cut_parity` and `AssignedParts.assignedLabel_fibers` to turn this into even uncovered old-core order.

A color gains at most two exceptional copies and four support vertices relative to its original joining class. A bundle color already covers both exceptions, so it does not also receive their two star copies. Thus the intended final bounds are `3*L+2` copies and `6*L+4` support vertices. At an old-core vertex, every colored boundary copy lies in the actual retained-core complement, so `pool_core_incidence_le_error` can give the stronger final old-core load at most `a`, or `b` naturally. The large exceptional load `h` should not be confused with the old-core load bound.

The existing

```lean
NativeReserve.exists_uniform_native_reserve_completion_with_small_joining
```

chooses surviving robustness before every requested error tolerance. It supplies the residual, `r≤h`, `k/30≤r`, original density `α*n≤k`, retained core degree at least `h-a`, and `max a (h-r)≤δ*n`. Hence `α*n/30≤h` and `D≤δ*n`.

Choose the requested tolerance before constructing the host, with

```text
δ ≤ α/3840,
δ ≤ ε*α/720.
```

Then `128*D≤h`. The weighted gap satisfies `g≥h/4≥α*n/120`, and the same division estimate as in the existing protected-budget proof gives

```text
6*L ≤ (360*δ/α)*n + 6.
```

For joining classes alone, `n≥12/ε` gives `6*L≤ε*n`. For the eventual classes enlarged by exceptional copies, retain the additional four vertices: `n≥20/ε` gives `6*L+4≤ε*n`. A bound relative to an original core uses the global tolerance `c*ε_core` and the existing lower bound `c*n≤|U_i|`.

These new numeric wrappers still require formal proof. The parameter order is compatible with the existing uniform theorem because robustness is fixed before the smaller requested `δ`, and the original error/order thresholds are chosen afterward.

## 12. Remaining scope and obstruction assessment

No additional finite combinatorial obstruction was found under the displayed sufficient regime. The weighted grouping and asymmetric Hall ingredients are now proved, but the exact native composition has not yet been implemented. Its main remaining proof obligations are:

- derive native multiplicity, primary seed, common capacity, and parity certificates for the new weighted choice;
- preserve actual residual reserve/star membership through the original-to-residual subtype maps;
- prove the disjoint incidence partition and combined `j_z+t_z≤h-r` bound;
- prove the remaining-copy/free-color set balance and both sequential actual conflict counts;
- assemble all actual-copy matching, coverage, cut, footprint, and old-core load properties.

This plan addresses the unpaired-signature star branch. The existing exceptional-pair-fiber results are separate, and complete native pair/reserve composition still needs its own integration where required. Robust core completion, final factorization/reconstruction, the full Corollary 4.6, and the main theorem are not established by the current weighted milestone or by this plan.
