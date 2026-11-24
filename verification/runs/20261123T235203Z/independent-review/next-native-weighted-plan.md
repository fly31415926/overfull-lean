# Prospective native weighted joining and exceptional-star assembly

**Status: proof design only.** No theorem in this document was implemented, compiled, or audited during the independent review. This plan describes a concrete next stage after the eight frozen `Overfull.NativeStar` modules. The current source review, genuine strict target receipts, and final checker metadata comparison are recorded separately in `integrity-review.md` and `integrity-review.json`.

Reviewed worktree: `/workspace/scratch/0f64d20031b0/overfull-native-star`. Reviewed run: `20261123T235203Z`. The preceding verified local checkpoint is `af8dca22ef67d66d0de3f6d89954d31f06a4d2fa`. The final preservation checker is `cc66c9a1d5ee609a349a79c834f017d592c8d6c74341a53f74e9ea8298bbb8bf`. These identities do not establish that the new run passed its complete audit or was published.

## 1. The next proof bottleneck

The existing weighted grouping theorem already constructs matching joining classes with actual blocked-copy weight at most `h/8`. The new native-star theorems already construct the actual reserve-to-star injection, the exact remaining copy/color balance, and a sequential two-star extension. What remains is to connect those results with **one original palette `Fin h`**, explicit protected seed traces, and the actual reserve-plus-bundle initialized family.

The central bridge should prove that, for every color available to a particular star, the initialized family has exactly the same class as the weighted joining palette. This equality transfers both the restricted row-conflict budget and the whole-class star-weight budget. It avoids an unjustified global load claim after protected boundaries have been installed.

The prospective native wrapper covers the **unpaired signature** `coarseSignature G M U₀ Z = some σ`, with at most two exceptional vertices. The older paired-exception construction is a separate branch. Neither this plan nor the current eight modules completes full two-core Corollary 4.6, robust matching completion, or the main theorem.

## 2. Fixed objects and quantitative contract

Use the original representative and assignment throughout. The representative need not survive in the residual host.

| Symbol | Exact object and role |
| --- | --- |
| `H` | `NativeReserve.residualGraph G N T`, whose edge type is `{e : E // e ∉ removedCopies N T}`. |
| `label` | `AssignedParts.assignedLabel G M U₀ U₁ Z`, computed from the original `G,M`. |
| `W z` | `if σ z = 0 then U₀ else U₁`; the old core assigned to `z : Z`. |
| `R` | `BoundaryPacking G U₀ U₁ Z M r`; its compressed boundaries are pairwise disjoint, while their parent matchings need not be. |
| `K,q,f` | A finite selected index set, an injective assignment to original reserve indices, and an injective assignment to colors; `s = K.card`. A finite subtype may make both maps globally injective. |
| `Qcol` | `K.image f`, the protected **color** set. Its cardinality must be proved equal to `s`. |
| `J` | `FourOdd.joiningCopies H label`. |
| `C` | A `NativeReserve.JoiningPalette H label h D L parity`, returned together with the new weighted certificates. |
| `Jcol z` | `NativeStar.joiningUsedColors C z.val`. |
| `S z` | `AssignedParts.exceptionCorePool H z.val (W z)`, containing actual residual copies. |
| `P z` | `(K.biUnion (fun i => R.residualBoundary N T (q i))) ∩ S z`, the actual selected reserve copies in that star. |
| `A z` | `S z \ P z`, the remaining actual star pool. |
| `B` | The actual internal exceptional bundle; for two exceptions with equal assigned labels it is `NativeReserve.pairFiberCopies H x y`, and otherwise the relevant internal pool is empty. |
| `Bcol` | `univ.image c` for an injective assignment `c : B → Fin h`. |
| `F z` | `NativeStar.remainingStarColors Qcol (Jcol z) Bcol`, namely the complement of these three used-color sets in `Fin h`. |

The decomposition-level weighted wrappers should take actual host incidence bounds and the following natural-number regime:

```text
0 < h, 0 < L,
b ≤ D, 128*D ≤ h, 2*s ≤ h,
∀ v, H.degreeOn J v ≤ D,
Fintype.card V * D ≤ 2*L*(h-s-32*D).
```

For the native resource index use `κ := Z`, the subtype of actual exceptional vertices, with `z := Subtype.val` and `U := W`; `Fintype.card Z = Z.card ≤ 2` discharges the resource-count premise. For each of these resources `(z,W z)`, require `H.degree z ≤ h` and `∀ v ∈ W z, (H.parallelEdges z v).card ≤ b`. The native wrapper derives the former from residual `h`-regularity, and also takes the original partition, reserve avoidance, original unpaired signature, residual no-overfullness, and `h-r ≤ D` needed by the existing native balance theorem.

For the eventual sequential assembly, use a sufficiently explicit multiplicity hypothesis:

```text
∀ z ∈ Z, ∀ v ∈ U₀ ∪ U₁, (H.parallelEdges z v).card ≤ b.
```

This implies the weighted grouping requirements and the **cross-core** requirement of `exists_two_star_extension_on_available`: the first exceptional vertex needs a multiplicity bound into the second star's assigned core, even when that is not its own assigned core. A bound only on each star's own assigned core does not directly supply that premise. If the input estimate lives in `G`, prove its transfer to `H` by the injective residual-edge subtype map on parallel copies; do not assume this transfer without a lemma.

Existing arithmetic already handles the key natural-number truncations. In `Overfull/WeightedPalette/Loads.lean`, namespace `Overfull.NativeReserve`:

| Existing declaration | Available conclusion |
| --- | --- |
| `weighted_palette_item_bound` | `6*b ≤ h/8` from `b≤D` and `128*D≤h`. |
| `weighted_palette_protected_margin` | `s+32*D < h` when `0<h` and `2*s≤h`. |
| `weighted_palette_protected_gap` | `h ≤ 4*(h-s-32*D)`. |
| `weighted_palette_hall_bounds` | `2*(D+b) ≤ h-s-D` and `2*(h/8+b) ≤ h-s-D`. |

Use `NativeReserve.twice_piece_count_le_order_mul_degree` from `Overfull/ResidualPalette/PaletteGrouping.lean` to derive `2*Fintype.card I ≤ n*D` for the actual nonempty, disjoint joining pieces. Together with the proposed incidence budget this gives `Fintype.card I ≤ L*(h-s-32*D)`. The older capacity wrappers use a `6*D` gap; their proof pattern is reusable, but their conclusion is not the required new budget.

## 3. Weighted all-even joining wrapper

Proposed declaration name, not currently present: `EvenJoiningDecomposition.exists_star_weighted_palette_avoiding_colors`.

Start with `P : FourOdd.EvenJoiningDecomposition H label`, a prescribed `Qcol : Finset (Fin h)`, at most two resources, and the quantitative conditions above with `s=Qcol.card`. Return

```text
∃ C : JoiningPalette H label h D L (fun _ => 0),
  (∀ j ∈ Qcol, C.classes j = ∅) ∧
  (∀ resource j, starWeight H (z resource) (U resource) (C.classes j) ≤ h/8).
```

This contract deliberately retains `Fin h`. The old `EvenJoiningDecomposition.exists_palette_avoiding_colors` in `Overfull/ExceptionalPalette/EvenColors.lean` is an unweighted template using a palette of order `h-Qcol.card`. Its construction cannot simply be cited as a weighted theorem with the original threshold `h/8`.

The proof should use the exact decomposition interface already used by `EvenJoiningDecomposition.exists_palette` in `Overfull/ResidualPalette/JoiningGrouping.lean`:

1. Let `I := P.parts` and `M i := i.val`. Obtain matching, copy cardinality at most three, disjointness, nonemptiness, and coverage from `P.matching`, `P.card_le`, `P.disjoint`, `P.nonempty`, and `P.cover`.
2. Apply `WeightedPalette.exists_star_weighted_matching_grouping` with seed set `∅`, any default `I → Fin h`, and the actual protected color set `Qcol`. All seed count, seed properness, and seed weight premises are empty-set facts.
3. The returned protected-seed union is empty. Its actual whole-class `starWeight` conclusion supplies the requested certificate for every resource and every color.
4. Prove each grouped fiber cut even with `NativeReserve.cutOn_biUnion_even` and `P.even_cut`; construct the existing `JoiningPalette` structure without altering that structure.

The assigned-host lift can follow `AssignedParts.exists_assigned_even_joiningPalette_avoiding_colors_in_host`: use `FourOdd.exists_evenJoining_decomposition`, call the new weighted wrapper, transport the parity function with `JoiningPalette.congr_parity`, and obtain assigned-fiber uncovered evenness with `assigned_joiningPalette_uncovered_even`.

## 4. Weighted odd joining wrapper with exact seeds

Proposed declaration name, not currently present: `TwoOddJoiningDecomposition.exists_star_weighted_protected_palette`.

Use `P : FourOdd.TwoOddJoiningDecomposition H label a b h` and a protected set of primary **pieces** `Qpieces ⊆ P.primary`. Preserve the complete ordinary `JoiningPalette` result, return actual whole-class weight at most `h/8` for every resource, and return the protected singleton/whole-piece class witnesses. Prefer also returning the seed coloring or explicit protected-label map, so the native layer need not reconstruct information that the proof already has.

The old `TwoOddJoiningDecomposition.exists_protected_palette` in `Overfull/ResidualPalette/ProtectedGrouping.lean` supplies the concrete indexing template:

```text
I := P.primary ∪ P.surplus
M : I → Finset E := Subtype.val
A := univ.filter (fun i => i.val ∈ P.primary)
B := univ.filter (fun i => i.val ∈ Qpieces)
c₀ := NativeReserve.primarySeed A hA hh
Qcol := B.image c₀
```

Derive `A.card=h`, `B.card=Qpieces.card`, and `B⊆A` before invoking the weighted theorem. `primarySeed_injective` proves injectivity on all primary indices and hence `Qcol.card=B.card`.

The seed obligations have short, concrete proofs:

| Obligation | Proof source and necessary detail |
| --- | --- |
| Proper primary seed | Injectivity on `A`; `pieceConflict` includes distinct indices. |
| At most `L` seeded pieces in a color | Each seed fiber has at most one index, followed by `1≤L`. |
| Seed weight at most `h/8` | Reduce `paletteWeight A c₀ … j` to its unique primary contribution. Use `P.primary_card_le`, `WeightedPalette.starWeight_le_four_mul`, and `4*b≤6*b≤h/8`. |
| Ordinary piece cardinality at most three | Primary pieces have at most two copies; surplus pieces have at most three. |
| Capacity | Actual nonempty-piece incidence count with the new `32*D` protected gap. |

The seed weight is part of the total resource budget; it cannot be omitted on the grounds that only surplus pieces are added greedily. `NativeReserve.primarySeed_extension_unique` gives exactly one primary in each color after extension. Combine it with `cutOn_biUnion_mod_two_of_one_primary`, `P.primary_odd_cut_iff`, and the surplus even-cut property to retain the required parity at `a,b`.

The weighted theorem's protected-color equality is

```text
groupedCopies M c j = (A.filter (fun i => c₀ i = j)).biUnion M.
```

For `j∈Qcol`, seed injectivity reduces that union to precisely its protected primary piece. This proves complete class preservation, including the forced singleton case, rather than merely preservation of one selected copy inside a larger class.

## 5. Lift both parity branches to actual reserve traces

For the odd branch, follow the source construction of `NativeReserve.exists_native_protected_joiningPalette` in `Overfull/ResidualPalette/NativeProtectedPalette.lean`, replacing only its final unweighted grouping call with the new weighted wrapper:

1. Derive assigned-fiber parity from the original matching using `assignedLabel_parity_eq_core_crossing` and `corePart_card_parity`.
2. Obtain the actual residual crossing set of size `r/2` from `BoundaryPacking.exists_half_residual_crossing_reserve` in `Overfull/ResidualPalette/NativeReservedCrossings.lean`.
3. Use `NativeReserve.exists_twoOddJoining_decomposition_with_reserved_primary` in `Overfull/ResidualPalette/ReservedPrimary.lean` to make those exact copies singleton primary pieces. Discharge its reserve-size and degree-room conditions from the stronger weighted quantitative regime.
4. Run the weighted odd wrapper. Preserve both original reserve membership and exact singleton class equality. Choose reserve indices `q` and color labels `f` as in `NativeReserve.exists_native_reserved_palette` in `Overfull/ExceptionalPalette/ReserveNative.lean`.
5. Obtain the exact trace for every selected index from `BoundaryPacking.residualBoundary_joining_singleton`. Distinct selected original crossings yield injective reserve and color maps, as in the existing source proof.

For the even branch, choose the desired `s` distinct reserve indices and `s` distinct colors explicitly; the standard next target is `s=r/2`. The corresponding reserve/cardinality inequalities must be discharged. Apply the weighted all-even wrapper with this exact protected color set. Then `BoundaryPacking.residualBoundary_joining_empty` in `Overfull/ExceptionalPalette/ReserveCopies.lean` and the returned empty protected joining classes give the same trace interface.

Both branches should therefore return a common package containing `C`, its resource weights, selected actual reserve indices, injective colors, exact counts, and

```text
∀ i, R.residualBoundary N T (q i) ∩ J = C.classes (f i).
```

Retain the actual-copy type and trace equality in the output. A mere `s`-element color set plus a count of selected boundaries is insufficient for protected freeness, preservation, and the native balance theorem.

## 6. Reserve-plus-bundle initialization

First define `Rclass := NativeReserve.reserveClasses C boundary f`, where `boundary i := R.residualBoundary N T (q i)`. Existing declarations in `Overfull/ExceptionalPalette/ReserveInsertion.lean` prove the needed reserve properties:

| Existing declaration | Use |
| --- | --- |
| `reserveClasses_at` / `reserveClasses_other` | Exact protected classes and unchanged other classes. |
| `reserveClasses_matching` / `reserveClasses_disjoint` | Matching and copy disjointness from actual boundary matching/disjointness. |
| `reserveClasses_joining` / `reserveClasses_contains_original` | Exact joining trace and inclusion of every original joining class. |
| `reserveClasses_cut_eq` / `reserveClasses_cut_parity` | Preserve every assigned-fiber cut. |
| `reserveClasses_cover` | Exact joining-plus-selected-boundaries union. |

The native boundary certificates come from `BoundaryPacking.residualBoundary_matching`, `residualBoundary_disjoint`, `residualBoundary_card_le`, `residualBoundary_covers_exceptional`, and `residualBoundary_uncovered_even` in `ReserveCopies.lean`.

For two distinct exceptions with the same assigned label, use `NativeStar.exists_native_common_bundle_coloring` in `Overfull/NativeStar/NativeBalance.lean`. It identifies both internal pools with the same actual `pairFiberCopies H x y` and constructs an injection avoiding `Qcol`, `Jcol x`, and `Jcol y`. Its `4*D≤h` condition follows from `128*D≤h`. The proof derives `j_z+t≤D` from the reserve injection; it imposes no bound `t≤b` on exceptional-to-exception multiplicity.

Define the initialized family by

```text
Cinit j := Rclass j ∪ NativeReserve.pairColorClass H x y c j.
```

The general `pairColorClass_subset`, `pairColorClass_card_le_one`, `pairColorClass_isMatching`, `pairColorClass_support_subset`, `pairColorClass_disjoint`, and `pairColorClass_cover` in `Overfull/ExceptionalPalette/PairColoring.lean` are suitable building blocks. The older `JoiningPalette.pairExtended_isMatching` and related whole-pair completion theorems require the **entire assigned fiber** to be `{x,y}`. They are not directly applicable when that fiber also includes an old core. Prove the small union lemmas using the newly obtained simultaneous endpoint freeness and `pairColorClass_support_subset` instead.

The initialization proof must explicitly establish:

- Bundle classes are empty outside `Bcol`, and `Bcol` is disjoint from `Qcol` and both joining-used color sets.
- A bundle-used unprotected color has `Rclass j=C.classes j`, so both bundle endpoints are free there.
- No selected unpaired reserve boundary contains an internal exceptional-bundle copy. Use the same-signature parent matching and the exact assigned-star incidence identity, or unfold the compressed boundary into its exceptional incidences and parity-selected core crossing.
- Every remaining star pool is copy-disjoint from the base family. Its disjointness from joining and internal pools follows from `NativeStar.assigned_incidence_partition`; its disjointness from selected reserve copies follows from the definition of `P z`.
- The initialized class is a matching; different initialized classes are copy-disjoint; its exact union is joining copies, selected boundaries, and the internal bundle.

For two exceptions with different assigned labels, `NativeStar.exceptionInternalPool_pair_eq_empty` gives the empty internal pools; their mutual edges are joining copies already handled by `C`. For one or zero exceptions, use an empty bundle and the corresponding one-star or no-star branch. Keep those cardinality cases explicit.

## 7. The decisive available-color bridge

Proposed bridge statement, not currently proved:

```text
∀ z, ∀ j ∈ F z, Cinit j = C.classes j.
```

Membership in `remainingStarColors` gives `j∉Qcol`, `j∉Jcol z`, and `j∉Bcol`. The first fact invokes `reserveClasses_other`; the third makes the bundle class empty. The second proves exceptional-center freeness. Consequently:

```text
∀ v ∈ W z,
  ((F z).filter (fun j => v ∈ H.edgeSupport (Cinit j))).card ≤ D,
∀ j ∈ F z, starWeight H z.val (W z) (Cinit j) ≤ h/8,
∀ j ∈ F z, z.val ∉ H.edgeSupport (Cinit j).
```

For the first inequality, rewrite by the bridge and bound the restricted filter by the full-color support filter controlled by `C.vertex_load_le`. The second follows from the weighted wrapper's whole-class certificate. Do not assert global initialized load at most `D`: protected boundaries can occupy old-core vertices in excluded colors, and those colors need not satisfy the original class weight bound either.

Call `NativeStar.native_remaining_star_balance` separately at each exception with the same actual selected reserve family. It proves, rather than assumes, `|P z|=s`, `|Qcol|=s`, `|Bcol|=|B|`, and

```text
|A z| = h-s-|Jcol z|-|B| = |F z|,
h-s-D ≤ |A z|.
```

Its trace premise also derives the disjointness of protected colors from joining-used colors via `protected_joining_color_free_of_reserve_trace`.

## 8. Sequential native star contract

For `Z={x,y}` with `x≠y`, instantiate `NativeStar.exists_two_star_extension_on_available` in `Overfull/NativeStar/TwoStars.lean` with base `Cinit`, pools `A x,A y`, palettes `F x,F y`, and old-core sets `W x,W y`. These core sets may coincide; the theorem does not require them to be disjoint. What it requires is that each exception lie outside the other star's old core, supplied by the original core/exception partition.

The exact inputs to discharge are:

| Sequential premise | Native source |
| --- | --- |
| Actual pool inclusions | `A z = S z \ P z`. |
| Pool/color equalities and lower bounds | `native_remaining_star_balance`. |
| Matching, pairwise copy disjointness, base/pool disjointness | Reserve-plus-bundle initialization. |
| Exceptional-center freeness | `F z` excludes joining, protected, and bundle-used colors. |
| Available-only row load `≤D` and weight `≤h/8` | The bridge in Section 7. |
| First-center multiplicity into the second core | The explicit cross-core multiplicity bound from Section 2. |
| Second-center multiplicity into the second core | Its ordinary resource multiplicity bound. |

The theorem then constructs actual equivalences of pools with palettes and derives matching, pairwise copy disjointness, exact coverage, unchanged unavailable colors, exceptional coverage on each available palette, and placement of every newly assigned copy. Its second call uses derived `D+b` and `h/8+b` budgets after the first insertion. No new Hall theorem is needed.

For the one-exception branch, call `exists_star_extension_on_available` with the same actual initialization and balance. Its larger allowed bounds `D+b` and `h/8+b` follow immediately from the initial `D` and `h/8` bounds. The zero-exception branch performs no star insertion.

## 9. Final preservation, support, and load conclusions

The complete wrapper should return the exact final copy family, the initial joining palette, protected reserve maps, the concrete bundle assignment, and the concrete star assignments. Include matching/disjointness, exact prescribed boundary classes, assigned-fiber cut parity, and coverage of every exceptional vertex in every color.

For exceptional coverage in a fixed color, split its membership among `Qcol`, `Jcol z`, `Bcol`, and `F z`. The respective witnesses are the prescribed boundary, the original joining class, the assigned bundle copy, and the star equivalence. These disjoint used sets and their complement exhaust the original `Fin h`.

All newly added star copies are internal to their original assigned fiber, by `NativeStar.unpaired_assignment_fiber_bounds`. `NativeStar.starExtended_cut_eq` therefore preserves every fiber cut through both star insertions. Reserve replacement preserves cuts by `reserveClasses_cut_eq`; the same-label bundle is internal too. Combine final matching and unchanged cut parity to recover even uncovered assigned parts. Since all exceptions are covered, reduce these to the uncovered old-core parity conditions needed for later completion.

### Exact support-case argument

The current two-star theorem gives growth by at most two copies and four support vertices **relative to `Cinit`**. To obtain the sharper intended bound relative to the earlier joining palette, prove the following three color cases explicitly:

| Color case | Exact reason | Final copy/support bound |
| --- | --- | --- |
| `j∈Qcol` | Bundle and both stars avoid this color; final class is exactly its prescribed residual boundary. | Copies `≤Z.card+1≤3`; support `≤6`. |
| `j∉Qcol` and `j∈Bcol` | Reserve replacement leaves the joining class unchanged; injectivity adds at most one bundle copy; both star palettes exclude `j`. | Copies `≤3L+1`; support `≤6L+2`. |
| `j∉Qcol∪Bcol` | Initialized class equals the joining class; the two stars add at most one copy each. | Copies `≤3L+2`; support `≤6L+4`. |

With `1≤L`, the uniform conclusions are `finalClass.card≤3L+2` and `edgeSupport(finalClass).card≤6L+4`. This is a feasible proof argument, **not an existing compiled conclusion about the assembled native family**. A crude independent addition of a bundle increment and two star increments would miss this sharper bound.

### Old-core color load

Prove a support-load estimate from the **exact final copy union**. The selected protected star copies and the later remaining star copies lie in the same full actual star; they must not be charged as independent extra families. Show that selected boundaries add only joining copies and those selected assigned-star copies, using `compressedBoundary` and the unpaired-signature classification. The internal exceptional bundle contributes no incidence at an old-core vertex.

For `v∈U₀∪U₁`, the resulting colored incidence is at most joining degree plus the two full exceptional-star multiplicities. The target is therefore `D+2*b`. `NativeStar.star_degreeOn_le_parallel` in `Overfull/NativeStar/StarAccounting.lean` supplies the actual-copy incidence bound at a noncentral vertex. A short general disjoint-matching-family lemma can identify or bound its used-color count by degree on the exact union, following the proof of `reserveClasses_vertex_load_eq`.

This last bound needs its own proof. Neither the initial global joining load nor the intermediate available-only Hall load is already the final global old-core load statement.

## 10. Feasible proof sequence and remaining boundary

1. Add the actual weighted piece-capacity lemma and weighted all-even decomposition wrapper. This is the smallest direct application of the existing generic theorem.
2. Add the weighted odd primary wrapper, including the singleton seed-fiber weight computation and explicit protected-label image count.
3. Lift both wrappers to the native residual host with actual reserve traces; retain resource weights and the original palette order.
4. Prove the reserve-plus-common-bundle initialization lemmas and the available-color bridge. This is the most important new interface layer.
5. Instantiate native balance and the existing one/two-star extension. Prove exact protected classes, all-color exceptional coverage, and parity preservation.
6. Prove the three support cases and exact-union `D+2*b` old-core load bound; then connect those conclusions to the separate quantitative robust-completion hypotheses.

The strong natural-number regime and the original palette gap already have compiled supporting arithmetic. Deriving all manuscript-scale parameter inequalities, transferring robustness after the actual colored footprints, constructing the required robust matchings, and completing final factorization remain later obligations. No numbered assertion should be promoted merely because the wrapper design or its individual supporting lemmas exist.

## Source reference index

All paths below are relative to the reviewed candidate repository. The exact existing declaration names used above were read from these sources; proposed names are explicitly marked prospective.

| Source | Main interfaces used |
| --- | --- |
| `Overfull/WeightedPalette/Grouping.lean` | `exists_star_weighted_matching_grouping`, `groupedCopies_eq_seed_on_protected_color`. |
| `Overfull/WeightedPalette/StarWeights.lean` | `starWeight`, `starWeight_le_four_mul`, `starWeight_le_six_mul`, actual-copy weight accounting. |
| `Overfull/WeightedPalette/Loads.lean` | Natural-number item, protected-margin, gap, and Hall bounds. |
| `Overfull/ResidualPalette/PaletteGrouping.lean` | `twice_piece_count_le_order_mul_degree`, `primarySeed`, `primarySeed_injective`, `primarySeed_extension_unique`. |
| `Overfull/ResidualPalette/JoiningGrouping.lean` | `JoiningPalette`, `congr_parity`, `uncovered_even`, existing even/odd grouping templates. |
| `Overfull/ResidualPalette/ProtectedGrouping.lean` | Protected odd primary indexing and exact-class template. |
| `Overfull/ResidualPalette/PaletteParity.lean` | `cutOn_biUnion_even`, `cutOn_biUnion_mod_two_of_one_primary`, `exists_evenJoining_decomposition`. |
| `Overfull/ResidualPalette/ReservedPrimary.lean` | `exists_twoOddJoining_decomposition_with_reserved_primary`. |
| `Overfull/ResidualPalette/NativeReservedCrossings.lean` | `BoundaryPacking.exists_half_residual_crossing_reserve`. |
| `Overfull/ResidualPalette/NativeProtectedPalette.lean` | Existing native odd singleton-palette construction. |
| `Overfull/ExceptionalPalette/EvenColors.lean` | Existing even color-avoidance and original-assignment host templates. |
| `Overfull/ExceptionalPalette/ReserveCopies.lean` | Actual residual boundary matching, disjointness, size, coverage, parity, and singleton/empty joining traces. |
| `Overfull/ExceptionalPalette/ReserveNative.lean` | Native selected-index and prescribed-reserve assembly template. |
| `Overfull/ExceptionalPalette/ReserveInsertion.lean` | `reserveClasses` and exact replacement, cut, coverage, and load interfaces. |
| `Overfull/ExceptionalPalette/PairColoring.lean` | Generic actual bundle color classes and their matching/disjointness/coverage facts. |
| `Overfull/ExceptionalPalette/PairExtension.lean` | Older stronger whole-fiber pair interfaces; scope limitation explained in Section 6. |
| `Overfull/AssignedParts/BoundaryCompression.lean` | Compressed boundary decomposition and exceptional retention. |
| `Overfull/NativeStar/ReserveInjection.lean` | Actual reserve-star counts and selected-family cardinality. |
| `Overfull/NativeStar/IncidencePartition.lean` | Original-assignment incidence partition and internal-pool classification. |
| `Overfull/NativeStar/CommonPalette.lean` | Actual common bundle colors and remaining palette definitions. |
| `Overfull/NativeStar/NativeBalance.lean` | Native off-core bound, protected freeness, bundle injection, and exact remaining balance. |
| `Overfull/NativeStar/StarAccounting.lean` | Actual per-color copy and incidence accounting. |
| `Overfull/NativeStar/StarExtension.lean` | Available-only one-star extension and cut preservation. |
| `Overfull/NativeStar/TwoStars.lean` | Available-only sequential two-star extension and derived second-stage budgets. |

