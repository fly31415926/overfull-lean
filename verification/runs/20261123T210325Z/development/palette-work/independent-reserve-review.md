# Independent review of reserved singleton primaries and surviving crossing copies

Reviewed at 2026-11-23T21:05:32.713023+00:00.

Reviewed exact source hashes:

- `ReservedPrimary.lean`: `591c53ee1adff45f655ddaa06f3fefa0b979bd11ed64daebd69dbc2b0dfb9192`.
- `NativeReservedCrossings.lean`: `185029e1a02d75552b0013a95fbb1f23a8b119944db410958b5c73df186bbb6e`.

## Conclusion

No mathematical scope or original-copy transport defect was found in these two source files. The declarations' hypotheses are explicit. They do not assume that selected reserve crossings form a vertex-disjoint matching or that the original representative survives in the residual.

## Checked points

1. **Reserved-circuit induction.** Each selected original pair copy is removed together with one distinct virtual copy. Cuts not separating the two prescribed labels lose no selected copy. Separating cuts and the available virtual pool both decrease by exactly one. The class margin remains valid because `(|B|-1)-|A| = |B|-(|A|+1)` under the retained cardinal inequalities. The final remainder is proved admissible before applying the existing small-label circuit theorem.
2. **Compatibility.** An original copy and its virtual mate have different incidence-class tags. Hence their two-circuit is compatible even when different selected original copies share an original endpoint. Distinct selected circuits are edge-disjoint because both original and virtual copies are removed from their respective available sets at every step.
3. **Projection and colors.** The original restriction of a prescribed original/virtual pair is exactly the singleton containing that original copy. The existing injective part projection preserves all parallel-copy identities. Distinct primary pieces subsequently receive distinct palette labels; no pairwise endpoint-disjointness across differently colored primary pieces is required.
4. **Actual residual subtype.** The surviving family has type `Fin r → joiningCopies (residualGraph G N T) assignedLabel`. Each element retains both the actual original edge-copy value and the proof that it is outside the deleted matching union. The second subtype certificate proves it is a joining copy for the original representative's unchanged assignment.
5. **Survival and distinctness.** Survival is derived from disjointness of every deleted matching from the union of reserved boundaries. Distinctness is derived from the reserved boundaries' edge-copy disjointness, not from endpoint pairs. Thus even parallel copies remain distinct.
6. **Half-reserve selection.** The selected set has exactly `r/2` elements in the residual joining-copy subtype and retains both original-reserve membership and quotient endpoint pair `s(0,1)`. This is an exact floor statement, without an unsupported positive linear-size claim for small `r`.

## Parameter composition requirement

The final lemma `half_reserve_palette_room` proves `D ≤ h-r/2` from `r≤h` and `6D<h`; this suffices for the forced-primary circuit construction. The protected palette grouping has a stronger explicit hypothesis, `6D+r/2<h`. The former hypotheses alone do not imply the latter, so the two margins must not be conflated.

The root and joining-degree agents acknowledged this requirement. A separate `ProtectedBudget.lean` is being checked with `δ≤α/720` and a protected count `s≤h/2`, deriving the strict protected margin and `h-6D-s≥αn/120`. Its proposed quantitative bound is `6L≤(360δ/α)n+6`, with `δ≤εα/720` and `n≥12/ε` supplying `6L≤εn`. Final assembly must use the completed checked budget theorem or retain the protected margin as an explicit hypothesis. This review does not claim that an unfinished numeric lemma has passed.

## Remaining mathematical scope

The reviewed sources force selected actual crossing copies into singleton primary pieces. Together with `ProtectedGrouping.lean`, those protected pieces remain whole singleton joining-palette classes. They do not on their own restore every exceptional boundary prescription, construct the remaining internal robust matchings, or prove the final factorization.
