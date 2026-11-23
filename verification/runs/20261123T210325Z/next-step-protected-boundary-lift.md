# Next step: lift protected joining classes to actual reserved boundaries

Status: proof plan only. No theorem in this note has been added to Lean, and this note does not increase manuscript coverage. It was prepared while the corrected full audit `full-04` was running.

## Existing checked interfaces

The current odd-case theorem `NativeReserve.exists_native_protected_joiningPalette` returns a set `A` of `r / 2` actual surviving reserved crossing copies, a full joining palette, and an injective map from `A` to palette labels whose classes are exactly the respective singleton crossings. Its hypotheses include the protected margin and capacity. See [NativeProtectedPalette.lean](../../../Overfull/ResidualPalette/NativeProtectedPalette.lean).

For each original compressed reserve boundary, the following interfaces already exist:

| Property | Existing theorem |
| --- | --- |
| Matching, disjoint actual copy sets, at most `Z.card + 1` copies | `BoundaryPacking.isMatching`, `pairwise_disjoint`, `card_le` |
| Every exceptional vertex has one incident boundary copy | `BoundaryPacking.exceptional_degree` |
| Even uncovered old cores | `BoundaryPacking.uncovered_even` |
| All exceptional reserve incidences are internal under the fixed assignment | `BoundaryPacking.exceptional_label_eq` |
| Every reserved copy survives the selected removals | `BoundaryPacking.reserved_disjoint_removed` |
| Exactly one old-core crossing in the odd case | `BoundaryPacking.crossing_card_one_of_odd` |

The first group is in [PackingConstruction.lean](../../../Overfull/NativeReserve/PackingConstruction.lean), the internal/survival facts are in [JoiningBounds.lean](../../../Overfull/ResidualPalette/JoiningBounds.lean), and the crossing result is in [NativeReservedCrossings.lean](../../../Overfull/ResidualPalette/NativeReservedCrossings.lean).

## Proposed first interface: the residual boundary and its joining restriction

Let `H := residualGraph G N T`. Define the residual boundary `R j` as the finite set of actual residual copies whose original values belong to `Q.boundary j`. The disjointness from removed copies gives a bijection back to that original boundary; no parallel copies are identified.

Prove the transfer of matching, actual-copy disjointness, cardinality, exceptional degree, and old-core uncovered parity from `Q.boundary j` to `R j`. Then prove that its joining restriction is exactly its old-core crossing restriction. This uses the actual definition of `compressedBoundary`: exceptional copies together with a parity-selected old-core crossing. The exceptional copies have equal assigned endpoint labels by `exceptional_label_eq`, while an old-core crossing has labels zero and one.

In the odd case the joining restriction is a singleton. In the all-even case it is empty. These are stronger and more useful outputs than merely saying a selected crossing belongs to the union of reserved boundaries.

## Proposed second interface: recover the selected boundary indices

The existing protected-palette theorem records original reserve membership but does not expose the corresponding boundary index for each selected copy. Recover a map `b : A → Fin r` using that membership. Pairwise boundary-copy disjointness makes the index unique. The singleton joining restriction implies that two selected crossing copies assigned to the same boundary are equal, so `b` is injective.

Retain both injections:

- `b : A ↪ Fin r`, selecting distinct actual reserved boundaries;
- `f : A ↪ Fin h`, selecting the protected palette labels.

Do not replace either map by an endpoint map: distinct parallel copies must remain distinct.

## Proposed third interface: extend the protected classes

Replace each protected singleton class at label `f a` by the entire residual boundary `R (b a)`; leave the other joining classes as they are. A convenient alternative definition is to unite each class with the internal copies of its assigned reserved boundary.

The matching proof for a protected class is exactly the matching proof of that boundary. Copy disjointness between protected classes follows from `b`; disjointness from any other class follows because other classes contain only joining copies, while the selected boundary's joining restriction is exactly the protected singleton.

The extended family should explicitly record:

1. matching classes and pairwise disjoint actual copy sets;
2. each class's joining restriction equals its original joining class;
3. every protected class is exactly its assigned actual reserved boundary;
4. unchanged assigned-fiber cut parity, since the inserted copies are label-internal;
5. coverage of every exceptional vertex in every protected class;
6. even uncovered old cores for those protected classes.

Use a new boundary-family certificate, or return these properties directly. The extended family is not a `JoiningPalette`: that structure requires its full union to equal the set of joining copies, which the new internal copies would violate.

### Size and load bookkeeping

The protected replacement has at most three copies and six support vertices. Because `0 < L`, this stays within the existing per-class bounds `3 * L` and `6 * L`. Thus the protected-boundary replacement alone requires no larger whole-class footprint allowance.

The generic `D` vertex-load certificate cannot simply be copied: inserted internal incidences can increase the number of classes meeting a vertex, particularly at exceptions. For old-core vertices, use the already proved `NativeReserve.coreFootprint_load_le_error` from [CompletionFootprints.lean](../../../Overfull/NativeReserve/CompletionFootprints.lean). It applies to any pairwise copy-disjoint family outside the actual retained simple core and bounds the core footprint load by the actual core-complement error `a`. It has no three-copy size requirement.

This needs a genuine outside-core certificate for all extended classes. Joining copies are outside a constant-label core by `joiningCopies_disjoint_core`; reserved boundaries are outside by the native-pool argument `boundary_disjoint_core`. The residual transfer must use the retained residual core embedding.

## All-even case: reserve empty labels first

The current even joining palette does not promise enough empty labels. A direct next lemma can avoid constructing dummy primary pieces:

- Let `s := r / 2`.
- Apply `FourOdd.EvenJoiningDecomposition.exists_palette` with `h - s` colors.
- Embed those colors into the last `h - s` labels of `Fin h`, leaving the first `s` labels empty.
- Lift any `s` distinct surviving reserve boundaries into those empty labels.

The protected budget `6 * D + s < h` supplies the reduced-color margin, and the capacity becomes the same quantity `h - 6 * D - s` already handled by `uniform_protected_palette_budget`. Finite-label padding must retain matching, coverage, all-even cut parity, size, and load certificates explicitly. The case `s = 0` should reduce to the existing construction.

## Remaining gap after this step

Only the protected labels would then cover all exceptions. Every other label still needs its actual internal exceptional incidences assigned consistently, including parallel bundles and the case of two exceptions assigned to the same core. Only after every assigned exception is covered can assigned-fiber uncovered parity be transferred to uncovered old-core parity for every class. Robust-core completion and final factorization remain later obligations.
