# Independent semantic review of exceptional palette reserve extensions

Reviewer: next_proof_review agent (author of Pair modules, independent reviewer of Reserve and Even modules).

Review outcome: no missing mathematical hypothesis or overstatement found in the reviewed ReserveCopies, ReserveInsertion, ReserveNative, EvenNative and two scope documents. This is a source-level semantic review; root owns the full unchanged audit, preservation checks and checkpoint status.

## Residual copies and reserve alignment

- `survivingCopies` retains the actual residual subtype and the original edge-copy value. Full image, cardinality and support are claimed only under disjointness from deleted copies. The matching and disjointness lemmas correctly require no full-survival hypothesis because restriction preserves those properties.
- `BoundaryPacking.residualBoundary` refers to the original compressed boundary index. Its full exceptional coverage and old-core uncovered parity use actual survival, the original parent perfect matching, and the original partition hypotheses.
- The exact equality between a boundary's joining portion and its old-core crossing set uses the representative's assignment and same-signature certificates. Exceptional incidences are proved internal to that assignment; original parents are never assumed to survive as perfect residual matchings.
- In the odd case, each selected surviving crossing identifies a unique joining copy in its original boundary. The native wrapper recovers the original reserve index, proves that the index map is injective from the singleton joining traces, and retains the injective color map. Distinct parallel copies remain distinct throughout.

## Generic insertion

- `reserveClasses` replaces only injectively specified colors. The hypothesis that each full boundary's joining trace equals its original color class guarantees that no joining copy is lost and no inserted joining copy conflicts with another class.
- Matching is proved from the actual selected boundary at a protected color and the original matching at every other color. Edge-disjointness is proved separately, including the protected/unprotected cross case.
- Coverage is exactly the union of the joining-copy set and the chosen boundaries. The added-copy set is exactly the internal portion of those boundaries. Every cut of every union of assigned fibers is unchanged as a set, a stronger conclusion than parity alone.
- The class-size and support bounds apply to whole replaced classes. The vertex-load identity counts actual colored incidences; its bound adds the actual internal reserve degree rather than incorrectly retaining the original D bound at all vertices.

## Native all-even application

- `exists_native_even_reserved_palette` derives all-even fiber parity from the original matching representative and the first assigned core's parity.
- It constructs both injections from `Fin (r/2)` and the corresponding protected color set. The empty half-reserve case is handled by the same finite types.
- The margin and total-size hypotheses pay exactly `r/2` protected colors. The actual joining palette is constructed using the complement palette.
- The surviving boundary's joining part is proved empty, so the generic insertion applies. Full exception coverage and old-core uncovered parity are then derived at each protected color.

## Integration boundary with PairFiberCompletion

Both constructions are correctly based on the original `JoiningPalette`. `ReserveExtension.classes` includes internal copies and is therefore not itself a `JoiningPalette` with joining-only coverage; it must not be fed directly to the pair theorem.

For the paired signature with at most two exceptions, a further native composition can extract each selected boundary's unique actual pair copy, use the selected color map as an injective seed, and apply pair completion to the original joining palette. Protected singleton crossings miss the pair endpoints; protected even classes are empty. Pair completion then gives exactly the original joining class union the prescribed pair singleton, which can be identified with the whole selected boundary. That extraction/comparison wrapper is not asserted in this checkpoint.

The current Pair theorem already accepts such valid actual-copy seeds and preserves their labels and exact classes. The current Reserve theorems independently insert whole selected boundaries. The documentation does not claim that the native all-color composition has already been proved.

## Scope documentation

Both reviewed documents accurately distinguish completed pair-fiber coloring and selected protected-boundary insertion from unpaired exceptions assigned to old cores, even uncovered old-core order in every remaining color, final robust completions, residual factorization and reconstruction. The warning that small support and small vertex load alone do not settle weighted parallel star-copy compatibility is mathematically warranted. Coverage remains 47/69 and the main theorem remains unverified.

No source or documentation file was modified during this review.

## Reviewed file hashes

Review recorded at 2026-11-23T22:25:07.438179+00:00.

- `Overfull/ExceptionalPalette/ReserveCopies.lean`: `528e5f01eb4089f63243f92ab0a2fae00b7249c86e2f2d3e794f56f28ad09a14`
- `Overfull/ExceptionalPalette/ReserveInsertion.lean`: `ce33c662913bf4b70c8a6fdf17de9aa488c4c077fd09db94e013ea6c6ea47e8a`
- `Overfull/ExceptionalPalette/ReserveNative.lean`: `0c824cd0f9b7cb6872ca58463a268d453d6f6104a1564c66f8639a313c9cefd4`
- `Overfull/ExceptionalPalette/EvenNative.lean`: `f0410f63afefad2912fb15de5118335cf99221051285f47abb277d025d3f4db3`
- `docs/exceptional-palette-semantic-review.md`: `cb512512edc311235393f2d1281f4f3e194592d71de604253258eae7568ac471`
- `docs/exceptional-palette-verification.md`: `d96316bb7f64876186520c4c961d9fb6b1563eca420e1b60162899130d7f8472`
