# Next step: coloring the actual copies inside a two-vertex pair part

**Status: read-only mathematical/API plan, not an implemented or checked Lean proof.**
This concerns the genuine separate pair part `pairPart = {x,y}`. It does not
solve the case where two exceptions are assigned into the same core part.

## Proposed minimal interface

Work on the actual residual `H : Multigraph V E`, with its existing
`C : JoiningPalette H label h D L p`. Write

```text
J   := FourOdd.joiningCopies H label
B   := H.parallelEdges x y
F v := Finset.univ.filter (fun j : Fin h => v ∉ H.edgeSupport (C.classes j))
```

Assume `x ≠ y`, `FourOdd.labelShore label {a} = {x,y}`, `p a = 0`, and
`H.degree x = h`. The last hypothesis alone suffices for the counting step;
the intended native application already has regularity at every vertex.
No new robustness, no-overfull, simplicity, or multiplicity hypothesis is
needed for this local extension.

Allow a finite prescribed index type `R`, injective maps `q : R → B` and
`f : R → Fin h`, and `∀ r, f r ∈ F x`. The target is an equivalence

```text
φ : B ≃ F x
∀ r, (φ (q r)).val = f r
```

together with `F x = F y` and `B.card = (F x).card`. The prescription is
optional: use an empty index type for unrestricted pair coloring. The
equivalence acts on individual edge copies, not on their common endpoints.

## Proof route

1. **Equal free sets.** For each color, `C.cut_parity j a` and the matching
   parity identity imply that `{x,y} \ H.edgeSupport (C.classes j)` has even
   size. Since `x ≠ y`, its size can only be zero or two. Thus `x` is covered
   exactly when `y` is covered. This proves equality of the actual free sets,
   rather than just equality of their cardinalities.
2. **Exact number of free labels.** Matching, disjointness, and exact coverage
   give
   `#{j | x ∈ support(C.classes j)} = H.degreeOn J x`.
   The exact two-vertex fiber and looplessness partition the incidences at
   `x` into joining copies and the copies in `B`. Consequently
   `H.degreeOn J x + B.card = h`, and complement counting gives
   `(F x).card = B.card`. The existing family-load lemma gives only an upper
   bound; this equality must actually be proved, or obtained through the
   existing proper-coloring interface described below.
3. **Extend the prescribed finite bijection.** First choose any equivalence
   `e : B ≃ F x` by `Fintype.equivOfCardEq`. The injections `e ∘ q` and
   `r ↦ ⟨f r, hfree r⟩` identify two subtypes of `F x`. Their range
   equivalence, constructed with `Equiv.ofInjective`, extends to a permutation
   of `F x` using `Equiv.extendSubtype`. Compose this permutation with `e`.
   Alternatively pair the two equally sized complements directly. This
   extends all prescriptions simultaneously without recoloring any joining
   copy.
4. **Insert the copies.** For a free label `j`, add the singleton containing
   `(φ.symm ⟨j,hj⟩).val`; for other labels add the empty set. Let the resulting
   classes be `K j`. Both endpoints are free, so each union is a matching.
   Bijection injectivity gives disjointness and surjectivity gives exact
   coverage of every parallel copy.

The useful output certificates are:

- `K j ∩ J = C.classes j`, pairwise disjointness, and
  `univ.biUnion K = J ∪ B`;
- every color covers both `x` and `y`, and every prescribed `q r` belongs to
  `K (f r)`;
- every label-shore cut is exactly unchanged, since all added copies stay
  inside the single fiber `{x,y}`;
- `card(K j) ≤ 3L+1` and `card(support(K j)) ≤ 6L+2`;
- outside `{x,y}`, support membership and vertex load are unchanged.

**Do not return an unchanged `JoiningPalette`.** Its coverage field requires
only joining copies, and its global load bound is `D`; after extension the
two pair vertices meet all `h` colors. Return the augmented class family and
these precise certificates, optionally a coloring of `H.restrictEdges (J ∪ B)`.

## Existing interfaces to reuse

| Existing file/API | Role |
| --- | --- |
| [JoiningGrouping.lean](../../../Overfull/ResidualPalette/JoiningGrouping.lean): `JoiningPalette`, `uncovered_even`, `assigned_joiningPalette_uncovered_even` | Exact joining classes and parity. For the minimal interface, the matching parity identity avoids assuming parity data for every other fiber. |
| [BoundaryCompression.lean](../../../Overfull/AssignedParts/BoundaryCompression.lean): `IsMatching.uncovered_even_iff_cut_parity`, `degreeOn_sum_eq_covered` | Pair coverage parity and exact matching incidence counts. |
| [CriticalMultigraph.lean](../../../Overfull/CriticalMultigraph.lean): `parallelEdges`, `mem_parallelEdges`, `edge_eq_otherEnd`, `EdgeColoring.missingColors_card_add_degree` | Actual parallel-copy pool, endpoint identities, exact missing-color count. |
| [Palette.lean](../../../Overfull/BoundaryExtension/Palette.lean): `PaletteColoring.ofMatchingClasses`, `ofMatchingClasses_color_eq_iff`, `toEdgeColoring` | Convert the restricted joining class family to a proper coloring if that is the shorter counting route. |
| [Pairing.lean](../../../Overfull/CircuitPatterns/Pairing.lean): `isMatching_union_of_disjoint_support` | Matching preservation after adding a free pair copy. |
| [Basic.lean](../../../Overfull/AssignedParts/Basic.lean) and [Signatures.lean](../../../Overfull/AssignedParts/Signatures.lean): `assignedLabel_fibers`, `pairPart_card_eq_zero_or_two`, `pairPart_eq_exceptions_of_internal`, `corePart_eq_original_of_pairPart_eq` | Specialize to label `2`; a nonempty pair part equals all of `Z`, and the two core parts then equal the original cores. |

Pinned mathlib provides `Equiv.ofInjective` in `Mathlib.Logic.Equiv.Set` and
`Equiv.extendSubtype` / `extendSubtype_apply_of_mem` in
`Mathlib.Logic.Equiv.Fintype`. These are existing library APIs, not new project
proofs completed by this plan.

## Preserve the selected reserve boundaries

In the odd case, [NativeProtectedPalette.lean](../../../Overfull/ResidualPalette/NativeProtectedPalette.lean)
already returns selected actual reserve crossings and injectively indexed
singleton joining classes. Recover each crossing's boundary index from its
membership in the original reserve union. Boundary disjointness gives a
unique owner; the exactly-one-crossing certificate makes the recovered
indices injective. Use [NativeReservedCrossings.lean](../../../Overfull/ResidualPalette/NativeReservedCrossings.lean)
and `BoundaryPacking.crossing_card_one_of_odd` for that certificate.

For a genuine pair part, each corresponding compressed boundary consists of
that old-core crossing and one actual `x-y` copy. This exact two-copy identity
still needs a short source-preserving lemma: use the shared signature,
`retains_internal_pairs`, matching, and compression's retention of all
exceptional incidences. Boundary disjointness makes these pair copies
distinct, and reserve avoidance puts them in the actual residual pool `B`.
The protected singleton classes avoid both pair vertices. They therefore
provide `q`, `f`, and the free-label premise above. Prescribing their
bijection yields entire original compressed boundaries at those colors.

In the all-even case the compressed pair boundary has no old-core crossing.
The generic extension still colors all pair copies, but the current palette
theorem does not supply protected *empty* joining classes. Thus it does not
by itself restore a specified family as entire reserved color classes.

## Edge cases and remaining separation

- `B = ∅` gives an empty free set and no insertion; `h = 0` is harmless with
  an empty prescription. No positive-degree side condition is needed.
- An empty pair part is a separate branch. Cardinality two supplies distinct
  endpoints; do not model a one-vertex pair or allow a loop.
- Arbitrarily many parallel copies are permitted. Different copies receive
  different colors, and all arithmetic counts those copies separately.
- When both exceptions belong to the same assigned core, core-fiber parity
  does **not** imply equality of their free sets. Other internal neighbors
  also invalidate the deficit-equals-pair-pool identity. The same finite
  extension mechanism can be used only after explicit common-free-label and
  remaining-incidence conditions are proved; it supplies neither the missing
  Hall condition nor a recoloring argument.
- In the genuine pair case, additions have no old-core endpoint. Old-core
  footprints and uncovered sets remain exactly unchanged. The later robust
  completion and full residual factorization are still separate obligations.
