# Next-step analysis: assigned exceptions and old-core parity

**Status:** read-only source analysis during the residual-palette audit. This note proposes subsequent proof work; it adds no Lean theorem, test result, or coverage credit. No proof source or frozen audit input was changed. The handoff still records coverage **47/69**.

Repository: `/workspace/scratch/96ddfd820f7d/overfull-next`.

## 1. Boundary palette input and the narrow next result

Keep the original assignment fixed. Write `H := residualGraph G N T`, `label := assignedLabel G M U₀ U₁ Z`, `Wᵢ := corePart G M Z Uᵢ`, and `Xᵢ := assignedExceptions G M Z Uᵢ`. All new edge sets must use the actual surviving-copy type of `H`, not endpoint pairs or original copies without survival proofs.

The existing `exists_native_protected_joiningPalette` supplies an actual joining palette and `r/2` injectively indexed singleton reserved-crossing classes. It does **not** yet insert their full compressed boundaries. The root's separate protected-boundary-lift plan is the proposed input here: a family `B : Fin h → Finset {e : E // e ∉ removedCopies N T}` of pairwise copy-disjoint matchings, containing every joining copy, preserving its required assigned-fiber cut parity, and containing the selected complete reserve boundaries in prescribed colors.

Use a broader boundary-palette interface after that lift: its covered union now includes internal exceptional copies, so `JoiningPalette.cover` no longer fits. Likewise, once every exception is saturated, its palette load is `h`, not the old joining bound `D`.

The narrow next directly justified bookkeeping target is **exact unused-incidence/free-color accounting**. For any vertex `z`, define

\[
U_B=\bigcup_j B_j,\qquad
F_z=\{j:z\notin\operatorname{supp}(B_j)\},\qquad
E_z=\{e\notin U_B:z\in H(e)\}.
\]

From `H.degree z = h`, matching classes, and copy disjointness, prove

\[
|F_z|=h-H.\mathrm{degreeOn}(U_B,z)=|E_z|.
\]

This counts parallel copies separately. Existing ingredients are `NativeReserve.removed_degreeOn`, `Multigraph.isMatching_iff_incident_card_le_one`, `Multigraph.degreeOn_pos_iff`, and elementary finite-set subtraction. An alternative is to color `H.restrictEdges U_B` by the existing classes, then use `Multigraph.EdgeColoring.missingColors_card_eq_sub` and `Multigraph.PaletteColoring.ofMatchingClasses_color_eq_iff`.

Because all joining copies are already in `U_B`, every edge of `E_z` is label-internal. In the one-assigned-exception case, `assignedLabel_fibers` then identifies its other endpoint as belonging to the corresponding old core. A protected color already covering every exception is automatically absent from every `F_z`; a proper extension cannot add another exceptional incidence to it.

## 2. The actual one-star assignment obligation

Suppose `z` is the only exception in its assigned core. For the actual remaining copies `e ∈ E_z` and colors `j ∈ F_z`, the precise allowed relation is

\[
R(e,j)\iff H.\mathrm{otherEnd}(z,e)\notin\operatorname{supp}(B_j).
\]

An adjacency-preserving bijection `E_z ≃ F_z` inserts each remaining incidence exactly once, uses each free color once at `z`, and avoids all pre-existing core-endpoint conflicts. It also leaves every previously assigned copy/color intact. Finite Hall applies exactly when

\[
\forall S\subseteq E_z,\quad
|S|\le\left|\bigcup_{e\in S}\{j\in F_z:R(e,j)\}\right|.
\]

`Finset.all_card_le_biUnion_card_iff_existsInjective'` is already used by `DenseLinkPacking.dense_bipartite_bijection`; balanced cardinality upgrades its injection to a bijection. This is a useful modular target, but the **native Hall hypothesis remains to be proved**. A wrapper merely assuming this hypothesis would not complete the construction.

The present small joining degree and whole-class support bounds do not, by themselves, supply the missing proof. A proved old-core vertex load bound `b` would remove at most `b` colors from each row; after lifting, obtain that bound from the retained-core hypotheses rather than reusing `JoiningPalette.vertex_load_le` unchanged. Large row lists alone can still omit one common free color and fail Hall for the entire left side. In the graph interpretation, a color free at `z` might already cover every distinct internal neighbor of `z`; many parallel copies can be concentrated on a small neighbor set. A support bound of `ε n` does not rule that pattern out. This identifies an unproved inference; this note does not claim a counterexample satisfying every native-reserve hypothesis.

Two honest approaches remain: derive full Hall (or both half-degree conditions) from additional native structure, or prove a parity-preserving repair of the joining palette. `dense_bipartite_bijection` requires **both** left and right degree bounds. `PartialEdgeColoring.exists_edgeColoring_extending_from_lists` instead requires each uncolored edge's list to exceed its entire conflicting-copy count, which is not supplied at a saturated exceptional star.

A repair contract should retain the chosen reserve boundaries as subsets of their prescribed colors, preserve per-color cut parity and actual copy coverage, and track its support budget. It may need to move unprotected joining pieces; demanding that every original joining label and every protected class remain exact forever is an additional constraint that has not been justified. Moving an even-parity piece preserves cut parity, whereas moving a primary odd piece alone does not. No such repair is currently constructed.

## 3. Separate the two-exception cases

| Assignment | Remaining internal problem |
|---|---|
| One exception assigned to a core | One star with the allowed relation above. |
| Two exceptions assigned to different cores | Their mutual copies are joining and already covered. The remaining stars have disjoint old-core endpoints, so successful assignments can be combined without new cross-star conflicts. Each star still needs its own Hall proof. |
| Two exceptions assigned to the same core | Remaining copies can include a parallel bundle between the exceptions, and both stars may meet the same old-core vertex. The central bundle needs distinct colors in the intersection of the two free palettes; the stars then need compatible assignments avoiding each other. Independent bijections are insufficient. |
| An actual two-vertex `pairPart` fiber | Separate equal-free-palette argument owned by the semantic reviewer; it does not cover the previous row. |

The same-core case is essential: `pairPart` is defined from the representative matching `M`, so `pairPart = ∅` does not imply that `H` has no copies between the exceptions. The parity of an enlarged core fiber does not force simultaneous coverage of its two exceptional vertices. A joint extension API must record central-copy allocation and the updated free palettes before proving the star matching conditions. `SparseColoring.edgeColoring_two_centres` returns a coloring under its own degree and central-bundle hypotheses; it does not preserve an arbitrary given joining coloring or its per-color parity, so it is not an immediate substitute.

## 4. Exact transfer to the old cores

A small independent next lemma should make the parity transfer explicit. Let `B'_j` be an extended matching with unchanged cut on each assigned fiber, and suppose `Xᵢ ⊆ H.edgeSupport (B'_j)`. Since `Wᵢ = Uᵢ ∪ Xᵢ`,

\[
W_i\setminus\operatorname{supp}(B'_j)
=U_i\setminus\operatorname{supp}(B'_j).
\]

Every added label-internal edge leaves each assigned-fiber cut unchanged. Therefore `Multigraph.IsMatching.uncovered_even_iff_cut_parity`, the known fiber parity, and this equality give even uncovered order on **the old core**. Before exceptional coverage, only assigned-fiber parity is available. The protected complete boundaries already have the old-core conclusion directly from `BoundaryPacking.uncovered_even`; the unprotected colors are the outstanding ones.

After this step, `coreFootprint_parity` gives the exact parity required by the completion interface. For the quantitative inputs:

- If the lifted base palette has support at most `6L`, adding a matching of previously unused edges each touching `Z` adds at most `|Z| ≤ 2` edges per color. A safe whole-support bound is `6L + 2|Z| ≤ 6L+4`; the old-core footprint increases by at most `|Z|`, since each such edge has at most one old-core endpoint. Budget the additive term explicitly.
- `coreFootprint_load_le_error` applies to **any** pairwise copy-disjoint family outside the actual retained `coreEdges`. With residual regularity `h` and retained-core degree at least `h-a`, the old-core load remains at most `a`. Added edges touching `Z` lie outside those core edges; joining copies also do, as recorded in `JoiningBounds`.
- `coreFootprint_admissible` currently assumes class size at most three, so grouped palette classes need its parity/card/load components applied separately or a later generalized wrapper. Do not apply it unchanged.

The first useful implementation sequence is therefore: exact free-color accounting; explicit internal-extension assembly preserving actual copies and cuts; old-core parity and footprint transfer; then a genuine native Hall/repair theorem, including the same-core two-exception case. The all-even protected-empty-color construction and the final robust matching completion remain separate prerequisites/open obligations.

## Source evidence

All references below are existing source interfaces inspected read-only; proposed statements above have not been compiled.

| Source | Relevant exact names |
|---|---|
| [NativeProtectedPalette.lean](sandbox:/workspace/scratch/96ddfd820f7d/overfull-next/Overfull/ResidualPalette/NativeProtectedPalette.lean) | `NativeReserve.exists_native_protected_joiningPalette` |
| [JoiningGrouping.lean](sandbox:/workspace/scratch/96ddfd820f7d/overfull-next/Overfull/ResidualPalette/JoiningGrouping.lean) | `NativeReserve.JoiningPalette`; `JoiningPalette.uncovered_even`; `AssignedParts.assigned_joiningPalette_uncovered_even` |
| [AssignedParts/Basic.lean](sandbox:/workspace/scratch/96ddfd820f7d/overfull-next/Overfull/AssignedParts/Basic.lean) | `AssignedParts.assignedExceptions`; `corePart`; `pairPart`; `assignedLabel_fibers`; `exceptional_corePart_iff` |
| [BoundaryCompression.lean](sandbox:/workspace/scratch/96ddfd820f7d/overfull-next/Overfull/AssignedParts/BoundaryCompression.lean) | `Multigraph.IsMatching.degreeOn_sum_eq_covered`; `IsMatching.uncovered_even_iff_cut_parity` |
| [Residual.lean](sandbox:/workspace/scratch/96ddfd820f7d/overfull-next/Overfull/NativeReserve/Residual.lean) | `NativeReserve.removed_degreeOn`; `residual_pool_accounting`; `residualGraph` |
| [Deficits.lean](sandbox:/workspace/scratch/96ddfd820f7d/overfull-next/Overfull/ColoringExtension/Deficits.lean) and [Palette.lean](sandbox:/workspace/scratch/96ddfd820f7d/overfull-next/Overfull/BoundaryExtension/Palette.lean) | `Multigraph.EdgeColoring.missingColors_card_eq_sub`; `Multigraph.PaletteColoring.ofMatchingClasses_color_eq_iff` |
| [Candidates.lean](sandbox:/workspace/scratch/96ddfd820f7d/overfull-next/Overfull/Dense/LinkPacking/Candidates.lean) and [Greedy.lean](sandbox:/workspace/scratch/96ddfd820f7d/overfull-next/Overfull/ColoringExtension/Greedy.lean) | `DenseLinkPacking.dense_bipartite_bijection`; `Multigraph.PartialEdgeColoring.exists_edgeColoring_extending_from_lists` |
| [SparseColoring.lean](sandbox:/workspace/scratch/96ddfd820f7d/overfull-next/Overfull/SparseColoring.lean) | `Multigraph.SparseColoring.edgeColoring_two_centres` |
| [CompletionFootprints.lean](sandbox:/workspace/scratch/96ddfd820f7d/overfull-next/Overfull/NativeReserve/CompletionFootprints.lean) | `NativeReserve.coreFootprint_parity`; `coreFootprint_load_le_error`; `coreFootprint_admissible` |
| [PackingConstruction.lean](sandbox:/workspace/scratch/96ddfd820f7d/overfull-next/Overfull/NativeReserve/PackingConstruction.lean) and [JoiningBounds.lean](sandbox:/workspace/scratch/96ddfd820f7d/overfull-next/Overfull/ResidualPalette/JoiningBounds.lean) | `NativeReserve.BoundaryPacking.uncovered_even`; `BoundaryPacking.exceptional_label_eq`; `joiningCopies_disjoint_core` |
