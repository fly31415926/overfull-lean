import Overfull.BipartiteFactorization.Oriented

/-!
# Disjoint families of actual selected palette graphs

Disjoint palettes control exceptional-internal copies, while disjoint
core blocks control every copy incident with the core. Exact finite union
accounting then retains degrees, core rows, and correction-pool counts.
-/

noncomputable section

namespace Overfull.BipartiteFactorization

open Finset Classical

variable {V E ι : Type*} [Fintype V] [Fintype E] [Fintype ι]
variable (G : Multigraph V E)

omit [Fintype V] [Fintype ι] in
/-- A retained copy incident with the core meets the specified support. -/
theorem core_incidence_in_support (F : Finset E) (U W : Finset V)
    (hsupport : ∀ v ∈ U, v ∉ W → (G.restrictEdges F).degree v = 0)
    (e : E) (he : e ∈ F) (v : V) (hv : v ∈ U) (hve : v ∈ G.edge e) :
    v ∈ W := by
  by_contra hn
  have hpos : 0 < (G.restrictEdges F).degree v := by
    rw [G.restrictEdges_degree]
    exact Finset.card_pos.mpr ⟨e, Finset.mem_inter.mpr
      ⟨he, (G.mem_incidenceEdges v e).mpr hve⟩⟩
  rw [hsupport v hv hn] at hpos
  exact Nat.lt_irrefl 0 hpos

omit [Fintype ι] in
/-- Disjoint original palettes and disjoint core supports force disjoint
selected copies, including parallel copies and exceptional base copies. -/
theorem palette_supported_copies_disjoint {k : ℕ} (c : G.EdgeColoring k)
    (I J : Finset (Fin k)) (U W₁ W₂ : Finset V) (F H : Finset E)
    (hIJ : Disjoint I J) (hW : Disjoint W₁ W₂)
    (hbaseF : F ∩ G.internalEdges Uᶜ ⊆ paletteEdges c I)
    (hbaseH : H ∩ G.internalEdges Uᶜ ⊆ paletteEdges c J)
    (hsupportF : ∀ v ∈ U, v ∉ W₁ → (G.restrictEdges F).degree v = 0)
    (hsupportH : ∀ v ∈ U, v ∉ W₂ → (G.restrictEdges H).degree v = 0) :
    Disjoint F H := by
  apply Finset.disjoint_left.mpr
  intro e heF heH
  have hnone (v : V) (hve : v ∈ G.edge e) : v ∉ U := by
    intro hv
    exact Finset.disjoint_left.mp hW
      (core_incidence_in_support G F U W₁ hsupportF e heF v hv hve)
      (core_incidence_in_support G H U W₂ hsupportH e heH v hv hve)
  have heinternal : e ∈ G.internalEdges Uᶜ := by
    apply (G.mem_internalEdges Uᶜ e).mpr
    constructor
    · exact Finset.mem_compl.mpr (hnone _ (by rw [← G.edge_eq e]; simp))
    · exact Finset.mem_compl.mpr (hnone _ (by rw [← G.edge_eq e]; simp))
  exact Finset.disjoint_left.mp hIJ
    ((mem_paletteEdges c I e).mp (hbaseF (Finset.mem_inter.mpr ⟨heF, heinternal⟩)))
    ((mem_paletteEdges c J e).mp (hbaseH (Finset.mem_inter.mpr ⟨heH, heinternal⟩)))

/-- The actual union of a finite family of copy sets. -/
def familyCopies (F : ι → Finset E) : Finset E := univ.biUnion F

omit [Fintype V] [Fintype E] in
theorem mem_familyCopies (F : ι → Finset E) (e : E) :
    e ∈ familyCopies F ↔ ∃ i, e ∈ F i := by
  simp only [familyCopies, Finset.mem_biUnion, Finset.mem_univ, true_and]

omit [Fintype V] [Fintype E] in
theorem familyCopies_inter (F : ι → Finset E) (P : Finset E) :
    familyCopies F ∩ P = familyCopies (fun i => F i ∩ P) := by
  ext e
  simp only [mem_familyCopies, Finset.mem_inter]
  aesop

omit [Fintype V] [Fintype E] in
/-- Exact intersection counts in a disjoint family of original copies. -/
theorem familyCopies_inter_card (F : ι → Finset E)
    (hdisj : ∀ i j, i ≠ j → Disjoint (F i) (F j)) (P : Finset E) :
    (familyCopies F ∩ P).card = ∑ i, (F i ∩ P).card := by
  rw [familyCopies_inter, familyCopies]
  exact Finset.card_biUnion (fun i _ j _ hij =>
    (hdisj i j hij).mono Finset.inter_subset_left Finset.inter_subset_left)

omit [Fintype V] in
/-- Exact degree addition on the actual union restriction. -/
theorem familyCopies_degree (F : ι → Finset E)
    (hdisj : ∀ i j, i ≠ j → Disjoint (F i) (F j)) (v : V) :
    (G.restrictEdges (familyCopies F)).degree v =
      ∑ i, (G.restrictEdges (F i)).degree v := by
  simp only [G.restrictEdges_degree]
  exact familyCopies_inter_card F hdisj (G.incidenceEdges v)

omit [Fintype V] [Fintype E] in
theorem familyCopies_avoids (F : ι → Finset E) (D : Finset E)
    (hD : ∀ i, Disjoint (F i) D) : Disjoint (familyCopies F) D := by
  apply Finset.disjoint_left.mpr
  intro e he heD
  obtain ⟨i, hei⟩ := (mem_familyCopies F e).mp he
  exact Finset.disjoint_left.mp (hD i) hei heD

omit [Fintype V] in
theorem paletteEdges_family_union {k : ℕ} (c : G.EdgeColoring k)
    (I : ι → Finset (Fin k)) :
    familyCopies (fun i => paletteEdges c (I i)) = paletteEdges c (univ.biUnion I) := by
  ext e
  simp only [mem_familyCopies, mem_paletteEdges, Finset.mem_biUnion,
    Finset.mem_univ, true_and]

omit [Fintype V] [Fintype ι] in
theorem paletteEdges_disjoint {k : ℕ} (c : G.EdgeColoring k)
    {I J : Finset (Fin k)} (hIJ : Disjoint I J) :
    Disjoint (paletteEdges c I) (paletteEdges c J) := by
  apply Finset.disjoint_left.mpr
  intro e heI heJ
  exact Finset.disjoint_left.mp hIJ
    ((mem_paletteEdges c I e).mp heI) ((mem_paletteEdges c J e).mp heJ)

theorem paletteBase_family_union {k : ℕ} (c : G.EdgeColoring k)
    (I : ι → Finset (Fin k)) (U : Finset V) :
    familyCopies (fun i => paletteBase c U (I i)) =
      paletteBase c U (univ.biUnion I) := by
  simp only [paletteBase, ← familyCopies_inter, paletteEdges_family_union]

omit [Fintype V] in
theorem familyCopies_side_degrees (F : ι → Finset E)
    (hdisj : ∀ i j, i ≠ j → Disjoint (F i) (F j)) (A B : Finset V)
    (hbalance : ∀ i, (∑ v ∈ A, (G.restrictEdges (F i)).degree v) =
      ∑ v ∈ B, (G.restrictEdges (F i)).degree v) :
    (∑ v ∈ A, (G.restrictEdges (familyCopies F)).degree v) =
      ∑ v ∈ B, (G.restrictEdges (familyCopies F)).degree v := by
  simp only [familyCopies_degree G F hdisj]
  rw [Finset.sum_comm, Finset.sum_comm (s := B)]
  exact Finset.sum_congr rfl (fun i _ => hbalance i)

omit [Fintype ι] in
/-- Two selected palette graphs with disjoint palettes and disjoint block
unions retain disjoint original copies, whichever correction sign they use. -/
theorem OrientedPalette.copies_disjoint {k : ℕ} {c : G.EdgeColoring k}
    {I J : Finset (Fin k)} {A B A₁ B₁ A₂ B₂ ZA ZB : Finset V}
    {D₁ D₂ : Finset E}
    (S : OrientedPalette G c I A B A₁ B₁ ZA ZB D₁)
    (T : OrientedPalette G c J A B A₂ B₂ ZA ZB D₂)
    (hIJ : Disjoint I J) (hblocks : Disjoint (A₁ ∪ B₁) (A₂ ∪ B₂)) :
    Disjoint S.copies T.copies := by
  apply palette_supported_copies_disjoint G c I J (A ∪ B)
    (A₁ ∪ B₁) (A₂ ∪ B₂) S.copies T.copies hIJ hblocks
  · intro e he
    exact (paletteBase_subset c (A ∪ B) I) (S.base ▸ he)
  · intro e he
    exact (paletteBase_subset c (A ∪ B) J) (T.base ▸ he)
  · exact S.support
  · exact T.support

omit [Fintype ι] in
/-- Construct a finite family from the original per-palette conditions.
Disjoint copies are derived from the disjoint palettes and core blocks. -/
theorem exists_oriented_palette_family {k : ℕ} (c : G.EdgeColoring k)
    (I : ι → Finset (Fin k)) (A B ZA ZB : Finset V)
    (Ablock Bblock : ι → Finset V) (D : Finset E) (ω₁ ω₂ : ℝ)
    (h : ∀ i,
      PaletteSelectionConditions G c (I i) A B (Ablock i) (Bblock i) ZA ZB D ω₁ ω₂ ∨
      PaletteSelectionConditions G c (I i) B A (Bblock i) (Ablock i) ZB ZA D ω₁ ω₂)
    (hpalettes : ∀ i j, i ≠ j → Disjoint (I i) (I j))
    (hblocks : ∀ i j, i ≠ j →
      Disjoint (Ablock i ∪ Bblock i) (Ablock j ∪ Bblock j)) :
    ∃ S : ∀ i, OrientedPalette G c (I i) A B (Ablock i) (Bblock i) ZA ZB D,
      ∀ i j, i ≠ j → Disjoint (S i).copies (S j).copies := by
  have hex (i : ι) := exists_oriented_palette G c (I i) A B
    (Ablock i) (Bblock i) ZA ZB D ω₁ ω₂ (h i)
  let S := fun i => Classical.choice (hex i)
  exact ⟨S, fun i j hij => (S i).copies_disjoint G (S j)
    (hpalettes i j hij) (hblocks i j hij)⟩

variable {k : ℕ} {c : G.EdgeColoring k}
variable {I : ι → Finset (Fin k)} {A B ZA ZB : Finset V}
variable {Ablock Bblock : ι → Finset V} {D : Finset E}

/-- The union's exceptional base is the actual union-palette base. -/
theorem OrientedPalette.family_base
    (S : ∀ i, OrientedPalette G c (I i) A B (Ablock i) (Bblock i) ZA ZB D) :
    familyCopies (fun i => (S i).copies) ∩ G.internalEdges (A ∪ B)ᶜ =
      paletteBase c (A ∪ B) (univ.biUnion I) := by
  rw [familyCopies_inter]
  simp_rw [(S _).base]
  exact paletteBase_family_union G c I (A ∪ B)

/-- Exact exceptional degree of the selected family union. -/
theorem OrientedPalette.family_exceptional_degree
    (S : ∀ i, OrientedPalette G c (I i) A B (Ablock i) (Bblock i) ZA ZB D)
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i).copies (S j).copies)
    (x : V) (hx : x ∉ A ∪ B) :
    (G.restrictEdges (familyCopies (fun i => (S i).copies))).degree x =
      ∑ i, (I i).card := by
  rw [familyCopies_degree G _ hdisj]
  exact Finset.sum_congr rfl (fun i _ => (S i).exceptional_degree x hx)

/-- Disjoint palette cardinalities equal the exact selected union degree. -/
theorem OrientedPalette.family_exceptional_degree_palette_union
    (S : ∀ i, OrientedPalette G c (I i) A B (Ablock i) (Bblock i) ZA ZB D)
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i).copies (S j).copies)
    (hpalettes : ∀ i j, i ≠ j → Disjoint (I i) (I j))
    (x : V) (hx : x ∉ A ∪ B) :
    (G.restrictEdges (familyCopies (fun i => (S i).copies))).degree x =
      (univ.biUnion I).card := by
  rw [OrientedPalette.family_exceptional_degree G S hdisj x hx]
  exact (Finset.card_biUnion (fun i _ j _ hij => hpalettes i j hij)).symm

/-- Exact core-row counts add over the selected family. -/
theorem OrientedPalette.family_rows
    (S : ∀ i, OrientedPalette G c (I i) A B (Ablock i) (Bblock i) ZA ZB D)
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i).copies (S j).copies)
    (x : V) (hx : x ∉ A ∪ B) :
    (familyCopies (fun i => (S i).copies) ∩ G.edgesTo x (A ∪ B)).card =
      ∑ i, (paletteEdges c (I i) ∩ G.edgesTo x (A ∪ B)).card := by
  rw [familyCopies_inter_card _ hdisj]
  exact Finset.sum_congr rfl (fun i _ => (S i).rows x hx)

/-- The selected family's core rows equal the actual union-palette rows. -/
theorem OrientedPalette.family_rows_palette_union
    (S : ∀ i, OrientedPalette G c (I i) A B (Ablock i) (Bblock i) ZA ZB D)
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i).copies (S j).copies)
    (hpalettes : ∀ i j, i ≠ j → Disjoint (I i) (I j))
    (x : V) (hx : x ∉ A ∪ B) :
    (familyCopies (fun i => (S i).copies) ∩ G.edgesTo x (A ∪ B)).card =
      (paletteEdges c (univ.biUnion I) ∩ G.edgesTo x (A ∪ B)).card := by
  rw [OrientedPalette.family_rows G S hdisj x hx,
    ← paletteEdges_family_union G c I]
  exact (familyCopies_inter_card (fun i => paletteEdges c (I i))
    (fun i j hij => paletteEdges_disjoint G c (hpalettes i j hij))
    (G.edgesTo x (A ∪ B))).symm

/-- The exact total selected degree bounds the copies deleted from any
exceptional-to-core row. -/
theorem OrientedPalette.family_core_row_le
    (S : ∀ i, OrientedPalette G c (I i) A B (Ablock i) (Bblock i) ZA ZB D)
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i).copies (S j).copies)
    (x : V) (hx : x ∉ A ∪ B) :
    (familyCopies (fun i => (S i).copies) ∩ G.edgesTo x (A ∪ B)).card ≤
      ∑ i, (I i).card := by
  rw [← OrientedPalette.family_exceptional_degree G S hdisj x hx,
    G.restrictEdges_degree]
  apply Finset.card_le_card
  intro e he
  obtain ⟨heF, heU⟩ := Finset.mem_inter.mp he
  exact Finset.mem_inter.mpr ⟨heF, (G.mem_incidenceEdges x e).mpr
    ((G.mem_edgesTo x (A ∪ B) e).mp heU).1⟩

/-- Positive-pool use is exactly the sum of the positive signed differences. -/
theorem OrientedPalette.family_positive_count
    (S : ∀ i, OrientedPalette G c (I i) A B (Ablock i) (Bblock i) ZA ZB D)
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i).copies (S j).copies) :
    (familyCopies (fun i => (S i).copies) ∩ correctionPool G B ZA).card =
      ∑ i, ((paletteEdges c (I i) ∩ correctionPool G B ZA).card -
        (paletteEdges c (I i) ∩ correctionPool G A ZB).card) := by
  rw [familyCopies_inter_card _ hdisj]
  exact Finset.sum_congr rfl (fun i _ => (S i).positive_count)

/-- Negative-pool use is exactly the sum of the negative signed differences. -/
theorem OrientedPalette.family_negative_count
    (S : ∀ i, OrientedPalette G c (I i) A B (Ablock i) (Bblock i) ZA ZB D)
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i).copies (S j).copies) :
    (familyCopies (fun i => (S i).copies) ∩ correctionPool G A ZB).card =
      ∑ i, ((paletteEdges c (I i) ∩ correctionPool G A ZB).card -
        (paletteEdges c (I i) ∩ correctionPool G B ZA).card) := by
  rw [familyCopies_inter_card _ hdisj]
  exact Finset.sum_congr rfl (fun i _ => (S i).negative_count)

/-- Selected side-degree balance is preserved by the actual disjoint union. -/
theorem OrientedPalette.family_side_degrees
    (S : ∀ i, OrientedPalette G c (I i) A B (Ablock i) (Bblock i) ZA ZB D)
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i).copies (S j).copies) :
    (∑ v ∈ A, (G.restrictEdges (familyCopies (fun i => (S i).copies))).degree v) =
      ∑ v ∈ B, (G.restrictEdges (familyCopies (fun i => (S i).copies))).degree v :=
  familyCopies_side_degrees G _ hdisj A B (fun i => (S i).side_degrees)

end Overfull.BipartiteFactorization
