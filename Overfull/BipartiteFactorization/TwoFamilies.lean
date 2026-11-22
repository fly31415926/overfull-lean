import Overfull.BipartiteFactorization.Assembly
import Overfull.BipartiteFactorization.Families
import Overfull.BipartiteFactorization.FamilyColoring

/-!
# Two families of selected exterior graphs

Additional deletions are charged by their actual preferred-row and
correction-pool incidences. The bounds can be checked on the original
palettes before the fine copies are chosen.
-/

noncomputable section

namespace Overfull.BipartiteFactorization

open Finset Classical

variable {V E : Type*} [Fintype V] [Fintype E]
variable (G : Multigraph V E)

omit [Fintype V] [Fintype E] in
/-- Reserve the copies that an additional deletion may consume from one row. -/
theorem unused_row_after_deletion (P D T : Finset E) (n b : ℕ)
    (hT : (T ∩ P).card ≤ b) (hsupply : n + b ≤ (P \ D).card) :
    n ≤ (P \ (D ∪ T)).card := by
  have heq : (P \ D) \ T = P \ (D ∪ T) := by
    ext e
    simp only [Finset.mem_sdiff, Finset.mem_union, not_or]
    tauto
  have hloss : ((P \ D) ∩ T).card ≤ b := by
    apply (Finset.card_le_card _).trans hT
    intro e he
    obtain ⟨hePD, heT⟩ := Finset.mem_inter.mp he
    exact Finset.mem_inter.mpr ⟨heT, (Finset.mem_sdiff.mp hePD).1⟩
  have hcount := Finset.card_sdiff_add_card_inter (P \ D) T
  rw [heq] at hcount
  omega

omit [Fintype V] [Fintype E] in
/-- A local pool loses at most the original local deletion and the new
deletion's copies in a containing global pool. -/
theorem deleted_pool_union_bound (D T P Q : Finset E) (hPQ : P ⊆ Q) :
    ((D ∪ T) ∩ P).card ≤ (D ∩ P).card + (T ∩ Q).card := by
  rw [Finset.union_inter_distrib_right]
  exact (Finset.card_union_le _ _).trans
    (Nat.add_le_add_left (Finset.card_le_card
      (Finset.inter_subset_inter_left hPQ)) _)

omit [Fintype V] in
theorem correctionPool_mono {Bsmall B Z : Finset V} (hB : Bsmall ⊆ B) :
    correctionPool G Bsmall Z ⊆ correctionPool G B Z := by
  intro e he
  rcases Finset.mem_union.mp he with heB | heZ
  · apply Finset.mem_union_left
    obtain ⟨hx, hy⟩ := (G.mem_internalEdges Bsmall e).mp heB
    exact (G.mem_internalEdges B e).mpr ⟨hB hx, hB hy⟩
  · apply Finset.mem_union_right
    obtain ⟨x, hx, hex⟩ := Finset.mem_biUnion.mp heZ
    exact Finset.mem_biUnion.mpr ⟨x, hx,
      PreferredSelection.edgesTo_mono G hB x hex⟩

/-- Original-data conditions reserving room for later deletions. The row
and pool costs contain no choice of the later deleted copy set. -/
structure ReservedPaletteConditions {k : ℕ} (c : G.EdgeColoring k)
    (I : Finset (Fin k)) (A B Ablock Bblock ZA ZB : Finset V)
    (D : Finset E) (ω₁ ω₂ : ℝ) (rowCost : V → ℕ) (poolCost : ℕ) : Prop
    extends PaletteSelectionConditions G c I A B Ablock Bblock ZA ZB D ω₁ ω₂ where
  left_reserve : ∀ x ∈ ZA,
    (paletteEdges c I ∩ G.edgesTo x (A ∪ B)).card + rowCost x ≤
      (G.edgesTo x Ablock \ D).card
  right_reserve : ∀ x ∈ ZB,
    (paletteEdges c I ∩ G.edgesTo x (A ∪ B)).card + rowCost x ≤
      (G.edgesTo x Bblock \ D).card
  score_reserve : (((paletteEdges c I ∩ correctionPool G B ZA).card -
      (paletteEdges c I ∩ correctionPool G A ZB).card : ℕ) : ℝ) ≤
    ω₂ * (G.internalEdges Bblock).card +
      (∑ x : ZA, min (ω₁ * (G.edgesTo x.val Bblock).card)
        ((paletteEdges c I ∩ G.edgesTo x.val (A ∪ B)).card : ℝ)) -
      ω₂ * ((D ∩ correctionPool G Bblock ZA).card + poolCost)

/-- Transfer the original reserve inequalities to the actual enlarged
deleted set, with no independence assumption on its choice. -/
theorem ReservedPaletteConditions.after_deletion {k : ℕ}
    {c : G.EdgeColoring k} {I : Finset (Fin k)}
    {A B Ablock Bblock ZA ZB : Finset V} {D : Finset E}
    {ω₁ ω₂ : ℝ} {rowCost : V → ℕ} {poolCost : ℕ}
    (h : ReservedPaletteConditions G c I A B Ablock Bblock ZA ZB D
      ω₁ ω₂ rowCost poolCost)
    (T : Finset E) (hbase : Disjoint (paletteBase c (A ∪ B) I) T)
    (hrows : ∀ x ∈ ZA ∪ ZB, (T ∩ G.edgesTo x (A ∪ B)).card ≤ rowCost x)
    (hpool : (T ∩ correctionPool G B ZA).card ≤ poolCost) :
    PaletteSelectionConditions G c I A B Ablock Bblock ZA ZB (D ∪ T) ω₁ ω₂ := by
  refine { h.toPaletteSelectionConditions with
    base_avoids := Finset.disjoint_union_right.mpr ⟨h.base_avoids, hbase⟩
    left_supply := ?_
    right_supply := ?_
    score := ?_ }
  · intro x hx
    apply unused_row_after_deletion (G.edgesTo x Ablock) D T _ (rowCost x)
      _ (h.left_reserve x hx)
    exact (Finset.card_le_card (Finset.inter_subset_inter_left
      (PreferredSelection.edgesTo_mono G
        (h.left_block.trans Finset.subset_union_left) x))).trans
      (hrows x (Finset.mem_union_left _ hx))
  · intro x hx
    apply unused_row_after_deletion (G.edgesTo x Bblock) D T _ (rowCost x)
      _ (h.right_reserve x hx)
    exact (Finset.card_le_card (Finset.inter_subset_inter_left
      (PreferredSelection.edgesTo_mono G
        (h.right_block.trans Finset.subset_union_right) x))).trans
      (hrows x (Finset.mem_union_right _ hx))
  · have hcost := (deleted_pool_union_bound D T (correctionPool G Bblock ZA)
        (correctionPool G B ZA) (correctionPool_mono G h.right_block)).trans
        (Nat.add_le_add_left hpool _)
    have hcostR : (((D ∪ T) ∩ correctionPool G Bblock ZA).card : ℝ) ≤
        (D ∩ correctionPool G Bblock ZA).card + poolCost := by exact_mod_cast hcost
    have hω₂ : 0 ≤ ω₂ := h.weight_nonnegative.trans h.weights_ordered
    exact h.score_reserve.trans (sub_le_sub_left
      (mul_le_mul_of_nonneg_left hcostR hω₂) _)

/-- The original palettes determine the exact row cost of a first family. -/
def familyRowDemand {ι : Type*} [Fintype ι] {k : ℕ} (c : G.EdgeColoring k)
    (I : ι → Finset (Fin k)) (U : Finset V) (x : V) : ℕ :=
  ∑ i, (paletteEdges c (I i) ∩ G.edgesTo x U).card

/-- The original palettes determine the exact positive correction-pool cost. -/
def familyCorrectionDemand {ι : Type*} [Fintype ι] {k : ℕ} (c : G.EdgeColoring k)
    (I : ι → Finset (Fin k)) (A B ZA ZB : Finset V) : ℕ :=
  ∑ i, ((paletteEdges c (I i) ∩ correctionPool G B ZA).card -
    (paletteEdges c (I i) ∩ correctionPool G A ZB).card)

/-- Finite original-data conditions for two scales. The coarse supplies
reserve the exact row and pool costs determined by the fine palettes. -/
structure TwoFamilyConditions {ι κ : Type*} [Fintype ι] [Fintype κ] {k : ℕ}
    (c : G.EdgeColoring k) (I : ι → Finset (Fin k)) (J : κ → Finset (Fin k))
    (A B ZA ZB : Finset V) (Af Bf : ι → Finset V) (Ac Bc : κ → Finset V)
    (D : Finset E) (ωf₁ ωf₂ ωc₁ ωc₂ : ℝ) : Prop where
  fine_conditions : ∀ i,
    PaletteSelectionConditions G c (I i) A B (Af i) (Bf i) ZA ZB D ωf₁ ωf₂ ∨
    PaletteSelectionConditions G c (I i) B A (Bf i) (Af i) ZB ZA D ωf₁ ωf₂
  coarse_reserve : ∀ j,
    ReservedPaletteConditions G c (J j) A B (Ac j) (Bc j) ZA ZB D ωc₁ ωc₂
      (familyRowDemand G c I (A ∪ B)) (familyCorrectionDemand G c I A B ZA ZB) ∨
    ReservedPaletteConditions G c (J j) B A (Bc j) (Ac j) ZB ZA D ωc₁ ωc₂
      (familyRowDemand G c I (B ∪ A)) (familyCorrectionDemand G c I B A ZB ZA)
  fine_palettes : ∀ i j, i ≠ j → Disjoint (I i) (I j)
  coarse_palettes : ∀ i j, i ≠ j → Disjoint (J i) (J j)
  cross_palettes : ∀ i j, Disjoint (I i) (J j)
  fine_blocks : ∀ i j, i ≠ j → Disjoint (Af i ∪ Bf i) (Af j ∪ Bf j)
  coarse_blocks : ∀ i j, i ≠ j → Disjoint (Ac i ∪ Bc i) (Ac j ∪ Bc j)

/-- An inherited base with disjoint labels avoids every selected first-family
copy, even when the two scales have overlapping blocks. -/
theorem paletteBase_disjoint_family {ι : Type*} [Fintype ι] {k : ℕ}
    {c : G.EdgeColoring k} {I : ι → Finset (Fin k)}
    {A B ZA ZB : Finset V} {Af Bf : ι → Finset V} {D : Finset E}
    (S : ∀ i, OrientedPalette G c (I i) A B (Af i) (Bf i) ZA ZB D)
    (J : Finset (Fin k)) (hIJ : ∀ i, Disjoint (I i) J) :
    Disjoint (paletteBase c (A ∪ B) J) (familyCopies (fun i => (S i).copies)) := by
  apply Finset.disjoint_left.mpr
  intro e heJ heT
  obtain ⟨heJP, heInternal⟩ := Finset.mem_inter.mp heJ
  obtain ⟨i, heI⟩ := (mem_familyCopies _ e).mp heT
  have heBase : e ∈ paletteBase c (A ∪ B) (I i) :=
    (S i).base ▸ Finset.mem_inter.mpr ⟨heI, heInternal⟩
  exact Finset.disjoint_left.mp (hIJ i)
    ((mem_paletteEdges c (I i) e).mp (Finset.mem_inter.mp heBase).1)
    ((mem_paletteEdges c J e).mp heJP)

/-- Forget part of the deleted set after retaining the stronger avoidance
proof. The selected original copies and every count remain unchanged. -/
def OrientedPalette.weaken_deleted {k : ℕ} {c : G.EdgeColoring k}
    {I : Finset (Fin k)} {A B Ablock Bblock ZA ZB : Finset V}
    {Dsmall Dlarge : Finset E}
    (S : OrientedPalette G c I A B Ablock Bblock ZA ZB Dlarge)
    (hD : Dsmall ⊆ Dlarge) : OrientedPalette G c I A B Ablock Bblock ZA ZB Dsmall :=
  { S with avoids := S.avoids.mono_right hD }

/-- Construct the fine family first and the coarse family from its unused
copies. All input bounds depend only on the original palettes and pools. -/
theorem exists_two_palette_families {ι κ : Type*} [Fintype ι] [Fintype κ] {k : ℕ}
    (c : G.EdgeColoring k) (I : ι → Finset (Fin k)) (J : κ → Finset (Fin k))
    (A B ZA ZB : Finset V) (Af Bf : ι → Finset V) (Ac Bc : κ → Finset V)
    (D : Finset E) (ωf₁ ωf₂ ωc₁ ωc₂ : ℝ)
    (h : TwoFamilyConditions G c I J A B ZA ZB Af Bf Ac Bc D ωf₁ ωf₂ ωc₁ ωc₂) :
    ∃ S : ∀ i : ι ⊕ κ, OrientedPalette G c (Sum.elim I J i) A B
      (Sum.elim Af Ac i) (Sum.elim Bf Bc i) ZA ZB D,
      ∀ i j, i ≠ j → Disjoint (S i).copies (S j).copies := by
  obtain ⟨Sf, hf⟩ := exists_oriented_palette_family G c I A B ZA ZB Af Bf D ωf₁ ωf₂
    h.fine_conditions h.fine_palettes h.fine_blocks
  let T := familyCopies (fun i => (Sf i).copies)
  have hcoarse (j : κ) :
      PaletteSelectionConditions G c (J j) A B (Ac j) (Bc j) ZA ZB (D ∪ T) ωc₁ ωc₂ ∨
      PaletteSelectionConditions G c (J j) B A (Bc j) (Ac j) ZB ZA (D ∪ T) ωc₁ ωc₂ := by
    have hbase := paletteBase_disjoint_family G Sf (J j) (fun i => h.cross_palettes i j)
    rcases h.coarse_reserve j with hj | hj
    · apply Or.inl
      apply hj.after_deletion G T hbase
      · intro x hx
        have hxU : x ∉ A ∪ B := by
          rcases Finset.mem_union.mp hx with hxA | hxB
          · exact fun hxU => Finset.disjoint_left.mp hj.active_left hxA hxU
          · exact fun hxU => Finset.disjoint_left.mp hj.active_right hxB hxU
        exact (OrientedPalette.family_rows G Sf hf x hxU).le
      · exact (OrientedPalette.family_positive_count G Sf hf).le
    · apply Or.inr
      apply hj.after_deletion G T
        (by simpa only [Finset.union_comm B A] using hbase)
      · intro x hx
        have hxU : x ∉ A ∪ B := by
          have hn : x ∉ B ∪ A := by
            rcases Finset.mem_union.mp hx with hxB | hxA
            · exact fun hxU => Finset.disjoint_left.mp hj.active_left hxB hxU
            · exact fun hxU => Finset.disjoint_left.mp hj.active_right hxA hxU
          simpa only [Finset.union_comm B A] using hn
        simpa only [familyRowDemand, Finset.union_comm B A] using
          (OrientedPalette.family_rows G Sf hf x hxU).le
      · exact (OrientedPalette.family_negative_count G Sf hf).le
  obtain ⟨Sc, hc⟩ := exists_oriented_palette_family G c J A B ZA ZB Ac Bc (D ∪ T)
    ωc₁ ωc₂ hcoarse h.coarse_palettes h.coarse_blocks
  let Sc' := fun j => (Sc j).weaken_deleted G (Finset.subset_union_left : D ⊆ D ∪ T)
  let S : ∀ i : ι ⊕ κ, OrientedPalette G c (Sum.elim I J i) A B
      (Sum.elim Af Ac i) (Sum.elim Bf Bc i) ZA ZB D :=
    fun i => Sum.casesOn i Sf Sc'
  have hcross (i : ι) (j : κ) : Disjoint (Sf i).copies (Sc j).copies := by
    have hiT : (Sf i).copies ⊆ T := fun _ he =>
      (mem_familyCopies _ _).mpr ⟨i, he⟩
    exact ((Sc j).avoids.mono_right Finset.subset_union_right).symm.mono_left hiT
  refine ⟨S, ?_⟩
  intro i j hij
  rcases i with i | i <;> rcases j with j | j
  · exact hf i j (fun h => hij (congrArg Sum.inl h))
  · exact hcross i j
  · exact (hcross j i).symm
  · exact hc i j (fun h => hij (congrArg Sum.inr h))

section Combined

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {k : ℕ}
variable {c : G.EdgeColoring k} {I : ι → Finset (Fin k)} {J : κ → Finset (Fin k)}
variable {A B ZA ZB : Finset V} {Af Bf : ι → Finset V} {Ac Bc : κ → Finset V}
variable {D : Finset E} {ωf₁ ωf₂ ωc₁ ωc₂ : ℝ}

theorem TwoFamilyConditions.palettes_disjoint
    (h : TwoFamilyConditions G c I J A B ZA ZB Af Bf Ac Bc D ωf₁ ωf₂ ωc₁ ωc₂)
    (i j : ι ⊕ κ) (hij : i ≠ j) : Disjoint (Sum.elim I J i) (Sum.elim I J j) := by
  rcases i with i | i <;> rcases j with j | j
  · exact h.fine_palettes i j (fun h => hij (congrArg Sum.inl h))
  · exact h.cross_palettes i j
  · exact (h.cross_palettes j i).symm
  · exact h.coarse_palettes i j (fun h => hij (congrArg Sum.inr h))

/-- The original finite conditions supply block containment and low-row
exclusion in the common geometry, even when the correction sign varies. -/
theorem TwoFamilyConditions.palette_data
    (h : TwoFamilyConditions G c I J A B ZA ZB Af Bf Ac Bc D ωf₁ ωf₂ ωc₁ ωc₂)
    (i : ι ⊕ κ) :
    Sum.elim Af Ac i ⊆ A ∧ Sum.elim Bf Bc i ⊆ B ∧
      ∀ x, x ∉ A ∪ B → x ∉ ZA ∪ ZB →
        paletteEdges c (Sum.elim I J i) ∩ G.edgesTo x (A ∪ B) = ∅ := by
  rcases i with i | i
  · rcases h.fine_conditions i with hi | hi
    · exact ⟨hi.left_block, hi.right_block, hi.low⟩
    · refine ⟨hi.right_block, hi.left_block, ?_⟩
      simpa only [Finset.union_comm B A, Finset.union_comm ZB ZA] using hi.low
  · rcases h.coarse_reserve i with hi | hi
    · exact ⟨hi.left_block, hi.right_block, hi.low⟩
    · refine ⟨hi.right_block, hi.left_block, ?_⟩
      simpa only [Finset.union_comm B A, Finset.union_comm ZB ZA] using hi.low

/-- The union palette size is the exact sum of both families' sizes. -/
theorem TwoFamilyConditions.palette_card
    (h : TwoFamilyConditions G c I J A B ZA ZB Af Bf Ac Bc D ωf₁ ωf₂ ωc₁ ωc₂) :
    (univ.biUnion (Sum.elim I J)).card = (∑ i, (I i).card) + ∑ j, (J j).card := by
  rw [Finset.card_biUnion (fun i _ j _ hij => h.palettes_disjoint G i j hij)]
  exact Fintype.sum_sum_type _

end Combined

/-- Construct both edge-disjoint families, their balanced localized
colorings, and the coloring of the exact remaining graph. The combined
footprint load equals the original core degree. -/
theorem exists_colored_two_families {ι κ : Type*} [Fintype ι] [Fintype κ] {k : ℕ}
    (c : G.EdgeColoring k) (I : ι → Finset (Fin k)) (J : κ → Finset (Fin k))
    (A B ZA ZB : Finset V) (Af Bf : ι → Finset V) (Ac Bc : κ → Finset V)
    (D : Finset E) (ωf₁ ωf₂ ωc₁ ωc₂ : ℝ)
    (h : TwoFamilyConditions G c I J A B ZA ZB Af Bf Ac Bc D ωf₁ ωf₂ ωc₁ ωc₂)
    (a : ℝ) (ha : 0 ≤ a)
    (hAB : Disjoint A B) (hcard : A.card = B.card)
    (hZeven : Even (A ∪ B)ᶜ.card)
    (hZA : Disjoint ZA (A ∪ B)) (hZB : Disjoint ZB (A ∪ B))
    (hfull : ∀ x, x ∉ A ∪ B → G.degree x = k)
    (hfullBalanced : (∑ v ∈ A, G.degree v) = ∑ v ∈ B, G.degree v)
    (hcore : ∀ v ∈ A ∪ B, (G.degree v : ℝ) ≤ a)
    (hka : ∀ i : ι ⊕ κ, 2 * a < (Sum.elim I J i).card)
    (hactive : ∀ (i : ι ⊕ κ) x, x ∈ ZA ∪ ZB →
      2 * a < ((paletteEdges c (Sum.elim I J i) ∩ G.edgesTo x (A ∪ B)).card : ℝ))
    (hblockcard : ∀ i : ι ⊕ κ, (Sum.elim Af Ac i).card = (Sum.elim Bf Bc i).card)
    (hrest : 2 * a < (k - (univ.biUnion (Sum.elim I J)).card : ℕ))
    (hrestActive : ∀ x ∈ ZA ∪ ZB,
      2 * a < ((G.edgesTo x (A ∪ B)).card : ℝ) - (univ.biUnion (Sum.elim I J)).card) :
    ∃ S : ∀ i : ι ⊕ κ, OrientedPalette G c (Sum.elim I J i) A B
        (Sum.elim Af Ac i) (Sum.elim Bf Bc i) ZA ZB D,
      (∀ i j, i ≠ j → Disjoint (S i).copies (S j).copies) ∧
      (∀ x, x ∉ A ∪ B →
        (G.restrictEdges (familyCopies (fun i => (S i).copies))ᶜ).degree x =
          k - ((∑ i, (I i).card) + ∑ j, (J j).card)) ∧
      ∃ d : ∀ i, LocalizedColoring (G.restrictEdges (S i).copies)
          A B (Sum.elim Af Ac i) (Sum.elim Bf Bc i) (Sum.elim I J i).card a,
        ∃ dRest : LocalizedColoring
            (G.restrictEdges (familyCopies (fun i => (S i).copies))ᶜ)
            A B A B (k - (univ.biUnion (Sum.elim I J)).card) a,
          (∀ v ∈ A ∪ B,
            (∑ i, (univ.filter
              (fun j => v ∈ (d i).coloring.exteriorFootprint (A ∪ B) j)).card) +
              (univ.filter
                (fun j => v ∈ dRest.coloring.exteriorFootprint (A ∪ B) j)).card =
                  G.degree v) ∧
          (∀ v ∈ A ∪ B,
            (((∑ i, (univ.filter
              (fun j => v ∈ (d i).coloring.exteriorFootprint (A ∪ B) j)).card) +
              (univ.filter
                (fun j => v ∈ dRest.coloring.exteriorFootprint (A ∪ B) j)).card : ℕ) : ℝ) ≤ a) := by
  obtain ⟨S, hdisj⟩ := exists_two_palette_families G c I J A B ZA ZB Af Bf Ac Bc
    D ωf₁ ωf₂ ωc₁ ωc₂ h
  obtain ⟨d, dRest, hload, hloadle⟩ := exists_family_and_remaining_colorings G c
    (Sum.elim I J) A B ZA ZB (Sum.elim Af Ac) (Sum.elim Bf Bc) D S hdisj
    (h.palettes_disjoint G) a ha hAB hcard hZeven hZA hZB hfull hfullBalanced hcore
    hka (fun i => (h.palette_data G i).2.2) hactive
    (fun i => (h.palette_data G i).1) (fun i => (h.palette_data G i).2.1)
    hblockcard hrest hrestActive
  refine ⟨S, hdisj, ?_, d, dRest, hload, hloadle⟩
  intro x hx
  rw [← h.palette_card G]
  exact remaining_exceptional_degree G (familyCopies (fun i => (S i).copies))
    (A ∪ B) k (univ.biUnion (Sum.elim I J)).card hfull
    (fun y hy => OrientedPalette.family_exceptional_degree_palette_union G S
      hdisj (h.palettes_disjoint G) y hy) x hx

end Overfull.BipartiteFactorization
