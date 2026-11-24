import Overfull.BipartiteFactorization.LocalizationBounds

/-!
# Constructing actual localized graphs from sampled estimates

This file converts sampled row counts, correction-pool counts, and floor
scores into the deterministic selection conditions. The preferred supplies
and adaptive losses are counted on original copies. In particular, no
correction-capacity or coloring-existence conclusion is assumed.
-/

noncomputable section

namespace Overfull.BipartiteFactorization

open Finset Classical LocalizationBounds

variable {V E : Type*} [Fintype V] [Fintype E]
variable (G : Multigraph V E)

/-- The fixed graph, palette, and block geometry, before numerical supply
and correction-capacity conditions are derived. -/
structure PaletteGeometry {k : ℕ} (c : G.EdgeColoring k) (I : Finset (Fin k))
    (A B Ablock Bblock ZA ZB : Finset V) (D : Finset E) : Prop where
  sides : Disjoint A B
  active_left : Disjoint ZA (A ∪ B)
  active_right : Disjoint ZB (A ∪ B)
  active_disjoint : Disjoint ZA ZB
  left_block : Ablock ⊆ A
  right_block : Bblock ⊆ B
  full_degree : ∀ x, x ∉ A ∪ B → G.degree x = k
  balanced : ∀ i ∈ I, c.coveredCount A i = c.coveredCount B i
  low : ∀ x, x ∉ A ∪ B → x ∉ ZA ∪ ZB →
    paletteEdges c I ∩ G.edgesTo x (A ∪ B) = ∅
  base_avoids : Disjoint (paletteBase c (A ∪ B) I) D
  orientation : (paletteEdges c I ∩ correctionPool G A ZB).card ≤
    (paletteEdges c I ∩ correctionPool G B ZA).card

omit [Fintype V] [Fintype E] in
/-- A preferred row reserves an explicit number of copies for a later
family while still supplying the present palette. -/
theorem preferred_row_reserve (P F D : Finset E) (r cost : ℕ)
    (β p c lam : ℝ) (hc : 0 ≤ c) (hF : F ⊆ P)
    (hraw : β * p * c / 8 ≤ (F.card : ℝ))
    (hboundary : ((D ∩ F).card : ℝ) ≤ β * p * c / 32)
    (hcost : (cost : ℝ) ≤ β * p * c / 32)
    (hpalette : lam ≤ β * p / 32) (hdemand : (r : ℝ) ≤ 2 * lam * c) :
    r + cost ≤ (P \ D).card := by
  have hsplit : ((F \ D).card : ℝ) + (D ∩ F).card = F.card := by
    have hh := card_sdiff_add_card_inter F D
    rw [inter_comm F D] at hh
    exact_mod_cast hh
  have hcap := mul_le_mul_of_nonneg_right hpalette hc
  have hremain : ((r + cost : ℕ) : ℝ) ≤ (F \ D).card := by
    rw [Nat.cast_add]
    nlinarith
  exact (Nat.cast_le.mp hremain).trans
    (card_le_card (sdiff_subset_sdiff hF (Subset.refl _)))

omit [Fintype V] [Fintype E] in
/-- Ordinary representative rows and special incidence rows give the same
usable supply interface. Special rows are first stripped of their larger
permitted boundary loss. -/
theorem exists_preferred_supply_from_row_kind (P D : Finset E) (β p c : ℝ)
    (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (hp : 0 ≤ p) (hc : 0 ≤ c)
    (hrow :
      (∃ F : Finset E, F ⊆ P ∧ β * p * c / 8 ≤ (F.card : ℝ) ∧
        ((D ∩ F).card : ℝ) ≤ β * p * c / 32) ∨
      (p * c / 3 ≤ (P.card : ℝ) ∧ ((D ∩ P).card : ℝ) ≤ p * c / 12)) :
    ∃ F : Finset E, F ⊆ P ∧ β * p * c / 8 ≤ (F.card : ℝ) ∧
      ((D ∩ F).card : ℝ) ≤ β * p * c / 32 := by
  rcases hrow with h | h
  · exact h
  · refine ⟨P \ D, sdiff_subset, special_supply_after_boundary P D β p c
      hβ1 hp hc h.1 h.2, ?_⟩
    have heq : D ∩ (P \ D) = ∅ := by
      ext e
      simp only [mem_inter, mem_sdiff, notMem_empty]
      tauto
    rw [heq, card_empty, Nat.cast_zero]
    positivity

/-- Deleting core-boundary copies never deletes an exceptional-internal
base copy. This statement allows the boundary to depend on prior choices. -/
theorem paletteBase_avoids_boundary {k : ℕ} (c : G.EdgeColoring k)
    (I : Finset (Fin k)) (U Y : Finset V) (hY : Y ⊆ U) :
    Disjoint (paletteBase c U I) (boundaryCopies G Y) := by
  apply disjoint_left.mpr
  intro e heb heY
  obtain ⟨y, hy, hye⟩ := (mem_boundaryCopies G Y e).mp heY
  have hyU : y ∈ Uᶜ := PreferredSelection.internal_incident G Uᶜ e y
    (mem_inter.mp heb).2 hye
  exact (mem_compl.mp hyU) (hY hy)

/-- Equal correction demands need no score estimate or correction pool.
Zero weights construct the finite selection conditions directly. -/
theorem PaletteGeometry.zero_correction_conditions {k : ℕ}
    {c : G.EdgeColoring k} {I : Finset (Fin k)}
    {A B Ablock Bblock ZA ZB : Finset V} {D : Finset E}
    (h : PaletteGeometry G c I A B Ablock Bblock ZA ZB D)
    (hleft : ∀ x ∈ ZA, (paletteEdges c I ∩ G.edgesTo x (A ∪ B)).card ≤
      (G.edgesTo x Ablock \ D).card)
    (hright : ∀ x ∈ ZB, (paletteEdges c I ∩ G.edgesTo x (A ∪ B)).card ≤
      (G.edgesTo x Bblock \ D).card)
    (hzero : (paletteEdges c I ∩ correctionPool G B ZA).card =
      (paletteEdges c I ∩ correctionPool G A ZB).card) :
    PaletteSelectionConditions G c I A B Ablock Bblock ZA ZB D 0 0 := by
  exact {
    sides := h.sides
    active_left := h.active_left
    active_right := h.active_right
    active_disjoint := h.active_disjoint
    left_block := h.left_block
    right_block := h.right_block
    full_degree := h.full_degree
    balanced := h.balanced
    low := h.low
    base_avoids := h.base_avoids
    orientation := h.orientation
    left_supply := hleft
    right_supply := hright
    weight_nonnegative := le_rfl
    weights_ordered := le_rfl
    weight_at_most_one := by norm_num
    score := by simp [hzero] }

/-- Construct the actual selected graph in the zero-correction branch,
including the case where every correction pool is small and excluded. -/
theorem exists_selected_palette_without_correction {k : ℕ}
    (c : G.EdgeColoring k) (I : Finset (Fin k))
    (A B Ablock Bblock ZA ZB : Finset V) (D : Finset E)
    (h : PaletteGeometry G c I A B Ablock Bblock ZA ZB D)
    (hleft : ∀ x ∈ ZA, (paletteEdges c I ∩ G.edgesTo x (A ∪ B)).card ≤
      (G.edgesTo x Ablock \ D).card)
    (hright : ∀ x ∈ ZB, (paletteEdges c I ∩ G.edgesTo x (A ∪ B)).card ≤
      (G.edgesTo x Bblock \ D).card)
    (hzero : (paletteEdges c I ∩ correctionPool G B ZA).card =
      (paletteEdges c I ∩ correctionPool G A ZB).card) :
    ∃ S : SelectedPalette G c I A B Ablock Bblock ZA ZB D,
      S.copies ∩ correctionPool G B ZA = ∅ ∧
      S.copies ∩ correctionPool G A ZB = ∅ := by
  obtain ⟨S⟩ := exists_selected_palette G c I A B Ablock Bblock ZA ZB D 0 0
    (h.zero_correction_conditions G hleft hright hzero)
  refine ⟨S, card_eq_zero.mp ?_, S.negative_empty⟩
  rw [S.positive_count, hzero, Nat.sub_self]

/-- Derive every reserved supply and score condition from actual sampled
estimates and explicit original-copy boundary and earlier-family budgets. -/
theorem reserved_palette_conditions_of_samples {k : ℕ}
    (c : G.EdgeColoring k) (I : Finset (Fin k))
    (A B Ablock Bblock ZA ZB : Finset V) (D : Finset E)
    (hgeom : PaletteGeometry G c I A B Ablock Bblock ZA ZB D)
    (F : V → Finset E) (rowCost : V → ℕ) (poolCost : ℕ)
    (β p lam : ℝ) (hlam : 0 ≤ lam) (hp : 0 < p) (hp1 : p ≤ 1)
    (hweight : 64 * lam ≤ p ^ 2) (hpalette : lam ≤ β * p / 32)
    (hleft : ∀ x ∈ ZA, F x ⊆ G.edgesTo x Ablock)
    (hright : ∀ x ∈ ZB, F x ⊆ G.edgesTo x Bblock)
    (hraw : ∀ x ∈ ZA ∪ ZB, β * p * (G.edgesTo x (A ∪ B)).card / 8 ≤ (F x).card)
    (hboundary : ∀ x ∈ ZA ∪ ZB, ((D ∩ F x).card : ℝ) ≤
      β * p * (G.edgesTo x (A ∪ B)).card / 32)
    (hrowCost : ∀ x ∈ ZA ∪ ZB, (rowCost x : ℝ) ≤
      β * p * (G.edgesTo x (A ∪ B)).card / 32)
    (hrows : ∀ x ∈ ZA ∪ ZB,
      (15 / 16 : ℝ) * lam * (G.edgesTo x (A ∪ B)).card ≤
        ((paletteEdges c I ∩ G.edgesTo x (A ∪ B)).card : ℝ) ∧
      ((paletteEdges c I ∩ G.edgesTo x (A ∪ B)).card : ℝ) ≤
        2 * lam * (G.edgesTo x (A ∪ B)).card)
    (hpool : ((paletteEdges c I ∩ correctionPool G B ZA).card : ℝ) ≤
      (5 / 4 : ℝ) * lam * (correctionPool G B ZA).card)
    (hscore : (13 / 8 : ℝ) * lam * (correctionPool G B ZA).card ≤
      BlockSampling.cappedScore G ZA
        (fun x => (⌊(15 / 16 : ℝ) * lam * (G.edgesTo x (A ∪ B)).card⌋₊ : ℝ))
        (64 * lam / p) (64 * lam / p ^ 2) Bblock)
    (hloss : ((D ∩ correctionPool G Bblock ZA).card : ℝ) + poolCost ≤
      p ^ 2 * (correctionPool G B ZA).card / 512) :
    ReservedPaletteConditions G c I A B Ablock Bblock ZA ZB D
      (64 * lam / p) (64 * lam / p ^ 2) rowCost poolCost := by
  have hweights := selection_weights lam p hlam hp hp1 hweight
  have hleftReserve (x : V) (hx : x ∈ ZA) :
      (paletteEdges c I ∩ G.edgesTo x (A ∪ B)).card + rowCost x ≤
        (G.edgesTo x Ablock \ D).card := by
    have hx' := mem_union_left ZB hx
    exact preferred_row_reserve (G.edgesTo x Ablock) (F x) D _ (rowCost x)
      β p (G.edgesTo x (A ∪ B)).card lam (Nat.cast_nonneg _) (hleft x hx)
      (hraw x hx') (hboundary x hx') (hrowCost x hx') hpalette (hrows x hx').2
  have hrightReserve (x : V) (hx : x ∈ ZB) :
      (paletteEdges c I ∩ G.edgesTo x (A ∪ B)).card + rowCost x ≤
        (G.edgesTo x Bblock \ D).card := by
    have hx' := mem_union_right ZA hx
    exact preferred_row_reserve (G.edgesTo x Bblock) (F x) D _ (rowCost x)
      β p (G.edgesTo x (A ∪ B)).card lam (Nat.cast_nonneg _) (hright x hx)
      (hraw x hx') (hboundary x hx') (hrowCost x hx') hpalette (hrows x hx').2
  have hscoreReserve := reserved_score_of_sampled_bounds G c I A B ZA ZB Bblock
    D poolCost lam p hlam hp (fun x hx => (hrows x (mem_union_left _ hx)).1)
    hpool hscore hloss
  have hscoreNow := reserved_score_of_sampled_bounds G c I A B ZA ZB Bblock
    D 0 lam p hlam hp (fun x hx => (hrows x (mem_union_left _ hx)).1)
    hpool hscore (by simpa using le_trans (le_add_of_nonneg_right
      (Nat.cast_nonneg poolCost)) hloss)
  refine {
    sides := hgeom.sides
    active_left := hgeom.active_left
    active_right := hgeom.active_right
    active_disjoint := hgeom.active_disjoint
    left_block := hgeom.left_block
    right_block := hgeom.right_block
    full_degree := hgeom.full_degree
    balanced := hgeom.balanced
    low := hgeom.low
    base_avoids := hgeom.base_avoids
    orientation := hgeom.orientation
    left_supply := fun x hx => (Nat.le_add_right _ _).trans (hleftReserve x hx)
    right_supply := fun x hx => (Nat.le_add_right _ _).trans (hrightReserve x hx)
    weight_nonnegative := hweights.1
    weights_ordered := hweights.2.1
    weight_at_most_one := hweights.2.2
    score := by simpa using hscoreNow
    left_reserve := hleftReserve
    right_reserve := hrightReserve
    score_reserve := hscoreReserve }

omit [Fintype V] [Fintype E] in
/-- Active row and error bounds give the strict palette and active-degree
inequalities needed for the fan-coloring theorem. -/
theorem sampled_coloring_reserves (k s r : ℕ) (a lam θ c : ℝ)
    (hk : 0 < k) (hlam : 0 < lam) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hs : (s : ℝ) = lam * k) (hc : θ * k ≤ c)
    (hrow : (15 / 16 : ℝ) * lam * c ≤ r)
    (ha : a ≤ lam * θ * k / 16) :
    2 * a < s ∧ 2 * a < r := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hpos : 0 < lam * θ * k := by positivity
  have hθk := mul_le_mul_of_nonneg_right hθ1 (mul_nonneg hlam.le hkR.le)
  have hc' := mul_le_mul_of_nonneg_left hc hlam.le
  rw [hs]
  constructor <;> nlinarith

/-- Once the sampled bounds have supplied the reserved conditions, the
actual palette graph and its balanced localized coloring are constructed.
The strict coloring reserves are derived from the small error and active
row bounds, rather than supplied as coloring assumptions. -/
theorem exists_colored_sampled_palette {k : ℕ}
    (c : G.EdgeColoring k) (I : Finset (Fin k))
    (A B Ablock Bblock ZA ZB : Finset V) (D : Finset E)
    (ω₁ ω₂ : ℝ) (h : PaletteSelectionConditions G c I A B Ablock Bblock ZA ZB D ω₁ ω₂)
    (a lam θ : ℝ) (ha : 0 ≤ a) (hk : 0 < k)
    (hlam : 0 < lam) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hsize : (I.card : ℝ) = lam * k) (hsmall : a ≤ lam * θ * k / 16)
    (hactive : ∀ x ∈ ZA ∪ ZB, θ * k ≤ ((G.edgesTo x (A ∪ B)).card : ℝ))
    (hrows : ∀ x ∈ ZA ∪ ZB,
      (15 / 16 : ℝ) * lam * (G.edgesTo x (A ∪ B)).card ≤
        ((paletteEdges c I ∩ G.edgesTo x (A ∪ B)).card : ℝ))
    (hcard : A.card = B.card) (hZeven : Even (A ∪ B)ᶜ.card)
    (hcore : ∀ v ∈ A ∪ B, (G.degree v : ℝ) ≤ a)
    (hblockcard : Ablock.card = Bblock.card) :
    ∃ S : SelectedPalette G c I A B Ablock Bblock ZA ZB D,
      Nonempty (LocalizedColoring (G.restrictEdges S.copies)
        A B Ablock Bblock I.card a) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hpos : 0 < lam * θ * k := by positivity
  have hθk := mul_le_mul_of_nonneg_right hθ1 (mul_nonneg hlam.le hkR.le)
  have hka : 2 * a < I.card := by rw [hsize]; nlinarith
  obtain ⟨S⟩ := exists_selected_palette G c I A B Ablock Bblock ZA ZB D ω₁ ω₂ h
  obtain ⟨d, hd⟩ := S.exists_localized_coloring G a ha hka h.sides hcard hZeven hcore
    h.low (fun x hx => (sampled_coloring_reserves k I.card _ a lam θ
      (G.edgesTo x (A ∪ B)).card hk hlam hθ hθ1 hsize (hactive x hx)
      (hrows x hx) hsmall).2) h.active_left h.active_right h.left_block h.right_block hblockcard
  exact ⟨S, ⟨⟨d, hd.1, hd.2.1, hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2.1,
    hd.2.2.2.2.2.1, hd.2.2.2.2.2.2.1, hd.2.2.2.2.2.2.2⟩⟩⟩

end Overfull.BipartiteFactorization
