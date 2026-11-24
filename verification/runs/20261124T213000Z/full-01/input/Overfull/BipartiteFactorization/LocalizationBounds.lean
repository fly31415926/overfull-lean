import Overfull.BipartiteFactorization.TwoFamilies
import Overfull.BipartiteFactorization.BlockSelectionBudget
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Integer caps and losses in the localization construction

The actual floor caps and manuscript weights satisfy the sampling and
selection interfaces.  Boundary losses count original edge copies, and
representative rows lose at most one copy per boundary vertex.  All bounds
are deterministic and permit a boundary chosen after the random labels.
-/

noncomputable section

namespace Overfull.BipartiteFactorization.LocalizationBounds

open Finset Classical

/-- The floor error fits inside the gap between the two required cap
constants once the expected row size is at least 64. -/
theorem floor_cap_bounds (lam c : ℝ) (hsize : 64 ≤ lam * c) :
    (59 / 64 : ℝ) * lam * c ≤ (⌊(15 / 16 : ℝ) * lam * c⌋₊ : ℝ) ∧
      (⌊(15 / 16 : ℝ) * lam * c⌋₊ : ℝ) ≤ (15 / 16 : ℝ) * lam * c := by
  have hnonneg : 0 ≤ (15 / 16 : ℝ) * lam * c := by nlinarith
  have hlo := Nat.lt_floor_add_one ((15 / 16 : ℝ) * lam * c)
  exact ⟨by nlinarith, Nat.floor_le hnonneg⟩

/-- The cap is an integer no larger than the actual sampled row demand. -/
theorem floor_cap_le_row (lam c : ℝ) (r : ℕ)
    (hrow : (15 / 16 : ℝ) * lam * c ≤ r) :
    ⌊(15 / 16 : ℝ) * lam * c⌋₊ ≤ r :=
  Nat.floor_le_of_le hrow

/-- A uniform order threshold supplies every cap interval, for every later
palette fraction and active row above the fixed positive lower bounds. -/
theorem exists_uniform_floor_caps (lam₀ c₀ : ℝ) (hlam : 0 < lam₀) (hc : 0 < c₀) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ lam c : ℝ,
      lam₀ ≤ lam → c₀ * m ≤ c →
      (59 / 64 : ℝ) * lam * c ≤ (⌊(15 / 16 : ℝ) * lam * c⌋₊ : ℝ) ∧
        (⌊(15 / 16 : ℝ) * lam * c⌋₊ : ℝ) ≤ (15 / 16 : ℝ) * lam * c := by
  obtain ⟨m₀, hm₀⟩ := exists_nat_gt (64 / (lam₀ * c₀))
  refine ⟨m₀, ?_⟩
  intro m hm lam c hlam' hc'
  have hmR : (m₀ : ℝ) ≤ m := by exact_mod_cast hm
  have hprod : 64 < lam₀ * c₀ * m :=
    (div_lt_iff₀ (mul_pos hlam hc)).mp (hm₀.trans_le hmR) |>.trans_eq (by ring)
  have hnonneg : 0 ≤ c₀ * (m : ℝ) := mul_nonneg hc.le (Nat.cast_nonneg _)
  have hcompare : lam₀ * (c₀ * m) ≤ lam * c :=
    mul_le_mul hlam' hc' hnonneg (hlam.le.trans hlam')
  apply floor_cap_bounds
  nlinarith

/-- The exact weights in the manuscript are ordered and at most one. -/
theorem selection_weights (lam p : ℝ) (hlam : 0 ≤ lam)
    (hp : 0 < p) (hp1 : p ≤ 1) (hsmall : 64 * lam ≤ p ^ 2) :
    0 ≤ 64 * lam / p ∧ 64 * lam / p ≤ 64 * lam / p ^ 2 ∧
      64 * lam / p ^ 2 ≤ 1 := by
  have hpp : p ^ 2 ≤ p := by nlinarith
  refine ⟨by positivity, ?_, (div_le_one (sq_pos_of_pos hp)).mpr hsmall⟩
  exact div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hp) hpp

/-- The palette-size condition implies the weight bound, even at the
largest permitted ordinary and active-row parameters. -/
theorem selection_weights_of_palette_bound (lam p β θ : ℝ)
    (hlam : 0 ≤ lam) (hp : 0 < p) (hp1 : p ≤ 1)
    (_hβ : 0 ≤ β) (hβ1 : β ≤ 1) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hsmall : lam ≤ β * p ^ 2 * θ / 262144) :
    0 ≤ 64 * lam / p ∧ 64 * lam / p ≤ 64 * lam / p ^ 2 ∧
      64 * lam / p ^ 2 ≤ 1 := by
  have hprod : β * θ ≤ 1 := (mul_le_mul hβ1 hθ1 hθ (by norm_num)).trans_eq (by ring)
  have hh := mul_le_mul_of_nonneg_right hprod (sq_nonneg p)
  apply selection_weights lam p hlam hp hp1
  nlinarith [sq_nonneg p]

/-- The adaptive pool-loss budget consumes at most one eighth of its
palette-scaled mass. -/
theorem weighted_pool_loss (lam p M loss : ℝ) (hlam : 0 ≤ lam) (hp : 0 < p)
    (hloss : loss ≤ p ^ 2 * M / 512) :
    (64 * lam / p ^ 2) * loss ≤ lam * M / 8 := by
  calc
    _ ≤ (64 * lam / p ^ 2) * (p ^ 2 * M / 512) :=
      mul_le_mul_of_nonneg_left hloss (by positivity)
    _ = lam * M / 8 := by field_simp; ring

/-- After any deletion obeying the pool budget, the sampled score retains
three halves of the palette-scaled pool size. -/
theorem score_survives_pool_loss (lam p M score loss : ℝ)
    (hlam : 0 ≤ lam) (hp : 0 < p)
    (hscore : (13 / 8 : ℝ) * lam * M ≤ score)
    (hloss : loss ≤ p ^ 2 * M / 512) :
    (3 / 2 : ℝ) * lam * M ≤ score - (64 * lam / p ^ 2) * loss := by
  have hh := weighted_pool_loss lam p M loss hlam hp hloss
  linarith

/-- Fine corrections and the boundary each consume at most half of the
coarse loss budget. -/
theorem coarse_pool_loss (p M boundary fine : ℝ)
    (hboundary : boundary ≤ p ^ 2 * M / 1024)
    (hfine : fine ≤ p ^ 2 * M / 1024) :
    boundary + fine ≤ p ^ 2 * M / 512 := by linarith

variable {V E : Type*} [Fintype E]

/-- All original copies incident with at least one boundary vertex. -/
def boundaryCopies (G : Multigraph V E) (Y : Finset V) : Finset E :=
  Y.biUnion G.incidenceEdges

theorem mem_boundaryCopies (G : Multigraph V E) (Y : Finset V) (e : E) :
    e ∈ boundaryCopies G Y ↔ ∃ y ∈ Y, y ∈ G.edge e := by
  simp only [boundaryCopies, mem_biUnion, G.mem_incidenceEdges]

/-- For a source outside the boundary, a deleted row copy is exactly a
copy whose other endpoint belongs to the boundary. -/
theorem boundaryCopies_inter_row (G : Multigraph V E) (Y U : Finset V)
    (x : V) (hx : x ∉ Y) :
    boundaryCopies G Y ∩ G.edgesTo x U = G.edgesTo x (Y ∩ U) := by
  ext e
  constructor
  · rintro he
    obtain ⟨heY, heU⟩ := mem_inter.mp he
    obtain ⟨hxe, hoU⟩ := (G.mem_edgesTo x U e).mp heU
    obtain ⟨y, hy, hye⟩ := (mem_boundaryCopies G Y e).mp heY
    rw [G.edge_eq_otherEnd x e hxe, Sym2.mem_iff] at hye
    rcases hye with rfl | hyo
    · exact (hx hy).elim
    · exact (G.mem_edgesTo x (Y ∩ U) e).mpr
        ⟨hxe, mem_inter.mpr ⟨hyo ▸ hy, hoU⟩⟩
  · intro he
    obtain ⟨hxe, ho⟩ := (G.mem_edgesTo x (Y ∩ U) e).mp he
    obtain ⟨hoY, hoU⟩ := mem_inter.mp ho
    refine mem_inter.mpr ⟨?_, (G.mem_edgesTo x U e).mpr ⟨hxe, hoU⟩⟩
    apply (mem_boundaryCopies G Y e).mpr
    exact ⟨G.otherEnd x e, hoY, by rw [G.edge_eq_otherEnd x e hxe]; simp⟩

/-- Distinct representative endpoints turn the actual boundary deletion
into a cardinality loss of at most one per boundary vertex. -/
theorem representative_boundary_loss (G : Multigraph V E) (Y U : Finset V)
    (x : V) (hx : x ∉ Y) (F : Finset E) (hF : F ⊆ G.edgesTo x U)
    (hinj : Set.InjOn (G.otherEnd x) F) :
    (boundaryCopies G Y ∩ F).card ≤ Y.card := by
  have hinj' : Set.InjOn (G.otherEnd x) (↑(boundaryCopies G Y ∩ F) : Set E) := by
    intro e he f hf hef
    exact hinj (mem_inter.mp he).2 (mem_inter.mp hf).2 hef
  rw [← card_image_of_injOn hinj']
  apply card_le_card
  intro y hy
  obtain ⟨e, he, rfl⟩ := mem_image.mp hy
  have he' : e ∈ boundaryCopies G Y ∩ G.edgesTo x U :=
    mem_inter.mpr ⟨(mem_inter.mp he).1, hF (mem_inter.mp he).2⟩
  rw [boundaryCopies_inter_row G Y U x hx] at he'
  exact (mem_inter.mp ((G.mem_edgesTo x (Y ∩ U) e).mp he').2).1

omit [Fintype E] in
/-- Two arbitrary deleted copy sets consume only their intersections with
the actual supply. -/
theorem supply_card_le_remaining_add_losses (F D T : Finset E) :
    F.card ≤ (F \ (D ∪ T)).card + (D ∩ F).card + (T ∩ F).card := by
  have hsplit := card_sdiff_add_card_inter F (D ∪ T)
  have hloss : (F ∩ (D ∪ T)).card ≤ (D ∩ F).card + (T ∩ F).card := by
    rw [inter_union_distrib_left, inter_comm F D, inter_comm F T]
    exact card_union_le _ _
  omega

omit [Fintype E] in
/-- The raw preferred-row bound survives boundary and earlier-family
losses, and supplies the entire actual palette demand. -/
theorem preferred_supply_after_losses (P F D T : Finset E) (r : ℕ)
    (β p c lam : ℝ) (hc : 0 ≤ c) (hF : F ⊆ P)
    (hraw : β * p * c / 8 ≤ (F.card : ℝ))
    (hboundary : ((D ∩ F).card : ℝ) ≤ β * p * c / 32)
    (hearlier : ((T ∩ F).card : ℝ) ≤ β * p * c / 32)
    (hpalette : lam ≤ β * p / 32) (hdemand : (r : ℝ) ≤ 2 * lam * c) :
    r ≤ (P \ (D ∪ T)).card := by
  have hcount : (F.card : ℝ) ≤ (F \ (D ∪ T)).card +
      (D ∩ F).card + (T ∩ F).card := by
    exact_mod_cast supply_card_le_remaining_add_losses F D T
  have hcap := mul_le_mul_of_nonneg_right hpalette hc
  have hremain : (r : ℝ) ≤ (F \ (D ∪ T)).card := by nlinarith
  exact (Nat.cast_le.mp hremain).trans (card_le_card (sdiff_subset_sdiff hF (Subset.refl _)))

omit [Fintype E] in
/-- Special rows initially supply one third of their expected incidence;
the larger permitted boundary loss still leaves the ordinary row bound. -/
theorem special_supply_after_boundary (F D : Finset E) (β p c : ℝ)
    (hβ : β ≤ 1) (hp : 0 ≤ p) (hc : 0 ≤ c)
    (hraw : p * c / 3 ≤ (F.card : ℝ))
    (hloss : ((D ∩ F).card : ℝ) ≤ p * c / 12) :
    β * p * c / 8 ≤ ((F \ D).card : ℝ) := by
  have hsplit : ((F \ D).card : ℝ) + (D ∩ F).card = F.card := by
    have hh := card_sdiff_add_card_inter F D
    rw [inter_comm F D] at hh
    exact_mod_cast hh
  have hh := mul_le_mul_of_nonneg_right hβ (mul_nonneg hp hc)
  nlinarith [mul_nonneg hp hc]

/-- Raising row caps only increases the actual score on a fixed block. -/
theorem cappedScore_mono_caps (G : Multigraph V E) (Z T : Finset V)
    (ell ell' : V → ℝ) (ω₁ ω₂ : ℝ) (h : ∀ x ∈ Z, ell x ≤ ell' x) :
    BlockSampling.cappedScore G Z ell ω₁ ω₂ T ≤
      BlockSampling.cappedScore G Z ell' ω₁ ω₂ T := by
  unfold BlockSampling.cappedScore
  apply add_le_add_left
  exact sum_le_sum (fun x hx => min_le_min_left _ (h x hx))

/-- The sampled floor score is a lower bound for the actual palette-demand
score. The latter is the expression used by the correction construction. -/
theorem floor_score_le_palette_score (G : Multigraph V E) {k : ℕ}
    (c : G.EdgeColoring k) (I : Finset (Fin k)) (U Z T : Finset V)
    (lam ω₁ ω₂ : ℝ)
    (hrow : ∀ x ∈ Z, (15 / 16 : ℝ) * lam * (G.edgesTo x U).card ≤
      ((paletteEdges c I ∩ G.edgesTo x U).card : ℝ)) :
    BlockSampling.cappedScore G Z
      (fun x => (⌊(15 / 16 : ℝ) * lam * (G.edgesTo x U).card⌋₊ : ℝ)) ω₁ ω₂ T ≤
      ω₂ * (G.internalEdges T).card +
        ∑ x : Z, min (ω₁ * (G.edgesTo x.val T).card)
          ((paletteEdges c I ∩ G.edgesTo x.val U).card : ℝ) := by
  have h := cappedScore_mono_caps G Z T
    (fun x => (⌊(15 / 16 : ℝ) * lam * (G.edgesTo x U).card⌋₊ : ℝ))
    (fun x => ((paletteEdges c I ∩ G.edgesTo x U).card : ℝ)) ω₁ ω₂
    (fun x hx => Nat.cast_le.mpr (floor_cap_le_row lam _ _ (hrow x hx)))
  rw [sum_coe_sort Z (fun x : V => min (ω₁ * (G.edgesTo x T).card)
    ((paletteEdges c I ∩ G.edgesTo x U).card : ℝ))]
  exact h

/-- Actual sampled row, pool, and floor-score estimates imply the precise
reserved score needed by the deterministic palette construction. Only
deleted copies in the local correction pool are charged. -/
theorem reserved_score_of_sampled_bounds (G : Multigraph V E) {k : ℕ}
    (c : G.EdgeColoring k) (I : Finset (Fin k)) (A B ZA ZB T : Finset V)
    (D : Finset E) (poolCost : ℕ) (lam p : ℝ)
    (hlam : 0 ≤ lam) (hp : 0 < p)
    (hrow : ∀ x ∈ ZA, (15 / 16 : ℝ) * lam * (G.edgesTo x (A ∪ B)).card ≤
      ((paletteEdges c I ∩ G.edgesTo x (A ∪ B)).card : ℝ))
    (hpool : ((paletteEdges c I ∩ correctionPool G B ZA).card : ℝ) ≤
      (5 / 4 : ℝ) * lam * (correctionPool G B ZA).card)
    (hscore : (13 / 8 : ℝ) * lam * (correctionPool G B ZA).card ≤
      BlockSampling.cappedScore G ZA
        (fun x => (⌊(15 / 16 : ℝ) * lam * (G.edgesTo x (A ∪ B)).card⌋₊ : ℝ))
        (64 * lam / p) (64 * lam / p ^ 2) T)
    (hloss : ((D ∩ correctionPool G T ZA).card : ℝ) + poolCost ≤
      p ^ 2 * (correctionPool G B ZA).card / 512) :
    (((paletteEdges c I ∩ correctionPool G B ZA).card -
      (paletteEdges c I ∩ correctionPool G A ZB).card : ℕ) : ℝ) ≤
      (64 * lam / p ^ 2) * (G.internalEdges T).card +
        (∑ x : ZA, min ((64 * lam / p) * (G.edgesTo x.val T).card)
          ((paletteEdges c I ∩ G.edgesTo x.val (A ∪ B)).card : ℝ)) -
        (64 * lam / p ^ 2) * ((D ∩ correctionPool G T ZA).card + poolCost) := by
  have hfloor := floor_score_le_palette_score G c I (A ∪ B) ZA T lam
    (64 * lam / p) (64 * lam / p ^ 2) hrow
  have hretain := score_survives_pool_loss lam p
    (correctionPool G B ZA).card _
    (((D ∩ correctionPool G T ZA).card : ℝ) + poolCost)
    hlam hp hscore hloss
  have hdifference :
      (((paletteEdges c I ∩ correctionPool G B ZA).card -
        (paletteEdges c I ∩ correctionPool G A ZB).card : ℕ) : ℝ) ≤
      (paletteEdges c I ∩ correctionPool G B ZA).card := by
    exact_mod_cast Nat.sub_le
      (paletteEdges c I ∩ correctionPool G B ZA).card
      (paletteEdges c I ∩ correctionPool G A ZB).card
  have hnonneg : 0 ≤ lam * (correctionPool G B ZA).card := by positivity
  nlinarith

variable {ι : Type*} [Fintype ι]

/-- The actual fine-family row cost is bounded by the sum of the palette
fractions; it does not require choosing the fine graphs first. -/
theorem family_rowDemand_le (G : Multigraph V E) {k : ℕ}
    (c : G.EdgeColoring k) (I : ι → Finset (Fin k)) (U : Finset V)
    (lam : ι → ℝ) (x : V)
    (hrows : ∀ i, ((paletteEdges c (I i) ∩ G.edgesTo x U).card : ℝ) ≤
      2 * lam i * (G.edgesTo x U).card) :
    (familyRowDemand G c I U x : ℝ) ≤
      2 * (∑ i, lam i) * (G.edgesTo x U).card := by
  unfold familyRowDemand
  rw [Nat.cast_sum]
  calc
    _ ≤ ∑ i, 2 * lam i * (G.edgesTo x U).card := sum_le_sum (fun i _ => hrows i)
    _ = _ := by rw [← sum_mul, ← mul_sum]

/-- The exact positive correction cost of the fine family is bounded by
the original pool-demand estimates, before any fine copies are selected. -/
theorem family_correctionDemand_le (G : Multigraph V E) {k : ℕ}
    (c : G.EdgeColoring k) (I : ι → Finset (Fin k))
    (A B ZA ZB : Finset V) (lam : ι → ℝ)
    (hpools : ∀ i, ((paletteEdges c (I i) ∩ correctionPool G B ZA).card : ℝ) ≤
      (5 / 4 : ℝ) * lam i * (correctionPool G B ZA).card) :
    (familyCorrectionDemand G c I A B ZA ZB : ℝ) ≤
      (5 / 4 : ℝ) * (∑ i, lam i) * (correctionPool G B ZA).card := by
  unfold familyCorrectionDemand
  rw [Nat.cast_sum]
  calc
    _ ≤ ∑ i, (5 / 4 : ℝ) * lam i * (correctionPool G B ZA).card := by
      apply sum_le_sum
      intro i _
      have hh :
          (((paletteEdges c (I i) ∩ correctionPool G B ZA).card -
            (paletteEdges c (I i) ∩ correctionPool G A ZB).card : ℕ) : ℝ) ≤
          (paletteEdges c (I i) ∩ correctionPool G B ZA).card := by
        exact_mod_cast Nat.sub_le
          (paletteEdges c (I i) ∩ correctionPool G B ZA).card
          (paletteEdges c (I i) ∩ correctionPool G A ZB).card
      exact hh.trans (hpools i)
    _ = _ := by rw [← sum_mul, ← mul_sum]

/-- The manuscript's fine-family fraction bound gives the exact local
coarse reserve inequality, including the adaptive boundary loss. -/
theorem coarse_reserved_loss (G : Multigraph V E) {k : ℕ}
    (c : G.EdgeColoring k) (I : ι → Finset (Fin k))
    (A B ZA ZB T : Finset V) (D : Finset E) (lam : ι → ℝ) (p : ℝ)
    (hpools : ∀ i, ((paletteEdges c (I i) ∩ correctionPool G B ZA).card : ℝ) ≤
      (5 / 4 : ℝ) * lam i * (correctionPool G B ZA).card)
    (hboundary : ((D ∩ correctionPool G T ZA).card : ℝ) ≤
      p ^ 2 * (correctionPool G B ZA).card / 1024)
    (hfine : (5 / 4 : ℝ) * (∑ i, lam i) ≤ p ^ 2 / 1024) :
    ((D ∩ correctionPool G T ZA).card : ℝ) +
        familyCorrectionDemand G c I A B ZA ZB ≤
      p ^ 2 * (correctionPool G B ZA).card / 512 := by
  have hcost := family_correctionDemand_le G c I A B ZA ZB lam hpools
  have hscaled := mul_le_mul_of_nonneg_right hfine
    (Nat.cast_nonneg (correctionPool G B ZA).card)
  apply coarse_pool_loss
  · exact hboundary
  · nlinarith

omit [Fintype E] [Fintype ι] in
/-- A small total selected palette leaves the strict degree reserves used
by the fan-coloring argument for the exact remaining graph. -/
theorem residual_coloring_reserves (k selected : ℕ) (a θ c : ℝ)
    (hk : 0 < k) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hselected : (selected : ℝ) ≤ θ * k / 400)
    (hc : θ * k ≤ c) (ha : a ≤ θ * k / 16) :
    2 * a < (k - selected : ℕ) ∧ 2 * a < c - selected := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hpos : 0 < θ * k := mul_pos hθ hkR
  have hθk : θ * k ≤ (k : ℝ) := by nlinarith
  have hsk : selected ≤ k := by
    apply Nat.cast_le.mp (show (selected : ℝ) ≤ k from ?_)
    nlinarith
  rw [Nat.cast_sub hsk]
  constructor <;> nlinarith

end Overfull.BipartiteFactorization.LocalizationBounds
