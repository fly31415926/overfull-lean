import Overfull.BipartiteFactorization.PaletteBudgets

/-!
# Concentration of actual active palette rows

Properness identifies the selected original copies at a vertex with a
hypergeometric count of its actual allowed colors. The mean uses the allowed
population cardinality before comparison with the original palette fraction.
-/

noncomputable section

namespace Overfull.BipartiteFactorization.PaletteRowTails

open Finset Classical PaletteSampling PaletteBudgets

variable {V E : Type*} [Fintype E] {G : Multigraph V E} {k : ℕ}

/-- Core colors at one vertex, considered as members of the allowed population. -/
def rowColors (c : G.EdgeColoring k) (C : Finset (Fin k))
    (U : Finset V) (x : V) : Finset C :=
  univ.filter (fun i => i.val ∈ colorsOn c (G.edgesTo x U))

theorem lift_rowColors (c : G.EdgeColoring k) (C : Finset (Fin k))
    (U : Finset V) (x : V) :
    liftPalette C (rowColors c C U x) = colorsOn c (G.edgesTo x U) ∩ C := by
  ext i
  rw [mem_liftPalette, mem_inter]
  constructor
  · rintro ⟨hi, hrow⟩
    exact ⟨(mem_filter.mp hrow).2, hi⟩
  · rintro ⟨hrow, hi⟩
    exact ⟨hi, mem_filter.mpr ⟨mem_univ _, hrow⟩⟩

theorem rowColors_card (c : G.EdgeColoring k) (C : Finset (Fin k))
    (U : Finset V) (x : V) :
    (rowColors c C U x).card = (colorsOn c (G.edgesTo x U) ∩ C).card := by
  calc
    _ = (liftPalette C (rowColors c C U x)).card := (liftPalette_card _ _).symm
    _ = _ := congrArg Finset.card (lift_rowColors c C U x)

theorem rowColors_card_le (c : G.EdgeColoring k) (C : Finset (Fin k))
    (U : Finset V) (x : V) :
    (rowColors c C U x).card ≤ (G.edgesTo x U).card := by
  calc
    _ = (colorsOn c (G.edgesTo x U) ∩ C).card := rowColors_card c C U x
    _ ≤ (colorsOn c (G.edgesTo x U)).card := card_le_card inter_subset_left
    _ = _ := core_colors_card c x U

theorem colorsOn_palette_inter (c : G.EdgeColoring k)
    (I : Finset (Fin k)) (P : Finset E) :
    colorsOn c (paletteEdges c I ∩ P) = I ∩ colorsOn c P := by
  ext i
  simp only [colorsOn, mem_image, mem_inter, mem_paletteEdges]
  constructor
  · rintro ⟨e, ⟨heI, heP⟩, rfl⟩
    exact ⟨heI, e, heP, rfl⟩
  · rintro ⟨hi, e, heP, hei⟩
    exact ⟨e, ⟨hei ▸ hi, heP⟩, hei⟩

/-- Properness makes the original incident copies and their colors equinumerous. -/
theorem palette_row_card_eq_colors (c : G.EdgeColoring k)
    (I : Finset (Fin k)) (U : Finset V) (x : V) :
    (paletteEdges c I ∩ G.edgesTo x U).card =
      (I ∩ colorsOn c (G.edgesTo x U)).card := by
  have hcard : (colorsOn c (paletteEdges c I ∩ G.edgesTo x U)).card =
      (paletteEdges c I ∩ G.edgesTo x U).card := by
    apply card_image_of_injOn
    intro e he f hf hef
    exact c.proper hef ((G.mem_edgesTo x U e).mp (mem_inter.mp he).2).1
      ((G.mem_edgesTo x U f).mp (mem_inter.mp hf).2).1
  rw [colorsOn_palette_inter] at hcard
  exact hcard.symm

/-- The actual number of selected row copies is the actual hypergeometric count. -/
theorem row_poolDemand_eq_count (c : G.EdgeColoring k) (C : Finset (Fin k))
    (U : Finset V) (x : V) (T : Finset C) :
    poolDemand c C (G.edgesTo x U) T =
      (Hypergeometric.count (rowColors c C U x) T : ℝ) := by
  have heq : liftPalette C (rowColors c C U x ∩ T) =
      liftPalette C T ∩ colorsOn c (G.edgesTo x U) := by
    ext i
    rw [mem_liftPalette, mem_inter, mem_liftPalette]
    constructor
    · rintro ⟨hi, h⟩
      exact ⟨⟨hi, (mem_inter.mp h).2⟩, (mem_filter.mp (mem_inter.mp h).1).2⟩
    · rintro ⟨⟨hi, hT⟩, hrow⟩
      exact ⟨hi, mem_inter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hrow⟩, hT⟩⟩
  rw [poolDemand, palette_row_card_eq_colors, Hypergeometric.count,
    ← heq, liftPalette_card]
  apply congrArg (fun S : Finset C => (S.card : ℝ))
  ext i
  simp only [mem_inter]

theorem row_mean_lower (c : G.EdgeColoring k) (C : Finset (Fin k))
    (U : Finset V) (x : V) (s : ℕ) (hk : 0 < k)
    (hC : (32 / 33 : ℝ) * k ≤ C.card)
    (hretained : (31 / 32 : ℝ) * (G.edgesTo x U).card ≤
      (colorsOn c (G.edgesTo x U) ∩ C).card) :
    (31 / 32 : ℝ) * ((s : ℝ) / k) * (G.edgesTo x U).card ≤
      ((s : ℝ) / C.card) * (rowColors c C U x).card := by
  have hret : (31 / 32 : ℝ) * (G.edgesTo x U).card ≤
      (rowColors c C U x).card := by simpa only [rowColors_card] using hretained
  calc
    _ = ((s : ℝ) / k) * ((31 / 32 : ℝ) * (G.edgesTo x U).card) := by ring
    _ ≤ ((s : ℝ) / k) * (rowColors c C U x).card :=
      mul_le_mul_of_nonneg_left hret (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right (allowed_fraction_lower C s hk hC)
      (Nat.cast_nonneg _)

theorem row_mean_upper (c : G.EdgeColoring k) (C : Finset (Fin k))
    (U : Finset V) (x : V) (s : ℕ) (hk : 0 < k)
    (hC : (32 / 33 : ℝ) * k ≤ C.card) :
    ((s : ℝ) / C.card) * (rowColors c C U x).card ≤
      (33 / 32 : ℝ) * ((s : ℝ) / k) * (G.edgesTo x U).card := by
  calc
    _ ≤ ((s : ℝ) / C.card) * (G.edgesTo x U).card :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast rowColors_card_le c C U x)
        (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right (allowed_fraction_le C s hk hC)
      (Nat.cast_nonneg _)

/-- The active-row interval fails with an exponentially small probability.
The actual sample may be empty; no artificial positive-mean assumption is used. -/
theorem palette_row_tail (c : G.EdgeColoring k) (C : Finset (Fin k))
    (U : Finset V) (x : V) (s : ℕ) (hs : s ≤ C.card) (hk : 0 < k)
    (hC : (32 / 33 : ℝ) * k ≤ C.card)
    (hretained : (31 / 32 : ℝ) * (G.edgesTo x U).card ≤
      (colorsOn c (G.edgesTo x U) ∩ C).card) :
    Hypergeometric.probability s (fun T : Finset C =>
      poolDemand c C (G.edgesTo x U) T <
          (15 / 16 : ℝ) * ((s : ℝ) / k) * (G.edgesTo x U).card ∨
      2 * ((s : ℝ) / k) * (G.edgesTo x U).card <
          poolDemand c C (G.edgesTo x U) T) ≤
      2 * Real.exp (-((s : ℝ) / k) * (G.edgesTo x U).card / 4096) := by
  let μ : ℝ := ((s : ℝ) / C.card) * (rowColors c C U x).card
  have hlo := row_mean_lower c C U x s hk hC hretained
  have hhi := row_mean_upper c C U x s hk hC
  change (31 / 32 : ℝ) * ((s : ℝ) / k) * (G.edgesTo x U).card ≤ μ at hlo
  change μ ≤ (33 / 32 : ℝ) * ((s : ℝ) / k) * (G.edgesTo x U).card at hhi
  have hnonneg : 0 ≤ ((s : ℝ) / k) * (G.edgesTo x U).card := by positivity
  have hc := Hypergeometric.chernoff s (1 / 32 : ℝ)
    (by simpa using hs) (by norm_num) (by norm_num) (rowColors c C U x)
  have hc' : Hypergeometric.probability s (fun T : Finset C =>
      (1 / 32 : ℝ) * μ ≤ |(Hypergeometric.count (rowColors c C U x) T : ℝ) - μ|) ≤
      2 * Real.exp (-(1 / 32 : ℝ) ^ 2 * μ / 3) := by
    simpa only [Fintype.card_coe, μ] using hc
  calc
    _ ≤ Hypergeometric.probability s (fun T : Finset C =>
        (1 / 32 : ℝ) * μ ≤ |(Hypergeometric.count (rowColors c C U x) T : ℝ) - μ|) := by
      apply MatchingProbability.probability_mono _ (Hypergeometric.weight_nonneg s)
      intro T hT
      rw [row_poolDemand_eq_count] at hT
      rcases hT with hT | hT
      · exact le_trans (by nlinarith) (neg_le_abs _)
      · exact le_trans (by nlinarith) (le_abs_self _)
    _ ≤ 2 * Real.exp (-(1 / 32 : ℝ) ^ 2 * μ / 3) := hc'
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith))
      (by norm_num)

/-- Instantiate concentration using the actual excluded-label construction. -/
theorem palette_row_tail_of_exclusions (c : G.EdgeColoring k)
    (U L : Finset V) (P Q : Finset E) (T : ℝ) (x : V) (s : ℕ)
    (hk : 0 < k) (hTk : T ≤ k)
    (hexcluded : ((excludedColors c U L P Q (T / 65536)).card : ℝ) < T / 512)
    (hactive : T ≤ ((G.edgesTo x U).card : ℝ))
    (hs : s ≤ (allowedColors c U L P Q (T / 65536)).card) :
    Hypergeometric.probability s
      (fun S : Finset (allowedColors c U L P Q (T / 65536)) =>
        poolDemand c _ (G.edgesTo x U) S <
            (15 / 16 : ℝ) * ((s : ℝ) / k) * (G.edgesTo x U).card ∨
        2 * ((s : ℝ) / k) * (G.edgesTo x U).card <
            poolDemand c _ (G.edgesTo x U) S) ≤
      2 * Real.exp (-((s : ℝ) / k) * (G.edgesTo x U).card / 4096) := by
  apply palette_row_tail c _ U x s hs hk
  · have hcard := allowedColors_card_lower c U L P Q T hexcluded
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    linarith
  · have hret := active_core_colors_retained c U L P Q T x hexcluded hactive
    have hc0 : (0 : ℝ) ≤ (G.edgesTo x U).card := Nat.cast_nonneg _
    linarith

end Overfull.BipartiteFactorization.PaletteRowTails
