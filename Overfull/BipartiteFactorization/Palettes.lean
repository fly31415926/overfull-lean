import Overfull.BipartiteFactorization.Moves
import Overfull.Absorption.Thresholds

/-!
# Threshold separation and actual allowed colors

A bounded special set leaves an empty band in a fixed geometric schedule.
Colors on low special incidences and on the two small correction pools are
then removed from the actual coloring. Properness counts core colors exactly.
-/

noncomputable section

namespace Overfull.BipartiteFactorization

open Finset Classical

variable {V E : Type*}

/-- Among one more disjoint threshold bands than special vertices,
one band contains no actual special incidence value. -/
theorem exists_empty_threshold_band (Z : Finset V) (c : V → ℝ)
    (k : ℝ) (hk : 0 ≤ k) (ρ : ℕ → ℝ) (hρ : Antitone ρ)
    (z : ℕ) (hZ : Z.card ≤ z) :
    ∃ j < z + 1, AbsorptionThresholds.band Z c k ρ j = ∅ := by
  by_contra hnone
  push_neg at hnone
  have hdisj : ∀ i ∈ range (z + 1), ∀ j ∈ range (z + 1), i ≠ j →
      Disjoint (AbsorptionThresholds.band Z c k ρ i)
        (AbsorptionThresholds.band Z c k ρ j) := by
    intro i _ j _ hij
    exact AbsorptionThresholds.bands_disjoint Z c k ρ hk hρ hij
  have hsub : (range (z + 1)).biUnion (AbsorptionThresholds.band Z c k ρ) ⊆ Z := by
    intro x hx
    obtain ⟨j, _, hxj⟩ := mem_biUnion.mp hx
    exact AbsorptionThresholds.band_subset Z c k ρ j hxj
  have hbound : (∑ j ∈ range (z + 1),
      (AbsorptionThresholds.band Z c k ρ j).card) ≤ Z.card := by
    rw [← card_biUnion hdisj]
    exact card_le_card hsub
  have hlower : z + 1 ≤ ∑ j ∈ range (z + 1),
      (AbsorptionThresholds.band Z c k ρ j).card := by
    calc
      _ = ∑ _j ∈ range (z + 1), (1 : ℕ) := by simp
      _ ≤ _ := sum_le_sum (fun j hj =>
        Nat.one_le_iff_ne_zero.mpr (fun hc =>
          hnone j (mem_range.mp hj) (card_eq_zero.mp hc)))
  omega

/-- The finite threshold schedule is fixed before the graph. -/
def paletteThreshold (θ₀ : ℝ) (z j : ℕ) : ℝ :=
  θ₀ * (1 / (65536 * ((z : ℝ) + 1))) ^ j

theorem paletteThreshold_pos (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (z j : ℕ) :
    0 < paletteThreshold θ₀ z j := by
  unfold paletteThreshold
  positivity

theorem paletteThreshold_antitone (θ₀ : ℝ) (hθ₀ : 0 ≤ θ₀) (z : ℕ) :
    Antitone (paletteThreshold θ₀ z) := by
  apply antitone_nat_of_succ_le
  intro j
  have hz : (0 : ℝ) ≤ z := Nat.cast_nonneg _
  have hr : 1 / (65536 * ((z : ℝ) + 1)) ≤ 1 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hn : 0 ≤ θ₀ * (1 / (65536 * ((z : ℝ) + 1))) ^ j := by positivity
  simpa only [paletteThreshold, pow_succ, ← mul_assoc, mul_one] using
    mul_le_mul_of_nonneg_left hr hn

theorem paletteThreshold_succ (θ₀ : ℝ) (z j : ℕ) :
    paletteThreshold θ₀ z (j + 1) =
      paletteThreshold θ₀ z j / (65536 * ((z : ℝ) + 1)) := by
  simp only [paletteThreshold, pow_succ, div_eq_mul_inv, one_mul]
  ring

theorem paletteThreshold_le_initial (θ₀ : ℝ) (hθ₀ : 0 ≤ θ₀) (z j : ℕ) :
    paletteThreshold θ₀ z j ≤ θ₀ := by
  simpa only [paletteThreshold, pow_zero, mul_one] using
    paletteThreshold_antitone θ₀ hθ₀ z (Nat.zero_le j)

/-- An empty band separates low special vertices from every other
exceptional vertex, whose ordinary lower bound is used when needed. -/
theorem exists_palette_threshold (Z Z₀ : Finset V) (c : V → ℝ)
    (k θ₀ β : ℝ) (hk : 0 < k) (hθ₀ : 0 < θ₀) (hθβ : θ₀ ≤ β)
    (z : ℕ) (hcard : Z₀.card ≤ z)
    (hordinary : ∀ x ∈ Z \ Z₀, β * k ≤ c x) :
    ∃ j ≤ z, ∃ L : Finset V,
      L ⊆ Z₀ ∧ L.card ≤ z ∧
      (∀ x ∈ L, c x < paletteThreshold θ₀ z (j + 1) * k) ∧
      (∀ x ∈ Z \ L, paletteThreshold θ₀ z j * k ≤ c x) := by
  obtain ⟨j, hj, hband⟩ := exists_empty_threshold_band Z₀ c k hk.le
    (paletteThreshold θ₀ z) (paletteThreshold_antitone θ₀ hθ₀.le z) z hcard
  let L := Z₀.filter (fun x => c x < paletteThreshold θ₀ z (j + 1) * k)
  have hL : L ⊆ Z₀ := filter_subset _ _
  refine ⟨j, by omega, L, hL, (card_le_card hL).trans hcard, ?_, ?_⟩
  · intro x hx
    exact (mem_filter.mp hx).2
  · intro x hx
    obtain ⟨hxZ, hxL⟩ := mem_sdiff.mp hx
    by_cases hx₀ : x ∈ Z₀
    · have hlower : paletteThreshold θ₀ z (j + 1) * k ≤ c x := by
        apply le_of_not_gt
        exact fun hlt => hxL (mem_filter.mpr ⟨hx₀, hlt⟩)
      apply le_of_not_gt
      intro hlt
      have hm := (AbsorptionThresholds.mem_band Z₀ c k
        (paletteThreshold θ₀ z) j x).mpr ⟨hx₀, hlower, hlt⟩
      rw [hband] at hm
      exact notMem_empty x hm
    · have hh := hordinary x (mem_sdiff.mpr ⟨hxZ, hx₀⟩)
      have ht := mul_le_mul_of_nonneg_right
        ((paletteThreshold_le_initial θ₀ hθ₀.le z j).trans hθβ) hk.le
      exact ht.trans hh

variable [Fintype E] {G : Multigraph V E} {k : ℕ}

/-- Actual labels appearing on a set of edge copies. -/
def colorsOn (c : G.EdgeColoring k) (F : Finset E) : Finset (Fin k) :=
  F.image c.color

omit [Fintype E] in
theorem colorsOn_card_le (c : G.EdgeColoring k) (F : Finset E) :
    (colorsOn c F).card ≤ F.card := card_image_le

/-- Properness makes the colors on a fixed vertex's core copies distinct. -/
theorem core_colors_card (c : G.EdgeColoring k) (x : V) (U : Finset V) :
    (colorsOn c (G.edgesTo x U)).card = (G.edgesTo x U).card := by
  apply card_image_of_injOn
  intro e he f hf hcolor
  exact c.proper hcolor ((G.mem_edgesTo x U e).mp he).1
    ((G.mem_edgesTo x U f).mp hf).1

/-- Large pools contribute no exclusions; a small pool contributes all
its actual edge copies. -/
def smallPool (P : Finset E) (b : ℝ) : Finset E :=
  if b ≤ (P.card : ℝ) then ∅ else P

omit [Fintype E] in
theorem smallPool_card_lt (P : Finset E) (b : ℝ) (hb : 0 < b) :
    ((smallPool P b).card : ℝ) < b := by
  unfold smallPool
  split_ifs with h
  · simpa using hb
  · exact lt_of_not_ge h

/-- Exclude colors on low core incidences and on either small pool. -/
def excludedColors (c : G.EdgeColoring k) (U L : Finset V)
    (P Q : Finset E) (b : ℝ) : Finset (Fin k) :=
  (L.biUnion (fun x => colorsOn c (G.edgesTo x U)) ∪ colorsOn c (smallPool P b)) ∪
    colorsOn c (smallPool Q b)

def allowedColors (c : G.EdgeColoring k) (U L : Finset V)
    (P Q : Finset E) (b : ℝ) : Finset (Fin k) :=
  univ \ excludedColors c U L P Q b

theorem allowedColors_card_add_excluded (c : G.EdgeColoring k) (U L : Finset V)
    (P Q : Finset E) (b : ℝ) :
    (allowedColors c U L P Q b).card + (excludedColors c U L P Q b).card = k := by
  simpa only [allowedColors, Finset.card_univ, Fintype.card_fin] using
    card_sdiff_add_card_eq_card (subset_univ (excludedColors c U L P Q b))

theorem allowedColors_card_lower (c : G.EdgeColoring k) (U L : Finset V)
    (P Q : Finset E) (T : ℝ)
    (hexcluded : ((excludedColors c U L P Q (T / 65536)).card : ℝ) < T / 512) :
    (k : ℝ) - T / 512 < (allowedColors c U L P Q (T / 65536)).card := by
  have hh := allowedColors_card_add_excluded c U L P Q (T / 65536)
  have hr : ((allowedColors c U L P Q (T / 65536)).card : ℝ) +
      (excludedColors c U L P Q (T / 65536)).card = k := by exact_mod_cast hh
  linarith

theorem excludedColors_card_le (c : G.EdgeColoring k) (U L : Finset V)
    (P Q : Finset E) (b : ℝ) :
    (excludedColors c U L P Q b).card ≤
      (∑ x ∈ L, (G.edgesTo x U).card) + (smallPool P b).card + (smallPool Q b).card := by
  have hL : (L.biUnion (fun x => colorsOn c (G.edgesTo x U))).card ≤
      ∑ x ∈ L, (G.edgesTo x U).card := by
    apply card_biUnion_le.trans
    exact sum_le_sum (fun x _ => colorsOn_card_le c _)
  have hP := colorsOn_card_le c (smallPool P b)
  have hQ := colorsOn_card_le c (smallPool Q b)
  have hinner := card_union_le
    (L.biUnion (fun x => colorsOn c (G.edgesTo x U))) (colorsOn c (smallPool P b))
  have houter := card_union_le
    (L.biUnion (fun x => colorsOn c (G.edgesTo x U)) ∪ colorsOn c (smallPool P b))
    (colorsOn c (smallPool Q b))
  unfold excludedColors
  omega

/-- The actual excluded-color set is smaller than the manuscript budget. -/
theorem excludedColors_small (c : G.EdgeColoring k) (U L : Finset V)
    (P Q : Finset E) (T : ℝ) (hT : 0 < T) (z : ℕ) (hL : L.card ≤ z)
    (hlow : ∀ x ∈ L, ((G.edgesTo x U).card : ℝ) < T / (65536 * ((z : ℝ) + 1))) :
    ((excludedColors c U L P Q (T / 65536)).card : ℝ) < T / 512 := by
  have hz : (0 : ℝ) ≤ z := Nat.cast_nonneg _
  have hden : 0 < 65536 * ((z : ℝ) + 1) := by positivity
  have hr : 0 ≤ T / (65536 * ((z : ℝ) + 1)) := by positivity
  have hc : (L.card : ℝ) ≤ z := by exact_mod_cast hL
  have hsum : (∑ x ∈ L, ((G.edgesTo x U).card : ℝ)) ≤
      (z : ℝ) * (T / (65536 * ((z : ℝ) + 1))) := by
    calc
      _ ≤ ∑ _x ∈ L, T / (65536 * ((z : ℝ) + 1)) :=
        sum_le_sum (fun x hx => (hlow x hx).le)
      _ = (L.card : ℝ) * (T / (65536 * ((z : ℝ) + 1))) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hc hr
  have hdiv : (z : ℝ) * (T / (65536 * ((z : ℝ) + 1))) ≤ T / 65536 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 65536)).mpr
    have heq := div_mul_cancel₀ T (ne_of_gt hden)
    nlinarith
  have hP := smallPool_card_lt P (T / 65536) (by positivity)
  have hQ := smallPool_card_lt Q (T / 65536) (by positivity)
  have hn := excludedColors_card_le c U L P Q (T / 65536)
  have hreal : ((excludedColors c U L P Q (T / 65536)).card : ℝ) ≤
      (∑ x ∈ L, ((G.edgesTo x U).card : ℝ)) +
        (smallPool P (T / 65536)).card + (smallPool Q (T / 65536)).card := by
    exact_mod_cast hn
  linarith

theorem low_core_color_excluded (c : G.EdgeColoring k) (U L : Finset V)
    (P Q : Finset E) (b : ℝ) (x : V) (hx : x ∈ L)
    (e : E) (he : e ∈ G.edgesTo x U) :
    c.color e ∉ allowedColors c U L P Q b := by
  intro h
  have hm : c.color e ∈ L.biUnion (fun x => colorsOn c (G.edgesTo x U)) :=
    mem_biUnion.mpr ⟨x, hx, mem_image.mpr ⟨e, he, rfl⟩⟩
  exact (mem_sdiff.mp h).2 (mem_union_left _ (mem_union_left _ hm))

theorem small_pool_color_excluded (c : G.EdgeColoring k) (U L : Finset V)
    (P Q : Finset E) (b : ℝ) (e : E)
    (he : e ∈ smallPool P b ∨ e ∈ smallPool Q b) :
    c.color e ∉ allowedColors c U L P Q b := by
  intro h
  apply (mem_sdiff.mp h).2
  rcases he with hp | hq
  · exact mem_union_left _ (mem_union_right _ (mem_image.mpr ⟨e, hp, rfl⟩))
  · exact mem_union_right _ (mem_image.mpr ⟨e, hq, rfl⟩)

/-- Every active vertex retains at least 511/512 of its actual core colors. -/
theorem active_core_colors_retained (c : G.EdgeColoring k) (U L : Finset V)
    (P Q : Finset E) (T : ℝ) (x : V)
    (hexcluded : ((excludedColors c U L P Q (T / 65536)).card : ℝ) < T / 512)
    (hactive : T ≤ ((G.edgesTo x U).card : ℝ)) :
    (511 / 512 : ℝ) * (G.edgesTo x U).card ≤
      ((colorsOn c (G.edgesTo x U) ∩ allowedColors c U L P Q (T / 65536)).card : ℝ) := by
  let C := colorsOn c (G.edgesTo x U)
  let D := excludedColors c U L P Q (T / 65536)
  have heq : C ∩ allowedColors c U L P Q (T / 65536) = C \ D := by
    ext i
    simp only [allowedColors, mem_inter, mem_sdiff, mem_univ, true_and, D]
  have hh := card_sdiff_add_card_inter C D
  have hi := card_le_card (inter_subset_right : C ∩ D ⊆ D)
  have hn : C.card ≤ (C \ D).card + D.card := by omega
  have hreal : (C.card : ℝ) ≤ (C \ D).card + D.card := by exact_mod_cast hn
  have hc : C.card = (G.edgesTo x U).card := core_colors_card c x U
  rw [hc] at hreal
  rw [show colorsOn c (G.edgesTo x U) = C from rfl, heq]
  change (D.card : ℝ) < T / 512 at hexcluded
  linarith

/-- Choose the actual low set and allowed palette from a fixed schedule.
The threshold has a positive lower bound independent of the input graph;
all active core-color retention bounds are outputs of the construction. -/
theorem exists_allowed_palette_data (c : G.EdgeColoring k)
    (U Z Z₀ : Finset V) (P Q : Finset E) (θ₀ β : ℝ) (z : ℕ)
    (hk : 0 < k) (hθ₀ : 0 < θ₀) (hθβ : θ₀ ≤ β)
    (hZ₀ : Z₀ ⊆ Z) (hcard : Z₀.card ≤ z)
    (hordinary : ∀ x ∈ Z \ Z₀, β * k ≤ ((G.edgesTo x U).card : ℝ)) :
    ∃ j ≤ z, ∃ L : Finset V,
      let θ := paletteThreshold θ₀ z j
      let I := allowedColors c U L P Q (θ * k / 65536)
      0 < θ ∧ paletteThreshold θ₀ z z ≤ θ ∧ θ ≤ θ₀ ∧
      L ⊆ Z₀ ∧ L ⊆ Z ∧ L.card ≤ z ∧
      (∀ x ∈ L, ((G.edgesTo x U).card : ℝ) <
        paletteThreshold θ₀ z (j + 1) * k) ∧
      (∀ x ∈ Z \ L, θ * k ≤ ((G.edgesTo x U).card : ℝ)) ∧
      ((excludedColors c U L P Q (θ * k / 65536)).card : ℝ) < θ * k / 512 ∧
      (k : ℝ) - θ * k / 512 < (I.card : ℝ) ∧
      (∀ x ∈ Z \ L, (511 / 512 : ℝ) * (G.edgesTo x U).card ≤
        ((colorsOn c (G.edgesTo x U) ∩ I).card : ℝ)) ∧
      (∀ x ∈ L, ∀ e ∈ G.edgesTo x U, c.color e ∉ I) ∧
      (∀ e ∈ smallPool P (θ * k / 65536) ∪ smallPool Q (θ * k / 65536),
        c.color e ∉ I) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  obtain ⟨j, hj, L, hL₀, hLcard, hlow, hactive⟩ :=
    exists_palette_threshold Z Z₀ (fun x => ((G.edgesTo x U).card : ℝ))
      k θ₀ β hkR hθ₀ hθβ z hcard hordinary
  let θ := paletteThreshold θ₀ z j
  have hθ : 0 < θ := paletteThreshold_pos θ₀ hθ₀ z j
  have hT : 0 < θ * k := mul_pos hθ hkR
  have hexcluded : ((excludedColors c U L P Q (θ * k / 65536)).card : ℝ) <
      θ * k / 512 := by
    apply excludedColors_small c U L P Q (θ * k) hT z hLcard
    intro x hx
    have hh := hlow x hx
    rw [paletteThreshold_succ] at hh
    change ((G.edgesTo x U).card : ℝ) < (θ / (65536 * ((z : ℝ) + 1))) * k at hh
    convert hh using 1
    ring
  refine ⟨j, hj, L, hθ, paletteThreshold_antitone θ₀ hθ₀.le z hj,
    paletteThreshold_le_initial θ₀ hθ₀.le z j, hL₀,
    fun _ hx => hZ₀ (hL₀ hx), hLcard, hlow, hactive, hexcluded,
    allowedColors_card_lower c U L P Q (θ * k) hexcluded, ?_, ?_, ?_⟩
  · intro x hx
    exact active_core_colors_retained c U L P Q (θ * k) x hexcluded (hactive x hx)
  · intro x hx e he
    exact low_core_color_excluded c U L P Q _ x hx e he
  · intro e he
    exact small_pool_color_excluded c U L P Q _ e (mem_union.mp he)

end Overfull.BipartiteFactorization
