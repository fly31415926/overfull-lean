import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic

/-!
# Threshold bands for actual finite incidence weights

The weights and the entry degree stay fixed throughout this construction.
The disjoint-band argument uses their actual sums, and the cardinal bounds
apply to the actual sets left after one or both absorption steps.
-/

namespace Overfull.AbsorptionThresholds

open Finset Classical
open scoped BigOperators

variable {V : Type*}

/-- Vertices below one threshold in the fixed entry weighting. -/
noncomputable def low (Z : Finset V) (q : V → ℝ) (h ρ : ℝ) : Finset V :=
  Z.filter (fun z => q z < ρ*h)

/-- Vertices at or above one threshold in the fixed entry weighting. -/
noncomputable def high (Z : Finset V) (q : V → ℝ) (h ρ : ℝ) : Finset V :=
  Z.filter (fun z => ρ*h ≤ q z)

/-- One half-open band. Its endpoints refer to the entry graph. -/
noncomputable def band (Z : Finset V) (q : V → ℝ) (h : ℝ)
    (ρ : ℕ → ℝ) (i : ℕ) : Finset V :=
  Z.filter (fun z => ρ (i+1)*h ≤ q z ∧ q z < ρ i*h)

@[simp] theorem mem_low (Z : Finset V) (q : V → ℝ) (h ρ : ℝ) (z : V) :
    z ∈ low Z q h ρ ↔ z ∈ Z ∧ q z < ρ*h := by
  simp [low]

@[simp] theorem mem_high (Z : Finset V) (q : V → ℝ) (h ρ : ℝ) (z : V) :
    z ∈ high Z q h ρ ↔ z ∈ Z ∧ ρ*h ≤ q z := by
  simp [high]

@[simp] theorem mem_band (Z : Finset V) (q : V → ℝ) (h : ℝ)
    (ρ : ℕ → ℝ) (i : ℕ) (z : V) :
    z ∈ band Z q h ρ i ↔ z ∈ Z ∧ ρ (i+1)*h ≤ q z ∧ q z < ρ i*h := by
  simp [band]

theorem band_subset (Z : Finset V) (q : V → ℝ) (h : ℝ)
    (ρ : ℕ → ℝ) (i : ℕ) : band Z q h ρ i ⊆ Z := filter_subset _ _

theorem high_subset (Z : Finset V) (q : V → ℝ) (h ρ : ℝ) :
    high Z q h ρ ⊆ Z := filter_subset _ _

theorem complement_low (Z : Finset V) (q : V → ℝ) (h ρ : ℝ) :
    Z \ low Z q h ρ = high Z q h ρ := by
  ext z
  simp only [mem_sdiff, mem_low, mem_high]
  constructor
  · rintro ⟨hz, hn⟩
    exact ⟨hz, le_of_not_gt (fun ht => hn ⟨hz, ht⟩)⟩
  · rintro ⟨hz, hq⟩
    exact ⟨hz, fun ht => (not_lt_of_ge hq) ht.2⟩

theorem band_eq_high_sdiff (Z : Finset V) (q : V → ℝ) (h : ℝ)
    (ρ : ℕ → ℝ) (i : ℕ) :
    band Z q h ρ i = high Z q h (ρ (i+1)) \ high Z q h (ρ i) := by
  ext z
  simp only [mem_band, mem_sdiff, mem_high]
  constructor
  · rintro ⟨hz, hlow, hupp⟩
    exact ⟨⟨hz, hlow⟩, fun hh => (not_le_of_gt hupp) hh.2⟩
  · rintro ⟨⟨hz, hlow⟩, hn⟩
    exact ⟨hz, hlow, lt_of_not_ge (fun hh => hn ⟨hz, hh⟩)⟩

theorem high_after_band (Z : Finset V) (q : V → ℝ) (h : ℝ)
    (ρ : ℕ → ℝ) (i : ℕ) (hh : 0 ≤ h) (hρ : ρ (i+1) ≤ ρ i) :
    high Z q h (ρ (i+1)) \ band Z q h ρ i = high Z q h (ρ i) := by
  have hbound := mul_le_mul_of_nonneg_right hρ hh
  ext z
  simp only [mem_sdiff, mem_high, mem_band]
  constructor
  · rintro ⟨⟨hz, hlo⟩, hn⟩
    exact ⟨hz, le_of_not_gt (fun hlt => hn ⟨hz, hlo, hlt⟩)⟩
  · rintro ⟨hz, hhi⟩
    exact ⟨⟨hz, hbound.trans hhi⟩, fun hb => (not_lt_of_ge hhi) hb.2.2⟩

theorem remainder_after_two_absorptions (Z : Finset V) (q : V → ℝ) (h : ℝ)
    (ρ : ℕ → ℝ) (i : ℕ) (hh : 0 ≤ h) (hρ : ρ (i+1) ≤ ρ i) :
    (Z \ low Z q h (ρ (i+1))) \ band Z q h ρ i = high Z q h (ρ i) := by
  rw [complement_low]
  exact high_after_band Z q h ρ i hh hρ

theorem bands_disjoint_of_lt (Z : Finset V) (q : V → ℝ) (h : ℝ)
    (ρ : ℕ → ℝ) (hh : 0 ≤ h) (hρ : Antitone ρ)
    {i j : ℕ} (hij : i < j) :
    Disjoint (band Z q h ρ i) (band Z q h ρ j) := by
  apply Finset.disjoint_left.mpr
  intro z hzi hzj
  have hi := (mem_band Z q h ρ i z).mp hzi
  have hj := (mem_band Z q h ρ j z).mp hzj
  have hbound := mul_le_mul_of_nonneg_right (hρ (Nat.succ_le_of_lt hij)) hh
  linarith only [hi.2.1, hj.2.2, hbound]

theorem bands_disjoint (Z : Finset V) (q : V → ℝ) (h : ℝ)
    (ρ : ℕ → ℝ) (hh : 0 ≤ h) (hρ : Antitone ρ)
    {i j : ℕ} (hij : i ≠ j) :
    Disjoint (band Z q h ρ i) (band Z q h ρ j) := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact bands_disjoint_of_lt Z q h ρ hh hρ hlt
  · exact (bands_disjoint_of_lt Z q h ρ hh hρ hgt).symm

/-- Disjoint bands count each actual incidence weight at most once. -/
theorem total_band_mass_le (Z : Finset V) (q : V → ℝ) (h : ℝ)
    (ρ : ℕ → ℝ) (L : ℕ) (hh : 0 ≤ h) (hρ : Antitone ρ)
    (hq : ∀ z ∈ Z, 0 ≤ q z) :
    (∑ i ∈ range L, ∑ z ∈ band Z q h ρ i, q z) ≤ ∑ z ∈ Z, q z := by
  have hdisj : ∀ i ∈ range L, ∀ j ∈ range L, i ≠ j →
      Disjoint (band Z q h ρ i) (band Z q h ρ j) := by
    intro i _ j _ hij
    exact bands_disjoint Z q h ρ hh hρ hij
  have hsub : (range L).biUnion (band Z q h ρ) ⊆ Z := by
    intro z hz
    obtain ⟨i, _, hzi⟩ := mem_biUnion.mp hz
    exact band_subset Z q h ρ i hzi
  calc
    _ = ∑ z ∈ (range L).biUnion (band Z q h ρ), q z :=
      (Finset.sum_biUnion hdisj).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun z hz _ => hq z hz)

/-- A band with small actual incidence mass exists before any graph changes. -/
theorem exists_light_band (Z : Finset V) (q : V → ℝ) (h c : ℝ)
    (ρ : ℕ → ℝ) (L : ℕ) (hh : 0 < h) (hc : 0 ≤ c)
    (hρ : Antitone ρ) (hq : ∀ z ∈ Z, 0 ≤ q z)
    (htotal : (∑ z ∈ Z, q z) ≤ c*h) (hL : 8*c < (L : ℝ)) :
    ∃ i < L, (∑ z ∈ band Z q h ρ i, q z) ≤ h/8 := by
  have hLposR : (0 : ℝ) < L := lt_of_le_of_lt (by positivity) hL
  have hLpos : 0 < L := by exact_mod_cast hLposR
  by_contra hnone
  have hheavy (i : ℕ) (hi : i ∈ range L) :
      h/8 < ∑ z ∈ band Z q h ρ i, q z := by
    apply lt_of_not_ge
    intro hle
    exact hnone ⟨i, mem_range.mp hi, hle⟩
  have hmass : (∑ i ∈ range L, h/8) <
      ∑ i ∈ range L, ∑ z ∈ band Z q h ρ i, q z := by
    apply sum_lt_sum (fun i hi => (hheavy i hi).le)
    exact ⟨0, mem_range.mpr hLpos, hheavy 0 (mem_range.mpr hLpos)⟩
  have hbounded := (total_band_mass_le Z q h ρ L hh.le hρ hq).trans htotal
  simp only [sum_const, card_range, nsmul_eq_mul] at hmass
  have hscaled := mul_lt_mul_of_pos_right hL hh
  nlinarith only [hmass, hbounded, hscaled]

/-- The actual high set is bounded independently of the entry order. -/
theorem high_card_le (Z : Finset V) (q : V → ℝ) (h c ρ : ℝ)
    (hh : 0 < h) (hρ : 0 < ρ) (hq : ∀ z ∈ Z, 0 ≤ q z)
    (htotal : (∑ z ∈ Z, q z) ≤ c*h) :
    (high Z q h ρ).card ≤ Nat.ceil (c/ρ) := by
  have hmass : ((high Z q h ρ).card : ℝ)*(ρ*h) ≤ c*h := by
    calc
      _ = ∑ _z ∈ high Z q h ρ, ρ*h := by simp
      _ ≤ ∑ z ∈ high Z q h ρ, q z := by
        apply sum_le_sum
        intro z hz
        exact ((mem_high Z q h ρ z).mp hz).2
      _ ≤ ∑ z ∈ Z, q z := sum_le_sum_of_subset_of_nonneg
        (high_subset Z q h ρ) (fun z hz _ => hq z hz)
      _ ≤ _ := htotal
  have hcancel : ((high Z q h ρ).card : ℝ)*ρ ≤ c := by
    apply (mul_le_mul_iff_right₀ hh).mp
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hmass
  have hreal : ((high Z q h ρ).card : ℝ) ≤ (Nat.ceil (c/ρ) : ℝ) :=
    ((le_div_iff₀ hρ).mpr hcancel).trans (Nat.le_ceil _)
  exact_mod_cast hreal

/-- Both exceptional-set bounds use the same frozen entry weighting. -/
theorem absorption_card_bounds (Z : Finset V) (q : V → ℝ) (h c : ℝ)
    (ρ : ℕ → ℝ) (i : ℕ) (hh : 0 < h)
    (hρ : ∀ j, 0 < ρ j) (hanti : Antitone ρ)
    (hq : ∀ z ∈ Z, 0 ≤ q z) (htotal : (∑ z ∈ Z, q z) ≤ c*h) :
    (Z \ low Z q h (ρ (i+1))).card ≤ Nat.ceil (c / ρ (i+1)) ∧
    ((Z \ low Z q h (ρ (i+1))) \ band Z q h ρ i).card ≤
      Nat.ceil (c / ρ i) := by
  constructor
  · rw [complement_low]
    exact high_card_le Z q h c (ρ (i+1)) hh (hρ (i+1)) hq htotal
  · rw [remainder_after_two_absorptions Z q h ρ i hh.le
      (hanti (Nat.le_succ i))]
    exact high_card_le Z q h c (ρ i) hh (hρ i) hq htotal

end Overfull.AbsorptionThresholds
