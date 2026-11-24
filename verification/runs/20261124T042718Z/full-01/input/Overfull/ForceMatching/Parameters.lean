import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic

namespace Overfull.ForceMatching

/-- Fixed inequalities used by the core-completion and small-cut arguments. -/
theorem range_bounds (α ν τ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hν : 0 < ν) (hντ : ν ≤ τ) (hτ : τ ≤ α / 1000) :
    0 < α / 2 ∧ 0 < τ ∧ ν ≤ 1 ∧ τ ≤ 1 / 16 ∧
      24 * τ ≤ α / 2 ∧ ν / 2 ≤ τ ∧ τ ≤ (α / 2) / 10 := by
  constructor
  · positivity
  constructor
  · exact hν.trans_le hντ
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · linarith

/-- The error tolerance is independent of the exceptional-set bound.
Only the order threshold depends on that bound. -/
theorem uniform_order_threshold (α ν η : ℝ) (hα : 0 < α) (hν : 0 < ν)
    (hη : 0 < η)
    (nCut nSmall : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℕ, ∃ n₀ : ℕ,
      ∀ (n h : ℕ) (a : ℝ), n₀ ≤ n → α * n ≤ h → h ≤ n →
        0 ≤ a → a ≤ ε * n →
        0 < n ∧ 0 < h ∧ nSmall ≤ n ∧
        (α / 2) * n ≤ ((h - 1 : ℕ) : ℝ) ∧
        ((h - 1 : ℕ) : ℝ) ≤ 2 * n ∧ a ≤ (α / 2) * n / 10 ∧
        ∀ m : ℕ, m ≤ n → α * n ≤ m →
          nCut + (2 * t + 6) ≤ m ∧
          ((2 * t + 6 : ℕ) : ℝ) ≤ η * m ∧
          2 ≤ ν * m ∧ (α / 2) * m ≤ (h : ℝ) - a := by
  refine ⟨α / 20, by positivity, ?_⟩
  intro t
  let L : ℕ := 2 * t + 6
  let B : ℝ := max 1 (max (2 / α)
    (max (((nCut + L : ℕ) : ℝ) / α)
      (max ((L : ℝ) / (η * α)) (2 / (ν * α)))))
  obtain ⟨N, hN⟩ := exists_nat_gt B
  refine ⟨max N nSmall, ?_⟩
  intro n h a hn hdegree hhn ha haε
  have hNn : N ≤ n := (le_max_left _ _).trans hn
  have hbig : B < (n : ℝ) := hN.trans_le (by exact_mod_cast hNn)
  have hB1 : (1 : ℝ) ≤ B := le_max_left _ _
  have hB2 : 2 / α ≤ B :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hB3 : ((nCut + L : ℕ) : ℝ) / α ≤ B :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hB4 : (L : ℝ) / (η * α) ≤ B :=
    (le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))
  have hB5 : 2 / (ν * α) ≤ B :=
    (le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))
  have hnposR : (0 : ℝ) < n := lt_trans (by norm_num) (hB1.trans_lt hbig)
  have hnpos : 0 < n := by exact_mod_cast hnposR
  have htwo : (2 : ℝ) < α * n := by
    have hh := (div_lt_iff₀ hα).mp (hB2.trans_lt hbig)
    nlinarith only [hh]
  have hhpos : 0 < h := by
    have hh : (0 : ℝ) < h := (by positivity : (0 : ℝ) < α * n).trans_le hdegree
    exact_mod_cast hh
  have hsub : ((h - 1 : ℕ) : ℝ) + 1 = h := by
    exact_mod_cast Nat.sub_add_cancel (show 1 ≤ h by omega)
  refine ⟨hnpos, hhpos, (le_max_right _ _).trans hn, ?_, ?_, ?_, ?_⟩
  · linarith
  · have hh : (h : ℝ) ≤ n := by exact_mod_cast hhn
    linarith
  · nlinarith only [haε]
  · intro m hmn hm
    have hlarge : ((nCut + L : ℕ) : ℝ) < α * n := by
      have hh := (div_lt_iff₀ hα).mp (hB3.trans_lt hbig)
      nlinarith only [hh]
    have hload : (L : ℝ) < η * α * n := by
      have hh := (div_lt_iff₀ (mul_pos hη hα)).mp (hB4.trans_lt hbig)
      nlinarith only [hh]
    have hrobust : (2 : ℝ) < ν * α * n := by
      have hh := (div_lt_iff₀ (mul_pos hν hα)).mp (hB5.trans_lt hbig)
      nlinarith only [hh]
    have hmR : (m : ℝ) ≤ n := by exact_mod_cast hmn
    refine ⟨?_, ?_, ?_, ?_⟩
    · have hh : ((nCut + L : ℕ) : ℝ) ≤ m := hlarge.le.trans hm
      exact_mod_cast hh
    · change (L : ℝ) ≤ η * m
      have hh := mul_le_mul_of_nonneg_left hm hη.le
      nlinarith only [hload, hh]
    · have hh := mul_le_mul_of_nonneg_left hm hν.le
      nlinarith only [hrobust, hh]
    · have hh := mul_le_mul_of_nonneg_left hmR hα.le
      nlinarith only [hdegree, haε, hh]

end Overfull.ForceMatching
