import Overfull.Dense.Reserve
import Mathlib.Data.Real.Sqrt

/-!
# Numerical bounds for dense balance repair

The constants are fixed before the graph. Once the imbalance parameter
is fixed, a uniform order threshold absorbs the integer rounding of the
per-vertex internal-path capacity.
-/

namespace Overfull.Dense.BalanceRepairBounds

/-- The missing-neighbor, used-edge and forbidden-vertex losses leave
strictly positive room for each short-path choice. -/
theorem routing_bounds (n c₀ s D η : ℝ) (hn : 0 < n)
    (hc₀ : c₀ ≤ 1 / 1000) (hs : 1 ≤ s) (hsc : s ≤ c₀ * n / 100)
    (hD : D ≤ 5 * s) (hη : 0 ≤ η) :
    c₀ * n + D + 16 * s + 2 < n / 2 ∧
    2 * (c₀ * n + D) + 16 * s + 2 < n / 2 ∧
    c₀ * n + D + 16 * s + 2 < (1 / 2 + η) * n - D := by
  have hc := mul_le_mul_of_nonneg_right hc₀ hn.le
  have hηn := mul_nonneg hη hn.le
  constructor
  · nlinarith only [hc, hs, hsc, hD, hn]
  constructor
  · nlinarith only [hc, hs, hsc, hD, hn]
  · nlinarith only [hc, hs, hsc, hD, hn, hηn]

theorem thresholds (η : ℝ) (hη : 0 < η) :
    let c₀ := min η 1 / 1000
    let ξ₀ := (c₀ / 100) ^ 2
    0 < c₀ ∧ c₀ ≤ η / 1000 ∧ c₀ ≤ 1 / 1000 ∧ 0 < ξ₀ ∧
    ∀ ξ : ℝ, 0 < ξ → ξ ≤ ξ₀ → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      let L := Nat.ceil (Real.sqrt ξ * n)
      0 < n ∧ 1 ≤ Real.sqrt ξ * n ∧ Real.sqrt ξ ≤ c₀ / 100 ∧
      Real.sqrt ξ * n ≤ c₀ * n / 100 ∧ 0 < L ∧
      (L : ℝ) ≤ 2 * Real.sqrt ξ * n ∧
      ξ * n ≤ Real.sqrt ξ * n ∧
      16 * ξ * (n : ℝ)^2 / L ≤ 16 * Real.sqrt ξ * n ∧
      2 * (L : ℝ) + ξ * n ≤ 5 * Real.sqrt ξ * n ∧
      16 * Real.sqrt ξ * n ≤ c₀ * n ∧
      5 * Real.sqrt ξ * n ≤ c₀ * n := by
  let c₀ := min η 1 / 1000
  let ξ₀ := (c₀ / 100)^2
  have hc₀ : 0 < c₀ := by dsimp [c₀]; positivity
  have hcη : c₀ ≤ η / 1000 :=
    div_le_div_of_nonneg_right (min_le_left η 1) (by norm_num)
  have hc1 : c₀ ≤ 1 / 1000 :=
    div_le_div_of_nonneg_right (min_le_right η 1) (by norm_num)
  have hξ₀ : 0 < ξ₀ := by dsimp [ξ₀]; positivity
  refine ⟨hc₀, hcη, hc1, hξ₀, ?_⟩
  intro ξ hξ hξsmall
  have hs : 0 < Real.sqrt ξ := Real.sqrt_pos.2 hξ
  have hs2 : (Real.sqrt ξ)^2 = ξ := Real.sq_sqrt hξ.le
  have hsc : Real.sqrt ξ ≤ c₀ / 100 := by
    change ξ ≤ (c₀ / 100)^2 at hξsmall
    nlinarith only [hξsmall, hs2, hs, hc₀]
  have hs1 : Real.sqrt ξ ≤ 1 := by linarith only [hsc, hc1]
  have hξs : ξ ≤ Real.sqrt ξ := by nlinarith only [hs2, hs, hs1]
  obtain ⟨n₀, hn₀⟩ := exists_nat_ge (1 / Real.sqrt ξ)
  refine ⟨n₀, ?_⟩
  intro n hn
  have horder : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
  have hlarge : 1 ≤ Real.sqrt ξ * n := by
    have h := (div_le_iff₀ hs).mp (hn₀.trans horder)
    simpa only [mul_comm] using h
  have hnposR : (0 : ℝ) < n := by nlinarith only [hlarge, hs]
  have hnpos : 0 < n := by exact_mod_cast hnposR
  let L := Nat.ceil (Real.sqrt ξ * n)
  have hLlower : Real.sqrt ξ * n ≤ (L : ℝ) := Nat.le_ceil _
  have hLpositiveR : (0 : ℝ) < L := by linarith only [hLlower, hlarge]
  have hLpositive : 0 < L := by exact_mod_cast hLpositiveR
  have hLupper : (L : ℝ) ≤ 2 * Real.sqrt ξ * n := by
    have hceil := Nat.ceil_lt_add_one (show 0 ≤ Real.sqrt ξ * n by positivity)
    change (L : ℝ) < Real.sqrt ξ * n + 1 at hceil
    linarith only [hceil, hlarge]
  have hendpoint := mul_le_mul_of_nonneg_right hξs hnposR.le
  have hsaturation : 16 * ξ * (n : ℝ)^2 / L ≤ 16 * Real.sqrt ξ * n := by
    apply (div_le_iff₀ hLpositiveR).mpr
    calc
      16 * ξ * (n : ℝ)^2 = 16 * (Real.sqrt ξ)^2 * (n : ℝ)^2 := by rw [hs2]
      _ = (16 * Real.sqrt ξ * n) * (Real.sqrt ξ * n) := by ring
      _ ≤ (16 * Real.sqrt ξ * n) * L :=
        mul_le_mul_of_nonneg_left hLlower (by positivity)
  have hscaled := mul_le_mul_of_nonneg_right hsc hnposR.le
  have hscaled' : Real.sqrt ξ * n ≤ c₀ * n / 100 := by linarith only [hscaled]
  have hcn : 0 ≤ c₀ * n := by positivity
  refine ⟨hnpos, hlarge, hsc, hscaled', hLpositive, hLupper, hendpoint, hsaturation, ?_, ?_, ?_⟩
  · linarith only [hLupper, hendpoint]
  · change 16 * Real.sqrt ξ * n ≤ c₀ * n
    linarith only [hscaled, hcn]
  · change 5 * Real.sqrt ξ * n ≤ c₀ * n
    linarith only [hscaled, hcn]

end Overfull.Dense.BalanceRepairBounds
