import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic

/-!
# Parameters for dense link packing

The order threshold is chosen after the fixed parameters and before the
graph order.  A cubic lower bound for the exponential controls the complete
finite union of load failures.  All rounding and probability-rate estimates
are explicit real inequalities.
-/

noncomputable section

namespace Overfull.Dense.LinkPacking.Parameters

/-- The allowed load, written without a real exponent. -/
def load (lam : ℝ) (n : ℕ) : ℝ := lam * Real.sqrt lam * n

/-- Number of candidate matchings offered in each round. -/
def choices (b lam : ℝ) (n : ℕ) : ℕ := ⌈24 * b * load lam n⌉₊

/-- Conditional success bound outside the monitored link's own round. -/
def rate (b lam : ℝ) : ℝ := Real.sqrt lam / (4 * b)

theorem load_nonneg (lam : ℝ) (n : ℕ) (hlam : 0 ≤ lam) : 0 ≤ load lam n := by
  dsimp [load]
  positivity

theorem load_pos (lam : ℝ) (n : ℕ) (hlam : 0 < lam) (hn : 0 < n) :
    0 < load lam n := by
  dsimp [load]
  exact mul_pos (mul_pos hlam (Real.sqrt_pos.mpr hlam)) (by exact_mod_cast hn)

/-- The square-root expression is exactly the manuscript's power. -/
theorem rpow_three_halves (lam : ℝ) (hlam : 0 ≤ lam) :
    lam ^ (3 / 2 : ℝ) = lam * Real.sqrt lam := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
    Real.rpow_add_of_nonneg hlam (by norm_num) (by norm_num),
    Real.rpow_one, ← Real.sqrt_eq_rpow]

theorem load_eq_rpow (lam : ℝ) (n : ℕ) (hlam : 0 ≤ lam) :
    load lam n = lam ^ (3 / 2 : ℝ) * n := by
  rw [rpow_three_halves lam hlam]
  rfl

theorem choices_pos (b lam : ℝ) (n : ℕ) (hb : 1 ≤ b) (hL : 8 ≤ load lam n) :
    0 < choices b lam n := by
  apply Nat.ceil_pos.mpr
  have hbpos : 0 < b := by linarith
  have hLpos : 0 < load lam n := by linarith
  positivity

theorem choices_lower (b lam : ℝ) (n : ℕ) :
    24 * b * load lam n ≤ (choices b lam n : ℝ) :=
  Nat.le_ceil _

theorem choices_upper (b lam : ℝ) (n : ℕ) (hb : 1 ≤ b) (hL : 8 ≤ load lam n) :
    (choices b lam n : ℝ) ≤ 25 * b * load lam n := by
  have hbpos : 0 < b := by linarith
  have hLpos : 0 < load lam n := by linarith
  have hprod := mul_le_mul_of_nonneg_right hb hLpos.le
  have hceil := Nat.ceil_lt_add_one
    (show (0 : ℝ) ≤ 24 * b * load lam n by positivity)
  change (⌈24 * b * load lam n⌉₊ : ℝ) ≤ _
  nlinarith

theorem load_add_choices_le (b lam : ℝ) (n : ℕ)
    (hb : 1 ≤ b) (hL : 8 ≤ load lam n) :
    load lam n + choices b lam n ≤ 81 * b * load lam n := by
  have hc := choices_upper b lam n hb hL
  have hLnonneg : 0 ≤ load lam n := by linarith
  have hprod := mul_le_mul_of_nonneg_right hb hLnonneg
  nlinarith

theorem rate_nonneg (b lam : ℝ) (hb : 0 ≤ b) : 0 ≤ rate b lam := by
  dsimp [rate]
  positivity

theorem rate_pos (b lam : ℝ) (hb : 0 < b) (hlam : 0 < lam) : 0 < rate b lam := by
  exact div_pos (Real.sqrt_pos.mpr hlam) (by positivity)

theorem rate_le_quarter (b lam : ℝ) (hb : 1 ≤ b) (hlam : lam ≤ 1) :
    rate b lam ≤ 1 / 4 := by
  have hbpos : 0 < b := by linarith
  apply (div_le_iff₀ (show (0 : ℝ) < 4 * b by positivity)).mpr
  have hsqrt : Real.sqrt lam ≤ 1 := Real.sqrt_le_one.mpr hlam
  nlinarith

/-- Divide the actual number of harmful candidates by the actual rounded
candidate count.  The lower bound on `choices` supplies the needed margin. -/
theorem local_ratio_le (b lam : ℝ) (n : ℕ) (hb : 1 ≤ b) (hlam : 0 ≤ lam)
    (hL : 8 ≤ load lam n) :
    6 * lam ^ 2 * n / choices b lam n ≤ rate b lam := by
  have ht : (0 : ℝ) < choices b lam n := by
    exact_mod_cast choices_pos b lam n hb hL
  have hbpos : 0 < b := by linarith
  apply (div_le_div_iff₀ ht (show (0 : ℝ) < 4 * b by positivity)).mpr
  calc
    6 * lam ^ 2 * n * (4 * b) =
        (24 * b * lam * n) * (Real.sqrt lam) ^ 2 := by
      rw [Real.sq_sqrt hlam]
      ring
    _ = Real.sqrt lam * (24 * b * load lam n) := by dsimp [load]; ring
    _ ≤ Real.sqrt lam * (choices b lam n : ℝ) :=
      mul_le_mul_of_nonneg_left (choices_lower b lam n) (Real.sqrt_nonneg lam)

/-- The incidence bound contributes exactly half the allowed load. -/
theorem rate_incidence (b lam : ℝ) (n : ℕ) (hb : b ≠ 0) :
    rate b lam * (2 * b * lam * n) = load lam n / 2 := by
  dsimp [rate, load]
  field_simp [hb]
  ring

/-- A direct bound for the complete quadratic failure budget. -/
theorem quadratic_exp_decay_bound (b c x : ℝ) (hb : 0 ≤ b)
    (hc : 0 < c) (hx : 0 < x) :
    (3 * b * x) * (3 * x) * Real.exp (-c * x) ≤ 54 * b / (c ^ 3 * x) := by
  have he := Real.pow_div_factorial_le_exp (c * x) (mul_nonneg hc.le hx.le) 3
  norm_num at he
  calc
    (3 * b * x) * (3 * x) * Real.exp (-c * x) =
        (9 * b * x ^ 2) / Real.exp (c * x) := by
      rw [neg_mul, Real.exp_neg]
      ring
    _ ≤ (9 * b * x ^ 2) / ((c * x) ^ 3 / 6) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) he
    _ = 54 * b / (c ^ 3 * x) := by
      field_simp [ne_of_gt hc, ne_of_gt hx]
      ring

/-- One threshold, chosen from the fixed parameters before `n`, ensures
positive order, load at least eight, and total failure budget below one. -/
theorem exists_threshold (b lam : ℝ) (hb : 1 ≤ b) (hlam : 0 < lam) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      0 < n ∧ 8 ≤ load lam n ∧
        (3 * b * n) * (3 * n) * Real.exp (-load lam n / 24) < 1 := by
  let d : ℝ := lam * Real.sqrt lam
  let c : ℝ := d / 24
  have hbpos : 0 < b := by linarith
  have hd : 0 < d := mul_pos hlam (Real.sqrt_pos.mpr hlam)
  have hc : 0 < c := div_pos hd (by norm_num)
  let K : ℝ := max (8 / d) (54 * b / c ^ 3 + 1)
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt K
  refine ⟨n₀, ?_⟩
  intro n hn
  have hnn : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
  have hK : K < (n : ℝ) := hn₀.trans_le hnn
  have hlarge : 54 * b / c ^ 3 + 1 < (n : ℝ) :=
    (le_max_right _ _).trans_lt hK
  have hsmallnonneg : 0 ≤ 54 * b / c ^ 3 := by positivity
  have hnpos : (0 : ℝ) < n := by linarith
  have hload : 8 ≤ load lam n := by
    have hbound : 8 / d < (n : ℝ) := (le_max_left _ _).trans_lt hK
    have hmul := (div_lt_iff₀ hd).mp hbound
    dsimp [load, d] at *
    nlinarith
  refine ⟨by exact_mod_cast hnpos, hload, ?_⟩
  have hsmall : 54 * b / (c ^ 3 * (n : ℝ)) < 1 := by
    apply (div_lt_iff₀ (mul_pos (pow_pos hc 3) hnpos)).mpr
    have hbound : 54 * b / c ^ 3 < (n : ℝ) := by linarith
    have hmul := (div_lt_iff₀ (pow_pos hc 3)).mp hbound
    nlinarith
  rw [show -load lam n / 24 = -c * (n : ℝ) by dsimp [load, c, d]; ring]
  exact (quadratic_exp_decay_bound b c n hbpos.le hc hnpos).trans_lt hsmall

end Overfull.Dense.LinkPacking.Parameters
