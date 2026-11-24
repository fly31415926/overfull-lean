import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic

/-!
# Uniform thresholds for an explicit finite failure budget

The constants are fixed before the order and error. A quadratic lower bound
for the exponential gives a direct numerical choice of the order threshold;
no limit or graph-specific probability premise is assumed.
-/

noncomputable section

namespace Overfull.FiniteProbability

private theorem linear_exp_decay_bound (u r m : ℝ) (hu : 0 ≤ u)
    (hr : 0 < r) (hm : 0 < m) :
    u * m * Real.exp (-r * m) ≤ (2 * u / r ^ 2) / m := by
  have he := Real.pow_div_factorial_le_exp (r * m) (mul_nonneg hr.le hm.le) 2
  norm_num at he
  calc
    u * m * Real.exp (-r * m) = (u * m) / Real.exp (r * m) := by
      rw [neg_mul, Real.exp_neg, div_eq_mul_inv]
    _ ≤ (u * m) / ((r * m) ^ 2 / 2) :=
      div_le_div_of_nonneg_left (mul_nonneg hu hm.le) (by positivity) he
    _ = (2 * u / r ^ 2) / m := by
      field_simp [ne_of_gt hr, ne_of_gt hm]

/-- Fixed nonnegative coefficients and a positive decay rate admit one
positive error tolerance and one integer threshold making every subsequent
budget strictly less than one. All choices precede both `m` and `a`. -/
theorem exists_uniform_failure_budget (u v w r : ℝ)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) (hr : 0 < r) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ m₀ : ℕ,
      ∀ m : ℕ, m₀ ≤ m → ∀ a : ℝ, 0 ≤ a → a ≤ ε * m →
        u * m * Real.exp (-r * m) + v * a / m + w / m < 1 := by
  let ε : ℝ := 1 / (4 * (v + 1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεbudget : v * ε ≤ (1 / 4 : ℝ) := by
    have hden : 0 < 4 * (v + 1) := by positivity
    calc
      v * ε = v / (4 * (v + 1)) := by dsimp [ε]; ring
      _ ≤ (1 / 4 : ℝ) := by
        apply (div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 4)).mpr
        linarith
  let H : ℝ := 2 * u / r ^ 2 + w
  have hH : 0 ≤ H := by dsimp [H]; positivity
  obtain ⟨m₀, hm₀⟩ := exists_nat_gt (4 * H + 1)
  refine ⟨ε, hε, m₀, ?_⟩
  intro m hm a _ha ha
  have hmm : (m₀ : ℝ) ≤ m := by exact_mod_cast hm
  have hthreshold : 4 * H + 1 < (m : ℝ) := hm₀.trans_le hmm
  have hmpos : (0 : ℝ) < m := by nlinarith
  have hsmall : H / m < (1 / 4 : ℝ) := by
    apply (div_lt_iff₀ hmpos).mpr
    nlinarith
  have hlinear : v * a / m ≤ v * ε := by
    apply (div_le_iff₀ hmpos).mpr
    calc
      v * a ≤ v * (ε * m) := mul_le_mul_of_nonneg_left ha hv
      _ = (v * ε) * m := by ring
  have hdecay := linear_exp_decay_bound u r m hu hr hmpos
  have hremaining : u * m * Real.exp (-r * m) + w / m ≤ H / m := by
    calc
      _ ≤ (2 * u / r ^ 2) / m + w / m := add_le_add_right hdecay _
      _ = H / m := by dsimp [H]; ring
  linarith

end Overfull.FiniteProbability
