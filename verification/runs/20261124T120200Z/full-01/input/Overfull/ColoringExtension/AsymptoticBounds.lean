import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-!
# Uniform numerical bounds for sparse conflict repair

A small linear bound on the forbidden palette supplies both the finite
permutation-counting criterion and enough unused colors for greedy repair.
The proof uses a single exponential-series term, not Stirling's theorem.
-/

namespace Overfull.ColoringExtension

private theorem exp_one_lt_three_for_factorial : Real.exp 1 < 3 := by
  have h := Real.exp_bound' (x := 1) (n := 2)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- A convenient elementary lower bound for the factorial in the finite
permutation criterion. -/
theorem two_pow_mul_pow_le_factorial (b t : ℕ) (hbt : 6 * b ≤ t) :
    2 ^ t * b ^ t ≤ t.factorial := by
  have hfactorial : (0 : ℝ) < t.factorial := by exact_mod_cast Nat.factorial_pos t
  have hterm : (t : ℝ) ^ t ≤ Real.exp t * t.factorial :=
    (div_le_iff₀ hfactorial).mp
      (Real.pow_div_factorial_le_exp (t : ℝ) (Nat.cast_nonneg t) t)
  have hexp : Real.exp (t : ℝ) ≤ (3 : ℝ) ^ t := by
    have heq : Real.exp (t : ℝ) = Real.exp 1 ^ t := by
      simpa only [mul_one] using Real.exp_nat_mul (1 : ℝ) t
    rw [heq]
    exact pow_le_pow_left₀ (Real.exp_pos 1).le exp_one_lt_three_for_factorial.le t
  have hbase : 3 * (2 * (b : ℝ)) ≤ t := by
    have h : (6 : ℝ) * b ≤ t := by exact_mod_cast hbt
    linarith
  have hpower : (3 : ℝ) ^ t * (2 ^ t * (b : ℝ) ^ t) ≤ (t : ℝ) ^ t := by
    have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 3 * (2 * (b : ℝ))) hbase t
    simpa only [mul_pow] using h
  have htotal : (3 : ℝ) ^ t * (2 ^ t * (b : ℝ) ^ t) ≤ 3 ^ t * t.factorial :=
    hpower.trans (hterm.trans (mul_le_mul_of_nonneg_right hexp hfactorial.le))
  have hcancel := (mul_le_mul_iff_right₀ (pow_pos (by norm_num : (0 : ℝ) < 3) t)).mp htotal
  exact_mod_cast hcancel

/-- The elementary exponential bound needed to make the finite union bound
strictly smaller than one. -/
theorem sq_le_two_pow_of_four_le (t : ℕ) (ht : 4 ≤ t) : t ^ 2 ≤ 2 ^ t := by
  induction t, ht using Nat.le_induction with
  | base => norm_num
  | succ t ht ih =>
    have hsquare : (t + 1) ^ 2 ≤ 2 * t ^ 2 := by nlinarith
    calc
      (t + 1) ^ 2 ≤ 2 * t ^ 2 := hsquare
      _ ≤ 2 * 2 ^ t := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (t + 1) := by rw [pow_succ]; omega

/-- Uniformly choose the forbidden-label allowance and order threshold.
The witness is one quarter of the rounded linear slack. Both the exact
factorial criterion and the strict unused-palette bound hold for every
later graph order and forbidden-set bound. -/
theorem exists_uniform_coloring_bounds (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ b : ℕ,
      (b : ℝ) ≤ ε * n → ∃ t : ℕ,
        1 ≤ t ∧ n * b ^ t < t.factorial ∧ b + 2 * (t - 1) < Nat.ceil (δ * n) := by
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt
    (max (1 : ℝ) (max (128 / δ ^ 2) (32 / δ)))
  refine ⟨δ / 128, by positivity, n₀, ?_⟩
  intro n hn b hb
  have hnR : max (1 : ℝ) (max (128 / δ ^ 2) (32 / δ)) < n :=
    hn₀.trans_le (by exact_mod_cast hn)
  have hn1 : (1 : ℝ) < n := (le_max_left _ _).trans_lt hnR
  have hnpos : (0 : ℝ) < n := by linarith
  have hnquad : 128 / δ ^ 2 < (n : ℝ) :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hnR
  have hnlinear : 32 / δ < (n : ℝ) :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hnR
  have hlinear : (32 : ℝ) < δ * n := by
    have h := (div_lt_iff₀ hδ).mp hnlinear
    nlinarith
  let s := Nat.ceil (δ * n)
  let t := s / 4
  have hceil : δ * n ≤ (s : ℝ) := Nat.le_ceil _
  have hs32 : 32 ≤ s := by exact_mod_cast (hlinear.le.trans hceil)
  have ht4 : 4 ≤ t := by
    dsimp only [t]
    exact (Nat.le_div_iff_mul_le (by decide : 0 < 4)).mpr (by omega)
  have hround_upper : 4 * t ≤ s := by
    have h := Nat.div_mul_le_self s 4
    change t * 4 ≤ s at h
    omega
  have hround_lower : s < 4 * (t + 1) := by
    have h := (Nat.div_lt_iff_lt_mul (by decide : 0 < 4)).mp (Nat.lt_succ_self (s / 4))
    change s < (t + 1) * 4 at h
    omega
  have hst : s ≤ 8 * t := by omega
  have hscaled : δ * n ≤ 8 * (t : ℝ) :=
    hceil.trans (by exact_mod_cast hst)
  have htR : δ * n / 8 ≤ (t : ℝ) := by linarith
  have hquadratic : (128 : ℝ) < δ ^ 2 * n := by
    have h := (div_lt_iff₀ (sq_pos_of_pos hδ)).mp hnquad
    nlinarith
  have hlarge_square := mul_lt_mul_of_pos_right hquadratic hnpos
  have ht_square := pow_le_pow_left₀
    (by positivity : (0 : ℝ) ≤ δ * n / 8) htR 2
  have hnlt_square_real : (n : ℝ) < (t : ℝ) ^ 2 := by nlinarith
  have hnlt_square : n < t ^ 2 := by exact_mod_cast hnlt_square_real
  have hnlt_pow : n < 2 ^ t := hnlt_square.trans_le (sq_le_two_pow_of_four_le t ht4)
  have hbt_real : (6 : ℝ) * b ≤ t := by
    have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    nlinarith
  have hbt : 6 * b ≤ t := by exact_mod_cast hbt_real
  have htpos : 0 < t := by omega
  refine ⟨t, by omega, ?_, ?_⟩
  · by_cases hbzero : b = 0
    · rw [hbzero, zero_pow (Nat.ne_of_gt htpos), Nat.mul_zero]
      exact Nat.factorial_pos t
    · have hbpos : 0 < b := Nat.pos_of_ne_zero hbzero
      exact (Nat.mul_lt_mul_of_pos_right hnlt_pow (pow_pos hbpos t)).trans_le
        (two_pow_mul_pow_le_factorial b t hbt)
  · change b + 2 * (t - 1) < s
    omega

end Overfull.ColoringExtension
