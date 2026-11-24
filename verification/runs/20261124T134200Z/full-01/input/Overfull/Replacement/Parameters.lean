import Overfull.RobustRealization

/-!
# Uniform constants for replacing a dense core

The robust parameter is fixed before the error tolerance. The order
threshold makes the robust cut bound larger than the allowed maximum degree.
-/

namespace Overfull.Replacement

theorem exists_replacement_parameters (β μ τ : ℝ) (nReal : ℕ)
    (hβ : 0 < β) (hμ : 0 < μ) (hτ : 0 ≤ τ) (hτβ : τ ≤ β/16) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∃ n₀ : ℕ,
      ∀ n q k : ℕ, ∀ a : ℝ, n₀ ≤ n → q ≤ n →
        2*β*n ≤ q → β*n ≤ k → 0 ≤ a → a+1 ≤ ξ*n → k ≤ (q : ℝ)+a →
        0 < n ∧ nReal ≤ q ∧ 1 ≤ β*n/2 ∧ a+1 ≤ β*n/2 ∧
        a ≤ μ*q ∧ 2*a+1 ≤ (k : ℝ)/8 ∧ τ*q ≤ (k : ℝ)/8 ∧
        (k : ℝ) < μ^2*(q : ℝ)^2 ∧ a+1 < (q : ℝ)/2 := by
  let ξ := min (β/128) (min (μ*β) (1/4))
  have hξ : 0 < ξ := by dsimp [ξ]; positivity
  have hξβ : ξ ≤ β/128 := min_le_left _ _
  have hξμ : ξ ≤ μ*β := (min_le_right _ _).trans (min_le_left _ _)
  have hξone : ξ ≤ 1/4 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt
    (max (4/β) (max ((nReal : ℝ)/(2*β)) (1/(μ^2*β^2))))
  refine ⟨ξ,hξ,n₀,?_⟩
  intro n q k a hn hqn hqlo hklo ha haξ hkupper
  have hnR : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
  have hmax := hn₀.trans_le hnR
  have hfour : 4/β < (n : ℝ) := (le_max_left _ _).trans_lt hmax
  have hreal : (nReal : ℝ)/(2*β) < n :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hmax
  have hquad : 1/(μ^2*β^2) < (n : ℝ) :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hmax
  have hnpos : (0 : ℝ) < n := lt_trans (by positivity : 0 < 4/β) hfour
  have hfour' := (div_lt_iff₀ hβ).mp hfour
  have hreal' := (div_lt_iff₀ (show 0 < 2*β by positivity)).mp hreal
  have hquad' := (div_lt_iff₀ (show 0 < μ^2*β^2 by positivity)).mp hquad
  have hqnR : (q : ℝ) ≤ n := by exact_mod_cast hqn
  have haβ : a+1 ≤ (β/128)*n := haξ.trans
    (mul_le_mul_of_nonneg_right hξβ (Nat.cast_nonneg n))
  have haμ : a+1 ≤ (μ*β)*n := haξ.trans
    (mul_le_mul_of_nonneg_right hξμ (Nat.cast_nonneg n))
  have haone : a+1 ≤ (1/4 : ℝ)*n := haξ.trans
    (mul_le_mul_of_nonneg_right hξone (Nat.cast_nonneg n))
  have hμq := mul_le_mul_of_nonneg_left hqlo hμ.le
  have hτq := mul_le_mul_of_nonneg_left hqnR hτ
  have hτn := mul_le_mul_of_nonneg_right hτβ (Nat.cast_nonneg n)
  have hsq := mul_self_le_mul_self (show 0 ≤ 2*β*(n : ℝ) by positivity) hqlo
  have hμsq := mul_le_mul_of_nonneg_left hsq (sq_nonneg μ)
  have hquadn := mul_lt_mul_of_pos_right hquad' hnpos
  have hkquad : (k : ℝ) < μ^2*(q : ℝ)^2 := by
    nlinarith only [hkupper,hqnR,haone,hμsq,hquadn,hnpos]
  refine ⟨by exact_mod_cast hnpos, ?_, by nlinarith only [hfour'],
    by nlinarith only [haβ,hfour'], by nlinarith only [haμ,hμq,ha],
    by nlinarith only [haβ,hklo,ha], by nlinarith only [hτq,hτn,hklo],
    hkquad, by nlinarith only [haβ,hqlo,hfour']⟩
  have hh : (nReal : ℝ) ≤ q := by nlinarith only [hreal',hqlo]
  exact_mod_cast hh

end Overfull.Replacement
