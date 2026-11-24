import Overfull.RobustRealization.Intervals

/-!
# Uniform expansion constants for large cycle powers

The robust parameter and order threshold are fixed before the graph and its
degree sequence. Deleting a graph of maximum degree one is permitted.
-/

namespace Overfull.RobustRealization

open Finset Classical SimpleGraph

set_option maxHeartbeats 800000 in
theorem exists_cyclePower_robust_parameters (δ τ : ℝ) (hδ : 0 < δ) (hτ : 0 < τ) :
    ∃ ν : ℝ, 0 < ν ∧ ∃ n₀ : ℕ, 0 < n₀ ∧
      ∀ (n : ℕ) [NeZero n], n₀ ≤ n →
        ∀ (r : ℕ), δ * n / 3 ≤ r →
          ∀ (G M : SimpleGraph (Fin n)),
            cyclePower n r ≤ G ⊔ M → (∀ v, M.degree v ≤ 1) →
              IsRobustExpander G ν τ := by
  obtain ⟨l, hl⟩ := exists_nat_gt (max 1 (16 / δ))
  have hlR : (1 : ℝ) < l := (le_max_left _ _).trans_lt hl
  have hl0R : (0 : ℝ) < l := by linarith
  have hl0 : 0 < l := by exact_mod_cast hl0R
  have hδl : 16 ≤ δ * l := by
    have hh := (div_lt_iff₀ hδ).mp ((le_max_right _ _).trans_lt hl)
    nlinarith
  let ν := min (τ / (6*l)) (1 / (16*(l : ℝ)^2))
  have hν : 0 < ν := by dsimp [ν]; positivity
  have hν₁ : ν * (6*l) ≤ τ :=
    (le_div_iff₀ (by positivity : 0 < (6*(l : ℝ)))).mp (min_le_left _ _)
  have hν₂ : ν * (16*(l : ℝ)^2) ≤ 1 :=
    (le_div_iff₀ (by positivity : 0 < 16*(l : ℝ)^2)).mp (min_le_right _ _)
  have hντ : ν ≤ τ := by nlinarith
  have hsmall : 3*ν*l < τ := by nlinarith
  have hgap : 3*ν*l+ν ≤ 1 / (2*l) := by
    apply (le_div_iff₀ (by positivity : 0 < (2*(l : ℝ)))).mpr
    have hmul : 0 ≤ ν * ((l : ℝ)^2 - l) :=
      mul_nonneg hν.le (by nlinarith)
    nlinarith
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt
    (max (l : ℝ) (max (8*l/δ) (1/ν)))
  have hn₀pos : 0 < n₀ := by
    have hh := hl0R.trans ((le_max_left _ _).trans_lt hn₀)
    exact_mod_cast hh
  refine ⟨ν, hν, n₀, hn₀pos, ?_⟩
  intro n _ hn r hr G M hcover hM
  have hnn : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
  have hnlR : (l : ℝ) < n := (le_max_left _ _).trans_lt (hn₀.trans_le hnn)
  have hnl : l ≤ n := by exact_mod_cast hnlR.le
  have hnlarge : 1 ≤ ν*n := by
    have hh : 1/ν < (n : ℝ) :=
      (le_max_right _ _).trans ((le_max_right _ _)) |>.trans_lt (hn₀.trans_le hnn)
    have hh' := (div_lt_iff₀ hν).mp hh
    nlinarith
  have hδn : 8*l ≤ δ*n := by
    have hh : 8*(l : ℝ)/δ < n :=
      (le_max_left _ _).trans ((le_max_right _ _)) |>.trans_lt (hn₀.trans_le hnn)
    have hh' := (div_lt_iff₀ hδ).mp hh
    nlinarith
  let q := n/l
  have hq : 0 < q := Nat.div_pos hnl hl0
  have hqn : l*q ≤ n := by simpa [q, Nat.mul_comm] using Nat.div_mul_le_self n l
  have hnq : n < l*q+l := by
    have hh := Nat.lt_mul_div_succ n hl0
    dsimp [q]
    nlinarith
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hqnR : (l : ℝ)*q ≤ n := by exact_mod_cast hqn
  have h16q : 16*(q : ℝ) ≤ δ*n := by
    have hh₁ := mul_le_mul_of_nonneg_right hδl hqR.le
    have hh₂ := mul_le_mul_of_nonneg_left hqnR hδ.le
    nlinarith
  have hr' : 2*q+l ≤ r := by
    have hh : (2 : ℝ)*q+l ≤ r := by linarith
    exact_mod_cast hh
  have hsize : (1 / (2*(l : ℝ))) * n ≤ q := by
    have hnn : n ≤ 2*l*q := by nlinarith
    have hh : (n : ℝ) ≤ 2*l*q := by exact_mod_cast hnn
    rw [div_mul_eq_mul_div, one_mul]
    apply (div_le_iff₀ (by positivity : 0 < (2*(l : ℝ)))).mpr
    nlinarith
  exact robust_of_cyclePower n l q r hl0 hq hqn hnq hr' G M hcover hM
    ν τ (1/(2*l)) hν hντ hnlarge hsmall hgap hsize

end Overfull.RobustRealization
