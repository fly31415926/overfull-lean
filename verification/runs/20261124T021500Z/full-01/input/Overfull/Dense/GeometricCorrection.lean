import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

/-!
# Summing geometric corrections

A bounded correction that halves every residual can be repeated. The resulting
series converges to an exact correction, with twice the one-step bound. The
finite-coordinate theorem keeps continuity and convergence inside this module.
-/

namespace Overfull.GeometricCorrection

open Function Filter Finset
open scoped Topology

/-- The geometric-series step of the Banach open mapping proof, with the
constant retained exactly. The argument follows mathlib's
`ContinuousLinearMap.exists_preimage_norm_le`. -/
private theorem preimage_of_halving
    {P Q : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    (L : P →L[ℝ] Q) (C : ℝ) (hC : 0 ≤ C)
    (happrox : ∀ y : Q, ∃ p : P,
      ‖y - L p‖ ≤ (1 / 2 : ℝ) * ‖y‖ ∧ ‖p‖ ≤ C * ‖y‖)
    (y : Q) : ∃ p : P, L p = y ∧ ‖p‖ ≤ 2 * C * ‖y‖ := by
  classical
  choose g hg using happrox
  let h : Q → Q := fun y => y - L (g y)
  have hle : ∀ y, ‖h y‖ ≤ (1 / 2 : ℝ) * ‖y‖ := fun y => (hg y).1
  have hnle : ∀ n : ℕ, ‖h^[n] y‖ ≤ (1 / 2 : ℝ) ^ n * ‖y‖ := by
    intro n
    induction n with
    | zero => simp only [one_div, iterate_zero_apply, pow_zero, one_mul, le_rfl]
    | succ n ih =>
      rw [iterate_succ']
      apply (hle _).trans
      rw [pow_succ', mul_assoc]
      gcongr
  let u : ℕ → P := fun n => g (h^[n] y)
  have ule : ∀ n, ‖u n‖ ≤ (1 / 2 : ℝ) ^ n * (C * ‖y‖) := by
    intro n
    apply (hg _).2.trans
    calc
      C * ‖h^[n] y‖ ≤ C * ((1 / 2 : ℝ) ^ n * ‖y‖) :=
        mul_le_mul_of_nonneg_left (hnle n) hC
      _ = _ := by ring
  have sNu : Summable (fun n => ‖u n‖) := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ule ?_
    exact Summable.mul_right _ summable_geometric_two
  have su : Summable u := sNu.of_norm
  let p := ∑' n, u n
  have hp : ‖p‖ ≤ 2 * C * ‖y‖ := by
    calc
      ‖p‖ ≤ ∑' n, ‖u n‖ := norm_tsum_le_tsum_norm sNu
      _ ≤ ∑' n, (1 / 2 : ℝ) ^ n * (C * ‖y‖) :=
        sNu.tsum_le_tsum ule (Summable.mul_right _ summable_geometric_two)
      _ = (∑' n, (1 / 2 : ℝ) ^ n) * (C * ‖y‖) := tsum_mul_right
      _ = 2 * C * ‖y‖ := by rw [tsum_geometric_two, mul_assoc]
  have hsum : ∀ n : ℕ, L (∑ i ∈ Finset.range n, u i) = y - h^[n] y := by
    intro n
    induction n with
    | zero => simp [L.map_zero]
    | succ n ih =>
      rw [Finset.sum_range_succ, L.map_add, ih, iterate_succ_apply', sub_add]
  have htend : Tendsto (fun n => ∑ i ∈ Finset.range n, u i) atTop (𝓝 p) :=
    su.hasSum.tendsto_sum_nat
  have hfirst : Tendsto (fun n => L (∑ i ∈ Finset.range n, u i)) atTop (𝓝 (L p)) :=
    (L.continuous.tendsto _).comp htend
  simp only [hsum] at hfirst
  have hsecond : Tendsto (fun n => y - h^[n] y) atTop (𝓝 (y - 0)) := by
    refine tendsto_const_nhds.sub ?_
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) hnle ?_
    rw [← zero_mul ‖y‖]
    refine (_root_.tendsto_pow_atTop_nhds_zero_of_lt_one ?_ ?_).mul tendsto_const_nhds <;>
      norm_num
  have heq : L p = y - 0 := tendsto_nhds_unique hfirst hsecond
  exact ⟨p, by simpa using heq, hp⟩

/-- Finite-coordinate geometric correction. The only approximation assumption
is the stated one-step correction. Its iterates produce an exact preimage with
coordinate bound `2 * C * d`. Empty coordinate types and `C = 0` are allowed. -/
theorem exists_exact_correction
    {E T : Type*} [Fintype E] [Fintype T]
    (L : (T → ℝ) →ₗ[ℝ] (E → ℝ)) (S : Submodule ℝ (E → ℝ))
    (hLS : LinearMap.range L ≤ S) (C : ℝ) (hC : 0 ≤ C)
    (hstep : ∀ (r : E → ℝ), r ∈ S → ∀ d : ℝ, 0 ≤ d →
      (∀ e, |r e| ≤ d) → ∃ p : T → ℝ,
        (∀ t, |p t| ≤ C * d) ∧ (∀ e, |r e - (L p) e| ≤ d / 2))
    (r : E → ℝ) (hr : r ∈ S) (d : ℝ) (hd : 0 ≤ d)
    (hbound : ∀ e, |r e| ≤ d) :
    ∃ p : T → ℝ, L p = r ∧ ∀ t, |p t| ≤ 2 * C * d := by
  classical
  let L' : (T → ℝ) →ₗ[ℝ] S := L.codRestrict S (fun p => hLS ⟨p, rfl⟩)
  let f : (T → ℝ) →L[ℝ] S := LinearMap.toContinuousLinearMap L'
  have happrox : ∀ y : S, ∃ p : T → ℝ,
      ‖y - f p‖ ≤ (1 / 2 : ℝ) * ‖y‖ ∧ ‖p‖ ≤ C * ‖y‖ := by
    intro y
    have hycoord : ∀ e, |(y : E → ℝ) e| ≤ ‖y‖ := by
      intro e
      exact norm_le_pi_norm (y : E → ℝ) e
    obtain ⟨p, hp, hres⟩ := hstep y.val y.property ‖y‖ (norm_nonneg y) hycoord
    refine ⟨p, ?_, ?_⟩
    · change ‖(y : E → ℝ) - L p‖ ≤ (1 / 2 : ℝ) * ‖y‖
      apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
      intro e
      simpa only [Pi.sub_apply, Real.norm_eq_abs, one_div, div_eq_mul_inv, mul_comm, one_mul] using hres e
    · exact (pi_norm_le_iff_of_nonneg (mul_nonneg hC (norm_nonneg y))).mpr hp
  obtain ⟨p, hp, hpnorm⟩ := preimage_of_halving f C hC happrox ⟨r, hr⟩
  have hrnorm : ‖r‖ ≤ d := (pi_norm_le_iff_of_nonneg hd).mpr hbound
  refine ⟨p, ?_, ?_⟩
  · exact congrArg Subtype.val hp
  · intro t
    calc
      |p t| ≤ ‖p‖ := norm_le_pi_norm p t
      _ ≤ 2 * C * ‖r‖ := hpnorm
      _ ≤ 2 * C * d := mul_le_mul_of_nonneg_left hrnorm (by positivity)

end Overfull.GeometricCorrection
