import Overfull.Dense.Reserve.Graph

/-!
# Explicit estimates for the common reserve demands
-/

namespace Overfull.Dense

open Finset Classical

/-- The normalized common demand differs from either initial degree
demand by at most `4 * μ * θ` times that degree. -/
theorem reserve_demand_estimate (e θ μ t e₀ e₁ x y : ℝ)
    (he : 0 < e) (hθ : 0 ≤ θ) (hθsmall : θ ≤ 1/4) (hμ : 0 ≤ μ)
    (h₀ : (1-θ)*e ≤ e₀ ∧ e₀ ≤ (1+θ)*e)
    (h₁ : (1-θ)*e ≤ e₁ ∧ e₁ ≤ (1+θ)*e)
    (ht : μ*(1-θ)*e ≤ t ∧ t ≤ μ*(1+θ)*e)
    (hx : 0 ≤ x) (hxy : |x-y| ≤ θ*x) :
    |t*(x+y)/(e₀+e₁)-μ*x| ≤ 4*μ*θ*x := by
  have hSlo : 2*(1-θ)*e ≤ e₀+e₁ := by linarith [h₀.1,h₁.1]
  have hShi : e₀+e₁ ≤ 2*(1+θ)*e := by linarith [h₀.2,h₁.2]
  have hS : 0 < e₀+e₁ := by nlinarith
  have hθ1 : 0 ≤ 1-θ := by linarith
  have ht0 : 0 ≤ t := le_trans (by positivity : 0 ≤ μ*(1-θ)*e) ht.1
  have hμSlo := mul_le_mul_of_nonneg_left hSlo hμ
  have hμShi := mul_le_mul_of_nonneg_left hShi hμ
  have hratio : |2*t-μ*(e₀+e₁)| ≤ 4*μ*θ*e := by
    rw [abs_le]
    constructor <;> nlinarith [ht.1,ht.2]
  have heq : t*(x+y)/(e₀+e₁)-μ*x =
      (t*(y-x)+(2*t-μ*(e₀+e₁))*x)/(e₀+e₁) := by
    field_simp
    ring
  rw [heq, abs_div, abs_of_pos hS]
  apply (div_le_iff₀ hS).mpr
  calc
    _ ≤ t*|y-x| + |2*t-μ*(e₀+e₁)| *x := by
      simpa only [abs_mul, abs_of_nonneg ht0, abs_of_nonneg hx] using
        abs_add_le (t*(y-x)) ((2*t-μ*(e₀+e₁))*x)
    _ ≤ t*(θ*x) + (4*μ*θ*e)*x :=
      add_le_add (mul_le_mul_of_nonneg_left (by simpa only [abs_sub_comm] using hxy) ht0)
        (mul_le_mul_of_nonneg_right hratio hx)
    _ ≤ (μ*(1+θ)*e)*(θ*x) + (4*μ*θ*e)*x :=
      add_le_add_right (mul_le_mul_of_nonneg_right ht.2 (mul_nonneg hθ hx)) _
    _ = (μ*θ*e*x)*(5+θ) := by ring
    _ ≤ (μ*θ*e*x)*(8*(1-θ)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = (4*μ*θ*x)*(2*(1-θ)*e) := by ring
    _ ≤ (4*μ*θ*x)*(e₀+e₁) := mul_le_mul_of_nonneg_left hSlo (by positivity)

namespace SixCycleGraph

variable {V : Type*} [Fintype V] (G : SixCycleGraph V)

noncomputable def commonTotal (μ : ℝ) : ℝ :=
  μ / 6 * ∑ j : ZMod 6, (G.edgeCount j : ℝ)

noncomputable def reserveDemand (μ : ℝ) (v : V) : ℝ :=
  G.commonTotal μ * ((G.outDegree v : ℝ)+(G.inDegree v : ℝ)) /
    ((G.edgeCount (G.part v-1) : ℝ)+(G.edgeCount (G.part v) : ℝ))

theorem commonTotal_bounds (e θ μ : ℝ) (hμ : 0 ≤ μ)
    (hcounts : ∀ j, (1-θ)*e ≤ (G.edgeCount j : ℝ) ∧
      (G.edgeCount j : ℝ) ≤ (1+θ)*e) :
    μ*(1-θ)*e ≤ G.commonTotal μ ∧ G.commonTotal μ ≤ μ*(1+θ)*e := by
  have hl : (∑ _j : ZMod 6, (1-θ)*e) ≤ ∑ j : ZMod 6, (G.edgeCount j : ℝ) :=
    Finset.sum_le_sum (fun j _ => (hcounts j).1)
  have hu : (∑ j : ZMod 6, (G.edgeCount j : ℝ)) ≤ ∑ _j : ZMod 6, (1+θ)*e :=
    Finset.sum_le_sum (fun j _ => (hcounts j).2)
  have hμ6 : 0 ≤ μ/6 := by positivity
  constructor
  · calc
      _ = μ/6 * ∑ _j : ZMod 6, (1-θ)*e := by simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hl hμ6
  · calc
      _ ≤ μ/6 * ∑ _j : ZMod 6, (1+θ)*e := mul_le_mul_of_nonneg_left hu hμ6
      _ = _ := by simp; ring

theorem edgeCount_pos (e θ : ℝ) (he : 0 < e) (hθsmall : θ ≤ 1/4)
    (hcounts : ∀ j, (1-θ)*e ≤ (G.edgeCount j : ℝ)) (j : ZMod 6) :
    0 < (G.edgeCount j : ℝ) := by
  have := hcounts j
  nlinarith

theorem sum_reserveDemand (e θ μ : ℝ) (he : 0 < e) (hθsmall : θ ≤ 1/4)
    (hcounts : ∀ j, (1-θ)*e ≤ (G.edgeCount j : ℝ)) (j : ZMod 6) :
    (∑ v : G.Part j, G.reserveDemand μ v.val) = G.commonTotal μ := by
  have hden : (G.edgeCount (j-1) : ℝ)+(G.edgeCount j : ℝ) ≠ 0 := by
    have h₀ := G.edgeCount_pos e θ he hθsmall hcounts (j-1)
    have h₁ := G.edgeCount_pos e θ he hθsmall hcounts j
    positivity
  have hd (v : G.Part j) : G.reserveDemand μ v.val =
      G.commonTotal μ * ((G.outDegree v.val : ℝ)+(G.inDegree v.val : ℝ)) /
        ((G.edgeCount (j-1) : ℝ)+(G.edgeCount j : ℝ)) := by
    simp only [reserveDemand, v.property]
  simp_rw [hd]
  rw [← Finset.sum_div, ← Finset.mul_sum, Finset.sum_add_distrib,
    G.sum_outDegree_real, G.sum_inDegree_at_real]
  rw [add_comm (G.edgeCount j : ℝ), mul_div_cancel_right₀ _ hden]

theorem reserveDemand_out_error (e θ μ : ℝ) (he : 0 < e) (hθ : 0 ≤ θ)
    (hθsmall : θ ≤ 1/4) (hμ : 0 ≤ μ)
    (hcounts : ∀ j, (1-θ)*e ≤ (G.edgeCount j : ℝ) ∧
      (G.edgeCount j : ℝ) ≤ (1+θ)*e)
    (himbalance : ∀ v, |(G.outDegree v : ℝ)-(G.inDegree v : ℝ)| ≤
      θ * min (G.outDegree v : ℝ) (G.inDegree v : ℝ)) (v : V) :
    |G.reserveDemand μ v-μ*G.outDegree v| ≤ 4*μ*θ*G.outDegree v := by
  exact reserve_demand_estimate e θ μ (G.commonTotal μ)
    (G.edgeCount (G.part v-1)) (G.edgeCount (G.part v))
    (G.outDegree v) (G.inDegree v) he hθ hθsmall hμ
    (hcounts _) (hcounts _) (G.commonTotal_bounds e θ μ hμ hcounts)
    (Nat.cast_nonneg _)
    ((himbalance v).trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hθ))

theorem reserveDemand_in_error (e θ μ : ℝ) (he : 0 < e) (hθ : 0 ≤ θ)
    (hθsmall : θ ≤ 1/4) (hμ : 0 ≤ μ)
    (hcounts : ∀ j, (1-θ)*e ≤ (G.edgeCount j : ℝ) ∧
      (G.edgeCount j : ℝ) ≤ (1+θ)*e)
    (himbalance : ∀ v, |(G.outDegree v : ℝ)-(G.inDegree v : ℝ)| ≤
      θ * min (G.outDegree v : ℝ) (G.inDegree v : ℝ)) (v : V) :
    |G.reserveDemand μ v-μ*G.inDegree v| ≤ 4*μ*θ*G.inDegree v := by
  have h := reserve_demand_estimate e θ μ (G.commonTotal μ)
    (G.edgeCount (G.part v-1)) (G.edgeCount (G.part v))
    (G.inDegree v) (G.outDegree v) he hθ hθsmall hμ
    (hcounts _) (hcounts _) (G.commonTotal_bounds e θ μ hμ hcounts)
    (Nat.cast_nonneg _)
    (by simpa only [abs_sub_comm] using
      (himbalance v).trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hθ))
  simpa only [reserveDemand, add_comm (G.inDegree v : ℝ)] using h

end SixCycleGraph
end Overfull.Dense
