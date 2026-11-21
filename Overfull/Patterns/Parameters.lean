import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic

/-!
# Uniform parameters for the frequent-pattern step

The packing error and surviving robust parameter are fixed first. The
rounding loss, original error, and order threshold are then chosen for
the requested final error, uniformly in all graph and core data.
-/

namespace Overfull.Patterns

/-- Scalar estimates used by rounding, completion, small-cut safety, and
the final addition of the exceptional vertices. -/
structure PatternScalarBounds (α εp θ δ B C η : ℝ)
    (M t n k m z : ℕ) (a : ℝ) : Prop where
  order_pos : 0 < n
  degree_pos : 0 < k
  frequent_large : 6*B ≤ (k : ℝ)
  packing_error : a ≤ εp*m
  packing_order : M ≤ m
  footprint : ((2*t+6 : ℕ) : ℝ) ≤ εp*m
  safe_error : a ≤ (α/(4*B))*n/10
  robust_cut : 3 < θ^2*α^2*n
  addition : (z : ℝ) ≤ θ*m/4
  reserve : (α/(4*B))*m ≤ (k : ℝ)/(3*B)
  final_error : a+(η*k+B+C*a/η) ≤ δ*((k : ℝ)/(3*B))

set_option maxHeartbeats 800000 in
/-- In particular the output robustness need not depend on the requested
final error. Every parameter here is chosen before the graph. -/
theorem exists_pattern_parameters (α εp θ δ B C : ℝ)
    (hα : 0 < α) (hεp : 0 < εp) (hθ : 0 < θ)
    (hδ : 0 < δ) (hB : 0 < B) (hC : 0 ≤ C) (M t : ℕ) :
    ∃ η ε : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < ε ∧ ∃ N : ℕ,
      ∀ (n k m z : ℕ) (a : ℝ), N ≤ n →
        α*n ≤ k → α*n ≤ m → m ≤ n → z ≤ t →
        0 ≤ a → a ≤ ε*n →
        PatternScalarBounds α εp θ δ B C η M t n k m z a := by
  let η := min (1/2 : ℝ) (δ/(12*B))
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hη1 : η ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hηδ : η ≤ δ/(12*B) := min_le_right _ _
  let D := 1+C/η
  have hD : 0 < D := by dsimp [D]; positivity
  let ε := min (εp*α) (min (α/(40*B)) (δ*α/(12*B*D)))
  have hε : 0 < ε := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hεpack : ε ≤ εp*α := min_le_left _ _
  have hεsafe : ε ≤ α/(40*B) := (min_le_right _ _).trans (min_le_left _ _)
  have hεδ : ε ≤ δ*α/(12*B*D) := (min_le_right _ _).trans (min_le_right _ _)
  let b : Fin 7 → ℝ := ![1, 6*B/α, ((2*t+6 : ℕ) : ℝ)/(εp*α),
    4*(t : ℝ)/(θ*α), 4/(θ^2*α^2), (M : ℝ)/α, 12*B*B/(δ*α)]
  have hb : ∀ i, 0 ≤ b i := by
    intro i
    fin_cases i <;> dsimp [b] <;> positivity
  obtain ⟨N,hN⟩ := exists_nat_gt (∑ i, b i)
  refine ⟨η,ε,hη,hη1,hε,N,?_⟩
  intro n k m z a hn hk hm hmn hzt ha hae
  have hnlarge (i : Fin 7) : b i < (n : ℝ) :=
    (Finset.single_le_sum (fun j _ => hb j) (Finset.mem_univ i)).trans_lt
      (hN.trans_le (by exact_mod_cast hn))
  have hnR : (0 : ℝ) < n := by
    have h := hnlarge 0
    change (1 : ℝ) < n at h
    linarith
  have hkR : (0 : ℝ) < k := (mul_pos hα hnR).trans_le hk
  have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hztR : (z : ℝ) ≤ t := by exact_mod_cast hzt
  have hlarge : 6*B ≤ (k : ℝ) := by
    have h := (div_lt_iff₀ hα).mp (hnlarge 1)
    nlinarith only [h,hk]
  have hpack : a ≤ εp*m := by
    have h₁ := mul_le_mul_of_nonneg_right hεpack hnR.le
    have h₂ := mul_le_mul_of_nonneg_left hm hεp.le
    nlinarith only [hae,h₁,h₂]
  have hfoot : ((2*t+6 : ℕ) : ℝ) ≤ εp*m := by
    have h := (div_lt_iff₀ (mul_pos hεp hα)).mp (hnlarge 2)
    have h₂ := mul_le_mul_of_nonneg_left hm hεp.le
    nlinarith only [h,h₂]
  have hadd : (z : ℝ) ≤ θ*m/4 := by
    have h := (div_lt_iff₀ (mul_pos hθ hα)).mp (hnlarge 3)
    have h₂ := mul_le_mul_of_nonneg_left hm hθ.le
    nlinarith only [h,h₂,hztR]
  have hrobust : 3 < θ^2*α^2*n := by
    have h := (div_lt_iff₀ (show 0 < θ^2*α^2 by positivity)).mp (hnlarge 4)
    nlinarith only [h]
  have horder : M ≤ m := by
    have h := (div_lt_iff₀ hα).mp (hnlarge 5)
    have hR : (M : ℝ) ≤ m := by nlinarith only [h,hm]
    exact_mod_cast hR
  have hsafe : a ≤ (α/(4*B))*n/10 := by
    have h := hae.trans (mul_le_mul_of_nonneg_right hεsafe hnR.le)
    convert h using 1; ring
  have hreserve : (α/(4*B))*m ≤ (k : ℝ)/(3*B) := by
    have h₁ := mul_le_mul_of_nonneg_left hmnR hα.le
    have h₂ : α*(m : ℝ) ≤ k := h₁.trans hk
    apply (le_div_iff₀ (show 0 < 3*B by positivity)).mpr
    have heq : (α/(4*B)*(m : ℝ))*(3*B) = 3*(α*m)/4 := by field_simp
    rw [heq]
    nlinarith only [h₂, hkR]
  have hround : η*(k : ℝ) ≤ δ*k/(12*B) := by
    have h := mul_le_mul_of_nonneg_right hηδ hkR.le
    convert h using 1; ring
  have herror : D*a ≤ δ*k/(12*B) := by
    have hεδ' : D*ε ≤ δ*α/(12*B) := by
      have h := (le_div_iff₀ (show 0 < 12*B*D by positivity)).mp hεδ
      apply (le_div_iff₀ (show 0 < 12*B by positivity)).mpr
      nlinarith only [h]
    have h₁ := mul_le_mul_of_nonneg_left hae hD.le
    have h₂ := mul_le_mul_of_nonneg_right hεδ' hnR.le
    have h₃ := mul_le_mul_of_nonneg_left hk (show 0 ≤ δ/(12*B) by positivity)
    calc
      D*a ≤ D*(ε*n) := h₁
      _ = D*ε*n := by ring
      _ ≤ δ*α/(12*B)*n := h₂
      _ = δ/(12*B)*(α*n) := by ring
      _ ≤ δ/(12*B)*k := h₃
      _ = δ*k/(12*B) := by ring
  have hconstant : B ≤ δ*k/(12*B) := by
    have h := (div_lt_iff₀ (mul_pos hδ hα)).mp (hnlarge 6)
    have h₂ := mul_le_mul_of_nonneg_left hk hδ.le
    apply (le_div_iff₀ (show 0 < 12*B by positivity)).mpr
    nlinarith only [h,h₂]
  have hfinal : a+(η*k+B+C*a/η) ≤ δ*((k : ℝ)/(3*B)) := by
    have heq : D*a = a+C*a/η := by dsimp [D]; ring
    rw [heq] at herror
    have hr : δ*((k : ℝ)/(3*B)) = 4*(δ*k/(12*B)) := by ring
    rw [hr]
    have hnonneg : 0 ≤ δ*(k : ℝ)/(12*B) := by positivity
    linarith only [hround,herror,hconstant,hnonneg]
  exact ⟨by exact_mod_cast hnR, by exact_mod_cast hkR, hlarge,hpack,horder,
    hfoot,hsafe,hrobust,hadd,hreserve,hfinal⟩

end Overfull.Patterns
