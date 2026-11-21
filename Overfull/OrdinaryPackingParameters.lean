import Overfull.OrdinaryPackingBounds

/-!
# Uniform parameters for ordinary matching packing

The reserve density and expansion range are fixed first. After the
paired-cut constants are known, a positive error constant satisfies every
degree, saturation and augmenting-path budget simultaneously.
-/

namespace Overfull.OrdinaryPackingParameters

theorem reserve_parameters (α γ ν τ σ₀ : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hγ : 0 < γ)
    (hν : 0 < ν) (hντ : ν ≤ τ) (hτ : τ ≤ α / 8)
    (hσ₀ : 0 < σ₀) (hσ₀1 : σ₀ < 1 / 2) :
    let p := min γ 1 / 16
    let σ := min τ (min σ₀ (p * α / 1000)) / 2
    let δ₀ := p * α / 2
    let θ := p * min ν (α * σ / 4) / 4
    0 < p ∧ p ≤ 1 ∧ p ≤ γ / 8 ∧
    0 < σ ∧ σ ≤ τ ∧ σ ≤ σ₀ ∧ σ ≤ 1 / 16 ∧ 16 * σ ≤ δ₀ / 3 ∧
    0 < δ₀ ∧ 0 < θ ∧ θ ≤ 4 * σ ∧ θ ≤ 1 := by
  let p := min γ 1 / 16
  let σ := min τ (min σ₀ (p * α / 1000)) / 2
  let δ₀ := p * α / 2
  let θ := p * min ν (α * σ / 4) / 4
  have hτ0 : 0 < τ := hν.trans_le hντ
  have hp : 0 < p := by dsimp [p]; positivity
  have hp16 : p ≤ 1 / 16 := by
    have h := min_le_right γ (1 : ℝ)
    dsimp only [p]
    linarith
  have hpγ : p ≤ γ / 8 := by
    have h := min_le_left γ (1 : ℝ)
    dsimp only [p]
    linarith
  have hσ : 0 < σ := by dsimp [σ]; positivity
  have hστ : σ ≤ τ / 2 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hσσ₀ : σ ≤ σ₀ / 2 := div_le_div_of_nonneg_right
    ((min_le_right _ _).trans (min_le_left _ _)) (by norm_num)
  have hτ1 : τ ≤ 1 / 8 := hτ.trans (by linarith only [hα1])
  have hσsmall : σ ≤ 1 / 16 := by linarith only [hστ,hτ1]
  have hσhalf : σ ≤ 1 / 4 := by linarith only [hσσ₀,hσ₀1]
  have hσα : σ ≤ p * α / 2000 := by
    have h := div_le_div_of_nonneg_right
      ((min_le_right τ (min σ₀ (p * α / 1000))).trans (min_le_right _ _))
      (by norm_num : (0 : ℝ) ≤ 2)
    change σ ≤ _ at h
    nlinarith only [h]
  have hδ₀ : 0 < δ₀ := by dsimp [δ₀]; positivity
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hpa : p * α ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hα1 hp.le
    linarith
  have hθσ : θ ≤ σ / 16 := by
    have hmin := min_le_right ν (α * σ / 4)
    have hmul := mul_le_mul_of_nonneg_left hmin hp.le
    have hprod := mul_le_mul_of_nonneg_right hpa hσ.le
    dsimp only [θ]
    nlinarith only [hmul,hprod]
  change 0 < p ∧ p ≤ 1 ∧ p ≤ γ / 8 ∧
    0 < σ ∧ σ ≤ τ ∧ σ ≤ σ₀ ∧ σ ≤ 1 / 16 ∧ 16 * σ ≤ δ₀ / 3 ∧
    0 < δ₀ ∧ 0 < θ ∧ θ ≤ 4 * σ ∧ θ ≤ 1
  refine ⟨hp,by linarith,hpγ,hσ,by linarith,by linarith,hσsmall,?_,hδ₀,hθ,
    by linarith,by linarith only [hθσ,hσhalf]⟩
  dsimp only [δ₀]
  nlinarith only [hσα,mul_pos hp hα]

/-- Once the paired-cut parameter is fixed, a single positive error
constant satisfies all the ordinary packing estimates. -/
theorem exists_error_parameter (α γ p θ δ₀ ξ : ℝ)
    (hα : 0 < α) (hγ : 0 < γ) (hp : 0 < p)
    (hθ : 0 < θ) (hδ₀ : 0 < δ₀) (hξ : 0 < ξ) :
    let ℓ := Nat.ceil (2 / ξ) + 2
    let c₀ := Real.exp (120 * (ℓ : ℝ) / γ) - 1
    let μ := min θ δ₀ / 100
    2 ≤ ℓ ∧ 0 ≤ c₀ ∧ 0 < μ ∧ μ ≤ θ / 2 ∧
    ∃ ε : ℝ, 0 < ε ∧ μ + ε ≤ δ₀ / 2 ∧ ε ≤ θ / 2 ∧ ε ≤ 1 / 2 ∧
      ε ≤ γ / 40 ∧ ε ≤ p ∧ ε ≤ p * α / 8 ∧
      4 * c₀ * ε / μ < γ / 8 ∧
      (4 * c₀ / μ + 30 * (ℓ : ℝ) * (1 + c₀) / γ) * ε ≤ min ξ (δ₀ / 3) / 16 := by
  let ℓ := Nat.ceil (2 / ξ) + 2
  let c₀ := Real.exp (120 * (ℓ : ℝ) / γ) - 1
  let μ := min θ δ₀ / 100
  have hℓ : 2 ≤ ℓ := by dsimp [ℓ]; omega
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast (show 0 < ℓ by omega)
  have hc₀ : 0 ≤ c₀ := by
    have he : 1 ≤ Real.exp (120 * (ℓ : ℝ) / γ) :=
      Real.one_le_exp_iff.mpr (by positivity)
    dsimp only [c₀]
    linarith
  have hμ : 0 < μ := by dsimp [μ]; positivity
  have hμθ : μ ≤ θ / 100 :=
    div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hμδ₀ : μ ≤ δ₀ / 100 :=
    div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  let c := 4 * c₀ / μ + 30 * (ℓ : ℝ) * (1 + c₀) / γ
  have hc : 0 < c := by dsimp [c]; positivity
  have hsat : 0 < 4 * c₀ / μ + 1 := by positivity
  obtain ⟨ε,hε,hbounds⟩ := exists_between (show (0 : ℝ) <
    min (δ₀ / 4) (min (θ / 2) (min (1 / 2) (min (γ / 40)
      (min p (min (p * α / 8) (min ((γ / 8) / (4 * c₀ / μ + 1))
        (min ξ (δ₀ / 3) / (16 * c)))))))) by positivity)
  simp only [lt_min_iff] at hbounds
  obtain ⟨hεδ₀,hεθ,hε1,hεγ,hεp,hεα,hεsat,hεbudget⟩ := hbounds
  change 2 ≤ ℓ ∧ 0 ≤ c₀ ∧ 0 < μ ∧ μ ≤ θ / 2 ∧
    ∃ ε : ℝ, 0 < ε ∧ μ + ε ≤ δ₀ / 2 ∧ ε ≤ θ / 2 ∧ ε ≤ 1 / 2 ∧
      ε ≤ γ / 40 ∧ ε ≤ p ∧ ε ≤ p * α / 8 ∧
      4 * c₀ * ε / μ < γ / 8 ∧ c * ε ≤ min ξ (δ₀ / 3) / 16
  refine ⟨hℓ,hc₀,hμ,by linarith,ε,hε,by linarith,hεθ.le,hε1.le,hεγ.le,
    hεp.le,hεα.le,?_,?_⟩
  · have h := (lt_div_iff₀ hsat).mp hεsat
    have heq : 4 * c₀ * ε / μ = ε * (4 * c₀ / μ + 1) - ε := by ring
    rw [heq]
    linarith only [h,hε]
  · have h := (lt_div_iff₀ (show 0 < 16 * c by positivity)).mp hεbudget
    linarith

end Overfull.OrdinaryPackingParameters
