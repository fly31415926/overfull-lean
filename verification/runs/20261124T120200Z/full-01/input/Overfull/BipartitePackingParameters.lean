import Overfull.BipartitePackingBounds

/-!
# Fixed parameters for adaptive bipartite packing

All choices precede the graph, its order, and the forbidden sets. The path
length and the coefficient in the total load bound are the constants in
the manuscript.
-/

namespace Overfull.BipartitePackingParameters

/-- The fixed path bound is more than sufficient for the half-parameter
reserve used during the construction. -/
theorem path_length_bound (θ : ℝ) (hθ : 0 < θ) :
    Nat.ceil (2 / (θ / 2)) + 2 ≤ Nat.ceil (8 / θ) + 4 := by
  have harg : 2 / (θ / 2) ≤ 8 / θ := by
    rw [div_div_eq_mul_div]
    apply div_le_div_of_nonneg_right _ hθ.le
    norm_num
  have hceil := Nat.ceil_mono harg
  omega

/-- The exponential total-load coefficient is nonnegative. -/
theorem total_load_coefficient_nonneg (ℓ : ℕ) (γ : ℝ) (hγ : 0 < γ) :
    0 ≤ 8 * (Real.exp (8 * ℓ / γ) - 1) := by
  have harg : (0 : ℝ) ≤ 8 * ℓ / γ := by positivity
  have hex : 1 ≤ Real.exp (8 * ℓ / γ) := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr harg
  exact mul_nonneg (by norm_num) (sub_nonneg.mpr hex)

/-- A simultaneous choice of every small constant used by the packing
proof, expressed in terms of its original fixed parameters. -/
theorem exists_parameters (α γ p ν τ : ℝ)
    (hα : 0 < α) (hα1 : α < 1) (hγ : 0 < γ) (hγ1 : γ < 1)
    (hp : 0 < p) (hpγ : p < γ / 8) (hν : 0 < ν)
    (hτ : τ < p * α / 100) :
    let θ := p * ν / 2
    let δ₀ := p * α / 2
    let ℓ := Nat.ceil (8 / θ) + 4
    let c₀ := 8 * (Real.exp (8 * ℓ / γ) - 1)
    ∃ μ ε : ℝ, 0 < μ ∧ μ < min θ δ₀ / 100 ∧
      μ ≤ θ / 2 ∧ μ ≤ δ₀ / 2 ∧ 2 * τ ≤ δ₀ - μ ∧
      0 < ε ∧ ε ≤ p ∧ ε < 1 ∧ ε < p * α / 8 ∧ ε < γ / 16 ∧
      4 * c₀ * ε / μ < γ / 8 ∧
      (1 + 4 * c₀ / μ + 2 * (ℓ + 1) * (16 + 2 * c₀) / γ) * ε <
        min θ δ₀ / 8 := by
  let θ := p * ν / 2
  let δ₀ := p * α / 2
  let ℓ := Nat.ceil (8 / θ) + 4
  let c₀ := 8 * (Real.exp (8 * (ℓ : ℝ) / γ) - 1)
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hδ : 0 < δ₀ := by dsimp [δ₀]; positivity
  have hc : 0 ≤ c₀ := total_load_coefficient_nonneg ℓ γ hγ
  obtain ⟨μ, ε, hμ, hμsmall, hε, hεsmall, hbudget, hpaths⟩ :=
    BipartitePackingBounds.exists_load_parameters θ δ₀ γ p α c₀ ℓ hθ hδ hγ hp hα hc
  have hμθ : μ < θ / 100 := hμsmall.trans_le
    (div_le_div_of_nonneg_right (min_le_left θ δ₀) (by norm_num))
  have hμδ : μ < δ₀ / 100 := hμsmall.trans_le
    (div_le_div_of_nonneg_right (min_le_right θ δ₀) (by norm_num))
  have hεα := hεsmall.trans_le (min_le_left (p * α / 8) (γ / 16))
  have hεγ := hεsmall.trans_le (min_le_right (p * α / 8) (γ / 16))
  have hp1 : p < 1 := by linarith
  refine ⟨μ, ε, hμ, hμsmall, (show μ ≤ θ / 2 by linarith),
    (show μ ≤ δ₀ / 2 by linarith), ?_, hε, ?_, ?_,
    hεα, hεγ, hbudget, hpaths⟩
  · dsimp [δ₀] at *
    nlinarith
  · nlinarith [mul_pos hp (sub_pos.mpr hα1)]
  · linarith

/-- The sampling degree error still leaves the required linear minimum
degree in the original reserve. -/
theorem reserve_minimum_degree (m : ℕ) (α p ε Δ d : ℝ)
    (hp : 0 ≤ p) (hε : ε ≤ p * α / 8)
    (hΔ : α * m ≤ Δ) (hdegree : |d - p * Δ| ≤ 2 * ε * m) :
    p * α / 2 * m ≤ d := by
  have hΔ' := mul_le_mul_of_nonneg_left hΔ hp
  have hε' := mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg m)
  have hlower := (abs_le.mp hdegree).1
  have hnonneg := abs_nonneg (d - p * Δ)
  nlinarith

/-- The parameter choices imply the strict inequality needed to cover
every saturated vertex before using the reserve. -/
theorem capacity_budget (m : ℕ) (μ γ ε c₀ d : ℝ)
    (hm : 0 < m) (hμ : 0 < μ) (hγ : 0 < γ)
    (hlarge : 2 ≤ μ * m) (hε : ε < γ / 16)
    (hc : 4 * c₀ * ε / μ < γ / 8) (hd : γ * m / 2 ≤ d) :
    0 < Nat.floor (μ * m) ∧
      2 * (c₀ * ε * (m : ℝ) ^ 2) <
        (Nat.floor (μ * m) : ℝ) * (d - 4 * ε * m) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hfloor := BipartitePackingBounds.half_le_floor (μ * m) hlarge
  have hr : (0 : ℝ) < Nat.floor (μ * m) :=
    (by positivity : (0 : ℝ) < μ * m / 2).trans_le hfloor
  refine ⟨by exact_mod_cast hr, ?_⟩
  have hεm := mul_lt_mul_of_pos_right hε hmR
  have hdegree : γ * m / 4 ≤ d - 4 * ε * m := by nlinarith
  have hlower := mul_le_mul hfloor hdegree
    (by positivity : (0 : ℝ) ≤ γ * m / 4) hr.le
  have hcoefficient := (div_lt_iff₀ hμ).mp hc
  have hstrict := mul_lt_mul_of_pos_right hcoefficient
    (by positivity : (0 : ℝ) < (m : ℝ) ^ 2)
  have hpositive : (0 : ℝ) < μ * γ * (m : ℝ) ^ 2 := by positivity
  nlinarith

/-- The bounds on the forbidden set, saturated set and matching deficiency
give the complete path-packing budget. -/
theorem completion_budget (m h z s ℓ : ℕ) (θ δ₀ μ γ ε c₀ : ℝ)
    (hγ : 0 < γ) (hε : 0 ≤ ε) (hc₀ : 0 ≤ c₀)
    (hμδ : μ ≤ δ₀ / 2) (hlarge : 1 ≤ min θ δ₀ * m / 8)
    (hS : (s : ℝ) ≤ ε * m)
    (hZ : (z : ℝ) ≤ 2 * c₀ * ε * m / μ)
    (hH : (h : ℝ) ≤ (16 + 2 * c₀) * ε * m / γ)
    (hsmall : (1 + 4 * c₀ / μ + 2 * (ℓ + 1) * (16 + 2 * c₀) / γ) * ε <
      min θ δ₀ / 8) :
    (s : ℝ) + 2 * z + 2 * ℓ * h ≤
      min (θ / 2) (δ₀ - μ) * m / 2 - 1 := by
  apply BipartitePackingBounds.augmenting_path_budget m θ δ₀ μ _ hμδ hlarge
  let K := 1 + 4 * c₀ / μ + 2 * ((ℓ : ℝ) + 1) * (16 + 2 * c₀) / γ
  have hnonneg : 0 ≤ 2 * (16 + 2 * c₀) * ε * (m : ℝ) / γ := by positivity
  have hsum : (s : ℝ) + 2 * z + 2 * ℓ * h ≤
      ε * m + 2 * (2 * c₀ * ε * m / μ) +
        2 * ℓ * ((16 + 2 * c₀) * ε * m / γ) := by
    exact add_le_add (add_le_add hS (mul_le_mul_of_nonneg_left hZ (by norm_num)))
      (mul_le_mul_of_nonneg_left hH (by positivity))
  have hrewrite : ε * m + 2 * (2 * c₀ * ε * m / μ) +
        2 * ℓ * ((16 + 2 * c₀) * ε * m / γ) =
      K * ε * m - 2 * (16 + 2 * c₀) * ε * m / γ := by dsimp [K]; ring
  rw [hrewrite] at hsum
  have hsmallm := mul_le_mul_of_nonneg_right hsmall.le (Nat.cast_nonneg m)
  change K * ε * m ≤ min θ δ₀ / 8 * m at hsmallm
  linarith

/-- The natural number of permitted rounds has the needed finite bound,
and each of its initial rounds satisfies the nominal-degree estimate. -/
theorem round_count_bounds (m : ℕ) (Δ p γ : ℝ)
    (hp : 0 ≤ p) (hpγ : p ≤ γ / 8) (hγ : 0 ≤ γ) (hΔ : Δ < 2 * m) :
    Nat.floor (Δ - γ * m) ≤ 2 * m ∧
      ∀ s < Nat.floor (Δ - γ * m), γ * m / 2 ≤ (1 - p) * Δ - s := by
  constructor
  · apply Nat.floor_le_of_le
    push_cast
    have hnonneg := mul_nonneg hγ (Nat.cast_nonneg m)
    linarith
  · intro s hs
    have hs' : (s : ℝ) < Δ - γ * m := Nat.lt_of_lt_floor hs
    exact BipartitePackingBounds.nominal_degree_lower m s Δ p γ hp hpγ hγ hΔ.le hs'.le

end Overfull.BipartitePackingParameters
