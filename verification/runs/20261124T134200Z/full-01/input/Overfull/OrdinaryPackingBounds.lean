import Overfull.BipartitePackingBounds

/-!
# Reserve-load bounds for ordinary matching packing

The Tutte--Berge deficiency estimate gives the exact recurrence used in
Lemma 2.20. The order and path-budget estimates are independent of the
graph and of the adaptive sequence.
-/

namespace Overfull.OrdinaryPackingBounds

theorem geometric_factor_bound (m n : ℕ) (ℓ γ : ℝ)
    (hm : 0 < m) (hℓ : 0 ≤ ℓ) (hγ : 0 < γ) (hn : n ≤ 2 * m) :
    (1 + 60 * ℓ / (γ * m)) ^ n ≤ Real.exp (120 * ℓ / γ) := by
  have h := BipartitePackingBounds.geometric_factor_bound m n (15 * ℓ) γ
    hm (by positivity) hγ hn
  have h₁ : 4 * (15 * ℓ) / (γ * m) = 60 * ℓ / (γ * m) := by ring
  have h₂ : 8 * (15 * ℓ) / γ = 120 * ℓ / γ := by ring
  simpa only [h₁, h₂] using h

theorem reserve_step_bound (m h : ℕ) (ℓ γ ε t t' : ℝ)
    (hm : 0 < m) (hℓ : 0 ≤ ℓ) (hγ : 0 < γ)
    (hdef : (h : ℝ) ≤ (30 / γ) * (ε * m + t / m))
    (huse : t' ≤ t + 2 * ℓ * h) :
    t' ≤ (1 + 60 * ℓ / (γ * m)) * t + 60 * ℓ * ε * m / γ := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  calc
    t' ≤ t + 2 * ℓ * h := huse
    _ ≤ t + 2 * ℓ * ((30 / γ) * (ε * m + t / m)) :=
      add_le_add_left (mul_le_mul_of_nonneg_left hdef (by positivity)) t
    _ = _ := by field_simp; ring

/-- The manuscript's uniform total reserve-load bound. -/
theorem reserve_recurrence_bound (t : ℕ → ℝ) (m n : ℕ) (ℓ γ ε : ℝ)
    (hm : 0 < m) (hℓ : 0 ≤ ℓ) (hγ : 0 < γ) (hε : 0 ≤ ε)
    (hn : n ≤ 2 * m) (hzero : t 0 ≤ 0)
    (hstep : ∀ s < n, t (s + 1) ≤
      (1 + 60 * ℓ / (γ * m)) * t s + 60 * ℓ * ε * m / γ) :
    t n ≤ (Real.exp (120 * ℓ / γ) - 1) * ε * (m : ℝ)^2 := by
  have hstep' : ∀ s < n, t (s + 1) ≤
      (1 + 4 * (15 * ℓ) / (γ * m)) * t s +
        32 * (15 * ℓ) * (ε / 8) * m / γ := by
    intro s hs
    convert hstep s hs using 1
    ring
  have h := BipartitePackingBounds.reserve_recurrence_bound t m n (15 * ℓ) γ (ε / 8)
    hm (by positivity) hγ (by positivity) hn hzero hstep'
  have heq : 8 * (15 * ℓ) / γ = 120 * ℓ / γ := by ring
  rw [heq] at h
  convert h using 1
  ring

theorem deficiency_with_total_bound (m h : ℕ) (γ ε c₀ t : ℝ)
    (hm : 0 < m) (hγ : 0 < γ)
    (hdef : (h : ℝ) ≤ (30 / γ) * (ε * m + t / m))
    (htotal : t ≤ c₀ * ε * (m : ℝ)^2) :
    (h : ℝ) ≤ 30 * (1 + c₀) * ε * m / γ := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hdiv : t / m ≤ c₀ * ε * m := by
    apply (div_le_iff₀ hmR).mpr
    nlinarith
  calc
    (h : ℝ) ≤ (30 / γ) * (ε * m + t / m) := hdef
    _ ≤ (30 / γ) * (ε * m + c₀ * ε * m) :=
      mul_le_mul_of_nonneg_left (add_le_add_left hdiv _) (by positivity)
    _ = _ := by ring

/-- Transfer the ambient-order budget to the actual side order, retaining
the additive slack required by the augmenting-path theorem. -/
theorem path_budget_from_ambient (m m' : ℕ) (q η : ℝ)
    (hη : 0 ≤ η) (hside : m ≤ 4 * m')
    (hlarge : 16 ≤ η * m) (hbudget : q ≤ η * m / 16) :
    q ≤ η * m' / 2 - 1 := by
  have hsideR : (m : ℝ) ≤ 4 * m' := by exact_mod_cast hside
  have hmul := mul_le_mul_of_nonneg_left hsideR hη
  nlinarith

/-- The actual saturated-set and matching-deficiency estimates imply the
completion budget, once the error constant is sufficiently small. -/
theorem completion_budget (m m' z h : ℕ) (ℓ γ ε c₀ μ η : ℝ)
    (hℓ : 0 ≤ ℓ) (hη : 0 ≤ η)
    (hside : m ≤ 4 * m') (hlarge : 16 ≤ η * m)
    (hZ : (z : ℝ) ≤ 2 * c₀ * ε * m / μ)
    (hh : (h : ℝ) ≤ 30 * (1 + c₀) * ε * m / γ)
    (hsmall : (4 * c₀ / μ + 30 * ℓ * (1 + c₀) / γ) * ε ≤ η / 16) :
    2 * (z : ℝ) + ℓ * h ≤ η * m' / 2 - 1 := by
  apply path_budget_from_ambient m m' _ η hη hside hlarge
  have htimes := mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg m)
  calc
    2 * (z : ℝ) + ℓ * h ≤
        2 * (2 * c₀ * ε * m / μ) + ℓ * (30 * (1 + c₀) * ε * m / γ) :=
      add_le_add (mul_le_mul_of_nonneg_left hZ (by norm_num))
        (mul_le_mul_of_nonneg_left hh hℓ)
    _ = ((4 * c₀ / μ + 30 * ℓ * (1 + c₀) / γ) * ε) * m := by ring
    _ ≤ _ := by simpa only [div_mul_eq_mul_div] using htimes

end Overfull.OrdinaryPackingBounds
