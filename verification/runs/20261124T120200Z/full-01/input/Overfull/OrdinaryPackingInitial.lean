import Overfull.OrdinaryRandomReserveDegrees
import Overfull.OrdinaryPackingBounds
import Overfull.OrdinaryRobustStability

/-!
# Initial reserve for ordinary adaptive packing

The robust range of the original graph is reduced before sampling. A
single uniform order threshold then gives the actual sparse reserve,
its minimum degree, and the rounding and order estimates.
-/

namespace Overfull.OrdinaryPackingInitial

open Finset Classical SimpleGraph

theorem nominal_degree_lt_twice_order {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hm : 0 < Fintype.card V) (Δ ε : ℝ) (hε : ε ≤ 1)
    (hdegree : ∀ v, |(G.degree v : ℝ) - Δ| ≤ ε * Fintype.card V) :
    Δ < 2 * Fintype.card V := by
  obtain ⟨v⟩ := Fintype.card_pos_iff.mp hm
  have hd : (G.degree v : ℝ) < Fintype.card V := by
    exact_mod_cast G.degree_lt_card_verts v
  have he := mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg (Fintype.card V))
  have hb := (abs_le.mp (hdegree v)).1
  linarith

theorem exists_initial_reserve (α ν τ p σ ε μ : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hν : 0 < ν) (hτ : τ ≤ α / 8)
    (hp : 0 < p) (hp1 : p ≤ 1) (hσ : 0 < σ) (hστ : σ ≤ τ)
    (hε : 0 < ε) (hεp : ε ≤ p) (hεα : ε ≤ p * α / 8) (hμ : 0 < μ) :
    ∃ m₀ : ℕ, ∀ (V : Type*) [Fintype V] (G : SimpleGraph V) (Δ : ℝ),
      m₀ ≤ Fintype.card V → IsRobustExpander G ν τ →
      α * Fintype.card V ≤ Δ →
      (∀ v, |(G.degree v : ℝ) - Δ| ≤ ε * Fintype.card V) →
      ∃ R : SimpleGraph V,
        R ≤ G ∧ IsRobustExpander R (p * min ν (α * σ / 4) / 4) σ ∧
        (∀ v, |(R.degree v : ℝ) - p * Δ| ≤ 2 * ε * Fintype.card V) ∧
        (∀ v, (p * α / 2) * Fintype.card V ≤ (R.degree v : ℝ)) ∧
        Δ < 2 * Fintype.card V ∧ 0 < Fintype.card V ∧
        1 ≤ ε * Fintype.card V ∧ 2 ≤ μ * Fintype.card V ∧
        1 ≤ min (p * min ν (α * σ / 4) / 4) (p * α / 2) *
          Fintype.card V / 8 := by
  have hν' : 0 < min ν (α * σ / 4) := lt_min hν (by positivity)
  obtain ⟨m₁, hm₁⟩ := OrdinaryRandomReserve.exists_almost_regular_reserve
    p (min ν (α * σ / 4)) ε hp hp1 hν' hε hεp
  obtain ⟨m₂, hm₂⟩ := BipartitePackingBounds.exists_order_threshold
    μ (p * min ν (α * σ / 4) / 4) (p * α / 2) hμ (by positivity) (by positivity)
  obtain ⟨m₃, hm₃⟩ := exists_nat_gt (1 / ε)
  refine ⟨max m₁ (max m₂ m₃), ?_⟩
  intro V _ G Δ hm hrob hΔ hdegrees
  have hm₁' : m₁ ≤ Fintype.card V := (le_max_left _ _).trans hm
  have hmrest : max m₂ m₃ ≤ Fintype.card V := (le_max_right _ _).trans hm
  have hm₂' : m₂ ≤ Fintype.card V := (le_max_left _ _).trans hmrest
  have hm₃' : m₃ ≤ Fintype.card V := (le_max_right _ _).trans hmrest
  obtain ⟨hmpos, hround, hslack⟩ := hm₂ (Fintype.card V) hm₂'
  have hεα' : ε ≤ α / 2 := by
    have h := mul_le_mul_of_nonneg_right hp1 hα.le
    nlinarith
  have hminG : ∀ v, (α / 2) * Fintype.card V ≤ (G.degree v : ℝ) := by
    intro v
    have hl := (abs_le.mp (hdegrees v)).1
    have he := mul_le_mul_of_nonneg_right hεα' (Nat.cast_nonneg (Fintype.card V))
    linarith
  have hrange : IsRobustExpander G (min ν (α * σ / 4)) σ := by
    have heq : (α / 2) * σ / 2 = α * σ / 4 := by ring
    simpa only [heq] using robust_range_reduction G (α / 2) ν τ σ (by positivity)
      (by linarith) hν (by linarith) hσ hστ hminG hrob
  obtain ⟨ω, hRG, hRrob, hRdegrees⟩ :=
    hm₁ V G σ Δ hm₁' hrange hdegrees
  let R := OrdinaryRandomReserve.sampledGraph G ω
  have hdeg : ∀ v, |(R.degree v : ℝ) - p * Δ| ≤ 2 * ε * Fintype.card V := by
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using (hRdegrees v).le
  have hminR : ∀ v, (p * α / 2) * Fintype.card V ≤ (R.degree v : ℝ) := by
    intro v
    have hl := (abs_le.mp (hdeg v)).1
    have hΔ' := mul_le_mul_of_nonneg_left hΔ hp.le
    have he := mul_le_mul_of_nonneg_right hεα (Nat.cast_nonneg (Fintype.card V))
    nlinarith
  refine ⟨R, hRG, ?_, ?_, ?_,
    nominal_degree_lt_twice_order G hmpos Δ ε (hεp.trans hp1) hdegrees,
    hmpos, ?_, hround, hslack⟩
  · convert hRrob using 1
  · intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using hdeg v
  · intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using hminR v
  · have hmm : (m₃ : ℝ) ≤ Fintype.card V := by exact_mod_cast hm₃'
    have h := (div_lt_iff₀ hε).mp (hm₃.trans_le hmm)
    nlinarith

end Overfull.OrdinaryPackingInitial
