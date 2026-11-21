import Overfull.BipartitePackingParameters
import Overfull.BipartitePackingReserve

/-!
# Initial data for adaptive bipartite packing

A single order threshold provides the actual reserve, its minimum degree,
and the slack needed for the integer capacity and short-path estimates.
-/

namespace Overfull.BipartitePackingInitial

open Finset Classical SimpleGraph

/-- Simplicity and almost regularity bound the nominal degree by the side
order. This is the estimate limiting the number of packing rounds. -/
theorem nominal_degree_lt_twice_order {A B : Type*} [Fintype A] [Fintype B]
    (G : SimpleGraph (A ⊕ B))
    (hbip : G.IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr))
    (hbalance : Fintype.card A = Fintype.card B)
    (hm : 0 < Fintype.card A) (Δ ε : ℝ) (hε : ε < 1)
    (hdegree : ∀ v, |(G.degree v : ℝ) - Δ| ≤ ε * Fintype.card A) :
    Δ < 2 * Fintype.card A := by
  obtain ⟨a⟩ := Fintype.card_pos_iff.mp hm
  have hupper : G.degree (.inl a) ≤ Fintype.card A := by
    rw [← RandomReserve.crossingDegree_eq_degree G hbip]
    exact RandomReserve.crossingDegree_le G hbalance (.inl a)
  have hupperR : (G.degree (.inl a) : ℝ) ≤ Fintype.card A := by exact_mod_cast hupper
  have hlower := (abs_le.mp (hdegree (.inl a))).1
  have hmR : (0 : ℝ) < Fintype.card A := by exact_mod_cast hm
  have hεm := mul_lt_mul_of_pos_right hε hmR
  linarith

/-- The threshold and sampling choices depend only on fixed real
parameters, before any graph or forbidden set is supplied. -/
theorem exists_initial_reserve (p ν α ε μ : ℝ)
    (hp : 0 < p) (hp1 : p ≤ 1) (hν : 0 < ν) (hα : 0 < α)
    (hε : 0 < ε) (hεp : ε ≤ p) (hε1 : ε < 1)
    (hεα : ε ≤ p * α / 8) (hμ : 0 < μ) :
    ∃ m₀ : ℕ, ∀ (A B : Type*) [Fintype A] [Fintype B]
      (G : SimpleGraph (A ⊕ B)) (τ Δ : ℝ),
      G.IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr) →
      Fintype.card A = Fintype.card B → m₀ ≤ Fintype.card A →
      IsBipartiteRobustExpander G ν τ → α * Fintype.card A ≤ Δ →
      (∀ v, |(G.degree v : ℝ) - Δ| ≤ ε * Fintype.card A) →
      ∃ R : SimpleGraph (A ⊕ B),
        R ≤ G ∧ R.IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr) ∧
        IsBipartiteRobustExpander R (p * ν / 2) τ ∧
        (∀ v, |(R.degree v : ℝ) - p * Δ| ≤ 2 * ε * Fintype.card A) ∧
        (∀ v, (p * α / 2) * Fintype.card A ≤ (R.degree v : ℝ)) ∧
        Δ < 2 * Fintype.card A ∧ 0 < Fintype.card A ∧
        2 ≤ μ * Fintype.card A ∧
        1 ≤ min (p * ν / 2) (p * α / 2) * Fintype.card A / 8 := by
  obtain ⟨m₁, hm₁⟩ := RandomReserve.exists_almost_regular_reserve p ν ε hp hp1 hν hε hεp
  obtain ⟨m₂, hm₂⟩ := BipartitePackingBounds.exists_order_threshold μ (p * ν / 2)
    (p * α / 2) hμ (by positivity) (by positivity)
  refine ⟨max m₁ m₂, ?_⟩
  intro A B _ _ G τ Δ hbip hbalance hm hG hΔ hdegrees
  have hm₁' : m₁ ≤ Fintype.card A := (le_max_left _ _).trans hm
  have hm₂' : m₂ ≤ Fintype.card A := (le_max_right _ _).trans hm
  obtain ⟨hpositive, hround, hslack⟩ := hm₂ (Fintype.card A) hm₂'
  obtain ⟨ω, hRG, hbipR, hrobR, hdegR⟩ :=
    hm₁ A B G τ Δ hbip hbalance hm₁' hG hdegrees
  have hdeg : ∀ v, |((RandomReserve.sampledGraph G ω).degree v : ℝ) - p * Δ| ≤
      2 * ε * Fintype.card A := fun v => (hdegR v).le
  refine ⟨RandomReserve.sampledGraph G ω, hRG, hbipR, ?_, ?_, ?_,
    nominal_degree_lt_twice_order G hbip hbalance hpositive Δ ε hε1 hdegrees,
    hpositive, hround, hslack⟩
  · convert hrobR using 1
  · intro v
    convert hdeg v using 1
    apply congrArg (fun z : ℕ => |(z : ℝ) - p * Δ|)
    simp only [← SimpleGraph.card_neighborSet_eq_degree]
    congr
    exact Subsingleton.elim _ _
  · intro v
    convert BipartitePackingParameters.reserve_minimum_degree (Fintype.card A)
      α p ε Δ _ hp.le hεα hΔ (hdeg v) using 1
    apply congrArg (Nat.cast : ℕ → ℝ)
    simp only [← SimpleGraph.card_neighborSet_eq_degree]
    congr
    exact Subsingleton.elim _ _

end Overfull.BipartitePackingInitial
