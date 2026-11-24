import Overfull.OrdinaryFactorization.ResidualCore
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-!
# Explicit bipartite interface of the actual residual core

The two recorded sides partition the original core and have equal size.
The residual crossing core is bipartite in those actual sets, and its
side-indexed graph is isomorphic to it. Decreasing the robust parameter
gives the positive parameter at most the range required by a later
bipartite-core factorization theorem. No residual factorization is asserted.
-/

noncomputable section

namespace Overfull.OrdinaryFactorization

open Finset Classical SmallCuts SimpleGraph PairedCut

/-- The clipped robust parameter is positive and at most its range. -/
theorem residual_robust_parameters (ξ τ : ℝ) (hξ : 0 < ξ) (hτ : 0 < τ) :
    0 < min (ξ / 2) (4 * τ) ∧ min (ξ / 2) (4 * τ) ≤ 4 * τ := by
  exact ⟨lt_min (by positivity) (by positivity), min_le_right _ _⟩

variable {V E : Type*} [Fintype V] [Fintype E]
variable {G : Multigraph V E} {U : Finset V} {k : ℕ}
variable {α ν τ ξ p σ κ δ μ : ℝ}
variable (C : Core G U) (D : FirstHalfData G U C k α ν τ ξ p σ κ δ μ)

/-- The actual residual core is bipartite in the recorded original sides. -/
theorem residualCrossingCore_bipartite :
    (residualCrossingCore C D).graph.IsBipartiteWith
      (D.geometry.left : Set U) (D.geometry.right : Set U) := by
  have hright (v : U) (hv : v ∉ D.geometry.left) : v ∈ D.geometry.right := by
    have hcover : v ∈ D.geometry.left ∪ D.geometry.right := by
      rw [D.geometry.cover]
      exact mem_univ v
    exact (mem_union.mp hcover).resolve_left hv
  refine ⟨Finset.disjoint_coe.mpr D.geometry.disjoint, ?_⟩
  intro v w hvw
  have hcross := ((residualCrossing_adj C D v w).mp hvw).2.1
  by_cases hv : v ∈ D.geometry.left
  · refine Or.inl ⟨hv, hright w ?_⟩
    intro hw
    exact hcross (propext (iff_of_true hv hw))
  · refine Or.inr ⟨hright v hv, ?_⟩
    by_contra hw
    exact hcross (propext (iff_of_false hv hw))

/-- The sides cover every core vertex, including any isolated vertex. -/
theorem residualCrossingCore_sides_cover :
    (D.geometry.left : Set U) ∪ (D.geometry.right : Set U) = Set.univ := by
  rw [← Finset.coe_union, D.geometry.cover, Finset.coe_univ]

theorem residualCrossingCore_side_card : D.geometry.left.card = D.geometry.right.card :=
  D.geometry.left_card.trans D.geometry.right_card.symm

/-- The graph with sides as summands has exactly the intended bipartition. -/
theorem residualCutSides_bipartite :
    (cutSidesGraph (residualCrossingCore C D).graph D.geometry.left D.geometry.right).IsBipartiteWith
      (Set.range Sum.inl) (Set.range Sum.inr) := by
  refine ⟨?_, ?_⟩
  · apply Set.disjoint_left.mpr
    rintro v ⟨a, rfl⟩ ⟨b, hb⟩
    cases hb
  · intro x y hxy
    rcases x with a | b <;> rcases y with a' | b'
    · simp [cutSidesGraph, crossingGraph, a.property, a'.property] at hxy
    · exact Or.inl ⟨⟨a, rfl⟩, ⟨b', rfl⟩⟩
    · exact Or.inr ⟨⟨b, rfl⟩, ⟨a', rfl⟩⟩
    · have hb : b.val ∉ D.geometry.left := fun h =>
        Finset.disjoint_left.mp D.geometry.disjoint h b.property
      have hb' : b'.val ∉ D.geometry.left := fun h =>
        Finset.disjoint_left.mp D.geometry.disjoint h b'.property
      simp [cutSidesGraph, crossingGraph, hb, hb'] at hxy

theorem residualCutSides_balance :
    Fintype.card D.geometry.left = Fintype.card D.geometry.right := by
  simpa only [Fintype.card_coe] using residualCrossingCore_side_card C D

/-- Reindexing by the side sum preserves the entire actual residual core. -/
def residualCutSidesIso :
    cutSidesGraph (residualCrossingCore C D).graph D.geometry.left D.geometry.right ≃g
      (residualCrossingCore C D).graph := by
  simpa only [residualCrossingCore_graph, residualCrossing_crossing C D] using
    (cutSidesIso (residualCrossing C D) D.geometry.left D.geometry.right
      D.geometry.disjoint D.geometry.cover)

/-- The actual residual has a robust parameter no larger than its range.
The clipping is chosen before any subsequent tolerance for factorization. -/
theorem residualCutSides_robust_admissible (hμ : 0 ≤ μ) (hμξ : 4 * μ ≤ ξ) :
    IsBipartiteRobustExpander
      (cutSidesGraph (residualCrossingCore C D).graph D.geometry.left D.geometry.right)
      (min (ξ / 2) (4 * τ)) (4 * τ) := by
  exact IsBipartiteRobustExpander.mono_parameter _
    (residualCrossing_robust C D hμ hμξ) (min_le_left _ _)

end Overfull.OrdinaryFactorization
