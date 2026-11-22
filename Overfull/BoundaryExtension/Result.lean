import Overfull.BoundaryExtension.ContractionCuts
import Overfull.BoundaryExtension.Reassembly
import Overfull.BoundaryExtension.Triples

/-!
# The exact remaining factorization problem for a boundary coloring

This result records an actual deletion and an actual apex contraction,
together with a checked reconstruction from any coloring of that precise
contracted graph. It is a reduction, not a factorization assertion.
-/

namespace Overfull.BoundaryExtension

open Finset Classical

variable {V E : Type*} [Fintype E]

/-- Every part of the boundary-extension construction except the final
factorization. The missing coloring is supplied only to the reconstruction;
its existence is not a field or a hypothesis of the reduction theorem. -/
structure BoundaryReduction (G : Multigraph V E) (U : Finset V)
    (d : ℕ) (a γ θ σ : ℝ) (c : BoundaryColoring G U d) where
  completed : Fin c.tripleColors.card → Finset E
  deleted : Finset E
  deleted_eq : deleted = (univ : Finset (Fin c.tripleColors.card)).biUnion completed
  completed_matching : ∀ j, G.IsMatching (completed j)
  completed_disjoint : Pairwise (fun i j => Disjoint (completed i) (completed j))
  completed_covers : ∀ j (v : U), ∃! e, e ∈ completed j ∧ v.val ∈ G.edge e
  completed_retained : ∀ j e, e ∈ completed j → ∃ v : U, v.val ∈ G.edge e
  completed_boundary : ∀ (e : G.cutEdges U) j,
    e.val ∈ completed j ↔ c.color e = c.tripleLabel j
  residual_degree : ∀ v : U,
    (G.restrictEdges deletedᶜ).degree v.val = d - c.tripleColors.card
  residual_boundary : (G.restrictEdges deletedᶜ).cutSize U = d - c.tripleColors.card
  retained_density : γ * U.card ≤ (d - c.tripleColors.card : ℕ)
  core : SmallCuts.Core (G.restrictEdges deletedᶜ) U
  core_degree : ∀ v,
    ((d - c.tripleColors.card : ℕ) : ℝ) - a ≤ core.graph.degree v
  core_robust : IsRobustExpander core.graph θ σ
  contracted_regular : ∀ v : Vertex U,
    (contract (G.restrictEdges deletedᶜ) U).degree v = d - c.tripleColors.card
  contracted_even : Even (Fintype.card (Vertex U))
  contracted_no_overfull : ∀ X : Finset (Vertex U),
    ¬ (contract (G.restrictEdges deletedᶜ) U).IsOverfull (d - c.tripleColors.card) X
  extend : (contract (G.restrictEdges deletedᶜ) U).EdgeColoring
      (d - c.tripleColors.card) →
    ∃ full : (retainedGraph G U).EdgeColoring d,
      ∀ e : G.cutEdges U, full.color (boundaryLift G U e) = c.color e

end Overfull.BoundaryExtension

