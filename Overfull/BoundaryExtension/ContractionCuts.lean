import Overfull.BoundaryExtension.Contraction
import Overfull.OneCore.Cuts

/-!
# No overfull set after contracting an odd core's exterior

The contraction is the actual edge-copy preserving graph from
`BoundaryExtension.Contraction`.  Its regularity, even order, embedded
robust core, and one-vertex complement are proved from the original data.
The small-cut theorem then certifies its odd cuts and excludes overfull
sets, without any factorization input.
-/

namespace Overfull.BoundaryExtension

open Finset Classical

set_option maxHeartbeats 800000 in
/-- Uniform no-overfullness for the actual apex contraction.  The order
threshold precedes the host, core, and degree.  Boundary size and all core
degrees are exact counts of original edge copies. -/
theorem exists_contraction_cut_threshold (α ν τ : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hν : 0 < ν)
    (hντ : ν ≤ τ) (hτ : τ ≤ α / 20) :
    ∃ m₀ : ℕ, ∀ (V E : Type*) [Fintype E]
      (G : Multigraph V E) (U : Finset V) (C : SmallCuts.Core G U) (d : ℕ) (a : ℝ),
      m₀ ≤ U.card → Odd U.card →
      (∀ u : U, G.degree u.val = d) → G.cutSize U = d →
      α * U.card ≤ d → 0 ≤ a → a ≤ α * U.card / 20 →
      IsRobustExpander C.graph ν τ →
      (∀ u, (d : ℝ) - a ≤ C.graph.degree u) →
      (∀ X : Finset (Vertex U), X.card % 2 = 1 → d ≤ (contract G U).cutSize X) ∧
      (∀ X : Finset (Vertex U), ¬ (contract G U).IsOverfull d X) := by
  obtain ⟨m₀, hcut⟩ := OneCore.robust_one_exterior_no_overfull α ν τ hα hα1 hν hντ hτ
  refine ⟨m₀, ?_⟩
  intro V E _ G U C d a hm hodd hdegrees hboundary hd ha haSmall hrob hcore
  have heven : Fintype.card (Vertex U) % 2 = 0 := by
    exact Nat.even_iff.mp (even_contracted_order U hodd)
  have hreg := contract_regular G U d hdegrees hboundary
  have hrob' := contractCore_robust C ν τ hrob
  have hdegree : ∀ u : coreVertices U, (d : ℝ) - a ≤ (contractCore C).graph.degree u := by
    intro u
    rw [contractCore_degree]
    exact hcore ((coreEquiv U).symm u)
  refine hcut (Vertex U) (RetainedEdge G U) (contract G U) (coreVertices U)
    (contractCore C) d a (by simpa only [coreVertices_card] using hm)
    heven ?_ hreg (by simpa only [coreVertices_card] using hd) ha
    (by simpa only [coreVertices_card] using haSmall) ?_ ?_
  · letI : DecidableEq (Vertex U) := Classical.decEq _
    have hsub : (coreVertices U)ᶜ ⊆ {Sum.inr ()} := by
      intro v hv
      rcases v with u | u
      · exact ((Finset.mem_compl.mp hv) (inl_mem_coreVertices U u)).elim
      · cases u
        simp
    simpa only [Finset.card_singleton] using Finset.card_le_card hsub
  · convert hrob' using 1
  · intro u
    convert hdegree u using 1

end Overfull.BoundaryExtension
