import Overfull.BipartitePackingAccounting
import Overfull.RobustStability
import Overfull.BipartiteRange
import Overfull.RandomReserveDegrees

/-!
# The unused bipartite reserve

The reserve degree loss is the load defined by the actual edges already
used. A bound on that load preserves expansion both in the unused reserve
and in the entire remaining graph.
-/

namespace Overfull

open Finset Classical SimpleGraph
open scoped BigOperators

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

omit [DecidableEq B] in
theorem IsBipartiteRobustExpander.mono_parameter
    (G : SimpleGraph (A ⊕ B)) [DecidableRel G.Adj] {ν μ τ : ℝ}
    (hG : IsBipartiteRobustExpander G ν τ) (hμν : μ ≤ ν) :
    IsBipartiteRobustExpander G μ τ := by
  intro S hS hS'
  have h := hG S hS hS'
  have hc : ((bipartiteRobustNeighbors G ν S).card : ℝ) ≤
      (bipartiteRobustNeighbors G μ S).card := by
    exact_mod_cast Finset.card_le_card
      (bipartiteRobustNeighbors_mono_parameter G ν μ hμν S)
  have hm := mul_le_mul_of_nonneg_right hμν (Nat.cast_nonneg (Fintype.card A))
  linarith

namespace BipartitePackingReserve

open BipartitePackingAccounting

variable {I : Type*}
variable (G R : SimpleGraph (A ⊕ B))
  (M : I → G.Subgraph) (T : Finset I)

/-- Removing previously used edges loses exactly the recorded reserve load,
so the usual edge-deletion lemma applies to the actual residual graph. -/
theorem unused_reserve_robust (θ τ μ : ℝ)
    (hR : IsBipartiteRobustExpander R θ τ)
    (hbip : R.IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr))
    (hμ : 0 ≤ μ)
    (hload : ∀ v, (reserveLoad G R M T v : ℝ) ≤ μ * Fintype.card A) :
    IsBipartiteRobustExpander
      (R \ edgeUnion (fun i => (M i).spanningCoe) T) (θ - μ) τ := by
  apply IsBipartiteRobustExpander.after_edge_deletion_of_degree_bound R
    (R \ edgeUnion (fun i => (M i).spanningCoe) T) hR sdiff_le hμ
  · intro b b' h
    simpa using hbip.mem_of_adj h
  · intro b
    have h := unused_reserve_degree G R M T (Sum.inr b)
    have h' : ((R \ edgeUnion (fun i => (M i).spanningCoe) T).degree (.inr b) : ℝ) +
        reserveLoad G R M T (.inr b) = R.degree (.inr b) := by exact_mod_cast h
    linarith [hload (.inr b)]

/-- A half-parameter reserve survives all previously chosen matchings. -/
theorem unused_reserve_robust_half (θ τ μ : ℝ)
    (hR : IsBipartiteRobustExpander R θ τ)
    (hbip : R.IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr))
    (hμ : 0 ≤ μ) (hsmall : μ ≤ θ / 2)
    (hload : ∀ v, (reserveLoad G R M T v : ℝ) ≤ μ * Fintype.card A) :
    IsBipartiteRobustExpander
      (R \ edgeUnion (fun i => (M i).spanningCoe) T) (θ / 2) τ := by
  exact (unused_reserve_robust G R M T θ τ μ hR hbip hμ hload).mono_parameter _ (by linarith)

/-- The whole graph left after the previous matchings contains the unused
reserve and therefore has the same guaranteed robust expansion. -/
theorem residual_graph_robust_half (θ τ μ : ℝ) (hRG : R ≤ G)
    (hR : IsBipartiteRobustExpander R θ τ)
    (hbip : R.IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr))
    (hμ : 0 ≤ μ) (hsmall : μ ≤ θ / 2)
    (hload : ∀ v, (reserveLoad G R M T v : ℝ) ≤ μ * Fintype.card A) :
    IsBipartiteRobustExpander
      (G \ edgeUnion (fun i => (M i).spanningCoe) T) (θ / 2) τ := by
  have hsub : R \ edgeUnion (fun i => (M i).spanningCoe) T ≤
      G \ edgeUnion (fun i => (M i).spanningCoe) T := by
    intro v w hvw
    exact ⟨hRG hvw.1, hvw.2⟩
  exact (unused_reserve_robust_half G R M T θ τ μ hR hbip hμ hsmall hload).mono_graph
    _ _ hsub

/-- An integer per-vertex capacity supplies the real degree loss bound. -/
theorem residual_graph_robust_of_capacity (θ τ μ : ℝ) (hRG : R ≤ G)
    (hR : IsBipartiteRobustExpander R θ τ)
    (hbip : R.IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr))
    (hμ : 0 ≤ μ) (hsmall : μ ≤ θ / 2)
    (hload : ∀ v, reserveLoad G R M T v ≤ Nat.floor (μ * Fintype.card A)) :
    IsBipartiteRobustExpander
      (G \ edgeUnion (fun i => (M i).spanningCoe) T) (θ / 2) τ := by
  apply residual_graph_robust_half G R M T θ τ μ hRG hR hbip hμ hsmall
  intro v
  have h := hload v
  exact (by exact_mod_cast h : (reserveLoad G R M T v : ℝ) ≤
    Nat.floor (μ * Fintype.card A)).trans (Nat.floor_le (by positivity))

end BipartitePackingReserve
end Overfull
