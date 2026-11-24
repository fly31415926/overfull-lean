import Overfull.OrdinaryFactorization.FirstHalfData
import Overfull.RobustStability
import Overfull.BipartitePackingReserve

/-!
# The actual crossing graph after completing the first colors

A repaired matching can delete a crossing edge only through its reserve
part. Thus the actual reserve-use bound controls the degree lost from the
crossing graph. The balanced sides convert the full-order loss bound into
the side-order normalization used by bipartite robust expansion.
-/

noncomputable section

namespace Overfull.OrdinaryFactorization

open Finset Classical SimpleGraph
open BipartitePackingAccounting PairedCut

variable {V E : Type*} [Fintype V] [Fintype E]
variable {G : Multigraph V E} {U : Finset V} {k : ℕ}
variable {α ν τ ξ p σ κ δ μ : ℝ}

/-- Original crossing core edges outside the actual completed matching union. -/
def residualCrossing (C : SmallCuts.Core G U)
    (D : FirstHalfData G U C k α ν τ ξ p σ κ δ μ) : SimpleGraph U :=
  crossingGraph C.graph D.geometry.left \
    edgeUnion (fun i => (D.matchings i).spanningCoe) univ

variable (C : SmallCuts.Core G U) (D : FirstHalfData G U C k α ν τ ξ p σ κ δ μ)

@[simp] theorem residualCrossing_adj (v w : U) :
    (residualCrossing C D).Adj v w ↔
      C.graph.Adj v w ∧ ((v ∈ D.geometry.left) ≠ (w ∈ D.geometry.left)) ∧
        ∀ i : Fin D.count, ¬ (D.matchings i).Adj v w := by
  change ((C.graph.Adj v w ∧ ((v ∈ D.geometry.left) ≠ (w ∈ D.geometry.left))) ∧
    ¬ ∃ i ∈ (univ : Finset (Fin D.count)), (D.matchings i).Adj v w) ↔ _
  simp only [mem_univ, true_and, not_exists, and_assoc]

theorem residualCrossing_le_crossing :
    residualCrossing C D ≤ crossingGraph C.graph D.geometry.left := sdiff_le

theorem residualCrossing_le : residualCrossing C D ≤ C.graph :=
  (residualCrossing_le_crossing C D).trans (crossingGraph_le _ _)

/-- A crossing edge of a completed matching must be one of its reserve
edges: its original color class is contained in the internal graph. -/
theorem crossing_deletions_le_used_reserve :
    crossingGraph C.graph D.geometry.left ⊓
        edgeUnion (fun i => (D.matchings i).spanningCoe) univ ≤
      edgeUnion (fun i => (D.matchings i).spanningCoe ⊓ D.geometry.reserve) univ := by
  intro v w h
  obtain ⟨i, hi, hmatching⟩ := h.2
  rcases D.support i hmatching with hcolor | hreserve
  · have hinternal := colorMatching_le C.graph D.geometry.internal D.geometry.internal_le
      D.internalColor i hcolor
    have hsame := ((D.geometry.internal_adj v w).mp hinternal).2.2
    exact (h.1.2 (propext hsame)).elim
  · exact ⟨i, hi, hmatching, hreserve⟩

theorem crossing_deleted_degree (v : U) :
    ((crossingGraph C.graph D.geometry.left ⊓
        edgeUnion (fun i => (D.matchings i).spanningCoe) univ).degree v : ℝ) ≤
      μ * U.card := by
  have hdegree := SimpleGraph.degree_le_of_le (v := v) (crossing_deletions_le_used_reserve C D)
  have hdegreeR :
      ((crossingGraph C.graph D.geometry.left ⊓
          edgeUnion (fun i => (D.matchings i).spanningCoe) univ).degree v : ℝ) ≤
        (edgeUnion (fun i => (D.matchings i).spanningCoe ⊓ D.geometry.reserve) univ).degree v := by
    exact_mod_cast hdegree
  exact hdegreeR.trans (D.reserve_used v)

/-- The residual and deleted crossing degrees add to the original degree. -/
theorem residualCrossing_degree_add_deleted (v : U) :
    (residualCrossing C D).degree v +
        (crossingGraph C.graph D.geometry.left ⊓
          edgeUnion (fun i => (D.matchings i).spanningCoe) univ).degree v =
      (crossingGraph C.graph D.geometry.left).degree v := by
  let M := edgeUnion (fun i => (D.matchings i).spanningCoe) univ
  let H := crossingGraph C.graph D.geometry.left
  have hremaining : (residualCrossing C D).neighborFinset v =
      H.neighborFinset v \ M.neighborFinset v := by
    ext w
    simp only [residualCrossing, M, H, SimpleGraph.mem_neighborFinset,
      SimpleGraph.sdiff_adj, Finset.mem_sdiff]
  have hdeleted : (H ⊓ M).neighborFinset v = H.neighborFinset v ∩ M.neighborFinset v := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.inf_adj, Finset.mem_inter]
  have h := Finset.card_sdiff_add_card_inter (H.neighborFinset v) (M.neighborFinset v)
  rw [← hremaining, ← hdeleted] at h
  simpa only [SimpleGraph.card_neighborFinset_eq_degree, H, M] using h

/-- The maximum loss is the actual recorded reserve use. -/
theorem residualCrossing_degree_loss (v : U) :
    ((crossingGraph C.graph D.geometry.left).degree v : ℝ) -
        (residualCrossing C D).degree v ≤ μ * U.card := by
  have hsum : ((residualCrossing C D).degree v : ℝ) +
      (crossingGraph C.graph D.geometry.left ⊓
        edgeUnion (fun i => (D.matchings i).spanningCoe) univ).degree v =
      (crossingGraph C.graph D.geometry.left).degree v := by
    exact_mod_cast residualCrossing_degree_add_deleted C D v
  linarith [crossing_deleted_degree C D v]

/-- Taking the same crossing graph again does not alter the residual. -/
theorem residualCrossing_crossing :
    crossingGraph (residualCrossing C D) D.geometry.left = residualCrossing C D := by
  ext v w
  change ((residualCrossing C D).Adj v w ∧
    ((v ∈ D.geometry.left) ≠ (w ∈ D.geometry.left))) ↔ (residualCrossing C D).Adj v w
  exact and_iff_left_of_imp (fun h => ((residualCrossing_adj C D v w).mp h).2.1)

/-- The two sides are an actual balanced partition of the original core. -/
theorem core_card_eq_twice_left_card : U.card = 2 * Fintype.card D.geometry.left := by
  have hsum := Finset.card_union_of_disjoint D.geometry.disjoint
  rw [D.geometry.cover, Finset.card_univ, Fintype.card_coe] at hsum
  have hbalance := D.geometry.left_card.trans D.geometry.right_card.symm
  rw [Fintype.card_coe]
  omega

theorem residualCutSides_le :
    cutSidesGraph (residualCrossing C D) D.geometry.left D.geometry.right ≤
      cutSidesGraph C.graph D.geometry.left D.geometry.right := by
  intro v w h
  exact ⟨residualCrossing_le C D h.1, h.2⟩

/-- A full-core loss of `μ * |U|` is a side-normalized loss of `2μ`. -/
theorem residualCutSides_degree_loss (b : D.geometry.right) :
    ((cutSidesGraph C.graph D.geometry.left D.geometry.right).degree (.inr b) : ℝ) -
        (cutSidesGraph (residualCrossing C D) D.geometry.left D.geometry.right).degree (.inr b) ≤
      (2 * μ) * Fintype.card D.geometry.left := by
  rw [cutSidesGraph_degree C.graph D.geometry.left D.geometry.right
      D.geometry.disjoint D.geometry.cover (.inr b),
    cutSidesGraph_degree (residualCrossing C D) D.geometry.left D.geometry.right
      D.geometry.disjoint D.geometry.cover (.inr b), residualCrossing_crossing C D]
  have h := residualCrossing_degree_loss C D b.val
  have hhalf : (U.card : ℝ) = 2 * Fintype.card D.geometry.left := by
    exact_mod_cast core_card_eq_twice_left_card C D
  rw [hhalf] at h
  simpa only [Sum.elim_inr, mul_assoc, mul_left_comm, mul_comm] using h

/-- Robust expansion of the actual remaining crossing graph. No residual
robustness assumption is supplied: it follows from the recorded reserve use. -/
theorem residualCrossing_robust (hμ : 0 ≤ μ) (hμξ : 4 * μ ≤ ξ) :
    IsBipartiteRobustExpander
      (cutSidesGraph (residualCrossing C D) D.geometry.left D.geometry.right)
      (ξ / 2) (4 * τ) := by
  have hbip : ∀ b b' : D.geometry.right,
      ¬ (cutSidesGraph C.graph D.geometry.left D.geometry.right).Adj (.inr b) (.inr b') := by
    intro b b' h
    have hb : b.val ∉ D.geometry.left := fun hleft =>
      Finset.disjoint_left.mp D.geometry.disjoint hleft b.property
    have hb' : b'.val ∉ D.geometry.left := fun hleft =>
      Finset.disjoint_left.mp D.geometry.disjoint hleft b'.property
    exact h.2 (propext (iff_of_false hb hb'))
  have hrob := IsBipartiteRobustExpander.after_edge_deletion_of_degree_bound
    (cutSidesGraph C.graph D.geometry.left D.geometry.right)
    (cutSidesGraph (residualCrossing C D) D.geometry.left D.geometry.right)
    D.geometry.crossing_robust (residualCutSides_le C D)
    (show 0 ≤ 2 * μ by linarith) hbip (residualCutSides_degree_loss C D)
  exact IsBipartiteRobustExpander.mono_parameter _ hrob (by linarith)

end Overfull.OrdinaryFactorization
