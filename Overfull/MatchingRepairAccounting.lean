import Overfull.BipartitePackingAccounting

/-!
# Released matching edges and reserve use

Extending a matching by edges from a reserve releases at most as many
incident old edges as it uses incident reserve edges. The same bound
holds for the actual unions of edge-disjoint matching families.
-/

namespace Overfull.MatchingRepairAccounting

open Finset Classical SimpleGraph
open scoped BigOperators
open BipartitePackingAccounting

variable {V I : Type*} [Fintype V]

theorem released_degree_le (G R : SimpleGraph V) (M N : G.Subgraph)
    (hM : M.IsMatching) (hN : N.IsMatching) (hverts : M.verts ⊆ N.verts)
    (hedges : N.spanningCoe ≤ M.spanningCoe ⊔ R) (v : V) :
    (M.spanningCoe \ N.spanningCoe).degree v ≤ (N.spanningCoe ⊓ R).degree v := by
  have hdegrees : M.spanningCoe.degree v ≤ N.spanningCoe.degree v := by
    rw [matching_degree G M hM v, matching_degree G N hN v]
    by_cases hv : v ∈ M.verts
    · simp only [if_pos hv, if_pos (hverts hv), le_refl]
    · simp only [if_neg hv, Nat.zero_le]
  have hforward := degree_sdiff_add_degree_inf M.spanningCoe N.spanningCoe v
  have hback := degree_sdiff_add_degree_inf N.spanningCoe M.spanningCoe v
  have hinter : (N.spanningCoe ⊓ M.spanningCoe).degree v =
      (M.spanningCoe ⊓ N.spanningCoe).degree v := by
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
    rw [inf_comm]
  have hdiff : N.spanningCoe \ M.spanningCoe ≤ N.spanningCoe ⊓ R := by
    intro x y hxy
    refine ⟨hxy.1, ?_⟩
    exact (hedges hxy.1).resolve_left hxy.2
  have hnew := (N.spanningCoe \ M.spanningCoe).degree_le_of_le hdiff (v := v)
  omega

theorem released_union_degree_le (G R : SimpleGraph V)
    (M N : I → G.Subgraph) (T : Finset I)
    (hM : ∀ i ∈ T, (M i).IsMatching) (hN : ∀ i ∈ T, (N i).IsMatching)
    (hverts : ∀ i ∈ T, (M i).verts ⊆ (N i).verts)
    (hedges : ∀ i ∈ T, (N i).spanningCoe ≤ (M i).spanningCoe ⊔ R)
    (hMdisj : ∀ i ∈ T, ∀ j ∈ T, i ≠ j →
      Disjoint (M i).spanningCoe (M j).spanningCoe)
    (hNdisj : ∀ i ∈ T, ∀ j ∈ T, i ≠ j →
      Disjoint (N i).spanningCoe (N j).spanningCoe)
    (v : V) :
    (edgeUnion (fun i => (M i).spanningCoe \ (N i).spanningCoe) T).degree v ≤
      (edgeUnion (fun i => (N i).spanningCoe ⊓ R) T).degree v := by
  rw [edgeUnion_degree_eq_sum _ T (by
      intro i hi j hj hij
      exact (hMdisj i hi j hj hij).mono sdiff_le sdiff_le),
    edgeUnion_degree_eq_sum _ T (by
      intro i hi j hj hij
      exact (hNdisj i hi j hj hij).mono inf_le_left inf_le_left)]
  apply Finset.sum_le_sum
  intro i hi
  simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using
    released_degree_le G R (M i) (N i) (hM i hi) (hN i hi)
      (hverts i hi) (hedges i hi) v

end Overfull.MatchingRepairAccounting
