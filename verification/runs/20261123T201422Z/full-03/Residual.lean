import Overfull.AssignedParts.NativePatternConstruction
import Overfull.OneCore.Cuts

/-!
# Exact residuals of disjoint original-copy matching families

Every deleted and surviving edge is an original multigraph copy. The
accounting applies to arbitrary finite copy pools, including cuts and
exceptional parallel bundles. Regularity follows from actual disjoint
perfect matchings, independently of the later odd-cut safety argument.
-/

noncomputable section

namespace Overfull.NativeReserve

open Finset Classical
open scoped BigOperators

variable {V E J : Type*}

/-- All original copies used by the selected members of a family. -/
def removedCopies (N : J → Finset E) (T : Finset J) : Finset E := T.biUnion N

/-- Delete exactly the supplied actual copy sets. -/
def residualGraph (G : Multigraph V E) (N : J → Finset E) (T : Finset J) :=
  MultigraphMatchingProbability.remainingGraph G (removedCopies N T)

@[simp] theorem mem_removedCopies (N : J → Finset E) (T : Finset J) (e : E) :
    e ∈ removedCopies N T ↔ ∃ j ∈ T, e ∈ N j := by
  simp [removedCopies]

theorem removed_pool_card (N : J → Finset E) (T : Finset J)
    (hdisj : (T : Set J).Pairwise (fun i j => Disjoint (N i) (N j))) (A : Finset E) :
    (removedCopies N T ∩ A).card = ∑ j ∈ T, (N j ∩ A).card := by
  have hset : removedCopies N T ∩ A = T.biUnion (fun j => N j ∩ A) := by
    ext e
    simp only [mem_inter, mem_removedCopies, mem_biUnion]
    constructor
    · rintro ⟨⟨j, hj, he⟩, heA⟩
      exact ⟨j, hj, he, heA⟩
    · rintro ⟨j, hj, he, heA⟩
      exact ⟨⟨j, hj, he⟩, heA⟩
  rw [hset, card_biUnion]
  intro i hi j hj hij
  exact (hdisj hi hj hij).mono inter_subset_left inter_subset_left

theorem residual_pool_accounting (N : J → Finset E) (T : Finset J)
    (hdisj : (T : Set J).Pairwise (fun i j => Disjoint (N i) (N j))) (A : Finset E) :
    (A \ removedCopies N T).card + ∑ j ∈ T, (N j ∩ A).card = A.card := by
  rw [← removed_pool_card N T hdisj, inter_comm (removedCopies N T) A]
  exact card_sdiff_add_card_inter A (removedCopies N T)

variable (G : Multigraph V E)

theorem removed_degreeOn (N : J → Finset E) (T : Finset J)
    (hdisj : (T : Set J).Pairwise (fun i j => Disjoint (N i) (N j))) (v : V) :
    G.degreeOn (removedCopies N T) v = ∑ j ∈ T, G.degreeOn (N j) v := by
  have hset : (removedCopies N T).filter (fun e => v ∈ G.edge e) =
      T.biUnion (fun j => (N j).filter (fun e => v ∈ G.edge e)) := by
    ext e
    simp only [mem_filter, mem_removedCopies, mem_biUnion]
    constructor
    · rintro ⟨⟨j, hj, he⟩, hv⟩
      exact ⟨j, hj, he, hv⟩
    · rintro ⟨j, hj, he, hv⟩
      exact ⟨⟨j, hj, he⟩, hv⟩
  unfold Multigraph.degreeOn
  rw [hset, card_biUnion]
  intro i hi j hj hij
  exact (hdisj hi hj hij).mono (filter_subset _ _) (filter_subset _ _)

variable [Fintype E]

theorem cutOn_eq_inter (F : Finset E) (X : Finset V) :
    G.cutOn F X = F ∩ G.cutEdges X := by
  ext e
  simp

theorem residual_cutSize (N : J → Finset E) (T : Finset J) (X : Finset V) :
    (residualGraph G N T).cutSize X =
      (G.cutEdges X \ removedCopies N T).card := by
  rw [residualGraph, ← MultigraphMatchingProbability.remaining_cut_count]
  unfold MultigraphMatchingProbability.cutCount
  congr 1
  ext e
  simp [MultigraphMatchingProbability.cutEdges,
    MultigraphMatchingProbability.remainingEdges, Lovasz.BMatch.cut, and_comm]

theorem residual_cut_accounting (N : J → Finset E) (T : Finset J)
    (hdisj : (T : Set J).Pairwise (fun i j => Disjoint (N i) (N j))) (X : Finset V) :
    (residualGraph G N T).cutSize X +
      ∑ j ∈ T, (G.cutOn (N j) X).card = G.cutSize X := by
  simp_rw [cutOn_eq_inter]
  rw [residual_cutSize]
  exact residual_pool_accounting N T hdisj (G.cutEdges X)

theorem residual_degree_accounting (N : J → Finset E) (T : Finset J)
    (hdisj : (T : Set J).Pairwise (fun i j => Disjoint (N i) (N j)))
    (hperfect : ∀ j ∈ T, G.IsPerfectMatching (N j)) (v : V) :
    (residualGraph G N T).degree v + T.card = G.degree v := by
  have h := MultigraphMatchingProbability.remaining_degree_add_selected
    (G := G) (removedCopies N T) v
  change (residualGraph G N T).degree v +
    G.degreeOn (removedCopies N T) v = G.degree v at h
  rw [removed_degreeOn G N T hdisj] at h
  have hs : (∑ j ∈ T, G.degreeOn (N j) v) = T.card := by
    calc
      _ = ∑ _j ∈ T, 1 := by
        apply sum_congr rfl
        intro j hj
        exact hperfect j hj v
      _ = _ := by simp
  rwa [hs] at h

theorem residual_regular {k : ℕ} (hregular : ∀ v, G.degree v = k)
    (N : J → Finset E) (T : Finset J)
    (hdisj : (T : Set J).Pairwise (fun i j => Disjoint (N i) (N j)))
    (hperfect : ∀ j ∈ T, G.IsPerfectMatching (N j)) (v : V) :
    (residualGraph G N T).degree v = k - T.card := by
  have h := residual_degree_accounting G N T hdisj hperfect v
  rw [hregular] at h
  omega

theorem family_card_le_degree [Nonempty V] {k : ℕ}
    (hregular : ∀ v, G.degree v = k)
    (N : J → Finset E) (T : Finset J)
    (hdisj : (T : Set J).Pairwise (fun i j => Disjoint (N i) (N j)))
    (hperfect : ∀ j ∈ T, G.IsPerfectMatching (N j)) : T.card ≤ k := by
  obtain ⟨v⟩ := ‹Nonempty V›
  have h := residual_degree_accounting G N T hdisj hperfect v
  rw [hregular] at h
  omega

theorem residual_cut_pool_unchanged (N : J → Finset E) (T : Finset J)
    (X : Finset V) (hzero : ∀ j ∈ T, (G.cutOn (N j) X).card = 0) :
    G.cutEdges X \ removedCopies N T = G.cutEdges X := by
  apply sdiff_eq_left.mpr
  apply disjoint_left.mpr
  intro e he heN
  obtain ⟨j, hj, heN⟩ := (mem_removedCopies N T e).mp heN
  have hz := card_eq_zero.mp (hzero j hj)
  have hm : e ∈ G.cutOn (N j) X := by
    rw [cutOn_eq_inter]
    exact mem_inter.mpr ⟨heN, he⟩
  rw [hz] at hm
  exact notMem_empty e hm

end Overfull.NativeReserve
