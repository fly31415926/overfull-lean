import Overfull.Patterns.Pairing

/-!
# Hall loads from actual incident edge copies

A finite edge-copy set has at most twice as many endpoint vertices as
copies. In an edge-disjoint indexed family, every member meeting a fixed
vertex contributes a distinct incident copy. Its vertex-membership load
is therefore bounded by the actual degree in any containing edge set.

The counting result does not require the family members to be matchings.
The final pairing corollary adds that hypothesis only to obtain matching
unions after the supports have been paired.
-/

noncomputable section

namespace Overfull.Multigraph

open Finset Classical
open scoped BigOperators

variable {V E I : Type*} (G : Multigraph V E)

/-- The endpoint support of a finite set of actual copies has at most
twice as many vertices as the set has copies. -/
theorem edgeSupport_card_le (C : Finset E) : (G.edgeSupport C).card ≤ 2 * C.card := by
  calc
    _ ≤ ∑ e ∈ C, (G.edge e).toFinset.card := card_biUnion_le
    _ = ∑ _e ∈ C, 2 := by
      apply sum_congr rfl
      intro e _
      exact Sym2.card_toFinset_of_not_isDiag _ (G.loopless e)
    _ = 2 * C.card := by simp [Nat.mul_comm]

/-- Three original edge copies have at most six actual endpoints. -/
theorem edgeSupport_card_le_six {C : Finset E} (hC : C.card ≤ 3) :
    (G.edgeSupport C).card ≤ 6 :=
  (G.edgeSupport_card_le C).trans (Nat.mul_le_mul_left 2 hC)

/-- Edge disjointness bounds the number of family members meeting a
vertex by the number of incident original copies available in `S`.
No matching or cardinality hypothesis is needed on individual members. -/
theorem family_support_load_le_degreeOn [Fintype I]
    (M : I → Finset E) (S : Finset E)
    (hdisjoint : Pairwise (fun i j => Disjoint (M i) (M j)))
    (hsubset : ∀ i, M i ⊆ S) (v : V) :
    (univ.filter (fun i => v ∈ G.edgeSupport (M i))).card ≤ G.degreeOn S v := by
  have hload : (univ.filter (fun i => v ∈ G.edgeSupport (M i))).card ≤
      ∑ i, G.degreeOn (M i) v := by
    rw [card_eq_sum_ones, sum_filter]
    apply sum_le_sum
    intro i _
    split_ifs with hv
    · exact (G.degreeOn_pos_iff (M i) v).mpr hv
    · exact Nat.zero_le _
  have hparts : (univ : Finset I).toSet.PairwiseDisjoint
      (fun i => (M i).filter (fun e => v ∈ G.edge e)) := by
    intro i _ j _ hij
    exact (hdisjoint hij).mono (filter_subset _ _) (filter_subset _ _)
  have hsub : univ.biUnion (fun i => (M i).filter (fun e => v ∈ G.edge e)) ⊆
      S.filter (fun e => v ∈ G.edge e) := by
    intro e he
    obtain ⟨i, _, hi⟩ := mem_biUnion.mp he
    obtain ⟨hiM, hev⟩ := mem_filter.mp hi
    exact mem_filter.mpr ⟨hsubset i hiM, hev⟩
  calc
    _ ≤ ∑ i, G.degreeOn (M i) v := hload
    _ = (univ.biUnion (fun i => (M i).filter (fun e => v ∈ G.edge e))).card :=
      (card_biUnion hparts).symm
    _ ≤ G.degreeOn S v := card_le_card hsub

end Overfull.Multigraph

namespace Overfull.Patterns

open Finset Classical

variable {V E I J : Type*}

/-- Derive all Hall support and load bounds from actual three-edge
matchings, edge disjointness within each family, and a containing set's
original vertex degrees. The two index types may differ but have equal
cardinality. -/
theorem exists_three_edge_pairing_of_degree_bound [Fintype I] [Fintype J]
    (G : Multigraph V E) (S : Finset E) (M : I → Finset E) (N : J → Finset E)
    (a : ℕ) (hcard : Fintype.card I = Fintype.card J)
    (hM : ∀ i, G.IsMatching (M i)) (hN : ∀ j, G.IsMatching (N j))
    (hsizeM : ∀ i, (M i).card ≤ 3) (hsizeN : ∀ j, (N j).card ≤ 3)
    (hdisjointM : Pairwise (fun i j => Disjoint (M i) (M j)))
    (hdisjointN : Pairwise (fun i j => Disjoint (N i) (N j)))
    (hsubsetM : ∀ i, M i ⊆ S) (hsubsetN : ∀ j, N j ⊆ S)
    (hdegree : ∀ v, G.degreeOn S v ≤ a)
    (hsize : 12 * a < Fintype.card I) :
    ∃ f : I ≃ J,
      (∀ i, Disjoint (G.edgeSupport (M i)) (G.edgeSupport (N (f i)))) ∧
      ∀ i, G.IsMatching (M i ∪ N (f i)) := by
  apply exists_matching_pairing G M N 6 a hcard hM hN
  · exact fun i => G.edgeSupport_card_le_six (hsizeM i)
  · exact fun j => G.edgeSupport_card_le_six (hsizeN j)
  · intro v
    exact (G.family_support_load_le_degreeOn M S hdisjointM hsubsetM v).trans (hdegree v)
  · intro v
    exact (G.family_support_load_le_degreeOn N S hdisjointN hsubsetN v).trans (hdegree v)
  · simpa only [Nat.reduceMul] using hsize

end Overfull.Patterns
