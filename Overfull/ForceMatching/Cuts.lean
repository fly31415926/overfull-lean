import Overfull.MatchingProbability
import Mathlib.Tactic

namespace Overfull.ForceMatching

open Finset Classical MatchingProbability FractionalMatching

variable {V I : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem matchingEdges_mono (M Q : G.Subgraph) (hQM : Q ≤ M) :
    matchingEdges Q ⊆ matchingEdges M := by
  intro e he
  exact mem_filter.mpr ⟨mem_univ _,SimpleGraph.Subgraph.edgeSet_mono hQM (mem_filter.mp he).2⟩

omit [Fintype V] [DecidableRel G.Adj] in
theorem cutEdges_mono (F H : Finset G.edgeSet) (h : F ⊆ H) (X : Finset V) :
    cutEdges F X ⊆ cutEdges H X := Finset.filter_subset_filter _ h

omit [Fintype V] [DecidableRel G.Adj] in
theorem incidentCount_mono (F H : Finset G.edgeSet) (h : F ⊆ H) (v : V) :
    incidentCount F v ≤ incidentCount H v :=
  card_le_card (Finset.filter_subset_filter _ h)

omit [Fintype V] in
/-- Internal edges of a core never cross a union containing that core
wholly or not at all. -/
theorem same_core_membership (U : I → Finset V) (X : Finset V)
    (hwhole : ∀ i, U i ⊆ X ∨ Disjoint (U i) X)
    {i : I} {u v : V} (hu : u ∈ U i) (hv : v ∈ U i) :
    u ∈ X ↔ v ∈ X := by
  rcases hwhole i with h | h
  · exact iff_of_true (h hu) (h hv)
  · exact iff_of_false (fun hx => disjoint_left.mp h hu hx)
      (fun hx => disjoint_left.mp h hv hx)

/-- Completing a prescribed matching only with edges internal to cores
does not change its crossing edge set on a whole-core union. -/
theorem completed_cutEdges_eq (U : I → Finset V) (Q N : G.Subgraph)
    (hQN : Q ≤ N)
    (hcomplete : ∀ u v, N.Adj u v → Q.Adj u v ∨ ∃ i, u ∈ U i ∧ v ∈ U i)
    (X : Finset V) (hwhole : ∀ i, U i ⊆ X ∨ Disjoint (U i) X) :
    cutEdges (matchingEdges N) X = cutEdges (matchingEdges Q) X := by
  apply subset_antisymm
  · intro e he
    obtain ⟨heN,hcross⟩ := mem_filter.mp he
    have heN' := (mem_filter.mp heN).2
    have hadj : N.Adj (firstEnd e) (secondEnd e) := by
      change s(firstEnd e,secondEnd e) ∈ N.edgeSet
      rw [edge_eq e]
      exact heN'
    rcases hcomplete _ _ hadj with heQ | ⟨i,hi,hj⟩
    · apply mem_filter.mpr
      refine ⟨mem_filter.mpr ⟨mem_univ _,?_⟩,hcross⟩
      rw [← edge_eq e]
      exact heQ
    · exact False.elim (hcross (propext (same_core_membership U X hwhole hi hj)))
  · exact cutEdges_mono _ _ (matchingEdges_mono N Q hQN) X

/-- Perfect matching cuts have the parity of the shore. Therefore
shrinking the actual cut-edge set also decreases every toggled cut. -/
theorem toggle_cut_le_of_cut_subset (M N : G.Subgraph)
    (hM : M.IsPerfectMatching) (hN : N.IsPerfectMatching) (X : Finset V)
    (hsub : cutEdges (matchingEdges N) X ⊆ cutEdges (matchingEdges M) X) (v : V) :
    cutCount (matchingEdges N) (toggle X v) ≤ cutCount (matchingEdges M) (toggle X v) := by
  have hle : cutCount (matchingEdges N) X ≤ cutCount (matchingEdges M) X := card_le_card hsub
  have hparM := matching_cut_handshake M hM X
  have hparN := matching_cut_handshake N hN X
  have htoggleM := cut_toggle (matchingEdges M) X v
  have htoggleN := cut_toggle (matchingEdges N) X v
  rw [incidentCount_matching M hM v] at htoggleM
  rw [incidentCount_matching N hN v] at htoggleN
  have hinc : incidentCount (cutEdges (matchingEdges M) X) v ≤ 1 := by
    have hh := incidentCount_mono (cutEdges (matchingEdges M) X) (matchingEdges M)
      (Finset.filter_subset _ _) v
    simpa only [incidentCount_matching M hM v] using hh
  by_cases heq : cutCount (matchingEdges N) X = cutCount (matchingEdges M) X
  · have hset : cutEdges (matchingEdges N) X = cutEdges (matchingEdges M) X :=
      eq_of_subset_of_card_le hsub heq.ge
    rw [hset] at htoggleN
    omega
  · have hgap : cutCount (matchingEdges N) X + 2 ≤ cutCount (matchingEdges M) X := by omega
    omega

/-- Both the original union and all its one-vertex changes have no more
matching crossing edges after compression and internal completion. -/
theorem completed_cut_comparison (U : I → Finset V) (M Q N : G.Subgraph)
    (hM : M.IsPerfectMatching) (hN : N.IsPerfectMatching) (hQM : Q ≤ M) (hQN : Q ≤ N)
    (hcomplete : ∀ u v, N.Adj u v → Q.Adj u v ∨ ∃ i, u ∈ U i ∧ v ∈ U i)
    (X : Finset V) (hwhole : ∀ i, U i ⊆ X ∨ Disjoint (U i) X) :
    cutCount (matchingEdges N) X ≤ cutCount (matchingEdges M) X ∧
      ∀ v, cutCount (matchingEdges N) (toggle X v) ≤ cutCount (matchingEdges M) (toggle X v) := by
  have hsub : cutEdges (matchingEdges N) X ⊆ cutEdges (matchingEdges M) X := by
    rw [completed_cutEdges_eq U Q N hQN hcomplete X hwhole]
    exact cutEdges_mono _ _ (matchingEdges_mono M Q hQM) X
  exact ⟨card_le_card hsub,toggle_cut_le_of_cut_subset M N hM hN X hsub⟩

theorem cutFailure_of_matching_cut_le (M N : G.Subgraph) (k : ℕ) (X : Finset V)
    (hle : cutCount (matchingEdges N) X ≤ cutCount (matchingEdges M) X) :
    CutFailure N k X → CutFailure M k X := by
  have hM := cut_partition M X
  have hN := cut_partition N X
  unfold CutFailure
  omega

/-- All tested inequalities survive actual internal completion. -/
theorem family_safe_after_completion (U : I → Finset V) (M Q N : G.Subgraph)
    (hM : M.IsPerfectMatching) (hN : N.IsPerfectMatching) (hQM : Q ≤ M) (hQN : Q ≤ N)
    (hcomplete : ∀ u v, N.Adj u v → Q.Adj u v ∨ ∃ i, u ∈ U i ∧ v ∈ U i)
    (k : ℕ) (𝓧 : Finset (Finset V))
    (hwhole : ∀ X ∈ 𝓧, ∀ i, U i ⊆ X ∨ Disjoint (U i) X)
    (hsafe : ¬ FamilyFailure M k 𝓧) : ¬ FamilyFailure N k 𝓧 := by
  rintro ⟨X,hX,hfail⟩
  obtain ⟨hbase,htoggle⟩ := completed_cut_comparison U M Q N hM hN hQM hQN hcomplete X (hwhole X hX)
  apply hsafe
  refine ⟨X,hX,?_⟩
  rcases hfail with ⟨hodd,hbad⟩ | ⟨heven,v,hbad⟩
  · exact Or.inl ⟨hodd,cutFailure_of_matching_cut_le M N k X hbase hbad⟩
  · exact Or.inr ⟨heven,v,cutFailure_of_matching_cut_le M N k (toggle X v) (htoggle v) hbad⟩

end Overfull.ForceMatching
