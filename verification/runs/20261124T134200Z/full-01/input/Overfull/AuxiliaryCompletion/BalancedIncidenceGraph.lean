import Overfull.AuxiliaryCompletion.BalancedIncidence
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-! # The actual simple bipartite graph of the balanced incidences -/

namespace Overfull.AuxiliaryCompletion

open Finset Classical SimpleGraph
open scoped BigOperators

variable {V B : Type*}

/-- Each prescribed neighbor belongs to the opposite side; every such
pair is one simple graph edge. -/
def incidenceGraph (N : V → Finset B) : SimpleGraph (V ⊕ B) where
  Adj v w := match v, w with
    | .inl a, .inr b => b ∈ N a
    | .inr b, .inl a => b ∈ N a
    | _, _ => False
  symm := by rintro (v | b) (w | c) h <;> exact h
  loopless := by rintro (v | b) h <;> exact h

theorem incidenceGraph_bipartite (N : V → Finset B) :
    (incidenceGraph N).IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr) := by
  constructor
  · rw [Set.disjoint_left]
    rintro _ ⟨v, rfl⟩ ⟨b, h⟩
    cases h
  · rintro (v | b) (w | c) h
    · exact h.elim
    · exact Or.inl ⟨⟨v, rfl⟩, ⟨c, rfl⟩⟩
    · exact Or.inr ⟨⟨b, rfl⟩, ⟨w, rfl⟩⟩
    · exact h.elim

variable [Fintype V] [Fintype B]

theorem incidenceGraph_left_degree (N : V → Finset B) (v : V) :
    (incidenceGraph N).degree (.inl v) = (N v).card := by
  classical
  have heq : (N v).image Sum.inr = (incidenceGraph N).neighborFinset (.inl v) := by
    ext w
    cases w <;> simp [incidenceGraph]
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← heq,
    Finset.card_image_of_injective _ Sum.inr_injective]

theorem incidenceGraph_right_degree (N : V → Finset B) (b : B) :
    (incidenceGraph N).degree (.inr b) = rightLoad N b := by
  classical
  have heq : (univ.filter (fun v => b ∈ N v)).image Sum.inl =
      (incidenceGraph N).neighborFinset (.inr b) := by
    ext w
    cases w <;> simp [incidenceGraph]
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← heq,
    Finset.card_image_of_injective _ Sum.inl_injective]
  rfl

/-- The prescribed degrees are realized in an actual simple bipartite
graph, with balanced right degrees and the required unit-degree restriction. -/
theorem exists_balanced_incidence_graph (d : V → ℕ)
    (horder : Fintype.card V ≤ Fintype.card B)
    (hd : ∀ v, d v ≤ Fintype.card B) :
    ∃ G : SimpleGraph (V ⊕ B),
      G.IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr) ∧
      (∀ v, G.degree (.inl v) = d v) ∧
      (∀ b c, G.degree (.inr b) ≤ G.degree (.inr c) + 1) ∧
      (∀ b, G.degree (.inr b) ≤ Nat.ceil ((∑ v, (d v : ℝ)) / Fintype.card B)) ∧
      ∀ b, (univ.filter (fun v => d v = 1 ∧ G.Adj (.inl v) (.inr b))).card ≤ 1 := by
  classical
  obtain ⟨N, hN, hbalance⟩ := exists_balanced_incidences (B := B) d horder hd
  refine ⟨incidenceGraph N, incidenceGraph_bipartite N, ?_, ?_, ?_, ?_⟩
  · intro v
    rw [incidenceGraph_left_degree]
    exact hN.1 v
  · intro b c
    simpa only [incidenceGraph_right_degree] using hbalance b c
  · intro b
    have hsum : (∑ c, rightLoad N c) = ∑ v, d v := by
      rw [sum_rightLoad]
      exact Finset.sum_congr rfl (fun v _ => hN.1 v)
    have hsumR : (∑ c, (rightLoad N c : ℝ)) = ∑ v, (d v : ℝ) := by
      exact_mod_cast hsum
    have h := rightLoad_le_ceil_average N hbalance b
    simpa only [incidenceGraph_right_degree, hsumR] using h
  · intro b
    have heq : (univ.filter (fun v : V => d v = 1 ∧
        (incidenceGraph N).Adj (.inl v) (.inr b))) =
        univ.filter (fun v : V => d v = 1 ∧ b ∈ N v) := by
      ext v
      simp only [Finset.mem_filter, incidenceGraph]
    rw [heq]
    exact hN.2 b

end Overfull.AuxiliaryCompletion
