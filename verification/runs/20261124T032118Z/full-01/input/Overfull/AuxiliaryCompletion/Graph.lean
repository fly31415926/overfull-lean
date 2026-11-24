import Overfull.MultigraphMatchingProbability
import Overfull.AuxiliaryCompletion.Incidence
import Mathlib.Data.Finset.Sum

/-!
# The graph obtained by adding an auxiliary core

Original edge copies are retained. The added edges consist of one edge
from an original vertex to each specified new neighbor, and the edges of
a simple graph on the new vertices.
-/

namespace Overfull.AuxiliaryCompletion

open Finset Classical
open scoped BigOperators

variable {V U E : Type*}

abbrev CrossEdges (N : V → Finset U) := (v : V) × N v

abbrev CompletionEdges (N : V → Finset U) (H : SimpleGraph U) :=
  E ⊕ (CrossEdges N ⊕ H.edgeSet)

noncomputable def firstVertex (G : Multigraph V E) (N : V → Finset U)
    (H : SimpleGraph U) : CompletionEdges (E := E) N H → V ⊕ U
  | .inl e => .inl (G.firstEnd e)
  | .inr (.inl e) => .inl e.1
  | .inr (.inr e) => .inr ((Multigraph.ofSimpleGraph H).firstEnd e)

noncomputable def secondVertex (G : Multigraph V E) (N : V → Finset U)
    (H : SimpleGraph U) : CompletionEdges (E := E) N H → V ⊕ U
  | .inl e => .inl (G.secondEnd e)
  | .inr (.inl e) => .inr e.2.val
  | .inr (.inr e) => .inr ((Multigraph.ofSimpleGraph H).secondEnd e)

noncomputable def graph (G : Multigraph V E) (N : V → Finset U) (H : SimpleGraph U) :
    Multigraph (V ⊕ U) (CompletionEdges (E := E) N H) where
  edge e := s(firstVertex G N H e, secondVertex G N H e)
  loopless := by
    intro e
    rcases e with e | e
    · simpa only [firstVertex, secondVertex, Sym2.mk_isDiag_iff, Sum.inl.injEq] using
        G.endpoints_distinct e
    · rcases e with e | e
      · simp [firstVertex, secondVertex]
      · simpa only [firstVertex, secondVertex, Sym2.mk_isDiag_iff, Sum.inr.injEq] using
          (Multigraph.ofSimpleGraph H).endpoints_distinct e

theorem original_edge (G : Multigraph V E) (N : V → Finset U)
    (H : SimpleGraph U) (e : E) :
    (graph G N H).edge (.inl e) = s(.inl (G.firstEnd e), .inl (G.secondEnd e)) := rfl

theorem crossing_edge (G : Multigraph V E) (N : V → Finset U)
    (H : SimpleGraph U) (e : CrossEdges N) :
    (graph G N H).edge (.inr (.inl e)) = s(.inl e.1, .inr e.2.val) := rfl

theorem auxiliary_edge (G : Multigraph V E) (N : V → Finset U)
    (H : SimpleGraph U) (e : H.edgeSet) :
    (graph G N H).edge (.inr (.inr e)) =
      (e.val.map Sum.inr : Sym2 (V ⊕ U)) := by
  change s((Sum.inr ((Multigraph.ofSimpleGraph H).firstEnd e) : V ⊕ U),
    .inr ((Multigraph.ofSimpleGraph H).secondEnd e)) = _
  rw [← Sym2.map_pair_eq, (Multigraph.ofSimpleGraph H).edge_eq]
  rfl

variable [Fintype V] [Fintype U] [Fintype E]

noncomputable def crossingCount (N : V → Finset U) (S : Finset V) (T : Finset U) : ℕ :=
  ∑ v ∈ S, (N v ∩ T).card

theorem left_degree (G : Multigraph V E) (N : V → Finset U)
    (H : SimpleGraph U) (v : V) :
    (graph G N H).degree (.inl v) = G.degree v + (N v).card := by
  classical
  simp only [Multigraph.degree, Multigraph.incidenceEdges, Finset.card_eq_sum_ones,
    Finset.sum_filter, Fintype.sum_sum_type, Fintype.sum_sigma]
  simp only [graph, firstVertex, secondVertex, Sym2.mem_iff,
    Sum.inl.injEq, Sum.inl_ne_inr, or_false,
    if_false, Finset.sum_const_zero, add_zero]
  have h₁ : (∑ e : E, if v = G.firstEnd e ∨ v = G.secondEnd e then 1 else 0) =
      ∑ e : E, if v ∈ G.edge e then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro e _
    simp only [G.incident_iff, eq_comm]
  rw [h₁]
  simp

theorem right_degree (G : Multigraph V E) (N : V → Finset U)
    (H : SimpleGraph U) [DecidableRel H.Adj] (u : U) :
    (graph G N H).degree (.inr u) = rightLoad N u + H.degree u := by
  classical
  have haux := Multigraph.ofSimpleGraph_degree H u
  simp only [Multigraph.degree, Multigraph.incidenceEdges, Finset.card_eq_sum_ones,
    Finset.sum_filter] at haux
  simp only [Multigraph.degree, Multigraph.incidenceEdges, Finset.card_eq_sum_ones,
    Finset.sum_filter, Fintype.sum_sum_type, Fintype.sum_sigma]
  simp only [graph, firstVertex, secondVertex, Sym2.mem_iff,
    Sum.inr.injEq, Sum.inr_ne_inl, or_false, false_or,
    if_false, Finset.sum_const_zero, zero_add]
  have h₁ : (∑ e : H.edgeSet,
      if u = (Multigraph.ofSimpleGraph H).firstEnd e ∨
        u = (Multigraph.ofSimpleGraph H).secondEnd e then 1 else 0) = H.degree u := by
    convert haux using 1
    apply Finset.sum_congr rfl
    intro e _
    simp only [(Multigraph.ofSimpleGraph H).incident_iff, eq_comm]
  rw [h₁]
  unfold rightLoad
  congr 1
  calc
    _ = ∑ v : V, if u ∈ N v then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      by_cases hu : u ∈ N v
      · have heq : ∀ x : N v, u = x.val ↔ x = ⟨u, hu⟩ := by
          intro x
          constructor
          · intro h
            exact Subtype.ext h.symm
          · intro h
            exact (congrArg Subtype.val h).symm
        simp only [heq]
        simp [hu]
      · have hne : ∀ x : N v, ¬ u = x.val := by
          intro x h
          exact hu (h.symm ▸ x.property)
        simp [hne, hu]
    _ = _ := by simp

theorem rightLoad_sum (N : V → Finset U) :
    (∑ u : U, rightLoad N u) = ∑ v : V, (N v).card := by
  classical
  simp only [rightLoad, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  simp

omit [Fintype V] in
theorem internal_card_eq_sum (G : Multigraph V E) (S : Finset V) :
    (G.internalEdges S).card =
      ∑ e : E, if G.firstEnd e ∈ S ∧ G.secondEnd e ∈ S then 1 else 0 := by
  classical
  rw [Finset.card_eq_sum_ones]
  simp only [Multigraph.internalEdges, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  rw [← G.edge_eq e]
  simp only [Sym2.toFinset_mk_eq, Finset.insert_subset_iff,
    Finset.singleton_subset_iff]

omit [Fintype U] in
theorem subtype_sum_indicator (S T : Finset U) :
    (∑ u : S, if u.val ∈ T then (1 : ℕ) else 0) = (S ∩ T).card := by
  classical
  calc
    _ = ∑ u ∈ S, if u ∈ T then (1 : ℕ) else 0 :=
      (Finset.sum_subtype (p := fun u => u ∈ S)
        (F := (inferInstance : Fintype S)) S (fun _ => Iff.rfl)
        (fun u => if u ∈ T then (1 : ℕ) else 0)).symm
    _ = _ := by simp

theorem internal_card_disjSum (G : Multigraph V E) (N : V → Finset U)
    (H : SimpleGraph U) (S : Finset V) (T : Finset U) :
    ((graph G N H).internalEdges (S.disjSum T)).card =
      (G.internalEdges S).card + crossingCount N S T +
        ((Multigraph.ofSimpleGraph H).internalEdges T).card := by
  classical
  conv_rhs => rw [internal_card_eq_sum, internal_card_eq_sum]
  simp only [Multigraph.internalEdges, Finset.card_eq_sum_ones,
    Finset.sum_filter, Fintype.sum_sum_type, Fintype.sum_sigma]
  simp only [graph, firstVertex, secondVertex, Sym2.toFinset_mk_eq,
    Finset.insert_subset_iff, Finset.singleton_subset_iff,
    Finset.inl_mem_disjSum, Finset.inr_mem_disjSum]
  have hcross :
      (∑ v : V, ∑ u : N v, if v ∈ S ∧ u.val ∈ T then (1 : ℕ) else 0) =
        crossingCount N S T := by
    calc
      _ = ∑ v : V, if v ∈ S then (N v ∩ T).card else 0 := by
        apply Finset.sum_congr rfl
        intro v _
        by_cases hv : v ∈ S
        · simp only [hv, true_and, if_true]
          exact subtype_sum_indicator (N v) T
        · simp [hv]
      _ = _ := by simp [crossingCount]
  rw [hcross]
  omega

theorem auxiliary_cut_le (G : Multigraph V E) (N : V → Finset U)
    (H : SimpleGraph U) (S : Finset V) (T : Finset U) :
    (Multigraph.ofSimpleGraph H).cutSize T ≤ (graph G N H).cutSize (S.disjSum T) := by
  classical
  apply Finset.card_le_card_of_injOn (fun e => Sum.inr (Sum.inr e))
  · intro e he
    obtain ⟨v, w, heq, hv, hw⟩ :=
      ((Multigraph.ofSimpleGraph H).mem_cutEdges_iff T e).mp he
    apply ((graph G N H).mem_cutEdges_iff (S.disjSum T) _).mpr
    refine ⟨Sum.inr v, Sum.inr w, ?_, by simpa using hv, by simpa using hw⟩
    rw [auxiliary_edge]
    change Sym2.map Sum.inr ((Multigraph.ofSimpleGraph H).edge e) = _
    rw [heq]
    rfl
  · intro e _ f _ h
    exact Sum.inr.inj (Sum.inr.inj h)

end Overfull.AuxiliaryCompletion
