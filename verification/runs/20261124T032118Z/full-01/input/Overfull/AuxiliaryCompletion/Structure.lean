import Overfull.AuxiliaryCompletion.Graph

/-!
# Original and added edge copies in the auxiliary completion
-/

namespace Overfull.AuxiliaryCompletion

open Finset Classical

variable {V U E : Type*}

theorem original_edge_map (G : Multigraph V E) (N : V → Finset U)
    (H : SimpleGraph U) (e : E) :
    (graph G N H).edge (Sum.inl e) = (G.edge e).map Sum.inl := by
  rw [← G.edge_eq e]
  rfl

/-- An added edge has multiplicity one in the whole completion. -/
theorem added_edge_simple (G : Multigraph V E) (N : V → Finset U)
    (H : SimpleGraph U) (e f : CompletionEdges (E := E) N H)
    (he : ∀ a : E, e ≠ Sum.inl a)
    (hedge : (graph G N H).edge e = (graph G N H).edge f) : e = f := by
  rcases e with e | e
  · exact (he e rfl).elim
  · rcases e with e | e
    · rcases f with f | f
      · simp only [graph, firstVertex, secondVertex, Sym2.eq_iff,
          Sum.inl.injEq, Sum.inr_ne_inl, and_false, or_self] at hedge
      · rcases f with f | f
        · have h : e.1 = f.1 ∧ e.2.val = f.2.val := by
            simpa only [graph, firstVertex, secondVertex, Sym2.eq_iff,
              Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, false_and, or_false]
              using hedge
          have hef : e = f := by
            rcases e with ⟨v, u⟩
            rcases f with ⟨w, z⟩
            dsimp at h
            obtain ⟨rfl, hval⟩ := h
            have hz : u = z := Subtype.ext hval
            subst z
            rfl
          exact congrArg (fun a => Sum.inr (Sum.inl a)) hef
        · simp only [graph, firstVertex, secondVertex, Sym2.eq_iff,
            Sum.inl_ne_inr, false_and, or_self] at hedge
    · rcases f with f | f
      · simp only [graph, firstVertex, secondVertex, Sym2.eq_iff,
          Sum.inr_ne_inl, false_and, or_self] at hedge
      · rcases f with f | f
        · simp only [graph, firstVertex, secondVertex, Sym2.eq_iff,
            Sum.inr_ne_inl, false_and, and_false, or_self] at hedge
        · rw [auxiliary_edge, auxiliary_edge] at hedge
          have hval : e.val = f.val := Sym2.map.injective Sum.inr_injective hedge
          exact congrArg (fun a => Sum.inr (Sum.inr a)) (Subtype.ext hval)

/-- If the original graph is simple, the whole completion is simple. -/
theorem graph_edges_injective (G : Multigraph V E) (N : V → Finset U)
    (H : SimpleGraph U) (hG : Function.Injective G.edge) :
    Function.Injective (graph G N H).edge := by
  intro e f h
  rcases e with e | e
  · rcases f with f | f
    · rw [original_edge_map, original_edge_map] at h
      exact congrArg Sum.inl (hG (Sym2.map.injective Sum.inl_injective h))
    · exact (added_edge_simple G N H (Sum.inr f) (Sum.inl e)
        (by intro a; simp) h.symm).symm
  · exact added_edge_simple G N H (Sum.inr e) f (by intro a; simp) h

theorem ofSimpleGraph_completion_simple (G : SimpleGraph V)
    (N : V → Finset U) (H : SimpleGraph U) :
    Function.Injective (graph (Multigraph.ofSimpleGraph G) N H).edge :=
  graph_edges_injective _ N H Subtype.val_injective

theorem added_edge_meets_aux (G : Multigraph V E) (N : V → Finset U)
    (H : SimpleGraph U) (e : CompletionEdges (E := E) N H)
    (he : ∀ a : E, e ≠ Sum.inl a) :
    ∃ u : U, Sum.inr u ∈ (graph G N H).edge e := by
  rcases e with e | e
  · exact (he e rfl).elim
  · rcases e with e | e
    · exact ⟨e.2.val, by simp [graph, firstVertex, secondVertex]⟩
    · exact ⟨(Multigraph.ofSimpleGraph H).firstEnd e,
        by simp [graph, firstVertex, secondVertex]⟩

variable [Fintype V] [Fintype U] [Fintype E]

def auxiliaryEmbedding (N : V → Finset U) (H : SimpleGraph U) :
    H.edgeSet ↪ CompletionEdges (E := E) N H where
  toFun e := Sum.inr (Sum.inr e)
  inj' := by intro e f h; exact Sum.inr.inj (Sum.inr.inj h)

/-- The original vertices induce exactly the original edge copies. -/
theorem internal_original_edges (G : Multigraph V E) (N : V → Finset U)
    (H : SimpleGraph U) :
    (graph G N H).internalEdges ((univ : Finset V).disjSum ∅) =
      (univ : Finset E).map Function.Embedding.inl := by
  classical
  ext e
  rcases e with e | e
  · simp [Multigraph.internalEdges, graph, firstVertex, secondVertex,
      Sym2.toFinset_mk_eq, Finset.insert_subset_iff, Finset.singleton_subset_iff]
  · rcases e with e | e <;>
      simp [Multigraph.internalEdges, graph, firstVertex, secondVertex,
        Sym2.toFinset_mk_eq, Finset.insert_subset_iff, Finset.singleton_subset_iff]

/-- The new vertices induce exactly the chosen simple auxiliary graph. -/
theorem internal_auxiliary_edges (G : Multigraph V E) (N : V → Finset U)
    (H : SimpleGraph U) :
    (graph G N H).internalEdges ((∅ : Finset V).disjSum (univ : Finset U)) =
      (univ : Finset H.edgeSet).map (auxiliaryEmbedding (E := E) N H) := by
  classical
  ext e
  rcases e with e | e
  · simp [Multigraph.internalEdges, graph, firstVertex, secondVertex,
      Sym2.toFinset_mk_eq, Finset.insert_subset_iff, Finset.singleton_subset_iff,
      auxiliaryEmbedding]
  · rcases e with e | e <;>
      simp [Multigraph.internalEdges, graph, firstVertex, secondVertex,
        Sym2.toFinset_mk_eq, Finset.insert_subset_iff, Finset.singleton_subset_iff,
        auxiliaryEmbedding]

end Overfull.AuxiliaryCompletion
