import Overfull.NativeTerminal.ShoreHost

/-!
# Coloring an optional closed exceptional pair

Every retained copy in a closed shore with at most two vertices has the
same two distinct endpoints. Its copy count is bounded by an actual vertex
degree, so an injective palette assignment colors every parallel copy.
-/

noncomputable section

namespace Overfull.NativeTerminal

open Finset Classical Multigraph BoundaryExtension

variable {V E : Type*} [Fintype E]

/-- A component on at most two vertices has a proper coloring with its
maximum degree. The empty component and every parallel copy are included. -/
theorem retained_pair_colorable (G : Multigraph V E) (B : Finset V) (k : ℕ)
    (hcut : G.cutEdges B = ∅) (hcard : B.card ≤ 2)
    (hdegree : ∀ v ∈ B, G.degree v ≤ k) :
    Nonempty ((retainedGraph G B).EdgeColoring k) := by
  by_cases hnonempty : Nonempty (RetainedEdge G B)
  · obtain ⟨e₀⟩ := hnonempty
    obtain ⟨v,_hve₀⟩ := e₀.property
    have hall (e : RetainedEdge G B) : v.val ∈ G.edge e.val := by
      obtain ⟨w,hwe⟩ := e.property
      have heI := internal_of_incident_of_cut_empty G B hcut w.property hwe
      have hsub : (G.edge e.val).toFinset ⊆ B := (mem_filter.mp heI).2
      have heq : (G.edge e.val).toFinset = B :=
        eq_of_subset_of_card_le hsub (by
          rw [Sym2.card_toFinset_of_not_isDiag _ (G.loopless e.val)]
          exact hcard)
      exact Sym2.mem_toFinset.mp (heq.symm ▸ v.property)
    have hinc : (retainedGraph G B).incidenceEdges v.val = univ := by
      ext e
      simp only [Multigraph.mem_incidenceEdges, retainedGraph_edge, mem_univ, iff_true]
      exact hall e
    have hsize : Fintype.card (RetainedEdge G B) ≤ k := by
      calc
        _ = (retainedGraph G B).degree v.val := by
          rw [Multigraph.degree,hinc,card_univ]
        _ = G.degree v.val := retainedGraph_degree_core G B v
        _ ≤ k := hdegree v.val v.property
    obtain ⟨f⟩ : Nonempty (RetainedEdge G B ↪ Fin k) :=
      Function.Embedding.nonempty_of_card_le (by simpa only [Fintype.card_fin] using hsize)
    exact ⟨⟨f, fun he _ _ => f.injective he⟩⟩
  · refine ⟨⟨fun e => (hnonempty ⟨e⟩).elim, ?_⟩⟩
    intro e
    exact (hnonempty ⟨e⟩).elim

end Overfull.NativeTerminal
