import Overfull.NativeTerminal.PairColoring

/-!
# Coloring two separately closed exceptional pairs

The two components reuse the same palette.  Every edge in the union is an
original retained copy, and closedness prevents a color conflict between
the two components.  No bound on their combined order by two is assumed.
-/

noncomputable section

namespace Overfull.NativeTerminal

open Finset Classical Multigraph BoundaryExtension

variable {V E : Type*} [Fintype E]

/-- Every incidence of a retained copy lies in its closed shore. -/
theorem incident_mem_of_retained_closed (G : Multigraph V E) (A : Finset V)
    (hcut : G.cutEdges A = ∅) (e : RetainedEdge G A) {v : V}
    (hv : v ∈ G.edge e.val) : v ∈ A := by
  obtain ⟨w, hw⟩ := e.property
  have hi := internal_of_incident_of_cut_empty G A hcut w.property hw
  have hends := (G.mem_internalEdges A e.val).mp hi
  rcases (G.incident_iff e.val v).mp hv with h | h
  · exact h ▸ hends.1
  · exact h ▸ hends.2

/-- Colorings of two disjoint closed shores give a coloring of all original
copies retained by their union, using exactly the same palette. -/
theorem retained_closed_union_colorable (G : Multigraph V E) (A B : Finset V)
    (k : ℕ) (hAB : Disjoint A B)
    (hA : G.cutEdges A = ∅) (hB : G.cutEdges B = ∅)
    (cA : (retainedGraph G A).EdgeColoring k)
    (cB : (retainedGraph G B).EdgeColoring k) :
    Nonempty ((retainedGraph G (A ∪ B)).EdgeColoring k) := by
  have inB (e : RetainedEdge G (A ∪ B))
      (ha : ¬ ∃ v : A, v.val ∈ G.edge e.val) :
      ∃ v : B, v.val ∈ G.edge e.val := by
    obtain ⟨v, hv⟩ := e.property
    rcases mem_union.mp v.property with hvA | hvB
    · exact (ha ⟨⟨v.val, hvA⟩, hv⟩).elim
    · exact ⟨⟨v.val, hvB⟩, hv⟩
  let color (e : RetainedEdge G (A ∪ B)) : Fin k :=
    if ha : ∃ v : A, v.val ∈ G.edge e.val then cA.color ⟨e.val, ha⟩
    else cB.color ⟨e.val, inB e ha⟩
  refine ⟨⟨color, ?_⟩⟩
  intro e f v hc hev hfv
  change v ∈ G.edge e.val at hev
  change v ∈ G.edge f.val at hfv
  dsimp only [color] at hc
  split_ifs at hc with heA hfA hfA
  · exact Subtype.ext
      (congrArg (fun q : RetainedEdge G A => q.val) (cA.proper hc hev hfv))
  · have hvA := incident_mem_of_retained_closed G A hA ⟨e.val, heA⟩ hev
    have hvB := incident_mem_of_retained_closed G B hB ⟨f.val, inB f hfA⟩ hfv
    exact (disjoint_left.mp hAB hvA hvB).elim
  · have hvB := incident_mem_of_retained_closed G B hB ⟨e.val, inB e heA⟩ hev
    have hvA := incident_mem_of_retained_closed G A hA ⟨f.val, hfA⟩ hfv
    exact (disjoint_left.mp hAB hvA hvB).elim
  · exact Subtype.ext
      (congrArg (fun q : RetainedEdge G B => q.val) (cB.proper hc hev hfv))

/-- The union of two separately closed exceptional pairs is colorable by
the maximum-degree palette.  Both parallel-copy pools are retained. -/
theorem retained_two_pairs_colorable (G : Multigraph V E) (B₀ B₁ : Finset V)
    (k : ℕ) (hdisjoint : Disjoint B₀ B₁)
    (hcut₀ : G.cutEdges B₀ = ∅) (hcut₁ : G.cutEdges B₁ = ∅)
    (hcard₀ : B₀.card ≤ 2) (hcard₁ : B₁.card ≤ 2)
    (hdegree : ∀ v ∈ B₀ ∪ B₁, G.degree v ≤ k) :
    Nonempty ((retainedGraph G (B₀ ∪ B₁)).EdgeColoring k) := by
  obtain ⟨c₀⟩ := retained_pair_colorable G B₀ k hcut₀ hcard₀
    (fun v hv => hdegree v (mem_union_left _ hv))
  obtain ⟨c₁⟩ := retained_pair_colorable G B₁ k hcut₁ hcard₁
    (fun v hv => hdegree v (mem_union_right _ hv))
  exact retained_closed_union_colorable G B₀ B₁ k hdisjoint hcut₀ hcut₁ c₀ c₁

end Overfull.NativeTerminal
