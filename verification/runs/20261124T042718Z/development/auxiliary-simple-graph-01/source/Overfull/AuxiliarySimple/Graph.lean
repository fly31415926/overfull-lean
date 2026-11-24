import Overfull.MultigraphColoring
import Overfull.SmallCuts

/-!
# A simple host for an injective-edge multigraph

The unordered edge map gives a simple graph on exactly the same vertex type.
When the map is injective, the explicit edge equivalence retains every copy,
and hence every degree, internal-edge count, cut size, and overfull set.
-/

noncomputable section

namespace Overfull.AuxiliarySimple

open Finset Classical SimpleGraph Multigraph

variable {V E : Type*} (G : Multigraph V E)

/-- Forget the copy names, retaining the exact unordered endpoints. -/
def simpleGraph : SimpleGraph V := SimpleGraph.fromEdgeSet (Set.range G.edge)

theorem simpleGraph_edgeSet : (simpleGraph G).edgeSet = Set.range G.edge := by
  ext e
  simp only [simpleGraph, SimpleGraph.edgeSet_fromEdgeSet, Set.mem_diff,
    Set.mem_setOf_eq]
  constructor
  · exact And.left
  · rintro ⟨f, rfl⟩
    exact ⟨⟨f, rfl⟩, G.loopless f⟩

theorem simpleGraph_adj (v w : V) :
    (simpleGraph G).Adj v w ↔ ∃ e, G.edge e = s(v, w) := by
  rw [← SimpleGraph.mem_edgeSet, simpleGraph_edgeSet]
  rfl

/-- With injective unordered endpoints, this is a bijection of actual edges,
not a quotient that loses parallel copies. -/
def edgeEquiv (hG : Function.Injective G.edge) : E ≃ (simpleGraph G).edgeSet :=
  Equiv.ofBijective
    (fun e => ⟨G.edge e, by rw [simpleGraph_edgeSet]; exact ⟨e, rfl⟩⟩)
    ⟨by intro e f h; exact hG (congrArg Subtype.val h), by
      intro e
      obtain ⟨f, hf⟩ := (show e.val ∈ Set.range G.edge by
        rw [← simpleGraph_edgeSet]; exact e.property)
      exact ⟨f, Subtype.ext hf⟩⟩

@[simp] theorem edgeEquiv_edge (hG : Function.Injective G.edge) (e : E) :
    (edgeEquiv G hG e).val = G.edge e := rfl

@[simp] theorem edgeEquiv_symm_edge (hG : Function.Injective G.edge)
    (e : (simpleGraph G).edgeSet) : G.edge ((edgeEquiv G hG).symm e) = e.val := by
  rw [← edgeEquiv_edge G hG, Equiv.apply_symm_apply]

variable [Fintype V] [Fintype E]

theorem incidenceEdges_image (hG : Function.Injective G.edge) (v : V) :
    (G.incidenceEdges v).image (edgeEquiv G hG) =
      (Multigraph.ofSimpleGraph (simpleGraph G)).incidenceEdges v := by
  ext e
  simp only [Finset.mem_image, Multigraph.mem_incidenceEdges]
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact hf
  · intro he
    exact ⟨(edgeEquiv G hG).symm e, by simpa using he, Equiv.apply_symm_apply _ _⟩

theorem degree_eq (hG : Function.Injective G.edge) (v : V) :
    (simpleGraph G).degree v = G.degree v := by
  rw [← Multigraph.ofSimpleGraph_degree]
  unfold Multigraph.degree
  rw [← incidenceEdges_image G hG, Finset.card_image_of_injective _ (edgeEquiv G hG).injective]

theorem internalEdges_image (hG : Function.Injective G.edge) (X : Finset V) :
    (G.internalEdges X).image (edgeEquiv G hG) = Overfull.internalEdges (simpleGraph G) X := by
  ext e
  simp only [Finset.mem_image, Multigraph.internalEdges, Overfull.internalEdges,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact hf
  · intro he
    exact ⟨(edgeEquiv G hG).symm e, by simpa using he, Equiv.apply_symm_apply _ _⟩

theorem internalEdges_card (hG : Function.Injective G.edge) (X : Finset V) :
    (Overfull.internalEdges (simpleGraph G) X).card = (G.internalEdges X).card := by
  rw [← internalEdges_image G hG, Finset.card_image_of_injective _ (edgeEquiv G hG).injective]

theorem isOverfull_iff (hG : Function.Injective G.edge) (k : ℕ) (X : Finset V) :
    Overfull.IsOverfull (simpleGraph G) k X ↔ G.IsOverfull k X := by
  unfold Overfull.IsOverfull Multigraph.IsOverfull
  rw [internalEdges_card G hG]

theorem cutEdges_image (hG : Function.Injective G.edge) (X : Finset V) :
    (G.cutEdges X).image (edgeEquiv G hG) =
      (Multigraph.ofSimpleGraph (simpleGraph G)).cutEdges X := by
  ext e
  simp only [Finset.mem_image, Multigraph.mem_cutEdges_iff]
  constructor
  · rintro ⟨f, ⟨v, w, h, hv, hw⟩, rfl⟩
    exact ⟨v, w, h, hv, hw⟩
  · rintro ⟨v, w, h, hv, hw⟩
    refine ⟨(edgeEquiv G hG).symm e, ⟨v, w, ?_, hv, hw⟩, Equiv.apply_symm_apply _ _⟩
    simpa using h

theorem cutSize_eq (hG : Function.Injective G.edge) (X : Finset V) :
    (Multigraph.ofSimpleGraph (simpleGraph G)).cutSize X = G.cutSize X := by
  unfold Multigraph.cutSize
  rw [← cutEdges_image G hG, Finset.card_image_of_injective _ (edgeEquiv G hG).injective]

/-- An already embedded simple core has the identical graph inside the simple
host. Thus its robust-expansion and minimum-degree assertions are unchanged. -/
theorem core_embed (U : Finset V) (C : SmallCuts.Core G U) :
    C.graph ≤ (simpleGraph G).induce (U : Set V) := by
  intro v w hvw
  change (simpleGraph G).Adj v.val w.val
  apply (simpleGraph_adj G _ _).mpr
  refine ⟨C.edgeMap ⟨s(v,w), hvw⟩, ?_⟩
  simpa using C.map_edge ⟨s(v,w), hvw⟩

end Overfull.AuxiliarySimple
