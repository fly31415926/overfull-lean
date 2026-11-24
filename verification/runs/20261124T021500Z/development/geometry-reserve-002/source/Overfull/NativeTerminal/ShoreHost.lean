import Overfull.BoundaryExtension.Colors
import Overfull.NativeCore.IndependentExterior

/-!
# Actual multigraphs on a shore

The induced host restricts both vertices and edge copies.  Its edges are
the original internal copies, so parallel copies are never identified.
A shore with empty cut retains every incidence at its vertices.
-/

noncomputable section

namespace Overfull.NativeTerminal

open Finset Classical SmallCuts BoundaryExtension Multigraph

variable {V E : Type*} [Fintype V] [Fintype E]

/-- The actual induced multigraph on the vertex subtype of a shore. -/
def inducedHost (G : Multigraph V E) (A : Finset V) :
    Multigraph A (G.internalEdges A) where
  edge e := s(⟨G.firstEnd e.val, ((G.mem_internalEdges A e.val).mp e.property).1⟩,
    ⟨G.secondEnd e.val, ((G.mem_internalEdges A e.val).mp e.property).2⟩)
  loopless e := by
    simp only [Sym2.mk_isDiag_iff]
    intro h
    exact G.endpoints_distinct e.val (congrArg Subtype.val h)

@[simp] theorem inducedHost_incident (G : Multigraph V E) (A : Finset V)
    (e : G.internalEdges A) (v : A) :
    v ∈ (inducedHost G A).edge e ↔ v.val ∈ G.edge e.val := by
  simp only [inducedHost, Sym2.mem_iff, Subtype.ext_iff, G.incident_iff]
  exact or_congr eq_comm eq_comm

/-- Mapping the induced endpoints back gives exactly the original edge. -/
theorem inducedHost_edge_map (G : Multigraph V E) (A : Finset V)
    (e : G.internalEdges A) :
    Sym2.map (Subtype.val : A → V) ((inducedHost G A).edge e) = G.edge e.val := by
  exact G.edge_eq e.val

theorem internal_of_incident_of_cut_empty (G : Multigraph V E) (A : Finset V)
    (hcut : G.cutEdges A = ∅) {e : E} {v : V}
    (hv : v ∈ A) (he : v ∈ G.edge e) : e ∈ G.internalEdges A := by
  have hn : e ∉ G.cutEdges A := by rw [hcut]; exact notMem_empty e
  rw [G.mem_cutEdges, not_not, eq_iff_iff] at hn
  rcases (G.incident_iff e v).mp he with h | h
  · have hfirst : G.firstEnd e ∈ A := h.symm ▸ hv
    exact (G.mem_internalEdges A e).mpr ⟨hfirst, hn.mp hfirst⟩
  · have hsecond : G.secondEnd e ∈ A := h.symm ▸ hv
    exact (G.mem_internalEdges A e).mpr ⟨hn.mpr hsecond, hsecond⟩

/-- The full original incidence set survives in a component shore. -/
def inducedIncidenceEquiv (G : Multigraph V E) (A : Finset V)
    (hcut : G.cutEdges A = ∅) (v : A) :
    G.incidenceEdges v.val ≃ (inducedHost G A).incidenceEdges v where
  toFun e := ⟨⟨e.val, internal_of_incident_of_cut_empty G A hcut v.property
    ((G.mem_incidenceEdges v.val e.val).mp e.property)⟩, by
    simpa only [Multigraph.mem_incidenceEdges, inducedHost_incident] using e.property⟩
  invFun e := ⟨e.val.val, by
    simpa only [Multigraph.mem_incidenceEdges, inducedHost_incident] using e.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem inducedHost_degree_of_cut_empty (G : Multigraph V E) (A : Finset V)
    (hcut : G.cutEdges A = ∅) (v : A) :
    (inducedHost G A).degree v = G.degree v.val := by
  have hh := Fintype.card_congr (inducedIncidenceEquiv G A hcut v)
  simpa only [Fintype.card_coe, Multigraph.degree] using hh.symm

theorem inducedHost_regular (G : Multigraph V E) (A : Finset V) (k : ℕ)
    (hcut : G.cutEdges A = ∅) (hregular : ∀ v ∈ A, G.degree v = k) :
    ∀ v, (inducedHost G A).degree v = k := by
  intro v
  exact (inducedHost_degree_of_cut_empty G A hcut v).trans (hregular v.val v.property)

/-- An induced coloring colors the original internal copies. -/
def inducedColoringToRestriction (G : Multigraph V E) (A : Finset V) (k : ℕ)
    (c : (inducedHost G A).EdgeColoring k) :
    (G.restrictEdges (G.internalEdges A)).EdgeColoring k where
  color := c.color
  proper := by
    intro e f v hc hev hfv
    have hv : v ∈ A := by
      rcases (G.incident_iff e.val v).mp hev with h | h
      · exact h ▸ ((G.mem_internalEdges A e.val).mp e.property).1
      · exact h ▸ ((G.mem_internalEdges A e.val).mp e.property).2
    exact c.proper hc ((inducedHost_incident G A e ⟨v,hv⟩).mpr hev)
      ((inducedHost_incident G A f ⟨v,hv⟩).mpr hfv)

/-- With empty cut, the retained edge copies are precisely the internal ones. -/
def retainedInternalEquiv (G : Multigraph V E) (A : Finset V)
    (hcut : G.cutEdges A = ∅) : RetainedEdge G A ≃ G.internalEdges A where
  toFun e := ⟨e.val, by
    obtain ⟨v,hv⟩ := e.property
    exact internal_of_incident_of_cut_empty G A hcut v.property hv⟩
  invFun e := ⟨e.val, ⟨⟨G.firstEnd e.val,
    ((G.mem_internalEdges A e.val).mp e.property).1⟩,
    (G.incident_iff e.val _).mpr (Or.inl rfl)⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A component coloring on the actual shore also colors its retained graph
on the original vertex type. -/
def inducedColoringToRetained (G : Multigraph V E) (A : Finset V) (k : ℕ)
    (hcut : G.cutEdges A = ∅) (c : (inducedHost G A).EdgeColoring k) :
    (retainedGraph G A).EdgeColoring k where
  color e := c.color (retainedInternalEquiv G A hcut e)
  proper := by
    intro e f v hc hev hfv
    apply (retainedInternalEquiv G A hcut).injective
    exact (inducedColoringToRestriction G A k c).proper hc hev hfv

/-- The old core vertices inside an induced shore. -/
abbrev inducedCoreVertices (A U : Finset V) : Finset A := shore A U

theorem inducedCoreVertices_card (A U : Finset V) (hUA : U ⊆ A) :
    (inducedCoreVertices A U).card = U.card := by
  rw [shore_card, inter_eq_left.mpr hUA]

theorem inducedCoreVertices_compl_card (A U : Finset V) :
    (inducedCoreVertices A U)ᶜ.card = (A \ U).card := shore_compl_card A U

theorem inducedHost_independent_exterior (G : Multigraph V E) (A U : Finset V)
    (hindependent : G.internalEdges (A \ U) = ∅) :
    (inducedHost G A).internalEdges (inducedCoreVertices A U)ᶜ = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  have ends := ((inducedHost G A).mem_internalEdges _ e).mp he
  have h₁ : (inducedHost G A).firstEnd e ∈ (inducedHost G A).edge e :=
    ((inducedHost G A).incident_iff e _).mpr (Or.inl rfl)
  have h₂ : (inducedHost G A).secondEnd e ∈ (inducedHost G A).edge e :=
    ((inducedHost G A).incident_iff e _).mpr (Or.inr rfl)
  have hm₁ := (inducedHost_incident G A e _).mp h₁
  have hm₂ := (inducedHost_incident G A e _).mp h₂
  have hnot₁ : ((inducedHost G A).firstEnd e).val ∉ U := by
    simpa only [mem_compl, mem_shore] using ends.1
  have hnot₂ : ((inducedHost G A).secondEnd e).val ∉ U := by
    simpa only [mem_compl, mem_shore] using ends.2
  have horiginal : e.val ∈ G.internalEdges (A \ U) := by
    have heq := inducedHost_edge_map G A e
    rw [← (inducedHost G A).edge_eq e, Sym2.map_pair_eq] at heq
    exact (G.internalEdges_iff_of_edge e.val _ _ heq.symm _).mpr
      ⟨mem_sdiff.mpr ⟨((inducedHost G A).firstEnd e).property,hnot₁⟩,
        mem_sdiff.mpr ⟨((inducedHost G A).secondEnd e).property,hnot₂⟩⟩
  rw [hindependent] at horiginal
  exact notMem_empty e.val horiginal

end Overfull.NativeTerminal
