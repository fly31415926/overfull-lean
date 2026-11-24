import Overfull.BoundaryExtension.Contraction

/-!
# Simultaneous contraction to finitely many distinct apices

Every retained copy has distinct image endpoints. Core vertices remain
separate, while an actual outside label gives each contracted shore its
own apex. Original edge-copy identities are preserved.
-/

noncomputable section

namespace Overfull.TerminalFourOdd.Multi

open Finset Classical SmallCuts Multigraph

variable {V E I : Type*}

abbrev CentralVertex (U : Finset V) (I : Type*) := U ⊕ I

/-- Retain every core vertex and use the actual labels outside the core. -/
def centralMap (U : Finset V) (label : V → I) (v : V) : CentralVertex U I :=
  if hv : v ∈ U then Sum.inl ⟨v,hv⟩ else Sum.inr (label v)

@[simp] theorem centralMap_core (U : Finset V) (label : V → I) (u : U) :
    centralMap U label u.val = Sum.inl u := by
  simp [centralMap,u.property]

@[simp] theorem centralMap_eq_inl_iff (U : Finset V) (label : V → I) (v : V) (u : U) :
    centralMap U label v = Sum.inl u ↔ v = u.val := by
  by_cases hv : v ∈ U
  · simp [centralMap,hv,Subtype.ext_iff]
  · have hn : v ≠ u.val := by rintro rfl; exact hv u.property
    simp [centralMap,hv,hn]

theorem centralMap_injective_at_core (U : Finset V) (label : V → I) {v w : V}
    (hv : v ∈ U) (heq : centralMap U label v = centralMap U label w) : v = w := by
  have hw : centralMap U label w = Sum.inl (⟨v,hv⟩ : U) :=
    heq.symm.trans (centralMap_core U label ⟨v,hv⟩)
  exact ((centralMap_eq_inl_iff U label w ⟨v,hv⟩).mp hw).symm

/-- Every surviving central edge is an actual original copy. -/
abbrev CentralEdge (G : Multigraph V E) (U : Finset V) (label : V → I) :=
  {e : E // centralMap U label (G.firstEnd e) ≠ centralMap U label (G.secondEnd e)}

instance centralEdgeFintype [Fintype E] (G : Multigraph V E) (U : Finset V) (label : V → I) :
    Fintype (CentralEdge G U label) := Fintype.ofFinite _

def centralGraph (G : Multigraph V E) (U : Finset V) (label : V → I) :
    Multigraph (CentralVertex U I) (CentralEdge G U label) where
  edge e := Sym2.map (centralMap U label) (G.edge e.val)
  loopless e := by
    rw [← G.edge_eq e.val]
    change ¬ (s(centralMap U label (G.firstEnd e.val),
      centralMap U label (G.secondEnd e.val))).IsDiag
    rw [Sym2.mk_isDiag_iff]
    exact e.property

theorem centralGraph_edge (G : Multigraph V E) (U : Finset V) (label : V → I)
    (e : CentralEdge G U label) :
    (centralGraph G U label).edge e = Sym2.map (centralMap U label) (G.edge e.val) := rfl

theorem central_incident_of_original (G : Multigraph V E) (U : Finset V) (label : V → I)
    (e : CentralEdge G U label) {v : V} (hv : v ∈ G.edge e.val) :
    centralMap U label v ∈ (centralGraph G U label).edge e := by
  rw [centralGraph_edge,Sym2.mem_map]
  exact ⟨v,hv,rfl⟩

@[simp] theorem central_incident_inl_iff (G : Multigraph V E) (U : Finset V) (label : V → I)
    (e : CentralEdge G U label) (u : U) :
    Sum.inl u ∈ (centralGraph G U label).edge e ↔ u.val ∈ G.edge e.val := by
  rw [centralGraph_edge,Sym2.mem_map]
  constructor
  · rintro ⟨v,hv,hmap⟩
    simpa only [(centralMap_eq_inl_iff U label v u).mp hmap] using hv
  · intro hu
    exact ⟨u.val,hu,centralMap_core U label u⟩

theorem central_incident_iff (G : Multigraph V E) (U : Finset V) (label : V → I)
    (e : CentralEdge G U label) (v : CentralVertex U I) :
    v ∈ (centralGraph G U label).edge e ↔
      centralMap U label (G.firstEnd e.val) = v ∨ centralMap U label (G.secondEnd e.val) = v := by
  rw [centralGraph_edge,← G.edge_eq e.val]
  change v ∈ s(centralMap U label (G.firstEnd e.val),centralMap U label (G.secondEnd e.val)) ↔ _
  simp only [Sym2.mem_iff]
  exact or_congr eq_comm eq_comm

theorem central_retained_of_core_incident (G : Multigraph V E) (U : Finset V) (label : V → I)
    {e : E} {v : V} (hv : v ∈ U) (he : v ∈ G.edge e) :
    centralMap U label (G.firstEnd e) ≠ centralMap U label (G.secondEnd e) := by
  intro h
  rcases (G.incident_iff e v).mp he with hf | hs
  · exact G.endpoints_distinct e (centralMap_injective_at_core U label (hf.symm ▸ hv) h)
  · exact G.endpoints_distinct e (centralMap_injective_at_core U label (hs.symm ▸ hv) h.symm).symm

section FiniteEdges

variable [Fintype E]

theorem central_retained_of_cut (G : Multigraph V E) (U X : Finset V) (label : V → I)
    (z : CentralVertex U I) (hfiber : ∀ v, centralMap U label v = z ↔ v ∈ X)
    {e : E} (he : e ∈ G.cutEdges X) :
    centralMap U label (G.firstEnd e) ≠ centralMap U label (G.secondEnd e) := by
  intro h
  apply (G.mem_cutEdges X e).mp he
  apply propext
  rw [← hfiber,← hfiber,h]

theorem central_incident_fiber_iff (G : Multigraph V E) (U X : Finset V) (label : V → I)
    (z : CentralVertex U I) (hfiber : ∀ v, centralMap U label v = z ↔ v ∈ X)
    (e : CentralEdge G U label) :
    z ∈ (centralGraph G U label).edge e ↔ e.val ∈ G.cutEdges X := by
  have hnot : ¬ (G.firstEnd e.val ∈ X ∧ G.secondEnd e.val ∈ X) := by
    intro h
    exact e.property (((hfiber _).mpr h.1).trans ((hfiber _).mpr h.2).symm)
  rw [central_incident_iff,G.mem_cutEdges]
  simp only [hfiber,ne_eq,eq_iff_iff]
  tauto

def centralCoreIncidenceEquiv (G : Multigraph V E) (U : Finset V) (label : V → I) (u : U) :
    G.incidenceEdges u.val ≃ (centralGraph G U label).incidenceEdges (Sum.inl u) where
  toFun e := ⟨⟨e.val,central_retained_of_core_incident G U label u.property
    ((G.mem_incidenceEdges u.val e.val).mp e.property)⟩, by
      simpa only [Multigraph.mem_incidenceEdges,central_incident_inl_iff] using e.property⟩
  invFun e := ⟨e.val.val,by
    simpa only [Multigraph.mem_incidenceEdges,central_incident_inl_iff] using e.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem central_degree_inl (G : Multigraph V E) (U : Finset V) (label : V → I) (u : U) :
    (centralGraph G U label).degree (Sum.inl u) = G.degree u.val := by
  have h := Fintype.card_congr (centralCoreIncidenceEquiv G U label u)
  simpa only [Fintype.card_coe,Multigraph.degree] using h.symm

def centralBoundaryLift (G : Multigraph V E) (U X : Finset V) (label : V → I)
    (z : CentralVertex U I) (hfiber : ∀ v, centralMap U label v = z ↔ v ∈ X)
    (e : G.cutEdges X) : CentralEdge G U label :=
  ⟨e.val,central_retained_of_cut G U X label z hfiber e.property⟩

def centralBoundaryEquiv (G : Multigraph V E) (U X : Finset V) (label : V → I)
    (z : CentralVertex U I) (hfiber : ∀ v, centralMap U label v = z ↔ v ∈ X) :
    G.cutEdges X ≃ (centralGraph G U label).incidenceEdges z where
  toFun e := ⟨centralBoundaryLift G U X label z hfiber e,by
    simpa only [Multigraph.mem_incidenceEdges,central_incident_fiber_iff G U X label z hfiber]
      using e.property⟩
  invFun e := ⟨e.val.val,by
    simpa only [Multigraph.mem_incidenceEdges,central_incident_fiber_iff G U X label z hfiber]
      using e.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem central_degree_fiber (G : Multigraph V E) (U X : Finset V) (label : V → I)
    (z : CentralVertex U I) (hfiber : ∀ v, centralMap U label v = z ↔ v ∈ X) :
    (centralGraph G U label).degree z = G.cutSize X := by
  have h := Fintype.card_congr (centralBoundaryEquiv G U X label z hfiber)
  simpa only [Fintype.card_coe,Multigraph.degree,Multigraph.cutSize] using h.symm

end FiniteEdges

def centralCoreVertices (U : Finset V) (I : Type*) : Finset (CentralVertex U I) :=
  univ.image (Sum.inl : U → CentralVertex U I)

@[simp] theorem central_inl_mem_core (U : Finset V) (u : U) :
    Sum.inl u ∈ centralCoreVertices U I I := by simp [centralCoreVertices]

@[simp] theorem central_apex_not_mem_core (U : Finset V) (i : I) :
    Sum.inr i ∉ centralCoreVertices U I := by simp [centralCoreVertices]

@[simp] theorem centralCoreVertices_card (U : Finset V) (I : Type*) :
    (centralCoreVertices U I).card = U.card := by
  rw [centralCoreVertices,Finset.card_image_of_injective _ Sum.inl_injective]
  simp

def centralCoreEquiv (U : Finset V) (I : Type*) : U ≃ ↥(centralCoreVertices U I) :=
  Equiv.ofBijective (fun u => ⟨Sum.inl u,central_inl_mem_core U u⟩) (by
    constructor
    · intro u v h
      exact Sum.inl_injective (congrArg Subtype.val h)
    · rintro ⟨v,hv⟩
      obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hv
      exact ⟨u,rfl⟩)

@[simp] theorem centralCoreEquiv_apply_val (U : Finset V) (u : U) :
    (centralCoreEquiv U I u).val = Sum.inl u := rfl

@[simp] theorem centralCoreEquiv_symm_val (U : Finset V) (u : centralCoreVertices U I) :
    Sum.inl ((centralCoreEquiv U I).symm u) = u.val :=
  congrArg Subtype.val ((centralCoreEquiv U I).apply_symm_apply u)

def centralCoreEdgeMap {G : Multigraph V E} {U : Finset V}
    (C : Core G U) (label : V → I) : C.graph.edgeSet ↪ CentralEdge G U label where
  toFun e := ⟨C.edgeMap e,central_retained_of_core_incident G U label e.val.out.1.property (by
    rw [C.map_edge]
    exact Sym2.mem_map.mpr ⟨e.val.out.1,e.val.out_fst_mem,rfl⟩)⟩
  inj' := by
    intro e f h
    exact C.edgeMap.injective (congrArg Subtype.val h)

theorem centralCoreEdgeMap_edge {G : Multigraph V E} {U : Finset V}
    (C : Core G U) (label : V → I) (e : C.graph.edgeSet) :
    (centralGraph G U label).edge (centralCoreEdgeMap C label e) =
      Sym2.map (Sum.inl : U → CentralVertex U I) e.val := by
  rw [centralGraph_edge]
  change Sym2.map (centralMap U label) (G.edge (C.edgeMap e)) = _
  rw [C.map_edge,Sym2.map_map]
  congr 1
  funext u
  exact centralMap_core U label u

def centralCore {G : Multigraph V E} {U : Finset V}
    (C : Core G U) (label : V → I) : Core (centralGraph G U label) (centralCoreVertices U I) where
  graph := C.graph.comap (centralCoreEquiv U I).symm
  edgeMap := (SimpleGraph.Iso.comap (centralCoreEquiv U I).symm C.graph).mapEdgeSet.toEmbedding.trans
    (centralCoreEdgeMap C label)
  map_edge e := by
    rw [Function.Embedding.trans_apply,centralCoreEdgeMap_edge]
    change Sym2.map (Sum.inl : U → CentralVertex U I)
      (Sym2.map (centralCoreEquiv U I).symm e.val) = Sym2.map Subtype.val e.val
    rw [Sym2.map_map]
    congr 1
    funext u
    exact centralCoreEquiv_symm_val U u

@[simp] theorem centralCore_graph {G : Multigraph V E} {U : Finset V}
    (C : Core G U) (label : V → I) :
    (centralCore C label).graph = C.graph.comap (centralCoreEquiv U I).symm := rfl

instance centralCoreAdjDecidable {G : Multigraph V E} {U : Finset V}
    (C : Core G U) (label : V → I) [DecidableRel C.graph.Adj] :
    DecidableRel (centralCore C label).graph.Adj :=
  inferInstanceAs (DecidableRel (C.graph.comap (centralCoreEquiv U I).symm).Adj)

theorem centralCore_degree {G : Multigraph V E} {U : Finset V}
    (C : Core G U) (label : V → I) [DecidableRel C.graph.Adj] (u : centralCoreVertices U I) :
    (centralCore C label).graph.degree u = C.graph.degree ((centralCoreEquiv U I).symm u) := by
  exact RobustRealization.comap_equiv_degree C.graph (centralCoreEquiv U I).symm u

set_option maxHeartbeats 800000 in
theorem centralCore_robust {G : Multigraph V E} {U : Finset V}
    (C : Core G U) (label : V → I) [DecidableRel C.graph.Adj] (ν τ : ℝ)
    (hC : IsRobustExpander C.graph ν τ) :
    IsRobustExpander (centralCore C label).graph ν τ := by
  exact RobustRealization.robust_comap_equiv C.graph (centralCoreEquiv U I).symm ν τ hC

end Overfull.TerminalFourOdd.Multi
