import Overfull.BoundaryExtension.Contraction

/-!
# Simultaneous contraction to two separate apices

The retained core vertices remain distinct.  The two other covering shores
are sent to different apices, and only copies whose endpoints become equal
are discarded.  Every joining copy and every retained-core copy keeps its
original identity.
-/

noncomputable section

namespace Overfull.Terminal

open Finset Classical SmallCuts Multigraph

variable {V E : Type*}

abbrev CentralVertex (U : Finset V) := U ⊕ Fin 2

/-- Keep the first shore and distinguish the other two shores. -/
def centralMap (U A : Finset V) (v : V) : CentralVertex U :=
  if hv : v ∈ U then Sum.inl ⟨v,hv⟩ else if v ∈ A then Sum.inr 0 else Sum.inr 1

@[simp] theorem centralMap_core (U A : Finset V) (u : U) :
    centralMap U A u.val = Sum.inl u := by
  simp [centralMap,u.property]

@[simp] theorem centralMap_eq_inl_iff (U A : Finset V) (v : V) (u : U) :
    centralMap U A v = Sum.inl u ↔ v = u.val := by
  by_cases hv : v ∈ U
  · simp [centralMap,hv,Subtype.ext_iff]
  · have hn : v ≠ u.val := by rintro rfl; exact hv u.property
    by_cases ha : v ∈ A <;> simp [centralMap,hv,hn,ha]

theorem centralMap_injective_at_core (U A : Finset V) {v w : V}
    (hv : v ∈ U) (heq : centralMap U A v = centralMap U A w) : v = w := by
  have hw : centralMap U A w = Sum.inl (⟨v,hv⟩ : U) :=
    heq.symm.trans (centralMap_core U A ⟨v,hv⟩)
  exact ((centralMap_eq_inl_iff U A w ⟨v,hv⟩).mp hw).symm

theorem centralMap_eq_first_apex_iff (U A : Finset V) (hUA : Disjoint U A) (v : V) :
    centralMap U A v = Sum.inr 0 ↔ v ∈ A := by
  by_cases hv : v ∈ U
  · have hn : v ∉ A := fun ha => disjoint_left.mp hUA hv ha
    simp [centralMap,hv,hn]
  · by_cases ha : v ∈ A <;> simp [centralMap,hv,ha]

theorem centralMap_eq_second_apex_iff (U A B : Finset V)
    (hUB : Disjoint U B) (hAB : Disjoint A B)
    (hcover : ∀ v, v ∈ U ∨ v ∈ A ∨ v ∈ B) (v : V) :
    centralMap U A v = Sum.inr 1 ↔ v ∈ B := by
  by_cases hv : v ∈ U
  · have hn : v ∉ B := fun hb => disjoint_left.mp hUB hv hb
    simp [centralMap,hv,hn]
  · by_cases ha : v ∈ A
    · have hn : v ∉ B := fun hb => disjoint_left.mp hAB ha hb
      simp [centralMap,hv,ha,hn]
    · have hb : v ∈ B := (hcover v).resolve_left hv |>.resolve_left ha
      simp [centralMap,hv,ha,hb]

/-- Every surviving central edge is an actual original copy. -/
abbrev CentralEdge (G : Multigraph V E) (U A : Finset V) :=
  {e : E // centralMap U A (G.firstEnd e) ≠ centralMap U A (G.secondEnd e)}

instance centralEdgeFintype [Fintype E] (G : Multigraph V E) (U A : Finset V) :
    Fintype (CentralEdge G U A) := Fintype.ofFinite _

def centralGraph (G : Multigraph V E) (U A : Finset V) :
    Multigraph (CentralVertex U) (CentralEdge G U A) where
  edge e := Sym2.map (centralMap U A) (G.edge e.val)
  loopless e := by
    rw [← G.edge_eq e.val]
    change ¬ (s(centralMap U A (G.firstEnd e.val),
      centralMap U A (G.secondEnd e.val))).IsDiag
    rw [Sym2.mk_isDiag_iff]
    exact e.property

theorem centralGraph_edge (G : Multigraph V E) (U A : Finset V)
    (e : CentralEdge G U A) :
    (centralGraph G U A).edge e = Sym2.map (centralMap U A) (G.edge e.val) := rfl

theorem central_incident_of_original (G : Multigraph V E) (U A : Finset V)
    (e : CentralEdge G U A) {v : V} (hv : v ∈ G.edge e.val) :
    centralMap U A v ∈ (centralGraph G U A).edge e := by
  rw [centralGraph_edge,Sym2.mem_map]
  exact ⟨v,hv,rfl⟩

@[simp] theorem central_incident_inl_iff (G : Multigraph V E) (U A : Finset V)
    (e : CentralEdge G U A) (u : U) :
    Sum.inl u ∈ (centralGraph G U A).edge e ↔ u.val ∈ G.edge e.val := by
  rw [centralGraph_edge,Sym2.mem_map]
  constructor
  · rintro ⟨v,hv,hmap⟩
    simpa only [(centralMap_eq_inl_iff U A v u).mp hmap] using hv
  · intro hu
    exact ⟨u.val,hu,centralMap_core U A u⟩

theorem central_incident_iff (G : Multigraph V E) (U A : Finset V)
    (e : CentralEdge G U A) (v : CentralVertex U) :
    v ∈ (centralGraph G U A).edge e ↔
      centralMap U A (G.firstEnd e.val) = v ∨ centralMap U A (G.secondEnd e.val) = v := by
  rw [centralGraph_edge,← G.edge_eq e.val]
  change v ∈ s(centralMap U A (G.firstEnd e.val),centralMap U A (G.secondEnd e.val)) ↔ _
  simp only [Sym2.mem_iff]
  exact or_congr eq_comm eq_comm

theorem central_retained_of_core_incident (G : Multigraph V E) (U A : Finset V)
    {e : E} {v : V} (hv : v ∈ U) (he : v ∈ G.edge e) :
    centralMap U A (G.firstEnd e) ≠ centralMap U A (G.secondEnd e) := by
  intro h
  rcases (G.incident_iff e v).mp he with hf | hs
  · exact G.endpoints_distinct e (centralMap_injective_at_core U A (hf.symm ▸ hv) h)
  · exact G.endpoints_distinct e (centralMap_injective_at_core U A (hs.symm ▸ hv) h.symm).symm

section FiniteEdges

variable [Fintype E]

theorem central_retained_of_cut (G : Multigraph V E) (U A X : Finset V)
    (z : CentralVertex U) (hfiber : ∀ v, centralMap U A v = z ↔ v ∈ X)
    {e : E} (he : e ∈ G.cutEdges X) :
    centralMap U A (G.firstEnd e) ≠ centralMap U A (G.secondEnd e) := by
  intro h
  apply (G.mem_cutEdges X e).mp he
  apply propext
  rw [← hfiber,← hfiber,h]

theorem central_incident_fiber_iff (G : Multigraph V E) (U A X : Finset V)
    (z : CentralVertex U) (hfiber : ∀ v, centralMap U A v = z ↔ v ∈ X)
    (e : CentralEdge G U A) :
    z ∈ (centralGraph G U A).edge e ↔ e.val ∈ G.cutEdges X := by
  have hnot : ¬ (G.firstEnd e.val ∈ X ∧ G.secondEnd e.val ∈ X) := by
    intro h
    exact e.property (((hfiber _).mpr h.1).trans ((hfiber _).mpr h.2).symm)
  rw [central_incident_iff,G.mem_cutEdges]
  simp only [hfiber,ne_eq,eq_iff_iff]
  tauto

theorem central_incident_first_apex_iff (G : Multigraph V E) (U A : Finset V)
    (hUA : Disjoint U A) (e : CentralEdge G U A) :
    Sum.inr 0 ∈ (centralGraph G U A).edge e ↔ e.val ∈ G.cutEdges A :=
  central_incident_fiber_iff G U A A (Sum.inr 0) (centralMap_eq_first_apex_iff U A hUA) e

theorem central_incident_second_apex_iff (G : Multigraph V E) (U A B : Finset V)
    (hUB : Disjoint U B) (hAB : Disjoint A B)
    (hcover : ∀ v, v ∈ U ∨ v ∈ A ∨ v ∈ B) (e : CentralEdge G U A) :
    Sum.inr 1 ∈ (centralGraph G U A).edge e ↔ e.val ∈ G.cutEdges B :=
  central_incident_fiber_iff G U A B (Sum.inr 1)
    (centralMap_eq_second_apex_iff U A B hUB hAB hcover) e

def centralCoreIncidenceEquiv (G : Multigraph V E) (U A : Finset V) (u : U) :
    G.incidenceEdges u.val ≃ (centralGraph G U A).incidenceEdges (Sum.inl u) where
  toFun e := ⟨⟨e.val,central_retained_of_core_incident G U A u.property
    ((G.mem_incidenceEdges u.val e.val).mp e.property)⟩, by
      simpa only [Multigraph.mem_incidenceEdges,central_incident_inl_iff] using e.property⟩
  invFun e := ⟨e.val.val,by
    simpa only [Multigraph.mem_incidenceEdges,central_incident_inl_iff] using e.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem central_degree_inl (G : Multigraph V E) (U A : Finset V) (u : U) :
    (centralGraph G U A).degree (Sum.inl u) = G.degree u.val := by
  have h := Fintype.card_congr (centralCoreIncidenceEquiv G U A u)
  simpa only [Fintype.card_coe,Multigraph.degree] using h.symm

def centralBoundaryLift (G : Multigraph V E) (U A X : Finset V)
    (z : CentralVertex U) (hfiber : ∀ v, centralMap U A v = z ↔ v ∈ X)
    (e : G.cutEdges X) : CentralEdge G U A :=
  ⟨e.val,central_retained_of_cut G U A X z hfiber e.property⟩

def centralBoundaryEquiv (G : Multigraph V E) (U A X : Finset V)
    (z : CentralVertex U) (hfiber : ∀ v, centralMap U A v = z ↔ v ∈ X) :
    G.cutEdges X ≃ (centralGraph G U A).incidenceEdges z where
  toFun e := ⟨centralBoundaryLift G U A X z hfiber e,by
    simpa only [Multigraph.mem_incidenceEdges,central_incident_fiber_iff G U A X z hfiber]
      using e.property⟩
  invFun e := ⟨e.val.val,by
    simpa only [Multigraph.mem_incidenceEdges,central_incident_fiber_iff G U A X z hfiber]
      using e.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem central_degree_fiber (G : Multigraph V E) (U A X : Finset V)
    (z : CentralVertex U) (hfiber : ∀ v, centralMap U A v = z ↔ v ∈ X) :
    (centralGraph G U A).degree z = G.cutSize X := by
  have h := Fintype.card_congr (centralBoundaryEquiv G U A X z hfiber)
  simpa only [Fintype.card_coe,Multigraph.degree,Multigraph.cutSize] using h.symm

theorem central_regular (G : Multigraph V E) (U A B : Finset V) (k : ℕ)
    (hUA : Disjoint U A) (hUB : Disjoint U B) (hAB : Disjoint A B)
    (hcover : ∀ v, v ∈ U ∨ v ∈ A ∨ v ∈ B)
    (hregular : ∀ u ∈ U, G.degree u = k) (hA : G.cutSize A = k) (hB : G.cutSize B = k) :
    ∀ v, (centralGraph G U A).degree v = k := by
  rintro (u | i)
  · exact (central_degree_inl G U A u).trans (hregular u.val u.property)
  · fin_cases i
    · exact (central_degree_fiber G U A A (Sum.inr 0)
        (centralMap_eq_first_apex_iff U A hUA)).trans hA
    · exact (central_degree_fiber G U A B (Sum.inr 1)
        (centralMap_eq_second_apex_iff U A B hUB hAB hcover)).trans hB

end FiniteEdges

def centralCoreVertices (U : Finset V) : Finset (CentralVertex U) :=
  univ.image (Sum.inl : U → CentralVertex U)

@[simp] theorem central_inl_mem_core (U : Finset V) (u : U) :
    Sum.inl u ∈ centralCoreVertices U := by simp [centralCoreVertices]

@[simp] theorem central_apex_not_mem_core (U : Finset V) (i : Fin 2) :
    Sum.inr i ∉ centralCoreVertices U := by simp [centralCoreVertices]

@[simp] theorem centralCoreVertices_card (U : Finset V) :
    (centralCoreVertices U).card = U.card := by
  rw [centralCoreVertices,Finset.card_image_of_injective _ Sum.inl_injective]
  simp

@[simp] theorem centralVertex_card (U : Finset V) :
    Fintype.card (CentralVertex U) = U.card + 2 := by simp [CentralVertex]

@[simp] theorem centralCoreVertices_compl_card (U : Finset V) :
    (centralCoreVertices U)ᶜ.card = 2 := by
  rw [Finset.card_compl,centralCoreVertices_card,centralVertex_card]
  omega

theorem central_even_order (U : Finset V) (hU : Even U.card) :
    Even (Fintype.card (CentralVertex U)) := by
  obtain ⟨m,hm⟩ := hU
  refine ⟨m+1,?_⟩
  rw [centralVertex_card,hm]
  omega

def centralCoreEquiv (U : Finset V) : U ≃ ↥(centralCoreVertices U) :=
  Equiv.ofBijective (fun u => ⟨Sum.inl u,central_inl_mem_core U u⟩) (by
    constructor
    · intro u v h
      exact Sum.inl_injective (congrArg Subtype.val h)
    · rintro ⟨v,hv⟩
      obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hv
      exact ⟨u,rfl⟩)

@[simp] theorem centralCoreEquiv_apply_val (U : Finset V) (u : U) :
    (centralCoreEquiv U u).val = Sum.inl u := rfl

@[simp] theorem centralCoreEquiv_symm_val (U : Finset V) (u : centralCoreVertices U) :
    Sum.inl ((centralCoreEquiv U).symm u) = u.val :=
  congrArg Subtype.val ((centralCoreEquiv U).apply_symm_apply u)

def centralCoreEdgeMap {G : Multigraph V E} {U : Finset V}
    (C : Core G U) (A : Finset V) : C.graph.edgeSet ↪ CentralEdge G U A where
  toFun e := ⟨C.edgeMap e,central_retained_of_core_incident G U A e.val.out.1.property (by
    rw [C.map_edge]
    exact Sym2.mem_map.mpr ⟨e.val.out.1,e.val.out_fst_mem,rfl⟩)⟩
  inj' := by
    intro e f h
    exact C.edgeMap.injective (congrArg Subtype.val h)

theorem centralCoreEdgeMap_edge {G : Multigraph V E} {U : Finset V}
    (C : Core G U) (A : Finset V) (e : C.graph.edgeSet) :
    (centralGraph G U A).edge (centralCoreEdgeMap C A e) =
      Sym2.map (Sum.inl : U → CentralVertex U) e.val := by
  rw [centralGraph_edge]
  change Sym2.map (centralMap U A) (G.edge (C.edgeMap e)) = _
  rw [C.map_edge,Sym2.map_map]
  congr 1
  funext u
  exact centralMap_core U A u

def centralCore {G : Multigraph V E} {U : Finset V}
    (C : Core G U) (A : Finset V) : Core (centralGraph G U A) (centralCoreVertices U) where
  graph := C.graph.comap (centralCoreEquiv U).symm
  edgeMap := (SimpleGraph.Iso.comap (centralCoreEquiv U).symm C.graph).mapEdgeSet.toEmbedding.trans
    (centralCoreEdgeMap C A)
  map_edge e := by
    rw [Function.Embedding.trans_apply,centralCoreEdgeMap_edge]
    change Sym2.map (Sum.inl : U → CentralVertex U)
      (Sym2.map (centralCoreEquiv U).symm e.val) = Sym2.map Subtype.val e.val
    rw [Sym2.map_map]
    congr 1
    funext u
    exact centralCoreEquiv_symm_val U u

@[simp] theorem centralCore_graph {G : Multigraph V E} {U : Finset V}
    (C : Core G U) (A : Finset V) :
    (centralCore C A).graph = C.graph.comap (centralCoreEquiv U).symm := rfl

instance centralCoreAdjDecidable {G : Multigraph V E} {U : Finset V}
    (C : Core G U) (A : Finset V) [DecidableRel C.graph.Adj] :
    DecidableRel (centralCore C A).graph.Adj :=
  inferInstanceAs (DecidableRel (C.graph.comap (centralCoreEquiv U).symm).Adj)

theorem centralCore_degree {G : Multigraph V E} {U : Finset V}
    (C : Core G U) (A : Finset V) [DecidableRel C.graph.Adj] (u : centralCoreVertices U) :
    (centralCore C A).graph.degree u = C.graph.degree ((centralCoreEquiv U).symm u) := by
  exact RobustRealization.comap_equiv_degree C.graph (centralCoreEquiv U).symm u

set_option maxHeartbeats 800000 in
theorem centralCore_robust {G : Multigraph V E} {U : Finset V}
    (C : Core G U) (A : Finset V) [DecidableRel C.graph.Adj] (ν τ : ℝ)
    (hC : IsRobustExpander C.graph ν τ) :
    IsRobustExpander (centralCore C A).graph ν τ := by
  exact RobustRealization.robust_comap_equiv C.graph (centralCoreEquiv U).symm ν τ hC

end Overfull.Terminal
