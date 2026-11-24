import Overfull.SmallCuts
import Overfull.RobustRealization.Relabeling

/-!
# Contracting the exterior of an actual multigraph core

Retain exactly the original edge copies with an endpoint in the core.  The
contraction sends all outside endpoints to one apex and keeps the retained
edge type unchanged.  Internal core edges and parallel boundary copies are
therefore preserved separately.
-/

namespace Overfull.BoundaryExtension

open Finset Classical

variable {V E : Type*}

/-- The original core vertices together with one new exterior vertex. -/
abbrev Vertex (U : Finset V) := U ⊕ Unit

/-- Every retained edge has an actual endpoint in the core. -/
abbrev RetainedEdge (G : Multigraph V E) (U : Finset V) :=
  {e : E // ∃ u : U, u.val ∈ G.edge e}

noncomputable instance retainedEdgeFintype [Fintype E]
    (G : Multigraph V E) (U : Finset V) : Fintype (RetainedEdge G U) :=
  Fintype.ofFinite _

/-- Keep each core vertex and identify every exterior vertex with the apex. -/
noncomputable def vertexMap (U : Finset V) (v : V) : Vertex U :=
  if h : v ∈ U then Sum.inl ⟨v, h⟩ else Sum.inr ()

@[simp] theorem vertexMap_core (U : Finset V) (u : U) :
    vertexMap U u.val = Sum.inl u := by
  simp [vertexMap, u.property]

@[simp] theorem vertexMap_eq_inl_iff (U : Finset V) (v : V) (u : U) :
    vertexMap U v = Sum.inl u ↔ v = u.val := by
  by_cases hv : v ∈ U
  · simp [vertexMap, hv, Subtype.ext_iff]
  · have hne : v ≠ u.val := by rintro rfl; exact hv u.property
    simp [vertexMap, hv, hne]

@[simp] theorem vertexMap_eq_apex_iff (U : Finset V) (v : V) :
    vertexMap U v = Sum.inr () ↔ v ∉ U := by
  by_cases hv : v ∈ U <;> simp [vertexMap, hv]

theorem vertexMap_injective_at_core (U : Finset V) {v w : V}
    (hv : v ∈ U) (h : vertexMap U v = vertexMap U w) : v = w := by
  have hw : vertexMap U w = Sum.inl (⟨v, hv⟩ : U) :=
    h.symm.trans (vertexMap_core U ⟨v, hv⟩)
  exact ((vertexMap_eq_inl_iff U w ⟨v, hv⟩).mp hw).symm

theorem retained_endpoints (G : Multigraph V E) (U : Finset V)
    (e : RetainedEdge G U) : G.firstEnd e.val ∈ U ∨ G.secondEnd e.val ∈ U := by
  obtain ⟨u, hu⟩ := e.property
  rcases (G.incident_iff e.val u.val).mp hu with h | h
  · exact Or.inl (h.symm ▸ u.property)
  · exact Or.inr (h.symm ▸ u.property)

private theorem mapped_endpoints_distinct (G : Multigraph V E) (U : Finset V)
    (e : RetainedEdge G U) :
    vertexMap U (G.firstEnd e.val) ≠ vertexMap U (G.secondEnd e.val) := by
  intro h
  rcases retained_endpoints G U e with hfirst | hsecond
  · exact G.endpoints_distinct e.val (vertexMap_injective_at_core U hfirst h)
  · exact G.endpoints_distinct e.val (vertexMap_injective_at_core U hsecond h.symm).symm

/-- The part of the original host to be colored, with original vertices and
with precisely the edge copies incident with the core. -/
def retainedGraph (G : Multigraph V E) (U : Finset V) :
    Multigraph V (RetainedEdge G U) where
  edge e := G.edge e.val
  loopless e := G.loopless e.val

/-- Contract the exterior, keeping every retained original edge copy. -/
noncomputable def contract (G : Multigraph V E) (U : Finset V) :
    Multigraph (Vertex U) (RetainedEdge G U) where
  edge e := Sym2.map (vertexMap U) (G.edge e.val)
  loopless e := by
    rw [← G.edge_eq e.val]
    change ¬ (s(vertexMap U (G.firstEnd e.val),
      vertexMap U (G.secondEnd e.val))).IsDiag
    rw [Sym2.mk_isDiag_iff]
    exact mapped_endpoints_distinct G U e

@[simp] theorem retainedGraph_edge (G : Multigraph V E) (U : Finset V)
    (e : RetainedEdge G U) : (retainedGraph G U).edge e = G.edge e.val := rfl

theorem contract_edge (G : Multigraph V E) (U : Finset V)
    (e : RetainedEdge G U) :
    (contract G U).edge e = Sym2.map (vertexMap U) (G.edge e.val) := rfl

/-- Original incidence always gives incidence at the mapped vertex. -/
theorem contract_incident_of_original (G : Multigraph V E) (U : Finset V)
    (e : RetainedEdge G U) {v : V} (hv : v ∈ G.edge e.val) :
    vertexMap U v ∈ (contract G U).edge e := by
  rw [contract_edge, Sym2.mem_map]
  exact ⟨v, hv, rfl⟩

/-- At a core vertex the incidence correspondence is exact. -/
@[simp] theorem incident_inl_iff (G : Multigraph V E) (U : Finset V)
    (e : RetainedEdge G U) (u : U) :
    Sum.inl u ∈ (contract G U).edge e ↔ u.val ∈ G.edge e.val := by
  rw [contract_edge, Sym2.mem_map]
  constructor
  · rintro ⟨v, hv, hmap⟩
    have h := (vertexMap_eq_inl_iff U v u).mp hmap
    simpa only [h] using hv
  · intro hu
    exact ⟨u.val, hu, vertexMap_core U u⟩

/-- Apex incidence means that an original endpoint lies outside the core. -/
theorem incident_apex_iff_outside (G : Multigraph V E) (U : Finset V)
    (e : RetainedEdge G U) :
    Sum.inr () ∈ (contract G U).edge e ↔ ∃ v, v ∈ G.edge e.val ∧ v ∉ U := by
  rw [contract_edge, Sym2.mem_map]
  simp only [vertexMap_eq_apex_iff]

@[simp] theorem card_vertex (U : Finset V) : Fintype.card (Vertex U) = U.card + 1 := by
  simp [Vertex]

/-- The edge embedding of an actual simple core survives the contraction. -/
noncomputable def coreEdgeMap {G : Multigraph V E} {U : Finset V}
    (C : SmallCuts.Core G U) : C.graph.edgeSet ↪ RetainedEdge G U where
  toFun e := ⟨C.edgeMap e, by
    refine ⟨e.val.out.1, ?_⟩
    rw [C.map_edge]
    exact Sym2.mem_map.mpr ⟨e.val.out.1, e.val.out_fst_mem, rfl⟩⟩
  inj' := by
    intro e f h
    exact C.edgeMap.injective (congrArg Subtype.val h)

@[simp] theorem coreEdgeMap_val {G : Multigraph V E} {U : Finset V}
    (C : SmallCuts.Core G U) (e : C.graph.edgeSet) :
    (coreEdgeMap C e).val = C.edgeMap e := rfl

theorem coreEdgeMap_edge {G : Multigraph V E} {U : Finset V}
    (C : SmallCuts.Core G U) (e : C.graph.edgeSet) :
    (contract G U).edge (coreEdgeMap C e) =
      Sym2.map (Sum.inl : U → Vertex U) e.val := by
  rw [contract_edge, coreEdgeMap_val, C.map_edge, Sym2.map_map]
  have hmap : vertexMap U ∘ (Subtype.val : U → V) = (Sum.inl : U → Vertex U) := by
    funext u
    exact vertexMap_core U u
  rw [hmap]

/-- The actual core vertex set in the contracted host. -/
noncomputable def coreVertices (U : Finset V) : Finset (Vertex U) :=
  univ.image (Sum.inl : U → Vertex U)

@[simp] theorem inl_mem_coreVertices (U : Finset V) (u : U) :
    Sum.inl u ∈ coreVertices U := by
  simp [coreVertices]

@[simp] theorem apex_not_mem_coreVertices (U : Finset V) :
    Sum.inr () ∉ coreVertices U := by
  simp [coreVertices]

@[simp] theorem coreVertices_card (U : Finset V) : (coreVertices U).card = U.card := by
  rw [coreVertices, Finset.card_image_of_injective _ Sum.inl_injective]
  simp

theorem coreVertices_compl (U : Finset V) :
    (coreVertices U)ᶜ = {Sum.inr ()} := by
  ext v
  rcases v with u | u
  · simp
  · cases u
    simp

/-- The original core and its actual vertex set after contraction are bijective. -/
noncomputable def coreEquiv (U : Finset V) : U ≃ ↥(coreVertices U) :=
  Equiv.ofBijective (fun u => ⟨Sum.inl u, inl_mem_coreVertices U u⟩) (by
    constructor
    · intro u v h
      exact Sum.inl_injective (congrArg Subtype.val h)
    · rintro ⟨v, hv⟩
      obtain ⟨u, _hu, rfl⟩ := Finset.mem_image.mp hv
      exact ⟨u, rfl⟩)

@[simp] theorem coreEquiv_apply_val (U : Finset V) (u : U) :
    (coreEquiv U u).val = Sum.inl u := rfl

@[simp] theorem coreEquiv_symm_val (U : Finset V) (u : coreVertices U) :
    Sum.inl ((coreEquiv U).symm u) = u.val := by
  exact congrArg Subtype.val ((coreEquiv U).apply_symm_apply u)

/-- The original simple core, embedded into the actual contracted vertex set. -/
noncomputable def contractCore {G : Multigraph V E} {U : Finset V}
    (C : SmallCuts.Core G U) : SmallCuts.Core (contract G U) (coreVertices U) where
  graph := C.graph.comap (coreEquiv U).symm
  edgeMap := (SimpleGraph.Iso.comap (coreEquiv U).symm C.graph).mapEdgeSet.toEmbedding.trans
    (coreEdgeMap C)
  map_edge e := by
    rw [Function.Embedding.trans_apply, coreEdgeMap_edge]
    change Sym2.map (Sum.inl : U → Vertex U)
      (Sym2.map (coreEquiv U).symm e.val) = Sym2.map Subtype.val e.val
    rw [Sym2.map_map]
    congr 1
    funext u
    exact coreEquiv_symm_val U u

@[simp] theorem contractCore_graph {G : Multigraph V E} {U : Finset V}
    (C : SmallCuts.Core G U) :
    (contractCore C).graph = C.graph.comap (coreEquiv U).symm := rfl

noncomputable instance contractCoreAdjDecidable {G : Multigraph V E} {U : Finset V}
    (C : SmallCuts.Core G U) [DecidableRel C.graph.Adj] :
    DecidableRel (contractCore C).graph.Adj :=
  inferInstanceAs (DecidableRel (C.graph.comap (coreEquiv U).symm).Adj)

theorem contractCore_degree {G : Multigraph V E} {U : Finset V}
    (C : SmallCuts.Core G U) [DecidableRel C.graph.Adj] (u : coreVertices U) :
    (contractCore C).graph.degree u = C.graph.degree ((coreEquiv U).symm u) := by
  exact RobustRealization.comap_equiv_degree C.graph (coreEquiv U).symm u

/-- Relabeling the core loses neither expansion nor its robust parameters. -/
theorem contractCore_robust {G : Multigraph V E} {U : Finset V}
    (C : SmallCuts.Core G U) [DecidableRel C.graph.Adj] (ν τ : ℝ)
    (hC : IsRobustExpander C.graph ν τ) :
    IsRobustExpander (contractCore C).graph ν τ := by
  exact RobustRealization.robust_comap_equiv C.graph (coreEquiv U).symm ν τ hC

theorem even_contracted_order (U : Finset V) (hodd : Odd U.card) :
    Even (Fintype.card (Vertex U)) := by
  obtain ⟨m, hm⟩ := hodd
  refine ⟨m + 1, ?_⟩
  rw [card_vertex, hm]
  omega

section FiniteEdges

variable [Fintype E]

/-- The apex is incident exactly with the original boundary edge copies. -/
@[simp] theorem incident_apex_iff (G : Multigraph V E) (U : Finset V)
    (e : RetainedEdge G U) :
    Sum.inr () ∈ (contract G U).edge e ↔ e.val ∈ G.cutEdges U := by
  rw [incident_apex_iff_outside, G.mem_cutEdges]
  have hret := retained_endpoints G U e
  constructor
  · rintro ⟨v, hv, hout⟩
    rcases (G.incident_iff e.val v).mp hv with h | h
    · have hn : G.firstEnd e.val ∉ U := h ▸ hout
      tauto
    · have hn : G.secondEnd e.val ∉ U := h ▸ hout
      tauto
  · intro hcut
    by_cases hfirst : G.firstEnd e.val ∈ U
    · refine ⟨G.secondEnd e.val, ?_, ?_⟩
      · rw [← G.edge_eq e.val]; simp
      · tauto
    · refine ⟨G.firstEnd e.val, ?_, hfirst⟩
      rw [← G.edge_eq e.val]; simp

theorem retained_of_boundary (G : Multigraph V E) (U : Finset V)
    {e : E} (he : e ∈ G.cutEdges U) : ∃ u : U, u.val ∈ G.edge e := by
  obtain ⟨v, w, hedge, hv, _hw⟩ := (G.mem_cutEdges_iff U e).mp he
  refine ⟨⟨v, hv⟩, ?_⟩
  rw [hedge]
  simp

/-- Regard a boundary edge copy as a retained edge, without changing its identity. -/
def boundaryLift (G : Multigraph V E) (U : Finset V)
    (e : G.cutEdges U) : RetainedEdge G U :=
  ⟨e.val, retained_of_boundary G U e.property⟩

@[simp] theorem boundaryLift_val (G : Multigraph V E) (U : Finset V)
    (e : G.cutEdges U) : (boundaryLift G U e).val = e.val := rfl

/-- Original boundary copies correspond bijectively to apex incidences. -/
noncomputable def boundaryApexEquiv (G : Multigraph V E) (U : Finset V) :
    ↥(G.cutEdges U) ≃ ↥((contract G U).incidenceEdges (Sum.inr ())) where
  toFun e := ⟨boundaryLift G U e, by
    simpa only [Multigraph.mem_incidenceEdges, incident_apex_iff, boundaryLift_val]
      using e.property⟩
  invFun e := ⟨e.val.val, by
    simpa only [Multigraph.mem_incidenceEdges, incident_apex_iff] using e.property⟩
  left_inv _ := by rfl
  right_inv _ := by rfl

@[simp] theorem boundaryApexEquiv_val (G : Multigraph V E) (U : Finset V)
    (e : G.cutEdges U) : (boundaryApexEquiv G U e).val = boundaryLift G U e := rfl

/-- The incidence correspondence at each core vertex preserves edge copies. -/
noncomputable def coreIncidenceEquiv (G : Multigraph V E) (U : Finset V) (u : U) :
    ↥(G.incidenceEdges u.val) ≃ ↥((contract G U).incidenceEdges (Sum.inl u)) where
  toFun e := ⟨⟨e.val, ⟨u, (G.mem_incidenceEdges u.val e.val).mp e.property⟩⟩, by
    simpa only [Multigraph.mem_incidenceEdges, incident_inl_iff] using e.property⟩
  invFun e := ⟨e.val.val, by
    simpa only [Multigraph.mem_incidenceEdges, incident_inl_iff] using e.property⟩
  left_inv _ := by rfl
  right_inv _ := by rfl

/-- Every core degree is preserved exactly, counting parallel copies. -/
@[simp] theorem degree_inl (G : Multigraph V E) (U : Finset V) (u : U) :
    (contract G U).degree (Sum.inl u) = G.degree u.val := by
  have h := Fintype.card_congr (coreIncidenceEquiv G U u)
  simpa only [Fintype.card_coe, Multigraph.degree] using h.symm

/-- The apex degree is the number of original boundary copies. -/
@[simp] theorem degree_apex (G : Multigraph V E) (U : Finset V) :
    (contract G U).degree (Sum.inr ()) = (G.cutEdges U).card := by
  have h := Fintype.card_congr (boundaryApexEquiv G U)
  simpa only [Fintype.card_coe, Multigraph.degree] using h.symm

theorem degree_apex_eq_cutSize (G : Multigraph V E) (U : Finset V) :
    (contract G U).degree (Sum.inr ()) = G.cutSize U := degree_apex G U

@[simp] theorem retainedGraph_degree_core (G : Multigraph V E) (U : Finset V)
    (u : U) : (retainedGraph G U).degree u.val = G.degree u.val := by
  have hsets : (retainedGraph G U).incidenceEdges u.val =
      (contract G U).incidenceEdges (Sum.inl u) := by
    ext e
    simp only [Multigraph.mem_incidenceEdges, retainedGraph_edge, incident_inl_iff]
  rw [Multigraph.degree, hsets]
  exact degree_inl G U u

/-- Core regularity and the boundary count certify regularity after contraction. -/
theorem contract_regular (G : Multigraph V E) (U : Finset V) (h : ℕ)
    (hcore : ∀ u : U, G.degree u.val = h) (hboundary : G.cutSize U = h) :
    ∀ v, (contract G U).degree v = h := by
  rintro (u | ⟨⟩)
  · exact (degree_inl G U u).trans (hcore u)
  · exact (degree_apex_eq_cutSize G U).trans hboundary

end FiniteEdges

end Overfull.BoundaryExtension
