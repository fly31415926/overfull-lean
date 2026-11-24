import Overfull.NativeTerminal.ShoreHost

/-!
# Embedded old cores inside larger shores

A terminal shore can include assigned exceptional vertices in addition to
its old robust core.  Both the induced host and the apex contraction retain
the exact simple core with its original edge-copy embedding.
-/

noncomputable section

namespace Overfull.NativeTerminal

open Finset Classical SmallCuts BoundaryExtension Multigraph

variable {V E : Type*} [Fintype E] {G : Multigraph V E} {A U : Finset V}

/-- The old core, viewed among the actual vertices of the larger shore. -/
def inducedCoreEquiv (hUA : U ⊆ A) : U ≃ inducedCoreVertices A U where
  toFun u := ⟨⟨u.val,hUA u.property⟩, (mem_shore A U _).mpr u.property⟩
  invFun u := ⟨u.val.val,(mem_shore A U _).mp u.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem inducedCoreEquiv_val (hUA : U ⊆ A) (u : U) :
    (inducedCoreEquiv hUA u).val.val = u.val := rfl

@[simp] theorem inducedCoreEquiv_symm_val (hUA : U ⊆ A)
    (u : inducedCoreVertices A U) :
    ((inducedCoreEquiv hUA).symm u).val = u.val.val := rfl

def inducedCoreEdgeMap (C : Core G U) (hUA : U ⊆ A) :
    C.graph.edgeSet ↪ G.internalEdges A where
  toFun e := ⟨C.edgeMap e, by
    have hsub : (G.edge (C.edgeMap e)).toFinset ⊆ A := by
      intro v hv
      rw [C.map_edge] at hv
      obtain ⟨u, _hu, rfl⟩ := Sym2.mem_map.mp (Sym2.mem_toFinset.mp hv)
      exact hUA u.property
    exact mem_filter.mpr ⟨mem_univ _,hsub⟩⟩
  inj' := fun _ _ h => C.edgeMap.injective (congrArg Subtype.val h)

@[simp] theorem inducedCoreEdgeMap_val (C : Core G U) (hUA : U ⊆ A)
    (e : C.graph.edgeSet) : (inducedCoreEdgeMap C hUA e).val = C.edgeMap e := rfl

/-- The same old simple core embedded into the actual induced shore. -/
def inducedCore (C : Core G U) (hUA : U ⊆ A) :
    Core (inducedHost G A) (inducedCoreVertices A U) where
  graph := C.graph.comap (inducedCoreEquiv hUA).symm
  edgeMap := (SimpleGraph.Iso.comap (inducedCoreEquiv hUA).symm C.graph).mapEdgeSet.toEmbedding.trans
    (inducedCoreEdgeMap C hUA)
  map_edge e := by
    apply Sym2.map.injective (Subtype.val_injective (p := fun v => v ∈ A))
    rw [Function.Embedding.trans_apply, inducedHost_edge_map, inducedCoreEdgeMap_val, C.map_edge]
    change Sym2.map (Subtype.val : U → V)
      (Sym2.map (inducedCoreEquiv hUA).symm e.val) =
        Sym2.map (Subtype.val : A → V) (Sym2.map Subtype.val e.val)
    rw [Sym2.map_map, Sym2.map_map]
    rfl

theorem inducedCore_degree (C : Core G U) (hUA : U ⊆ A)
    (u : inducedCoreVertices A U) :
    (inducedCore C hUA).graph.degree u =
      C.graph.degree ((inducedCoreEquiv hUA).symm u) := by
  exact RobustRealization.comap_equiv_degree C.graph (inducedCoreEquiv hUA).symm u

theorem inducedCore_robust (C : Core G U) (hUA : U ⊆ A) (ν τ : ℝ)
    (hrob : IsRobustExpander C.graph ν τ) :
    IsRobustExpander (inducedCore C hUA).graph ν τ :=
  RobustRealization.robust_comap_equiv C.graph (inducedCoreEquiv hUA).symm ν τ hrob

/-- The old core's actual vertex set in the apex contraction of its larger shore. -/
def contractedCoreVertices (A U : Finset V) : Finset (Vertex A) :=
  (inducedCoreVertices A U).image Sum.inl

@[simp] theorem inl_mem_contractedCoreVertices (A U : Finset V) (u : A) :
    Sum.inl u ∈ contractedCoreVertices A U ↔ u.val ∈ U := by
  simp [contractedCoreVertices, mem_shore]

@[simp] theorem apex_not_mem_contractedCoreVertices (A U : Finset V) :
    Sum.inr () ∉ contractedCoreVertices A U := by
  simp [contractedCoreVertices]

@[simp] theorem vertexMap_mem_contractedCoreVertices (A U : Finset V) (v : V) :
    vertexMap A v ∈ contractedCoreVertices A U ↔ v ∈ A ∧ v ∈ U := by
  by_cases hv : v ∈ A <;> simp [vertexMap, hv]

theorem contractedCoreVertices_card (hUA : U ⊆ A) :
    (contractedCoreVertices A U).card = U.card := by
  rw [contractedCoreVertices, card_image_of_injective _ Sum.inl_injective,
    inducedCoreVertices_card A U hUA]

theorem contractedCoreVertices_compl_card (hUA : U ⊆ A) :
    (contractedCoreVertices A U)ᶜ.card = (A \ U).card + 1 := by
  rw [card_compl, card_vertex, contractedCoreVertices_card hUA,
    card_sdiff_of_subset hUA]
  have hle := card_le_card hUA
  omega

def contractedCoreEquiv (hUA : U ⊆ A) : U ≃ contractedCoreVertices A U :=
  Equiv.ofBijective (fun u => ⟨Sum.inl ⟨u.val,hUA u.property⟩,
    (inl_mem_contractedCoreVertices A U _).mpr u.property⟩) (by
    constructor
    · intro u v h
      exact Subtype.ext (congrArg Subtype.val (Sum.inl_injective (congrArg Subtype.val h)))
    · rintro ⟨v,hv⟩
      rcases v with a | ⟨⟩
      · exact ⟨⟨a.val,(inl_mem_contractedCoreVertices A U a).mp hv⟩,rfl⟩
      · exact (apex_not_mem_contractedCoreVertices A U hv).elim)

@[simp] theorem contractedCoreEquiv_apply_val (hUA : U ⊆ A) (u : U) :
    (contractedCoreEquiv hUA u).val = Sum.inl ⟨u.val,hUA u.property⟩ := rfl

theorem contractedCoreEquiv_symm_map (hUA : U ⊆ A)
    (u : contractedCoreVertices A U) :
    vertexMap A ((contractedCoreEquiv hUA).symm u).val = u.val := by
  have hh := congrArg Subtype.val ((contractedCoreEquiv hUA).apply_symm_apply u)
  rw [contractedCoreEquiv_apply_val] at hh
  rw [vertexMap, dif_pos (hUA ((contractedCoreEquiv hUA).symm u).property)]
  exact hh

def contractedCoreEdgeMap (C : Core G U) (hUA : U ⊆ A) :
    C.graph.edgeSet ↪ RetainedEdge G A where
  toFun e := ⟨C.edgeMap e, by
    refine ⟨⟨e.val.out.1.val,hUA e.val.out.1.property⟩,?_⟩
    rw [C.map_edge]
    exact Sym2.mem_map.mpr ⟨e.val.out.1,e.val.out_fst_mem,rfl⟩⟩
  inj' := fun _ _ h => C.edgeMap.injective (congrArg Subtype.val h)

@[simp] theorem contractedCoreEdgeMap_val (C : Core G U) (hUA : U ⊆ A)
    (e : C.graph.edgeSet) : (contractedCoreEdgeMap C hUA e).val = C.edgeMap e := rfl

/-- A smaller old core survives contraction of the larger shore's complement. -/
def contractedCore (C : Core G U) (hUA : U ⊆ A) :
    Core (contract G A) (contractedCoreVertices A U) where
  graph := C.graph.comap (contractedCoreEquiv hUA).symm
  edgeMap := (SimpleGraph.Iso.comap (contractedCoreEquiv hUA).symm C.graph).mapEdgeSet.toEmbedding.trans
    (contractedCoreEdgeMap C hUA)
  map_edge e := by
    rw [Function.Embedding.trans_apply, contract_edge, contractedCoreEdgeMap_val, C.map_edge]
    change Sym2.map (vertexMap A) (Sym2.map (Subtype.val : U → V)
      (Sym2.map (contractedCoreEquiv hUA).symm e.val)) = Sym2.map Subtype.val e.val
    rw [Sym2.map_map, Sym2.map_map]
    congr 1
    funext u
    exact contractedCoreEquiv_symm_map hUA u

theorem contractedCore_degree (C : Core G U) (hUA : U ⊆ A)
    (u : contractedCoreVertices A U) :
    (contractedCore C hUA).graph.degree u =
      C.graph.degree ((contractedCoreEquiv hUA).symm u) :=
  RobustRealization.comap_equiv_degree C.graph (contractedCoreEquiv hUA).symm u

theorem contractedCore_robust (C : Core G U) (hUA : U ⊆ A) (ν τ : ℝ)
    (hrob : IsRobustExpander C.graph ν τ) :
    IsRobustExpander (contractedCore C hUA).graph ν τ :=
  RobustRealization.robust_comap_equiv C.graph (contractedCoreEquiv hUA).symm ν τ hrob

/-- Contracting the other shore keeps the exterior independent when every
crossing endpoint in this shore belongs to its old core. -/
theorem contractedHost_independent_exterior (G : Multigraph V E) (A U : Finset V)
    (hindependent : G.internalEdges (A \ U) = ∅)
    (hcross : ∀ e ∈ G.cutEdges A, ∀ v, v ∈ G.edge e → v ∈ A → v ∈ U) :
    (contract G A).internalEdges (contractedCoreVertices A U)ᶜ = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  have hends : ∀ v ∈ G.edge e.val, v ∈ A → v ∉ U := by
    intro v hv hvA hvU
    have hm := contract_incident_of_original G A e hv
    have he' := (mem_filter.mp he).2 (Sym2.mem_toFinset.mpr hm)
    exact (mem_compl.mp he') ((vertexMap_mem_contractedCoreVertices A U v).mpr ⟨hvA,hvU⟩)
  have hf := (G.incident_iff e.val (G.firstEnd e.val)).mpr (Or.inl rfl)
  have hs := (G.incident_iff e.val (G.secondEnd e.val)).mpr (Or.inr rfl)
  rcases retained_endpoints G A e with hfirst | hsecond
  · by_cases hsecond : G.secondEnd e.val ∈ A
    · have hi := (G.mem_internalEdges (A \ U) e.val).mpr
        ⟨mem_sdiff.mpr ⟨hfirst,hends _ hf hfirst⟩,
          mem_sdiff.mpr ⟨hsecond,hends _ hs hsecond⟩⟩
      rw [hindependent] at hi
      exact notMem_empty e.val hi
    · have hc := (G.mem_cutEdges A e.val).mpr (by simp only [hfirst,hsecond]; decide)
      exact hends _ hf hfirst (hcross _ hc _ hf hfirst)
  · by_cases hfirst : G.firstEnd e.val ∈ A
    · have hi := (G.mem_internalEdges (A \ U) e.val).mpr
        ⟨mem_sdiff.mpr ⟨hfirst,hends _ hf hfirst⟩,
          mem_sdiff.mpr ⟨hsecond,hends _ hs hsecond⟩⟩
      rw [hindependent] at hi
      exact notMem_empty e.val hi
    · have hc := (G.mem_cutEdges A e.val).mpr (by simp only [hfirst,hsecond]; decide)
      exact hends _ hs hsecond (hcross _ hc _ hs hsecond)

end Overfull.NativeTerminal
