import Overfull.Terminal.CentralMatchings

/-! Both even cores embed in the central graph on their union and two apices. -/

noncomputable section

namespace Overfull.TerminalFourTwoOdd

open Finset Classical Multigraph SmallCuts Terminal

variable {V E : Type*}

def keptVertex {S W : Finset V} (hWS : W ⊆ S) (w : W) : CentralVertex S :=
  Sum.inl ⟨w.val, hWS w.property⟩

theorem keptVertex_injective {S W : Finset V} (hWS : W ⊆ S) :
    Function.Injective (keptVertex hWS) := by
  intro u v h
  exact Subtype.ext (congrArg (fun z : S => z.val) (Sum.inl_injective h))

def keptSet {S W : Finset V} (hWS : W ⊆ S) : Finset (CentralVertex S) :=
  univ.image (keptVertex hWS)

@[simp] theorem keptSet_card {S W : Finset V} (hWS : W ⊆ S) :
    (keptSet hWS).card = W.card := by
  rw [keptSet, card_image_of_injective _ (keptVertex_injective hWS)]
  simp

@[simp] theorem inl_mem_keptSet {S W : Finset V} (hWS : W ⊆ S) (u : S) :
    Sum.inl u ∈ keptSet hWS ↔ u.val ∈ W := by
  constructor
  · intro h
    obtain ⟨w, _, hw⟩ := mem_image.mp h
    exact (congrArg Subtype.val (Sum.inl_injective hw)) ▸ w.property
  · intro h
    exact mem_image.mpr ⟨⟨u.val,h⟩,mem_univ _,congrArg Sum.inl (Subtype.ext rfl)⟩

@[simp] theorem apex_not_mem_keptSet {S W : Finset V} (hWS : W ⊆ S) (i : Fin 2) :
    Sum.inr i ∉ keptSet hWS := by
  simp [keptSet, keptVertex]

theorem centralMap_mem_keptSet {S W : Finset V} (hWS : W ⊆ S)
    (A : Finset V) (v : V) : centralMap S A v ∈ keptSet hWS ↔ v ∈ W := by
  by_cases hv : v ∈ S
  · rw [show centralMap S A v = Sum.inl (⟨v,hv⟩ : S) from centralMap_core S A ⟨v,hv⟩]
    exact inl_mem_keptSet hWS ⟨v,hv⟩
  · have hn : v ∉ W := fun hw => hv (hWS hw)
    by_cases ha : v ∈ A <;> simp [centralMap,hv,ha,hn]

def keptEquiv {S W : Finset V} (hWS : W ⊆ S) : W ≃ ↥(keptSet hWS) :=
  Equiv.ofBijective (fun w => ⟨keptVertex hWS w,mem_image.mpr ⟨w,mem_univ _,rfl⟩⟩) (by
    constructor
    · intro u v h
      exact keptVertex_injective hWS (congrArg Subtype.val h)
    · rintro ⟨v,hv⟩
      obtain ⟨w,_,rfl⟩ := mem_image.mp hv
      exact ⟨w,rfl⟩)

theorem keptEquiv_symm_val {S W : Finset V} (hWS : W ⊆ S) (v : keptSet hWS) :
    keptVertex hWS ((keptEquiv hWS).symm v) = v.val :=
  congrArg Subtype.val ((keptEquiv hWS).apply_symm_apply v)

def keptCoreEdgeMap {G : Multigraph V E} {S W : Finset V} (hWS : W ⊆ S)
    (C : Core G W) (A : Finset V) : C.graph.edgeSet ↪ CentralEdge G S A where
  toFun e := ⟨C.edgeMap e,central_retained_of_core_incident G S A
    (hWS e.val.out.1.property) (by
      rw [C.map_edge]
      exact Sym2.mem_map.mpr ⟨e.val.out.1,e.val.out_fst_mem,rfl⟩)⟩
  inj' := by
    intro e f h
    exact C.edgeMap.injective (congrArg Subtype.val h)

theorem keptCoreEdgeMap_edge {G : Multigraph V E} {S W : Finset V} (hWS : W ⊆ S)
    (C : Core G W) (A : Finset V) (e : C.graph.edgeSet) :
    (centralGraph G S A).edge (keptCoreEdgeMap hWS C A e) =
      Sym2.map (keptVertex hWS) e.val := by
  rw [centralGraph_edge]
  change Sym2.map (centralMap S A) (G.edge (C.edgeMap e)) = _
  rw [C.map_edge,Sym2.map_map]
  congr 1
  funext w
  exact centralMap_core S A ⟨w.val,hWS w.property⟩

def keptCore {G : Multigraph V E} {S W : Finset V} (hWS : W ⊆ S)
    (C : Core G W) (A : Finset V) : Core (centralGraph G S A) (keptSet hWS) where
  graph := C.graph.comap (keptEquiv hWS).symm
  edgeMap := (SimpleGraph.Iso.comap (keptEquiv hWS).symm C.graph).mapEdgeSet.toEmbedding.trans
    (keptCoreEdgeMap hWS C A)
  map_edge e := by
    rw [Function.Embedding.trans_apply,keptCoreEdgeMap_edge]
    change Sym2.map (keptVertex hWS) (Sym2.map (keptEquiv hWS).symm e.val) =
      Sym2.map Subtype.val e.val
    rw [Sym2.map_map]
    congr 1
    funext v
    exact keptEquiv_symm_val hWS v

instance keptCoreAdjDecidable {G : Multigraph V E} {S W : Finset V} (hWS : W ⊆ S)
    (C : Core G W) (A : Finset V) [DecidableRel C.graph.Adj] :
    DecidableRel (keptCore hWS C A).graph.Adj :=
  inferInstanceAs (DecidableRel (C.graph.comap (keptEquiv hWS).symm).Adj)

theorem keptCore_degree {G : Multigraph V E} {S W : Finset V} (hWS : W ⊆ S)
    (C : Core G W) (A : Finset V) [DecidableRel C.graph.Adj] (v : keptSet hWS) :
    (keptCore hWS C A).graph.degree v = C.graph.degree ((keptEquiv hWS).symm v) :=
  RobustRealization.comap_equiv_degree C.graph (keptEquiv hWS).symm v

theorem keptCore_robust {G : Multigraph V E} {S W : Finset V} (hWS : W ⊆ S)
    (C : Core G W) (A : Finset V) [DecidableRel C.graph.Adj] (ν τ : ℝ)
    (hC : IsRobustExpander C.graph ν τ) :
    IsRobustExpander (keptCore hWS C A).graph ν τ :=
  RobustRealization.robust_comap_equiv C.graph (keptEquiv hWS).symm ν τ hC

theorem keptSet_disjoint {S U W : Finset V} (hUS : U ⊆ S) (hWS : W ⊆ S)
    (hUW : Disjoint U W) : Disjoint (keptSet hUS) (keptSet hWS) := by
  apply disjoint_left.mpr
  rintro (u | i) hu hw
  · exact disjoint_left.mp hUW ((inl_mem_keptSet hUS u).mp hu)
      ((inl_mem_keptSet hWS u).mp hw)
  · exact apex_not_mem_keptSet hUS i hu

def centralApices (S : Finset V) : Finset (CentralVertex S) :=
  univ.image (Sum.inr : Fin 2 → CentralVertex S)

@[simp] theorem centralApices_card (S : Finset V) : (centralApices S).card = 2 := by
  rw [centralApices,card_image_of_injective _ Sum.inr_injective]
  simp

@[simp] theorem centralApices_inl (S : Finset V) (u : S) :
    Sum.inl u ∉ centralApices S := by simp [centralApices]

@[simp] theorem centralApices_inr (S : Finset V) (i : Fin 2) :
    Sum.inr i ∈ centralApices S := by simp [centralApices]

theorem keptSet_disjoint_apices {S W : Finset V} (hWS : W ⊆ S) :
    Disjoint (keptSet hWS) (centralApices S) := by
  apply disjoint_left.mpr
  rintro (u | i) h hZ
  · exact centralApices_inl S u hZ
  · exact apex_not_mem_keptSet hWS i h

theorem central_two_core_cover (U W : Finset V) (v : CentralVertex (U ∪ W)) :
    v ∈ keptSet (subset_union_left : U ⊆ U ∪ W) ∨
      v ∈ keptSet (subset_union_right : W ⊆ U ∪ W) ∨ v ∈ centralApices (U ∪ W) := by
  rcases v with u | i
  · rcases mem_union.mp u.property with hu | hw
    · exact Or.inl ((inl_mem_keptSet subset_union_left u).mpr hu)
    · exact Or.inr (Or.inl ((inl_mem_keptSet subset_union_right u).mpr hw))
  · exact Or.inr (Or.inr (centralApices_inr _ i))

end Overfull.TerminalFourTwoOdd
