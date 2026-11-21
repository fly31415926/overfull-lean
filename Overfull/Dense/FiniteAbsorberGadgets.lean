import Overfull.Dense.FiniteAbsorberFamily
import Overfull.Dense.FiniteAbsorberCycles
import Overfull.Dense.TripartiteTriangleBridge

/-!
# Actual cycle gadgets and their two decompositions

The already verified cycle template is embedded in the actual host. Its
decompositions are transferred to finite sets of actual tripartite triangles.
-/

namespace Overfull.Dense.FiniteAbsorber

open Finset Classical
open TripartiteGraph

variable {A B W : Type*} [Fintype A] [Fintype B] [Fintype W]
variable (G : TripartiteGraph A B W)

/-- A cycle gadget together with its exact combinatorial guarantees. -/
structure Gadget {ℓ : ℕ} (C : Cycle G ℓ)
    (U Z : Finset (HostVertex (A := A) (B := B) (W := W))) where
  edges : Finset (EdgePosition (A := A) (B := B) (W := W))
  aux : Finset (HostVertex (A := A) (B := B) (W := W))
  edge_card : edges.card ≤ 9*ℓ
  aux_card : aux.card = 2*ℓ+1
  subgraph : edges ⊆ G.edgeFinset
  outside : ∀ v ∈ aux, v ∉ Z
  support : ∀ e ∈ edges, ∀ v ∈ edgePair e, v ∈ U ∨ v ∈ aux
  meets : ∀ e ∈ edges, ∃ v ∈ edgePair e, v ∈ aux
  default : ∃ T : Finset G.Triangle, G.IsTriangleDecomposition T edges
  activated : ∃ T : Finset G.Triangle,
    G.IsTriangleDecomposition T (edges ∪ (C.graph G).edgeFinset)

omit [Fintype A] [Fintype B] [Fintype W] in
theorem Placement.vertexMap_aux {ℓ : ℕ} {C : Cycle G ℓ}
    {Z : Finset (HostVertex (A := A) (B := B) (W := W))} (P : Placement G C Z)
    (v : CycleAbsorber.Vertex ℓ) (hv : CycleAbsorber.IsAuxiliary v) :
    P.vertexMap G v ∈ P.auxVertices G := by
  cases v <;> simp [CycleAbsorber.IsAuxiliary,Placement.vertexMap,
    Placement.auxVertices] at *

/-- Every placement gives an actual gadget, with precisely its selected
auxiliary vertices and with both required triangle decompositions. -/
theorem gadget_of_placement {ℓ : ℕ} (C : Cycle G ℓ) (hℓ : 0 < ℓ)
    (U Z : Finset (HostVertex (A := A) (B := B) (W := W)))
    (hUZ : U ⊆ Z) (hx : ∀ j, Sum.inl (C.x j) ∈ U)
    (hy : ∀ j, Sum.inr (Sum.inl (C.y j)) ∈ U)
    (hw : ∀ j, Sum.inr (Sum.inr (C.w j)) ∈ U)
    (P : Placement G C Z) :
    ∃ Q : Gadget G C U Z, Q.aux = P.auxVertices G := by
  let f := P.embedding G (fun j => hUZ (hx j)) (fun j => hUZ (hy j))
    (fun j => hUZ (hw j))
  let H := (CycleAbsorber.absorberGraph ℓ).map f
  let K := (CycleAbsorber.cycleGraph ℓ).map f
  obtain ⟨hH,hK,_,hDefault,hActivated,_,_,_⟩ :=
    CycleAbsorber.in_host G.toSimpleGraph hℓ f
      (P.edges_in_host G (fun j => hUZ (hx j)) (fun j => hUZ (hy j))
        (fun j => hUZ (hw j)))
  let E := univ.filter (fun e => edgePair e ∈ H.edgeSet)
  have hE (e) : e ∈ E ↔ edgePair e ∈ H.edgeSet := by simp [E]
  have hcycleEdge (p : Fin 3 × Fin ℓ) :
      edgePair (C.edgePosition G p) = Sym2.map f (CycleAbsorber.cycleEdge p) := by
    rcases p with ⟨i,j⟩
    fin_cases i <;> simp [edgePair,Cycle.edgePosition,abPos,awPos,bwPos,
      CycleAbsorber.cycleEdge,f,Placement.embedding,Placement.vertexMap,Sym2.eq_swap]
  have hcycle (e) : edgePair e ∈ K.edgeSet ↔ e ∈ (C.graph G).edgeFinset := by
    rw [C.edgeFinset_eq G]
    simp only [K,SimpleGraph.edgeSet_map,CycleAbsorber.cycleGraph_edgeSet,
      Set.mem_image,Finset.mem_coe]
    constructor
    · rintro ⟨u,hu,he⟩
      obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hu
      exact Finset.mem_image.mpr ⟨p,Finset.mem_univ _,
        edgePair_injective ((hcycleEdge p).trans he)⟩
    · intro he
      obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp he
      exact ⟨CycleAbsorber.cycleEdge p,
        Finset.mem_image.mpr ⟨p,Finset.mem_univ _,rfl⟩,(hcycleEdge p).symm⟩
  obtain ⟨T,hT⟩ := G.decomposition_of_simpleGraph H _ hH hDefault E hE
  obtain ⟨S,hS⟩ := G.decomposition_of_simpleGraph (H ⊔ K) _ (sup_le hH hK)
    hActivated (E ∪ (C.graph G).edgeFinset) (by
      intro e
      rw [Finset.mem_union,SimpleGraph.edgeSet_sup,Set.mem_union,hE,hcycle])
  have hEdgeImage : H.edgeSet =
      (((CycleAbsorber.absorberEdges ℓ).image (Sym2.map f)) : Set (Sym2 (HostVertex
        (A := A) (B := B) (W := W)))) := by
    simp only [H,SimpleGraph.edgeSet_map,CycleAbsorber.absorberGraph_edgeSet,
      Finset.coe_image]
    rfl
  have hcount : E.card ≤ 9*ℓ := by
    calc
      E.card ≤ ((CycleAbsorber.absorberEdges ℓ).image (Sym2.map f)).card := by
        apply Finset.card_le_card_of_injOn edgePair
        · intro e he
          exact hEdgeImage ▸ (hE e).mp he
        · exact edgePair_injective.injOn
      _ = 9*ℓ := by rw [Finset.card_image_of_injective _
          (Sym2.map.injective f.injective),CycleAbsorber.absorberEdges_card]
  have hclass (v : CycleAbsorber.Vertex ℓ) : f v ∈ U ∨ f v ∈ P.auxVertices G := by
    cases v with
    | x j => exact Or.inl (hx j)
    | y j => exact Or.inl (hy j)
    | w j => exact Or.inl (hw j)
    | xAux j => exact Or.inr (P.vertexMap_aux G (.xAux j) trivial)
    | yAux j => exact Or.inr (P.vertexMap_aux G (.yAux j) trivial)
    | center => exact Or.inr (P.vertexMap_aux G .center trivial)
  refine ⟨{
    edges := E
    aux := P.auxVertices G
    edge_card := hcount
    aux_card := P.auxVertices_card G
    subgraph := ?_
    outside := P.auxVertices_outside G
    support := ?_
    meets := ?_
    default := ⟨T,hT⟩
    activated := ⟨S,hS⟩ },rfl⟩
  · intro e he
    apply (G.mem_edgeFinset e).mpr
    apply (edgePair_mem G e).mp
    exact SimpleGraph.edgeSet_mono hH ((hE e).mp he)
  · intro e he v hv
    have heH := (hE e).mp he
    rw [hEdgeImage] at heH
    obtain ⟨u,_,hu⟩ := Finset.mem_image.mp heH
    rw [← hu] at hv
    obtain ⟨x,_,rfl⟩ := Sym2.mem_map.mp hv
    exact hclass x
  · intro e he
    have heH := (hE e).mp he
    rw [hEdgeImage] at heH
    obtain ⟨u,hu,heq⟩ := Finset.mem_image.mp heH
    obtain ⟨v,hvu,hvaux⟩ := CycleAbsorber.every_edge_has_auxiliary_endpoint hu
    refine ⟨f v,?_,P.vertexMap_aux G v ((CycleAbsorber.mem_auxiliaryVertices v).mp hvaux)⟩
    rw [← heq]
    exact Sym2.mem_map.mpr ⟨v,hvu,rfl⟩

end Overfull.Dense.FiniteAbsorber
