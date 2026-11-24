import Overfull.Dense.FiniteAbsorber
import Mathlib.Combinatorics.SimpleGraph.Subgraph

/-!
# The finite absorber as a subgraph with its own vertex set

The vertex set is precisely the set of incident vertices. Thus the literal
subgraph vertex count agrees with the count in the finite absorber theorem;
isolated ambient labels are not counted as absorber vertices.
-/

namespace Overfull.Dense.FiniteAbsorber

open Finset Classical
open TripartiteGraph

variable {A B W : Type*} [Fintype A] [Fintype B] [Fintype W]
variable (G : TripartiteGraph A B W)

/-- The actual subgraph specified by the edge coordinates, with no added
isolated ambient vertices. -/
noncomputable def supportedSubgraph
    (E : Finset (EdgePosition (A := A) (B := B) (W := W)))
    (hE : E ⊆ G.edgeFinset) : G.toSimpleGraph.Subgraph where
  verts := (supportVertices E : Set (HostVertex (A := A) (B := B) (W := W)))
  Adj x y := s(x,y) ∈ E.image edgePair
  adj_sub := by
    intro x y hxy
    obtain ⟨e,he,heq⟩ := Finset.mem_image.mp hxy
    have hh := (edgePair_mem G e).mpr ((G.mem_edgeFinset e).mp (hE he))
    rw [heq] at hh
    exact hh
  edge_vert := by
    intro x y hxy
    obtain ⟨e,he,heq⟩ := Finset.mem_image.mp hxy
    apply (mem_supportVertices E x).mpr
    refine ⟨e,he,?_⟩
    rw [heq]
    simp
  symm := by
    intro x y hxy
    rwa [Sym2.eq_swap]

@[simp] theorem supportedSubgraph_verts
    (E : Finset (EdgePosition (A := A) (B := B) (W := W)))
    (hE : E ⊆ G.edgeFinset) :
    (supportedSubgraph G E hE).verts = (supportVertices E : Set (HostVertex
      (A := A) (B := B) (W := W))) := rfl

@[simp] theorem supportedSubgraph_edgeSet
    (E : Finset (EdgePosition (A := A) (B := B) (W := W)))
    (hE : E ⊆ G.edgeFinset) :
    (supportedSubgraph G E hE).edgeSet =
      (E.image edgePair : Set (Sym2 (HostVertex (A := A) (B := B) (W := W)))) := by
  ext e
  induction e using Sym2.ind with
  | _ x y => rfl

@[simp] theorem supportedSubgraph_mem_edgeSet
    (E : Finset (EdgePosition (A := A) (B := B) (W := W)))
    (hE : E ⊆ G.edgeFinset) (e : EdgePosition (A := A) (B := B) (W := W)) :
    edgePair e ∈ (supportedSubgraph G E hE).edgeSet ↔ e ∈ E := by
  rw [supportedSubgraph_edgeSet]
  simp [edgePair_injective.eq_iff]

theorem supportedSubgraph_edgeCount
    (E : Finset (EdgePosition (A := A) (B := B) (W := W)))
    (hE : E ⊆ G.edgeFinset) : (supportedSubgraph G E hE).edgeSet.ncard = E.card := by
  rw [supportedSubgraph_edgeSet,Set.ncard_coe_finset,
    Finset.card_image_of_injective _ edgePair_injective]

theorem supportedSubgraph_verts_eq_support
    (E : Finset (EdgePosition (A := A) (B := B) (W := W)))
    (hE : E ⊆ G.edgeFinset) :
    (supportedSubgraph G E hE).verts = (supportedSubgraph G E hE).support := by
  apply Set.Subset.antisymm ?_ (supportedSubgraph G E hE).support_subset_verts
  intro v hv
  obtain ⟨e,he,hve⟩ := (mem_supportVertices E v).mp hv
  have heH := (supportedSubgraph_mem_edgeSet G E hE e).mpr he
  change ∃ w, (supportedSubgraph G E hE).Adj v w
  generalize hp : edgePair e = p at hve heH
  induction p using Sym2.ind with
  | _ x y =>
    rcases Sym2.mem_iff.mp hve with rfl | rfl
    · exact ⟨y,heH⟩
    · exact ⟨x,(supportedSubgraph G E hE).symm heH⟩

/-- Actual edge coordinates of an actual subgraph of the tripartite host. -/
noncomputable def subgraphCoordinates (H : G.toSimpleGraph.Subgraph) :
    Finset (EdgePosition (A := A) (B := B) (W := W)) :=
  univ.filter (fun e => edgePair e ∈ H.edgeSet)

@[simp] theorem supportedSubgraph_coordinates
    (E : Finset (EdgePosition (A := A) (B := B) (W := W)))
    (hE : E ⊆ G.edgeFinset) : subgraphCoordinates G (supportedSubgraph G E hE) = E := by
  ext e
  simp only [subgraphCoordinates,Finset.mem_filter,Finset.mem_univ,true_and,
    supportedSubgraph_mem_edgeSet]

/-- Lemma 5.5 with a literal subgraph vertex set and the literal edge and
vertex counts appearing in the manuscript. -/
theorem finite_absorber_subgraph (h : ℕ) (η γ : ℝ) (hη : 0 < η) (hγ : 0 < γ) :
    ∃ N : ℕ, ∀ (A B W : Type*) [Fintype A] [Fintype B] [Fintype W]
      (G : TripartiteGraph A B W) (ε : ℝ),
      N ≤ Fintype.card A → Density G η γ ε →
      0 < ε → ε ≤ η/32 → 16*(h : ℝ)*ε ≤ γ →
      ∀ U Z : Finset (HostVertex (A := A) (B := B) (W := W)),
      U ⊆ Z → U.card ≤ h → (Z.card : ℝ) ≤ min η γ*Fintype.card A/16 →
      ∃ H : G.toSimpleGraph.Subgraph,
        H.verts = H.support ∧
        Disjoint H.edgeSet (((⊤ : G.toSimpleGraph.Subgraph).induce
          (Z : Set (HostVertex (A := A) (B := B) (W := W)))).edgeSet) ∧
        H.verts \ (U : Set (HostVertex (A := A) (B := B) (W := W))) ⊆
          (Z : Set (HostVertex (A := A) (B := B) (W := W)))ᶜ ∧
        H.edgeSet.ncard+(H.verts \ (U : Set (HostVertex
          (A := A) (B := B) (W := W)))).ncard ≤ 4*h^2*2^(h^2) ∧
        (∃ T : Finset G.Triangle, G.IsTriangleDecomposition T (subgraphCoordinates G H)) ∧
        ∀ L : TripartiteGraph A B W, L.edgeFinset ⊆ internalEdges G U →
          L.IsLocallyBalanced → ∃ T : Finset G.Triangle,
            G.IsTriangleDecomposition T (subgraphCoordinates G H ∪ L.edgeFinset) := by
  obtain ⟨N,hN⟩ := finite_absorber h η γ hη hγ
  refine ⟨N,?_⟩
  intro A B W _ _ _ G ε horder hG hεpos hε hεh U Z hUZ hU hZ
  obtain ⟨E,hEG,hdis,houtside,hsize,hdefault,habsorb⟩ :=
    hN A B W G ε horder hG hεpos hε hεh U Z hUZ hU hZ
  let H := supportedSubgraph G E hEG
  refine ⟨H,supportedSubgraph_verts_eq_support G E hEG,?_,?_,?_,?_,?_⟩
  · apply Set.disjoint_left.mpr
    intro p hp hpZ
    rw [supportedSubgraph_edgeSet] at hp
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hp
    apply Finset.disjoint_left.mp hdis he
    apply (mem_internalEdges G Z e).mpr
    refine ⟨(G.mem_edgeFinset e).mp (hEG he),?_⟩
    intro v hv
    exact SimpleGraph.Subgraph.mem_verts_of_mem_edge hpZ hv
  · intro v hv
    apply houtside v
    exact Finset.mem_sdiff.mpr ⟨hv.1,hv.2⟩
  · rw [supportedSubgraph_edgeCount,supportedSubgraph_verts,
      ← Finset.coe_sdiff,Set.ncard_coe_finset]
    exact hsize
  · simpa only [H,supportedSubgraph_coordinates] using hdefault
  · intro L hL hbalanced
    simpa only [H,supportedSubgraph_coordinates] using habsorb L hL hbalanced

end Overfull.Dense.FiniteAbsorber
