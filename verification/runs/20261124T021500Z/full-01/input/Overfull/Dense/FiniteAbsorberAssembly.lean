import Overfull.Dense.FiniteAbsorberGadgets

/-!
# Combining the finite cycle gadgets

Distinct gadgets have disjoint auxiliary vertices. Since every gadget edge
meets an auxiliary vertex, their edge sets are disjoint as well.
-/

namespace Overfull.Dense.FiniteAbsorber

open Finset Classical
open TripartiteGraph

variable {A B W : Type*} [Fintype A] [Fintype B] [Fintype W]
variable (G : TripartiteGraph A B W)

/-- The actual vertices incident with a finite set of edge coordinates. -/
noncomputable def supportVertices
    (E : Finset (EdgePosition (A := A) (B := B) (W := W))) :
    Finset (HostVertex (A := A) (B := B) (W := W)) :=
  E.biUnion (fun e => (edgePair e).toFinset)

omit [Fintype A] [Fintype B] [Fintype W] in
@[simp] theorem mem_supportVertices
    (E : Finset (EdgePosition (A := A) (B := B) (W := W)))
    (v : HostVertex (A := A) (B := B) (W := W)) :
    v ∈ supportVertices E ↔ ∃ e ∈ E, v ∈ edgePair e := by
  simp [supportVertices]

theorem Cycle.edges_inside {ℓ : ℕ} (C : Cycle G ℓ)
    (U : Finset (HostVertex (A := A) (B := B) (W := W)))
    (hx : ∀ j, Sum.inl (C.x j) ∈ U)
    (hy : ∀ j, Sum.inr (Sum.inl (C.y j)) ∈ U)
    (hw : ∀ j, Sum.inr (Sum.inr (C.w j)) ∈ U) :
    ∀ e ∈ (C.graph G).edgeFinset, ∀ v ∈ edgePair e, v ∈ U := by
  intro e he v hv
  rw [C.edgeFinset_eq G] at he
  obtain ⟨⟨i,j⟩,_,rfl⟩ := Finset.mem_image.mp he
  fin_cases i
  · simp only [Cycle.edgePosition,abPos,edgePair,Sym2.mem_iff] at hv
    rcases hv with rfl | rfl
    · exact hx j
    · exact hy j
  · simp only [Cycle.edgePosition,bwPos,edgePair,Sym2.mem_iff] at hv
    rcases hv with rfl | rfl
    · exact hy j
    · exact hw j
  · simp only [Cycle.edgePosition,awPos,edgePair,Sym2.mem_iff] at hv
    rcases hv with rfl | rfl
    · exact hx (CycleAbsorber.next ℓ j)
    · exact hw j

theorem Gadget.disjoint_internal {ℓ : ℕ} {C : Cycle G ℓ}
    {U Z : Finset (HostVertex (A := A) (B := B) (W := W))}
    (Q : Gadget G C U Z) (hUZ : U ⊆ Z)
    (E : Finset (EdgePosition (A := A) (B := B) (W := W)))
    (hE : ∀ e ∈ E, ∀ v ∈ edgePair e, v ∈ U) : Disjoint Q.edges E := by
  apply Finset.disjoint_left.mpr
  intro e heQ heE
  obtain ⟨v,hve,hvaux⟩ := Q.meets e heQ
  exact Q.outside v hvaux (hUZ (hE e heE v hve))

theorem Gadget.disjoint_of_aux {ℓ k : ℕ} {C : Cycle G ℓ} {D : Cycle G k}
    {U Z : Finset (HostVertex (A := A) (B := B) (W := W))}
    (Q : Gadget G C U Z) (R : Gadget G D U Z) (hUZ : U ⊆ Z)
    (hd : Disjoint Q.aux R.aux) : Disjoint Q.edges R.edges := by
  apply Finset.disjoint_left.mpr
  intro e heQ heR
  obtain ⟨v,hve,hvaux⟩ := Q.meets e heQ
  rcases R.support e heR v hve with hvU | hvR
  · exact Q.outside v hvaux (hUZ hvU)
  · exact Finset.disjoint_left.mp hd hvaux hvR

theorem gadget_union_size {n : ℕ} {ℓ : Fin n → ℕ} {C : ∀ i, Cycle G (ℓ i)}
    {U Z : Finset (HostVertex (A := A) (B := B) (W := W))}
    (Q : ∀ i, Gadget G (C i) U Z) (hℓ : ∀ i, 0 < ℓ i) :
    (univ.biUnion (fun i => (Q i).edges)).card +
      (supportVertices (univ.biUnion (fun i => (Q i).edges)) \ U).card ≤
      4*(∑ i, 3*ℓ i) := by
  have hEdges : (univ.biUnion (fun i => (Q i).edges)).card ≤ ∑ i, 9*ℓ i :=
    Finset.card_biUnion_le.trans (Finset.sum_le_sum (fun i _ => (Q i).edge_card))
  have hs : supportVertices (univ.biUnion (fun i => (Q i).edges)) \ U ⊆
      univ.biUnion (fun i => (Q i).aux) := by
    intro v hv
    obtain ⟨hv,hvU⟩ := Finset.mem_sdiff.mp hv
    obtain ⟨e,he,hve⟩ := (mem_supportVertices _ _).mp hv
    obtain ⟨i,_,hei⟩ := Finset.mem_biUnion.mp he
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,
      ((Q i).support e hei v hve).resolve_left hvU⟩
  have hAux : (supportVertices (univ.biUnion (fun i => (Q i).edges)) \ U).card ≤
      ∑ i, (2*ℓ i+1) := by
    calc
      _ ≤ (univ.biUnion (fun i => (Q i).aux)).card := Finset.card_le_card hs
      _ ≤ ∑ i, (Q i).aux.card := Finset.card_biUnion_le
      _ = ∑ i, (2*ℓ i+1) := by simp_rw [Gadget.aux_card]
  calc
    _ ≤ (∑ i, 9*ℓ i)+(∑ i, (2*ℓ i+1)) := Nat.add_le_add hEdges hAux
    _ = ∑ i, (9*ℓ i+(2*ℓ i+1)) := Finset.sum_add_distrib.symm
    _ ≤ ∑ i, 4*(3*ℓ i) := Finset.sum_le_sum (fun i _ => by have := hℓ i; omega)
    _ = 4*(∑ i, 3*ℓ i) := (Finset.mul_sum _ _ _).symm

/-- Any subcollection of compatible cycles can be activated simultaneously. -/
theorem assemble_gadgets {n : ℕ} {ℓ : Fin n → ℕ} {C : ∀ i, Cycle G (ℓ i)}
    {U Z : Finset (HostVertex (A := A) (B := B) (W := W))}
    (Q : ∀ i, Gadget G (C i) U Z) (hUZ : U ⊆ Z)
    (haux : Pairwise (fun i j => Disjoint (Q i).aux (Q j).aux))
    (hinside : ∀ i, ∀ e ∈ ((C i).graph G).edgeFinset, ∀ v ∈ edgePair e, v ∈ U)
    (S : Finset (Fin n))
    (hS : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      Disjoint ((C i).graph G).edgeFinset ((C j).graph G).edgeFinset) :
    ∃ T : Finset G.Triangle, G.IsTriangleDecomposition T
      ((univ.biUnion (fun i => (Q i).edges)) ∪
        S.biUnion (fun i => ((C i).graph G).edgeFinset)) := by
  let E (i : Fin n) := (Q i).edges ∪ if i ∈ S then ((C i).graph G).edgeFinset else ∅
  have hE : Pairwise (fun i j => Disjoint (E i) (E j)) := by
    intro i j hij
    have hQQ := (Q i).disjoint_of_aux G (Q j) hUZ (haux hij)
    have hQC := (Q i).disjoint_internal G hUZ _ (hinside j)
    have hCQ := ((Q j).disjoint_internal G hUZ _ (hinside i)).symm
    by_cases hi : i ∈ S <;> by_cases hj : j ∈ S
    · simpa only [E,if_pos hi,if_pos hj,Finset.disjoint_union_left,
        Finset.disjoint_union_right] using ⟨⟨hQQ,hCQ⟩,hQC,hS i hi j hj hij⟩
    · simpa only [E,if_pos hi,if_neg hj,Finset.union_empty,
        Finset.disjoint_union_left] using ⟨hQQ,hCQ⟩
    · simpa only [E,if_neg hi,if_pos hj,Finset.union_empty,
        Finset.disjoint_union_right] using ⟨hQQ,hQC⟩
    · simpa only [E,if_neg hi,if_neg hj,Finset.union_empty] using hQQ
  have hdecomp (i : Fin n) : ∃ T : Finset G.Triangle, G.IsTriangleDecomposition T (E i) := by
    by_cases hi : i ∈ S
    · simpa only [E,if_pos hi] using (Q i).activated
    · simpa only [E,if_neg hi,Finset.union_empty] using (Q i).default
  have hunion : univ.biUnion E = (univ.biUnion (fun i => (Q i).edges)) ∪
      S.biUnion (fun i => ((C i).graph G).edgeFinset) := by
    ext e
    constructor
    · intro he
      obtain ⟨i,_,hei⟩ := Finset.mem_biUnion.mp he
      rcases Finset.mem_union.mp hei with heQ | heC
      · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,heQ⟩)
      · by_cases hi : i ∈ S
        · rw [if_pos hi] at heC
          exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i,hi,heC⟩)
        · simp only [if_neg hi,Finset.notMem_empty] at heC
    · intro he
      rcases Finset.mem_union.mp he with he | he
      · obtain ⟨i,_,hei⟩ := Finset.mem_biUnion.mp he
        exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_union_left _ hei⟩
      · obtain ⟨i,hi,hei⟩ := Finset.mem_biUnion.mp he
        refine Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_union_right _ ?_⟩
        rw [if_pos hi]
        exact hei
  rw [← hunion]
  exact G.decomposition_biUnion E hE hdecomp

end Overfull.Dense.FiniteAbsorber
