import Overfull.NativeTerminal.NativeGeometry
import Overfull.NativeCore.NativePrefix

/-!
# Native prefix residuals satisfy the terminal geometric interface

The twice-surviving original-copy embedding is explicit. Its external image
identity follows from the already proved prefix remainder, and the reserve
geometry theorems therefore apply to the actual residual graph.
-/

noncomputable section

namespace Overfull.NativeTerminal

open Finset Classical NativeReserve AssignedParts FourOdd

variable {V E F J K : Type*} [Fintype E]

omit [Fintype E] in
/-- On an arbitrary same-vertex host, the assigned joining and exceptional
copies are exactly the copies outside both old cores. -/
theorem externalCopies_eq_joining_exceptional [Fintype F]
    (G : Multigraph V E) (H : Multigraph V F) (U₀ U₁ Z : Finset V) {M : Finset E}
    (hM : G.IsPerfectMatching M)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) :
    externalCopies H U₀ U₁ =
      joiningCopies H (assignedLabel G M U₀ U₁ Z) ∪ exceptionalCopies H univ Z := by
  ext e
  simp only [mem_externalCopies,mem_union,mem_joiningCopies,
    mem_exceptionalCopies,mem_univ,true_and]
  have hx := hcover (H.firstEnd e)
  have hy := hcover (H.secondEnd e)
  have h₀ (v : V) (hv : v ∈ U₀) : assignedLabel G M U₀ U₁ Z v = 0 :=
    assignedLabel_on_core₀ G M U₀ U₁ Z hv
  have h₁ (v : V) (hv : v ∈ U₁) : assignedLabel G M U₀ U₁ Z v = 1 :=
    assignedLabel_on_core₁ G (hM.isMatching G) U₀ U₁ Z h01 h0Z h1Z hv
  rcases hx with hx | hx | hx <;> rcases hy with hy | hy | hy
  · simp [h₀ _ hx,h₀ _ hy,hx,hy,
      show H.firstEnd e ∉ Z from fun h => disjoint_left.mp h0Z hx h,
      show H.secondEnd e ∉ Z from fun h => disjoint_left.mp h0Z hy h]
  · simp [h₀ _ hx,h₁ _ hy,hx,hy,
      show H.firstEnd e ∉ U₁ from fun h => disjoint_left.mp h01 hx h,
      show H.secondEnd e ∉ U₀ from fun h => disjoint_left.mp h01 h hy]
  · simp [hy,show H.secondEnd e ∉ U₀ from fun h => disjoint_left.mp h0Z h hy,
      show H.secondEnd e ∉ U₁ from fun h => disjoint_left.mp h1Z h hy]
  · simp [h₁ _ hx,h₀ _ hy,hx,hy,
      show H.firstEnd e ∉ U₀ from fun h => disjoint_left.mp h01 h hx,
      show H.secondEnd e ∉ U₁ from fun h => disjoint_left.mp h01 hy h]
  · simp [h₁ _ hx,h₁ _ hy,hx,hy,
      show H.firstEnd e ∉ Z from fun h => disjoint_left.mp h1Z hx h,
      show H.secondEnd e ∉ Z from fun h => disjoint_left.mp h1Z hy h]
  · simp [hy,show H.secondEnd e ∉ U₀ from fun h => disjoint_left.mp h0Z h hy,
      show H.secondEnd e ∉ U₁ from fun h => disjoint_left.mp h1Z h hy]
  · simp [hx,show H.firstEnd e ∉ U₀ from fun h => disjoint_left.mp h0Z h hx,
      show H.firstEnd e ∉ U₁ from fun h => disjoint_left.mp h1Z h hx]
  · simp [hx,show H.firstEnd e ∉ U₀ from fun h => disjoint_left.mp h0Z h hx,
      show H.firstEnd e ∉ U₁ from fun h => disjoint_left.mp h1Z h hx]
  · simp [hx,show H.firstEnd e ∉ U₀ from fun h => disjoint_left.mp h0Z h hx,
      show H.firstEnd e ∉ U₁ from fun h => disjoint_left.mp h1Z h hx]

/-- The external-copy set commutes with actual copy deletion. -/
theorem externalCopies_residual (G : Multigraph V E) (U₀ U₁ : Finset V)
    (N : J → Finset E) (T : Finset J) :
    externalCopies (residualGraph G N T) U₀ U₁ =
      survivingCopies (removedCopies N T) (externalCopies G U₀ U₁) := by
  ext e
  rw [mem_externalCopies,mem_survivingCopies,mem_externalCopies]
  rfl

/-- Two rounds of actual copy deletion have the obvious injective original-copy map. -/
def twiceResidualEmbedding (G : Multigraph V E)
    (N : J → Finset E) (T : Finset J)
    (W : K → Finset {e : E // e ∉ removedCopies N T}) (S : Finset K) :
    CopyEmbedding G (residualGraph (residualGraph G N T) W S) where
  map := ⟨fun e => e.val.val,by
    intro e f h
    apply Subtype.ext
    exact Subtype.ext h⟩
  edge_eq _ := rfl

/-- The native prefix's exact external remainder gives the terminal reserve
image in the original edge-copy type, including all parallel copies. -/
theorem twiceResidual_external_image
    (G : Multigraph V E) (U₀ U₁ Z : Finset V) {M : Finset E}
    (hM : G.IsPerfectMatching M)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (r s : ℕ) (Q : NativeReserve.BoundaryPacking G U₀ U₁ Z M r)
    (q : Fin s → Fin r) (N : J → Finset E) (T : Finset J)
    (havoid : ∀ j ∈ T, Disjoint (N j) (removedCopies Q.boundary univ))
    (W : K → Finset {e : E // e ∉ removedCopies N T}) (S : Finset K)
    (hrem : (survivingCopies (removedCopies W S)
      (joiningCopies (residualGraph G N T) (assignedLabel G M U₀ U₁ Z) ∪
        exceptionalCopies (residualGraph G N T) univ Z)).image Subtype.val =
      univ.biUnion (fun i => Q.residualBoundary N T (q i))) :
    (externalCopies (residualGraph (residualGraph G N T) W S) U₀ U₁).image
      (twiceResidualEmbedding G N T W S).map = BoundaryPacking.selectedUnion Q q := by
  have hX : externalCopies (residualGraph (residualGraph G N T) W S) U₀ U₁ =
      survivingCopies (removedCopies W S)
        (joiningCopies (residualGraph G N T) (assignedLabel G M U₀ U₁ Z) ∪
          exceptionalCopies (residualGraph G N T) univ Z) := by
    ext e
    rw [mem_externalCopies,mem_survivingCopies]
    have hh := Finset.ext_iff.mp
      (externalCopies_eq_joining_exceptional G (residualGraph G N T) U₀ U₁ Z hM
        h01 h0Z h1Z hcover) e.val
    simp only [mem_externalCopies,mem_union,mem_joiningCopies,
      mem_exceptionalCopies,mem_univ,true_and] at hh ⊢
    exact hh
  rw [hX]
  change (survivingCopies (removedCopies W S)
      (joiningCopies (residualGraph G N T) (assignedLabel G M U₀ U₁ Z) ∪
        exceptionalCopies (residualGraph G N T) univ Z)).image
      (Subtype.val ∘ Subtype.val) = _
  rw [← image_image,hrem]
  ext e
  constructor
  · intro he
    obtain ⟨f,hf,rfl⟩ := mem_image.mp he
    obtain ⟨i,_,hfi⟩ := mem_biUnion.mp hf
    exact (BoundaryPacking.mem_selectedUnion Q q f.val).mpr
      ⟨i,(Q.mem_residualBoundary N T (q i) f).mp hfi⟩
  · intro he
    obtain ⟨i,hi⟩ := (BoundaryPacking.mem_selectedUnion Q q e).mp he
    have hsurvive : e ∉ removedCopies N T :=
      fun hh => disjoint_left.mp (Q.boundary_disjoint_removed N T havoid (q i)) hi hh
    refine mem_image.mpr ⟨⟨e,hsurvive⟩,?_,rfl⟩
    exact mem_biUnion.mpr ⟨i,mem_univ _,(Q.mem_residualBoundary N T (q i) _).mpr hi⟩

end Overfull.NativeTerminal
