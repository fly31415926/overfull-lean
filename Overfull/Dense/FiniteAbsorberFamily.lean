import Overfull.Dense.FiniteAbsorberEmbedding

/-!
# Simultaneous placements of cycle absorbers

All auxiliary vertices for distinct gadgets are chosen separately. The total
number of auxiliary vertices is controlled throughout the greedy construction.
-/

namespace Overfull.Dense.FiniteAbsorber

open Finset Classical
open TripartiteGraph

variable {A B W : Type*} [Fintype A] [Fintype B] [Fintype W]
variable (G : TripartiteGraph A B W)

noncomputable def Placement.auxVertices {ℓ : ℕ} {C : Cycle G ℓ}
    {Z : Finset (HostVertex (A := A) (B := B) (W := W))} (P : Placement G C Z) :
    Finset (HostVertex (A := A) (B := B) (W := W)) :=
  univ.image (fun j => Sum.inl (P.xAux j)) ∪
    univ.image (fun j => Sum.inr (Sum.inl (P.yAux j))) ∪
    {Sum.inr (Sum.inr P.center)}

omit [Fintype A] [Fintype B] [Fintype W] in
theorem Placement.auxVertices_card {ℓ : ℕ} {C : Cycle G ℓ}
    {Z : Finset (HostVertex (A := A) (B := B) (W := W))} (P : Placement G C Z) :
    (P.auxVertices G).card = 2*ℓ+1 := by
  have hX : Function.Injective (fun j => (Sum.inl (P.xAux j) : HostVertex
      (A := A) (B := B) (W := W))) := Sum.inl_injective.comp P.xAux.injective
  have hY : Function.Injective (fun j => (Sum.inr (Sum.inl (P.yAux j)) : HostVertex
      (A := A) (B := B) (W := W))) :=
    Sum.inr_injective.comp (Sum.inl_injective.comp P.yAux.injective)
  have hXY : Disjoint (univ.image (fun j => (Sum.inl (P.xAux j) : HostVertex
      (A := A) (B := B) (W := W))))
      (univ.image (fun j => Sum.inr (Sum.inl (P.yAux j)))) := by
    apply Finset.disjoint_left.mpr
    intro v hvx hvy
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hvx
    simp at hvy
  have hW : Disjoint
      (univ.image (fun j => (Sum.inl (P.xAux j) : HostVertex
          (A := A) (B := B) (W := W))) ∪
        univ.image (fun j => Sum.inr (Sum.inl (P.yAux j))))
      {Sum.inr (Sum.inr P.center)} := by simp
  rw [Placement.auxVertices,Finset.card_union_of_disjoint hW,
    Finset.card_union_of_disjoint hXY,
    Finset.card_image_of_injective _ hX,Finset.card_image_of_injective _ hY]
  simp
  omega

omit [Fintype A] [Fintype B] [Fintype W] in
theorem Placement.auxVertices_outside {ℓ : ℕ} {C : Cycle G ℓ}
    {Z : Finset (HostVertex (A := A) (B := B) (W := W))} (P : Placement G C Z) :
    ∀ v ∈ P.auxVertices G, v ∉ Z := by
  intro v hv
  rcases Finset.mem_union.mp hv with hv | hv
  · rcases Finset.mem_union.mp hv with hv | hv
    · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hv
      exact P.xOutside j
    · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hv
      exact P.yOutside j
  · exact (Finset.mem_singleton.mp hv) ▸ P.centerOutside

def Placement.restrict {ℓ : ℕ} {C : Cycle G ℓ}
    {Z Y : Finset (HostVertex (A := A) (B := B) (W := W))}
    (P : Placement G C Y) (hZY : Z ⊆ Y) : Placement G C Z where
  xAux := P.xAux
  yAux := P.yAux
  center := P.center
  xOutside j h := P.xOutside j (hZY h)
  yOutside j h := P.yOutside j (hZY h)
  centerOutside h := P.centerOutside (hZY h)
  centerA := P.centerA
  centerB := P.centerB
  pair := P.pair

omit [Fintype A] [Fintype B] [Fintype W] in
@[simp] theorem Placement.auxVertices_restrict {ℓ : ℕ} {C : Cycle G ℓ}
    {Z Y : Finset (HostVertex (A := A) (B := B) (W := W))}
    (P : Placement G C Y) (hZY : Z ⊆ Y) :
    (P.restrict G hZY).auxVertices G = P.auxVertices G := rfl

set_option maxHeartbeats 800000 in
/-- A bounded finite family of gadgets admits placements with pairwise
disjoint auxiliary vertex sets. -/
theorem exists_disjoint_placements (η γ ε : ℝ) (hη : 0 < η) (hγ : 0 < γ)
    (hε : ε ≤ η/32) (hmNat : 0 < Fintype.card A) (hG : Density G η γ ε) :
    ∀ (n : ℕ) (ℓ : Fin n → ℕ) (C : ∀ i, Cycle G (ℓ i)),
      (∀ i, 2*(ℓ i : ℝ)*ε ≤ γ/16) →
      ∀ Z : Finset (HostVertex (A := A) (B := B) (W := W)),
      (Z.card : ℝ)+(∑ i, (2*(ℓ i : ℝ)+1)) ≤ min η γ*Fintype.card A/8 →
      ∃ P : ∀ i, Placement G (C i) Z,
        Pairwise (fun i j => Disjoint ((P i).auxVertices G) ((P j).auxVertices G)) := by
  intro n
  induction n with
  | zero =>
    intro ℓ C _ Z _
    exact ⟨fun i => Fin.elim0 i,fun i => Fin.elim0 i⟩
  | succ n ih =>
    intro ℓ C hcenter Z hbudget
    have hsplit : (∑ i, (2*(ℓ i : ℝ)+1)) =
        (∑ i : Fin n, (2*(ℓ i.castSucc : ℝ)+1)) + (2*(ℓ (Fin.last n) : ℝ)+1) :=
      Fin.sum_univ_castSucc _
    have hlast : (0 : ℝ) ≤ ℓ (Fin.last n) := Nat.cast_nonneg _
    obtain ⟨P,hP⟩ := ih (fun i => ℓ i.castSucc) (fun i => C i.castSucc)
      (fun i => hcenter i.castSucc) Z (by rw [hsplit] at hbudget; linarith)
    let Y := Z ∪ univ.biUnion (fun i => (P i).auxVertices G)
    have hYcard : (Y.card : ℝ) ≤ Z.card+∑ i : Fin n, (2*(ℓ i.castSucc : ℝ)+1) := by
      have hu : ((univ.biUnion (fun i => (P i).auxVertices G)).card : ℝ) ≤
          ∑ i : Fin n, (((P i).auxVertices G).card : ℝ) := by
        exact_mod_cast (Finset.card_biUnion_le (s := (univ : Finset (Fin n)))
          (t := fun i => (P i).auxVertices G))
      have hz : (Y.card : ℝ) ≤ Z.card+
          (univ.biUnion (fun i => (P i).auxVertices G)).card := by
        exact_mod_cast Finset.card_union_le Z (univ.biUnion (fun i => (P i).auxVertices G))
      simp only [Placement.auxVertices_card,Nat.cast_add,Nat.cast_mul,
        Nat.cast_ofNat,Nat.cast_one] at hu
      linarith
    have hηbound : min η γ*(Fintype.card A : ℝ)/8 ≤ η*Fintype.card A/8 := by
      gcongr
      exact min_le_left _ _
    have hγbound : min η γ*(Fintype.card A : ℝ)/8 ≤ γ*Fintype.card A/8 := by
      gcongr
      exact min_le_right _ _
    obtain ⟨Q⟩ := exists_placement G η γ ε hη hγ hε hmNat hG (C (Fin.last n))
      (hcenter (Fin.last n)) Y (by rw [hsplit] at hbudget; linarith)
      (by rw [hsplit] at hbudget; linarith)
    let Q' := Q.restrict G (Finset.subset_union_left (s₂ := univ.biUnion
      (fun i => (P i).auxVertices G)))
    have hQP (i : Fin n) : Disjoint (Q'.auxVertices G) ((P i).auxVertices G) := by
      change Disjoint (Q.auxVertices G) ((P i).auxVertices G)
      apply Finset.disjoint_left.mpr
      intro v hvQ hvP
      exact Q.auxVertices_outside G v hvQ (Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hvP⟩))
    let P' : ∀ i : Fin (n+1), Placement G (C i) Z :=
      Fin.lastCases Q' (fun i => P i)
    refine ⟨P',?_⟩
    intro i j hij
    cases i using Fin.lastCases <;> cases j using Fin.lastCases <;>
      simp only [P',Fin.lastCases_last,Fin.lastCases_castSucc]
    · exact (hij rfl).elim
    · exact hQP _
    · exact (hQP _).symm
    · apply hP
      intro h
      exact hij (congrArg Fin.castSucc h)

end Overfull.Dense.FiniteAbsorber
