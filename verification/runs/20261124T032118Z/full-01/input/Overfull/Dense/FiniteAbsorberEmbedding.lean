import Overfull.Dense.TripartiteGraph
import Overfull.Dense.CycleAbsorber
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Embedding cycle absorbers from density hypotheses

All neighborhoods are those of the actual simple tripartite host. Auxiliary
vertices are selected outside the prescribed forbidden set and outside the
vertices selected earlier.
-/

namespace Overfull.Dense.FiniteAbsorber

open Finset Classical
open TripartiteGraph

variable {A B W : Type*} [Fintype A] [Fintype B] [Fintype W]
variable (G : TripartiteGraph A B W)

abbrev HostVertex := A ⊕ B ⊕ W

/-- The graph hypotheses used to embed the finite absorbers. Local balance
is required of the remainders, not of the ambient host. -/
structure Density (η γ ε : ℝ) : Prop where
  partSizes : Fintype.card A = Fintype.card B
  thirdSize : γ * Fintype.card A ≤ (Fintype.card W : ℝ)
  degreeA : ∀ a, (1/2+η)*Fintype.card A ≤ ((G.neighborsB a).card : ℝ)
  degreeB : ∀ b, (1/2+η)*Fintype.card A ≤ ((G.neighborsA b).card : ℝ)
  missingA : ∀ a, (Fintype.card W : ℝ)-(G.neighborsWA a).card ≤ ε*Fintype.card A
  missingB : ∀ b, (Fintype.card W : ℝ)-(G.neighborsWB b).card ≤ ε*Fintype.card A
  missingWA : ∀ w, (Fintype.card A : ℝ)-(G.linkA w).card ≤ ε*Fintype.card A
  missingWB : ∀ w, (Fintype.card A : ℝ)-(G.linkB w).card ≤ ε*Fintype.card A

/-- A simple directed cycle in the cyclic orientation A to B to W to A. -/
structure Cycle (ℓ : ℕ) where
  x : Fin ℓ ↪ A
  y : Fin ℓ ↪ B
  w : Fin ℓ ↪ W
  xy : ∀ j, G.ab (x j) (y j)
  yw : ∀ j, G.bw (y j) (w j)
  wx : ∀ j, G.aw (x (CycleAbsorber.next ℓ j)) (w j)

noncomputable def partA (Z : Finset (HostVertex (A := A) (B := B) (W := W))) : Finset A :=
  univ.filter (fun a => Sum.inl a ∈ Z)
noncomputable def partB (Z : Finset (HostVertex (A := A) (B := B) (W := W))) : Finset B :=
  univ.filter (fun b => Sum.inr (Sum.inl b) ∈ Z)
noncomputable def partW (Z : Finset (HostVertex (A := A) (B := B) (W := W))) : Finset W :=
  univ.filter (fun w => Sum.inr (Sum.inr w) ∈ Z)

omit [Fintype B] [Fintype W] in
theorem partA_card_le (Z : Finset (HostVertex (A := A) (B := B) (W := W))) :
    (partA Z).card ≤ Z.card := by
  apply Finset.card_le_card_of_injOn (fun a => Sum.inl a)
  · intro a ha; exact (Finset.mem_filter.mp ha).2
  · exact Sum.inl_injective.injOn

omit [Fintype A] [Fintype W] in
theorem partB_card_le (Z : Finset (HostVertex (A := A) (B := B) (W := W))) :
    (partB Z).card ≤ Z.card := by
  apply Finset.card_le_card_of_injOn (fun b => Sum.inr (Sum.inl b))
  · intro b hb; exact (Finset.mem_filter.mp hb).2
  · exact (Sum.inr_injective.comp Sum.inl_injective).injOn

omit [Fintype A] [Fintype B] in
theorem partW_card_le (Z : Finset (HostVertex (A := A) (B := B) (W := W))) :
    (partW Z).card ≤ Z.card := by
  apply Finset.card_le_card_of_injOn (fun w => Sum.inr (Sum.inr w))
  · intro w hw; exact (Finset.mem_filter.mp hw).2
  · exact (Sum.inr_injective.comp Sum.inr_injective).injOn

private theorem card_inter_lower {V : Type*} [Fintype V] (S T : Finset V) :
    (S.card : ℝ) ≤ (S ∩ T).card + ((Fintype.card V : ℝ)-T.card) := by
  have hpart := Finset.card_inter_add_card_sdiff S T
  have hsub : S \ T ⊆ Tᶜ := fun _ h => Finset.mem_compl.mpr (Finset.mem_sdiff.mp h).2
  have hbound := Finset.card_le_card hsub
  have hcomp := Finset.card_compl_add_card T
  have h : S.card+T.card ≤ (S ∩ T).card+Fintype.card V := by omega
  have hr : (S.card : ℝ)+T.card ≤ (S ∩ T).card+Fintype.card V := by exact_mod_cast h
  linarith

private theorem card_sdiff_lower {V : Type*} (S T : Finset V) :
    (S.card : ℝ) ≤ (S \ T).card+T.card := by
  have hpart := Finset.card_inter_add_card_sdiff S T
  have hbound := Finset.card_le_card (Finset.inter_subset_right : S ∩ T ⊆ T)
  exact_mod_cast (show S.card ≤ (S \ T).card+T.card by omega)

/-- A prescribed gadget step has an actual adjacent auxiliary pair outside
any small forbidden sets in its two parts. -/
theorem exists_auxiliary_pair (η γ ε : ℝ) (hη : 0 < η) (hε : ε ≤ η/32)
    (hmNat : 0 < Fintype.card A) (hG : Density G η γ ε)
    (x : A) (y : B) (w w₀ : W) (X : Finset A) (Y : Finset B)
    (hX : (X.card : ℝ) ≤ η*Fintype.card A/8)
    (hY : (Y.card : ℝ) ≤ η*Fintype.card A/8) :
    ∃ x' : A, ∃ y' : B,
      x' ∉ X ∧ y' ∉ Y ∧ G.ab x y' ∧ G.ab x' y' ∧ G.ab x' y ∧
      G.aw x' w ∧ G.aw x' w₀ ∧ G.bw y' w ∧ G.bw y' w₀ := by
  let X' := ((G.neighborsA y ∩ G.linkA w) ∩ G.linkA w₀) \ X
  let Y' := ((G.neighborsB x ∩ G.linkB w) ∩ G.linkB w₀) \ Y
  have hm : (0 : ℝ) < Fintype.card A := by exact_mod_cast hmNat
  have hεm := mul_le_mul_of_nonneg_right hε hm.le
  have hXsize : (1/2+η/2)*(Fintype.card A : ℝ) ≤ X'.card := by
    have h₁ := card_inter_lower (G.neighborsA y) (G.linkA w)
    have h₂ := card_inter_lower (G.neighborsA y ∩ G.linkA w) (G.linkA w₀)
    have h₃ := card_sdiff_lower ((G.neighborsA y ∩ G.linkA w) ∩ G.linkA w₀) X
    dsimp [X']
    nlinarith only [h₁,h₂,h₃,hG.degreeB y,hG.missingWA w,hG.missingWA w₀,hX,hεm]
  have hYsize : (1/2+η/2)*(Fintype.card A : ℝ) ≤ Y'.card := by
    have h₁ := card_inter_lower (G.neighborsB x) (G.linkB w)
    have h₂ := card_inter_lower (G.neighborsB x ∩ G.linkB w) (G.linkB w₀)
    rw [← hG.partSizes] at h₁ h₂
    have h₃ := card_sdiff_lower ((G.neighborsB x ∩ G.linkB w) ∩ G.linkB w₀) Y
    dsimp [Y']
    nlinarith only [h₁,h₂,h₃,hG.degreeA x,hG.missingWB w,hG.missingWB w₀,hY,hεm]
  have hYpos : 0 < Y'.card := by
    have hp : (0 : ℝ) < (1/2+η/2)*(Fintype.card A : ℝ) := by positivity
    exact_mod_cast hp.trans_le hYsize
  obtain ⟨y',hy'⟩ := Finset.card_pos.mp hYpos
  have hcommon := card_inter_lower X' (G.neighborsA y')
  have hcommonPos : 0 < (X' ∩ G.neighborsA y').card := by
    have hp : (0 : ℝ) < η*Fintype.card A := mul_pos hη hm
    have hr : (0 : ℝ) < (X' ∩ G.neighborsA y').card := by
      nlinarith only [hcommon,hXsize,hG.degreeB y',hp]
    exact_mod_cast hr
  obtain ⟨x',hx'⟩ := Finset.card_pos.mp hcommonPos
  have hxX := (Finset.mem_inter.mp hx').1
  have hxy := (Finset.mem_inter.mp hx').2
  simp only [X',Y',Finset.mem_sdiff,Finset.mem_inter,neighborsA,neighborsB,
    linkA,linkB,Finset.mem_filter,Finset.mem_univ,true_and] at hxX hy' hxy
  exact ⟨x',y',hxX.2,hy'.2,hy'.1.1.1,hxy,hxX.1.1.1,
    hxX.1.1.2,hxX.1.2,hy'.1.1.2,hy'.1.2⟩

/-- A common center exists outside the forbidden vertices. -/
theorem exists_center (η γ ε : ℝ) (hγ : 0 < γ)
    (hmNat : 0 < Fintype.card A) (hG : Density G η γ ε)
    {ℓ : ℕ} (C : Cycle G ℓ)
    (hε : 2*(ℓ : ℝ)*ε ≤ γ/16)
    (Z : Finset (HostVertex (A := A) (B := B) (W := W)))
    (hZ : (Z.card : ℝ) ≤ γ*Fintype.card A/8) :
    ∃ w₀ : W, Sum.inr (Sum.inr w₀) ∉ Z ∧
      (∀ j, G.aw (C.x j) w₀) ∧ (∀ j, G.bw (C.y j) w₀) := by
  let badA := univ.biUnion (fun j : Fin ℓ => (G.neighborsWA (C.x j))ᶜ)
  let badB := univ.biUnion (fun j : Fin ℓ => (G.neighborsWB (C.y j))ᶜ)
  have hbadA : (badA.card : ℝ) ≤ ℓ*ε*Fintype.card A := by
    calc
      (badA.card : ℝ) ≤ ∑ j : Fin ℓ, ((G.neighborsWA (C.x j))ᶜ.card : ℝ) := by
        exact_mod_cast (Finset.card_biUnion_le (s := (univ : Finset (Fin ℓ)))
          (t := fun j => (G.neighborsWA (C.x j))ᶜ))
      _ ≤ ∑ _j : Fin ℓ, ε*Fintype.card A := by
        apply Finset.sum_le_sum
        intro j _
        have hc : ((G.neighborsWA (C.x j))ᶜ.card : ℝ) +
            (G.neighborsWA (C.x j)).card = Fintype.card W := by
          exact_mod_cast Finset.card_compl_add_card (G.neighborsWA (C.x j))
        linarith [hG.missingA (C.x j)]
      _ = ℓ*ε*Fintype.card A := by simp; ring
  have hbadB : (badB.card : ℝ) ≤ ℓ*ε*Fintype.card A := by
    calc
      (badB.card : ℝ) ≤ ∑ j : Fin ℓ, ((G.neighborsWB (C.y j))ᶜ.card : ℝ) := by
        exact_mod_cast (Finset.card_biUnion_le (s := (univ : Finset (Fin ℓ)))
          (t := fun j => (G.neighborsWB (C.y j))ᶜ))
      _ ≤ ∑ _j : Fin ℓ, ε*Fintype.card A := by
        apply Finset.sum_le_sum
        intro j _
        have hc : ((G.neighborsWB (C.y j))ᶜ.card : ℝ) +
            (G.neighborsWB (C.y j)).card = Fintype.card W := by
          exact_mod_cast Finset.card_compl_add_card (G.neighborsWB (C.y j))
        linarith [hG.missingB (C.y j)]
      _ = ℓ*ε*Fintype.card A := by simp; ring
  let bad := partW Z ∪ badA ∪ badB
  have hbad : (bad.card : ℝ) ≤ Z.card+2*ℓ*ε*Fintype.card A := by
    have h₁ : ((partW Z ∪ badA).card : ℝ) ≤ (partW Z).card+badA.card := by
      exact_mod_cast Finset.card_union_le (partW Z) badA
    have h₂ : (bad.card : ℝ) ≤ (partW Z ∪ badA).card+badB.card := by
      exact_mod_cast Finset.card_union_le (partW Z ∪ badA) badB
    have h₃ : ((partW Z).card : ℝ) ≤ Z.card := by exact_mod_cast partW_card_le Z
    linarith
  have hm : (0 : ℝ) < Fintype.card A := by exact_mod_cast hmNat
  have hbadlt : bad.card < (univ : Finset W).card := by
    have hεm := mul_le_mul_of_nonneg_right hε hm.le
    have hpos : (0 : ℝ) < γ*Fintype.card A := mul_pos hγ hm
    have hr : (bad.card : ℝ) < Fintype.card W := by
      nlinarith only [hbad,hZ,hεm,hG.thirdSize,hpos]
    simpa using (show bad.card < Fintype.card W by exact_mod_cast hr)
  obtain ⟨w₀,_,hw₀⟩ := Finset.exists_mem_notMem_of_card_lt_card hbadlt
  have hwZ : w₀ ∉ partW Z := fun h => hw₀ (Finset.mem_union_left _
    (Finset.mem_union_left _ h))
  refine ⟨w₀, ?_, ?_, ?_⟩
  · simpa [partW] using hwZ
  · intro j
    by_contra h
    apply hw₀
    exact Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _, by simpa [neighborsWA] using h⟩))
  · intro j
    by_contra h
    apply hw₀
    exact Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _, by simpa [neighborsWB] using h⟩)

/-- Sequential choices with one new vertex in each part yield injective maps. -/
theorem exists_injective_pairs {X Y : Type*} (n : ℕ) (R : Fin n → X → Y → Prop)
    (hR : ∀ i (S : Finset X) (T : Finset Y), S.card < n → T.card < n →
      ∃ x, ∃ y, x ∉ S ∧ y ∉ T ∧ R i x y) :
    ∃ f : Fin n ↪ X, ∃ g : Fin n ↪ Y, ∀ i, R i (f i) (g i) := by
  induction n with
  | zero =>
      exact ⟨⟨Fin.elim0,fun i => Fin.elim0 i⟩,
        ⟨Fin.elim0,fun i => Fin.elim0 i⟩,fun i => Fin.elim0 i⟩
  | succ n ih =>
      obtain ⟨f,g,hfg⟩ := ih (fun i => R i.castSucc) (by
        intro i S T hS hT
        exact hR i.castSucc S T (by omega) (by omega))
      obtain ⟨x,y,hx,hy,hxy⟩ := hR (Fin.last n)
        (univ.image f) (univ.image g)
        (by simp [Finset.card_image_of_injective _ f.injective])
        (by simp [Finset.card_image_of_injective _ g.injective])
      have hx' : x ∉ Set.range f := by simpa using hx
      have hy' : y ∉ Set.range g := by simpa using hy
      refine ⟨⟨Fin.snoc f x,Fin.snoc_injective_of_injective f.injective hx'⟩,
        ⟨Fin.snoc g y,Fin.snoc_injective_of_injective g.injective hy'⟩,?_⟩
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hxy
      · simpa using hfg j

/-- The vertices and all actual host edges needed by a cycle gadget. -/
structure Placement {ℓ : ℕ} (C : Cycle G ℓ)
    (Z : Finset (HostVertex (A := A) (B := B) (W := W))) where
  xAux : Fin ℓ ↪ A
  yAux : Fin ℓ ↪ B
  center : W
  xOutside : ∀ j, Sum.inl (xAux j) ∉ Z
  yOutside : ∀ j, Sum.inr (Sum.inl (yAux j)) ∉ Z
  centerOutside : Sum.inr (Sum.inr center) ∉ Z
  centerA : ∀ j, G.aw (C.x j) center
  centerB : ∀ j, G.bw (C.y j) center
  pair : ∀ j, G.ab (C.x (CycleAbsorber.next ℓ j)) (yAux j) ∧
    G.ab (xAux j) (yAux j) ∧ G.ab (xAux j) (C.y j) ∧
    G.aw (xAux j) (C.w j) ∧ G.aw (xAux j) center ∧
    G.bw (yAux j) (C.w j) ∧ G.bw (yAux j) center

/-- All auxiliary vertices of one gadget can be selected simultaneously from
the actual density hypotheses. -/
theorem exists_placement (η γ ε : ℝ) (hη : 0 < η) (hγ : 0 < γ)
    (hε : ε ≤ η/32) (hmNat : 0 < Fintype.card A) (hG : Density G η γ ε)
    {ℓ : ℕ} (C : Cycle G ℓ) (hcenter : 2*(ℓ : ℝ)*ε ≤ γ/16)
    (Z : Finset (HostVertex (A := A) (B := B) (W := W)))
    (hZA : (Z.card : ℝ)+ℓ ≤ η*Fintype.card A/8)
    (hZW : (Z.card : ℝ) ≤ γ*Fintype.card A/8) :
    Nonempty (Placement G C Z) := by
  obtain ⟨w₀,hw₀,hcenterA,hcenterB⟩ :=
    exists_center G η γ ε hγ hmNat hG C hcenter Z hZW
  let R : Fin ℓ → A → B → Prop := fun j x y =>
    Sum.inl x ∉ Z ∧ Sum.inr (Sum.inl y) ∉ Z ∧
    G.ab (C.x (CycleAbsorber.next ℓ j)) y ∧ G.ab x y ∧ G.ab x (C.y j) ∧
    G.aw x (C.w j) ∧ G.aw x w₀ ∧ G.bw y (C.w j) ∧ G.bw y w₀
  obtain ⟨f,g,hfg⟩ := exists_injective_pairs ℓ R (by
    intro j S T hS hT
    have hS' : ((partA Z ∪ S).card : ℝ) ≤ η*Fintype.card A/8 := by
      have hu : ((partA Z ∪ S).card : ℝ) ≤ (partA Z).card+S.card := by
        exact_mod_cast Finset.card_union_le (partA Z) S
      have hp : ((partA Z).card : ℝ) ≤ Z.card := by exact_mod_cast partA_card_le Z
      have hs : (S.card : ℝ) < ℓ := by exact_mod_cast hS
      linarith
    have hT' : ((partB Z ∪ T).card : ℝ) ≤ η*Fintype.card A/8 := by
      have hu : ((partB Z ∪ T).card : ℝ) ≤ (partB Z).card+T.card := by
        exact_mod_cast Finset.card_union_le (partB Z) T
      have hp : ((partB Z).card : ℝ) ≤ Z.card := by exact_mod_cast partB_card_le Z
      have ht : (T.card : ℝ) < ℓ := by exact_mod_cast hT
      linarith
    obtain ⟨x,y,hx,hy,hxy⟩ := exists_auxiliary_pair G η γ ε hη hε hmNat hG
      (C.x (CycleAbsorber.next ℓ j)) (C.y j) (C.w j) w₀
      (partA Z ∪ S) (partB Z ∪ T) hS' hT'
    refine ⟨x,y,fun h => hx (Finset.mem_union_right _ h),
      fun h => hy (Finset.mem_union_right _ h),?_,?_,hxy⟩
    · intro h
      exact hx (Finset.mem_union_left _ (by simpa [partA] using h))
    · intro h
      exact hy (Finset.mem_union_left _ (by simpa [partB] using h)))
  exact ⟨⟨f,g,w₀,fun j => (hfg j).1,fun j => (hfg j).2.1,
    hw₀,hcenterA,hcenterB,fun j => (hfg j).2.2⟩⟩

def Placement.vertexMap {ℓ : ℕ} {C : Cycle G ℓ}
    {Z : Finset (HostVertex (A := A) (B := B) (W := W))} (P : Placement G C Z) :
    CycleAbsorber.Vertex ℓ → HostVertex (A := A) (B := B) (W := W)
  | .x j => Sum.inl (C.x j)
  | .y j => Sum.inr (Sum.inl (C.y j))
  | .w j => Sum.inr (Sum.inr (C.w j))
  | .xAux j => Sum.inl (P.xAux j)
  | .yAux j => Sum.inr (Sum.inl (P.yAux j))
  | .center => Sum.inr (Sum.inr P.center)

omit [Fintype A] [Fintype B] [Fintype W] in
theorem Placement.vertexMap_injective {ℓ : ℕ} {C : Cycle G ℓ}
    {Z : Finset (HostVertex (A := A) (B := B) (W := W))} (P : Placement G C Z)
    (hx : ∀ j, Sum.inl (C.x j) ∈ Z)
    (hy : ∀ j, Sum.inr (Sum.inl (C.y j)) ∈ Z)
    (hw : ∀ j, Sum.inr (Sum.inr (C.w j)) ∈ Z) :
    Function.Injective (P.vertexMap G) := by
  have hxa : ∀ i j, C.x i ≠ P.xAux j := by
    intro i j h
    exact P.xOutside j (h ▸ hx i)
  have hya : ∀ i j, C.y i ≠ P.yAux j := by
    intro i j h
    exact P.yOutside j (h ▸ hy i)
  have hwc : ∀ i, C.w i ≠ P.center := by
    intro i h
    exact P.centerOutside (h ▸ hw i)
  have hax : ∀ i j, P.xAux i ≠ C.x j := fun i j => (hxa j i).symm
  have hay : ∀ i j, P.yAux i ≠ C.y j := fun i j => (hya j i).symm
  have hcw : ∀ i, P.center ≠ C.w i := fun i => (hwc i).symm
  intro u v huv
  cases u <;> cases v <;>
    simp only [Placement.vertexMap, Sum.inl.injEq, Sum.inr.injEq,
      Sum.inl_ne_inr, Sum.inr_ne_inl, hxa, hya, hwc, hax, hay, hcw,
      C.x.injective.eq_iff, C.y.injective.eq_iff, C.w.injective.eq_iff,
      P.xAux.injective.eq_iff, P.yAux.injective.eq_iff] at huv <;>
    first | contradiction | subst_vars; rfl

def Placement.embedding {ℓ : ℕ} {C : Cycle G ℓ}
    {Z : Finset (HostVertex (A := A) (B := B) (W := W))} (P : Placement G C Z)
    (hx : ∀ j, Sum.inl (C.x j) ∈ Z)
    (hy : ∀ j, Sum.inr (Sum.inl (C.y j)) ∈ Z)
    (hw : ∀ j, Sum.inr (Sum.inr (C.w j)) ∈ Z) :
    CycleAbsorber.Vertex ℓ ↪ HostVertex (A := A) (B := B) (W := W) :=
  ⟨P.vertexMap G,P.vertexMap_injective G hx hy hw⟩

omit [Fintype A] [Fintype B] [Fintype W] in
theorem Placement.edges_in_host {ℓ : ℕ} {C : Cycle G ℓ}
    {Z : Finset (HostVertex (A := A) (B := B) (W := W))} (P : Placement G C Z)
    (hx : ∀ j, Sum.inl (C.x j) ∈ Z)
    (hy : ∀ j, Sum.inr (Sum.inl (C.y j)) ∈ Z)
    (hw : ∀ j, Sum.inr (Sum.inr (C.w j)) ∈ Z) :
    ∀ e ∈ CycleAbsorber.absorberEdges ℓ ∪ CycleAbsorber.cycleEdges ℓ,
      Sym2.map (P.embedding G hx hy hw) e ∈ G.toSimpleGraph.edgeSet := by
  intro e he
  rcases Finset.mem_union.mp he with he | he
  · obtain ⟨⟨i,j⟩,_,rfl⟩ := Finset.mem_image.mp he
    fin_cases i
    · simpa [CycleAbsorber.absorberEdge,Placement.embedding,Placement.vertexMap,
        toSimpleGraph] using (P.pair j).1
    · simpa [CycleAbsorber.absorberEdge,Placement.embedding,Placement.vertexMap,
        toSimpleGraph] using (P.pair j).2.1
    · simpa [CycleAbsorber.absorberEdge,Placement.embedding,Placement.vertexMap,
        toSimpleGraph] using (P.pair j).2.2.1
    · simpa [CycleAbsorber.absorberEdge,Placement.embedding,Placement.vertexMap,
        toSimpleGraph] using P.centerA (CycleAbsorber.next ℓ j)
    · simpa [CycleAbsorber.absorberEdge,Placement.embedding,Placement.vertexMap,
        toSimpleGraph] using (P.pair j).2.2.2.2.2.2
    · simpa [CycleAbsorber.absorberEdge,Placement.embedding,Placement.vertexMap,
        toSimpleGraph] using (P.pair j).2.2.2.2.1
    · simpa [CycleAbsorber.absorberEdge,Placement.embedding,Placement.vertexMap,
        toSimpleGraph] using P.centerB j
    · simpa [CycleAbsorber.absorberEdge,Placement.embedding,Placement.vertexMap,
        toSimpleGraph] using (P.pair j).2.2.2.2.2.1
    · simpa [CycleAbsorber.absorberEdge,Placement.embedding,Placement.vertexMap,
        toSimpleGraph] using (P.pair j).2.2.2.1
  · obtain ⟨⟨i,j⟩,_,rfl⟩ := Finset.mem_image.mp he
    fin_cases i
    · simpa [CycleAbsorber.cycleEdge,Placement.embedding,Placement.vertexMap,
        toSimpleGraph] using C.xy j
    · simpa [CycleAbsorber.cycleEdge,Placement.embedding,Placement.vertexMap,
        toSimpleGraph] using C.yw j
    · simpa [CycleAbsorber.cycleEdge,Placement.embedding,Placement.vertexMap,
        toSimpleGraph] using C.wx j

end Overfull.Dense.FiniteAbsorber
