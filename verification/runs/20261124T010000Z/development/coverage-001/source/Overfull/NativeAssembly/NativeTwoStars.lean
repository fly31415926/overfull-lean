import Overfull.NativeAssembly.NativeBundles

/-!
# Native completion of two exceptions assigned to the same core

The common internal bundle and the two remaining assigned stars are colored
on their actual residual copy types.  The star cardinalities come from the
native reserve, and the Hall budgets come from the weighted joining classes.
Protected whole boundaries and the original joining cuts are retained.
-/

noncomputable section

namespace Overfull.NativeAssembly

open Finset Classical AssignedParts FourOdd NativeReserve NativeStar WeightedPalette

variable {V E J I : Type*} [Fintype V] [Fintype E] [Fintype I]

set_option maxHeartbeats 800000 in
/-- Construct all exceptional incidences when two distinct unpaired exceptions
have the same assigned label.  No residual coloring or independent choice of
the two stars is assumed. -/
theorem exists_native_same_label_completion
    (G : Multigraph V E) {M : Finset E} (hM : G.IsPerfectMatching M)
    (U₀ U₁ Z : Finset V) (h01 : Disjoint U₀ U₁)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (σ : Z → Fin 2) (hcode : coarseSignature G M U₀ Z = some σ)
    (r : ℕ) (Q : BoundaryPacking G U₀ U₁ Z M r)
    (N : J → Finset E) (T : Finset J)
    (havoid : ∀ j ∈ T, Disjoint (N j) (removedCopies Q.boundary univ))
    {h D L : ℕ} {p : Fin 3 → ℕ}
    (C : JoiningPalette (residualGraph G N T) (assignedLabel G M U₀ U₁ Z) h D L p)
    (q : I → Fin r) (f : I → Fin h) (hq : Function.Injective q) (hf : Function.Injective f)
    (P : ReserveExtension C (fun i => Q.residualBoundary N T (q i)) f (Z.card+1))
    (z₀ z₁ : Z) (hZ : Z = {z₀.val,z₁.val}) (hxy : z₀.val ≠ z₁.val)
    (hsame : assignedLabel G M U₀ U₁ Z z₀.val = assignedLabel G M U₀ U₁ Z z₁.val)
    (hregular : ∀ v, (residualGraph G N T).degree v = h)
    (herror : h-r ≤ D) (b : ℕ) (hb : b ≤ D) (hD : 128*D ≤ h)
    (hs : 2*Fintype.card I ≤ h)
    (hweight₀ : ∀ j, starWeight (residualGraph G N T) z₀.val
      (if σ z₀ = 0 then U₀ else U₁) (C.classes j) ≤ h/8)
    (hweight₁ : ∀ j, starWeight (residualGraph G N T) z₁.val
      (if σ z₁ = 0 then U₀ else U₁) (C.classes j) ≤ h/8)
    (hparallel₀ : ∀ v ∈ (if σ z₁ = 0 then U₀ else U₁),
      ((residualGraph G N T).parallelEdges z₀.val v).card ≤ b)
    (hparallel₁ : ∀ v ∈ (if σ z₁ = 0 then U₀ else U₁),
      ((residualGraph G N T).parallelEdges z₁.val v).card ≤ b) :
    let H := residualGraph G N T
    let label := assignedLabel G M U₀ U₁ Z
    let R := fun i => Q.residualBoundary N T (q i)
    let S₀ := exceptionCorePool H z₀.val (if σ z₀ = 0 then U₀ else U₁)
    let S₁ := exceptionCorePool H z₁.val (if σ z₁ = 0 then U₀ else U₁)
    ∃ F : Fin h → Finset {e : E // e ∉ removedCopies N T},
      (∀ j, H.IsMatching (F j)) ∧
      Pairwise (fun i j => Disjoint (F i) (F j)) ∧
      univ.biUnion F = joiningCopies H label ∪ univ.biUnion R ∪
        pairFiberCopies H z₀.val z₁.val ∪ S₀ ∪ S₁ ∧
      (∀ j, C.classes j ⊆ F j) ∧
      (∀ i, F (f i) = R i) ∧
      (∀ j, Z ⊆ H.edgeSupport (F j)) ∧
      (∀ j k, H.cutOn (F j) (labelShore label {k}) =
        H.cutOn (C.classes j) (labelShore label {k})) ∧
      (∀ j, (F j).card ≤ max (3*L) (Z.card+1)+2) ∧
      (∀ j, (H.edgeSupport (F j)).card ≤ 2*max (3*L) (Z.card+1)+4) := by
  let H := residualGraph G N T
  let label := assignedLabel G M U₀ U₁ Z
  let R := fun i => Q.residualBoundary N T (q i)
  let Ux := if σ z₀ = 0 then U₀ else U₁
  let Uy := if σ z₁ = 0 then U₀ else U₁
  let S₀ := exceptionCorePool H z₀.val Ux
  let S₁ := exceptionCorePool H z₁.val Uy
  let B := pairFiberCopies H z₀.val z₁.val
  let Qcol := univ.image f
  have hQcard : Qcol.card = Fintype.card I := by
    rw [card_image_of_injective _ hf, card_univ]
  have htrace (i : I) : R i ∩ joiningCopies H label = C.classes (f i) := by
    have hh := P.joining (f i)
    rw [P.prescribed i] at hh
    ext e
    have he := Finset.ext_iff.mp hh e
    simpa only [R,mem_inter] using he
  obtain ⟨hB₀,hB₁,c,hc,hcolor⟩ := exists_native_common_bundle_coloring
    G hM U₀ U₁ Z h01 h0Z h1Z hcover σ hcode r Q N T havoid C
    z₀ z₁ hZ hsame hregular herror (by omega) Qcol (by rw [hQcard]; exact hs)
  have hBedge : ∀ e ∈ B, H.edge e = s(z₀.val,z₁.val) :=
    fun e he => (mem_pairFiberCopies_iff H z₀.val z₁.val e).mp he
  have hinternal : ∀ e ∈ B, label (H.firstEnd e) = label (H.secondEnd e) := by
    intro e he
    apply exceptionInternalPool_internal H label Z z₀.val e
    rw [hB₀]
    exact he
  have hBR : ∀ i, Disjoint B (R i) := by
    intro i
    have hh := native_internalPool_disjoint_boundary G hM U₀ U₁ Z h01 h0Z h1Z hcover
      σ hcode r Q N T havoid z₀ (q i)
    rw [hB₀] at hh
    exact hh
  let A₀ := S₀ \ ((univ.biUnion R) ∩ S₀)
  let A₁ := S₁ \ ((univ.biUnion R) ∩ S₁)
  let F₀ := remainingStarColors Qcol (joiningUsedColors C z₀.val) (univ.image c)
  let F₁ := remainingStarColors Qcol (joiningUsedColors C z₁.val) (univ.image c)
  let Base := bundleClasses P B c
  have hbal₀ := native_remaining_star_balance G hM U₀ U₁ Z h01 h0Z h1Z hcover
    σ hcode r Q N T havoid C z₀ (hregular z₀.val) herror
    univ q hq.injOn f hf.injOn (fun i _ => htrace i) B hB₀.symm c hc
    (fun e => ⟨(hcolor e).1,(hcolor e).2.1⟩)
  have hbal₁ := native_remaining_star_balance G hM U₀ U₁ Z h01 h0Z h1Z hcover
    σ hcode r Q N T havoid C z₁ (hregular z₁.val) herror
    univ q hq.injOn f hf.injOn (fun i _ => htrace i) B hB₁.symm c hc
    (fun e => ⟨(hcolor e).1,(hcolor e).2.2⟩)
  have hcard₀ : A₀.card = F₀.card := hbal₀.2.2.2.2.1
  have hcard₁ : A₁.card = F₁.card := hbal₁.2.2.2.2.1
  have hlower₀ : h-Fintype.card I-D ≤ A₀.card := by
    simpa only [card_univ] using hbal₀.2.2.2.2.2
  have hlower₁ : h-Fintype.card I-D ≤ A₁.card := by
    simpa only [card_univ] using hbal₁.2.2.2.2.2
  have hS₀ := assigned_incidence_partition G H hM U₀ U₁ Z
    h01 h0Z h1Z hcover σ hcode z₀
  have hS₁ := assigned_incidence_partition G H hM U₀ U₁ Z
    h01 h0Z h1Z hcover σ hcode z₁
  have hSB₀ : Disjoint S₀ B := by
    have hh := hS₀.2.2.1
    rw [hB₀] at hh
    exact hh
  have hSB₁ : Disjoint S₁ B := by
    have hh := hS₁.2.2.1
    rw [hB₁] at hh
    exact hh
  have hUxZ := (unpaired_assignment_fiber_bounds G hM U₀ U₁ Z
    h01 h0Z h1Z hcover σ hcode z₀).1
  have hUyZ := (unpaired_assignment_fiber_bounds G hM U₀ U₁ Z
    h01 h0Z h1Z hcover σ hcode z₁).1
  have hyUx : z₁.val ∉ Ux := fun hz => disjoint_left.mp hUxZ hz z₁.property
  have hxUy : z₀.val ∉ Uy := fun hz => disjoint_left.mp hUyZ hz z₀.property
  obtain ⟨g₀,g₁,hm,hd,hcov,hsub,hsize,hsupport,houtside,hcovers₀,hcovers₁,_,_⟩ :=
    exists_two_star_extension_on_available H Base z₀.val z₁.val Ux Uy
      A₀ A₁ F₀ F₁ D b (Fintype.card I)
      sdiff_subset sdiff_subset hxy hyUx hxUy hcard₀ hcard₁ hlower₀ hlower₁ hb hD hs
      (bundleClasses_matching P B c hc z₀.val z₁.val hBedge
        (fun e => (hcolor e).1) (fun e => (hcolor e).2))
      (bundleClasses_disjoint P B c hinternal hBR)
      (by
        intro j
        have hh := remaining_star_disjoint_bundleClasses P B S₀ c
          (native_star_disjoint_joining G hM U₀ U₁ Z h01 h0Z h1Z hcover σ hcode N T z₀) hSB₀ j
        apply disjoint_left.mpr
        intro e heA heC
        apply disjoint_left.mp hh _ heC
        simpa only [A₀,R,mem_sdiff,mem_inter,mem_biUnion] using heA)
      (by
        intro j
        have hh := remaining_star_disjoint_bundleClasses P B S₁ c
          (native_star_disjoint_joining G hM U₀ U₁ Z h01 h0Z h1Z hcover σ hcode N T z₁) hSB₁ j
        apply disjoint_left.mpr
        intro e heA heC
        apply disjoint_left.mp hh _ heC
        simpa only [A₁,R,mem_sdiff,mem_inter,mem_biUnion] using heA)
      (bundleClasses_free_on_remaining P B c z₀.val)
      (bundleClasses_free_on_remaining P B c z₁.val)
      (fun v _ => bundleClasses_available_load_le P B c z₀.val v)
      (fun v _ => bundleClasses_available_load_le P B c z₁.val v)
      (bundleClasses_available_weight_le P B c z₀.val Ux (h/8) hweight₀)
      (bundleClasses_available_weight_le P B c z₁.val Uy (h/8) hweight₁)
      hparallel₀ hparallel₁
  let C₁ := starExtendedClasses Base A₀ (fun e => (g₀ e).val)
  let C₂ := starExtendedClasses C₁ A₁ (fun e => (g₁ e).val)
  have hprotected : ∀ i, C₂ (f i) = R i := by
    intro i
    have hnot : f i ∉ F₀ ∪ F₁ := by
      intro hj
      have hQ : f i ∈ Qcol := mem_image_of_mem f (mem_univ i)
      rcases mem_union.mp hj with hj | hj
      · exact ((mem_remainingStarColors _ _ _ _).mp hj).1 hQ
      · exact ((mem_remainingStarColors _ _ _ _).mp hj).1 hQ
    exact (houtside (f i) hnot).trans
      (bundleClasses_prescribed P B c (fun e => (hcolor e).1) i)
  have hcover₀ (j : Fin h) : z₀.val ∈ H.edgeSupport (C₂ j) := by
    by_cases hj : j ∈ F₀
    · exact hcovers₀ j hj
    · have hh := bundleClasses_covers_not_remaining P B c z₀.val
        (fun e => (hcolor e).1)
        (fun i => Q.residualBoundary_covers_exceptional N T havoid (q i) z₀.property)
        (fun e he => by rw [hBedge e he]; simp) j hj
      obtain ⟨e,he,hze⟩ := (H.mem_edgeSupport _ z₀.val).mp hh
      exact (H.mem_edgeSupport _ _).mpr ⟨e,hsub j he,hze⟩
  have hcover₁ (j : Fin h) : z₁.val ∈ H.edgeSupport (C₂ j) := by
    by_cases hj : j ∈ F₁
    · exact hcovers₁ j hj
    · have hh := bundleClasses_covers_not_remaining P B c z₁.val
        (fun e => (hcolor e).1)
        (fun i => Q.residualBoundary_covers_exceptional N T havoid (q i) z₁.property)
        (fun e he => by rw [hBedge e he]; simp) j hj
      obtain ⟨e,he,hze⟩ := (H.mem_edgeSupport _ z₁.val).mp hh
      exact (H.mem_edgeSupport _ _).mpr ⟨e,hsub j he,hze⟩
  have hcut (j : Fin h) (k : Fin 3) :
      H.cutOn (C₂ j) (labelShore label {k}) =
        H.cutOn (C.classes j) (labelShore label {k}) := by
    rw [starExtended_cut_eq H label C₁ A₁ _
      (fun e he => native_star_internal G hM U₀ U₁ Z h01 h0Z h1Z hcover
        σ hcode N T z₁ e (mem_sdiff.mp he).1),
      starExtended_cut_eq H label Base A₀ _
      (fun e he => native_star_internal G hM U₀ U₁ Z h01 h0Z h1Z hcover
        σ hcode N T z₀ e (mem_sdiff.mp he).1)]
    change H.cutOn (starExtendedClasses P.classes B c j) (labelShore label {k}) = _
    rw [starExtended_cut_eq H label P.classes B c hinternal]
    exact P.cut_eq j {k}
  refine ⟨C₂,hm,hd,?_,?_,hprotected,?_,hcut,?_,?_⟩
  · have hh : univ.biUnion C₂ = univ.biUnion Base ∪ A₀ ∪ A₁ := by
      ext e
      have he := Finset.ext_iff.mp hcov e
      simpa only [C₂,C₁,mem_biUnion,mem_union] using he
    have hbcover : univ.biUnion Base = joiningCopies H label ∪ univ.biUnion R ∪ B := by
      ext e
      have he := Finset.ext_iff.mp (bundleClasses_cover P B c) e
      simpa only [Base,R,mem_biUnion,mem_union] using he
    rw [hh,hbcover]
    change joiningCopies H label ∪ univ.biUnion R ∪ B ∪
      (S₀ \ ((univ.biUnion R) ∩ S₀)) ∪ (S₁ \ ((univ.biUnion R) ∩ S₁)) =
      joiningCopies H label ∪ univ.biUnion R ∪ B ∪ S₀ ∪ S₁
    ext e
    simp only [mem_union,mem_sdiff,mem_inter]
    tauto
  · intro j
    exact (P.contains_original j).trans
      ((bundleClasses_contains_reserve P B c j).trans (hsub j))
  · intro j z hz
    rw [hZ] at hz
    rcases mem_insert.mp hz with hz | hz
    · exact hz.symm ▸ hcover₀ j
    · exact (mem_singleton.mp hz).symm ▸ hcover₁ j
  · intro j
    by_cases hjB : j ∈ univ.image c
    · have hnot : j ∉ F₀ ∪ F₁ := by
        intro hj
        rcases mem_union.mp hj with hj | hj
        · exact ((mem_remainingStarColors _ _ _ _).mp hj).2.2 hjB
        · exact ((mem_remainingStarColors _ _ _ _).mp hj).2.2 hjB
      have heq : C₂ j = Base j := houtside j hnot
      rw [heq]
      exact (bundleClasses_card_le P B c hc j).trans (by omega)
    · have hbase : Base j = P.classes j := by
        apply starExtended_eq_of_color_avoided
        intro e he
        exact hjB (he ▸ mem_image_of_mem c (mem_univ e))
      have hh := hsize j
      rw [hbase] at hh
      exact hh.trans (Nat.add_le_add_right (P.card_le j) 2)
  · intro j
    by_cases hjB : j ∈ univ.image c
    · have hnot : j ∉ F₀ ∪ F₁ := by
        intro hj
        rcases mem_union.mp hj with hj | hj
        · exact ((mem_remainingStarColors _ _ _ _).mp hj).2.2 hjB
        · exact ((mem_remainingStarColors _ _ _ _).mp hj).2.2 hjB
      have heq : C₂ j = Base j := houtside j hnot
      rw [heq]
      exact (bundleClasses_support_card_le P B c hc j).trans (by omega)
    · have hbase : Base j = P.classes j := by
        apply starExtended_eq_of_color_avoided
        intro e he
        exact hjB (he ▸ mem_image_of_mem c (mem_univ e))
      have hh := hsupport j
      rw [hbase] at hh
      exact hh.trans (Nat.add_le_add_right (P.support_card_le j) 4)

end Overfull.NativeAssembly
