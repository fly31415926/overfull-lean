import Overfull.NativeAssembly.OtherCases

/-!
# Native star completion for exceptions assigned different labels

All mutual copies are already joining copies, so the internal exceptional
pool is empty at both centers. Native selected-reserve balance and the
actual available-color budgets therefore produce both complete stars.
-/

noncomputable section

namespace Overfull.NativeAssembly

open Finset Classical AssignedParts FourOdd NativeReserve NativeStar WeightedPalette

variable {V E J I : Type*} [Fintype V] [Fintype E] [Fintype I]

set_option maxHeartbeats 800000 in
/-- Complete both actual stars when the two unpaired exceptions have
distinct assigned labels, retaining exact copies, every reserve color,
all exceptional coverage and all assigned-fiber cuts. -/
theorem exists_native_separate_stars_extension
    (G : Multigraph V E) {M : Finset E} (hM : G.IsPerfectMatching M)
    (U₀ U₁ Z : Finset V) (h01 : Disjoint U₀ U₁)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (σ : Z → Fin 2) (hcode : coarseSignature G M U₀ Z = some σ)
    (r : ℕ) (R : BoundaryPacking G U₀ U₁ Z M r)
    (N : J → Finset E) (T : Finset J)
    (havoid : ∀ j ∈ T, Disjoint (N j) (removedCopies R.boundary univ))
    {h D b L : ℕ} {p : Fin 3 → ℕ}
    (C : JoiningPalette (residualGraph G N T) (assignedLabel G M U₀ U₁ Z) h D L p)
    (z₀ z₁ : Z) (hZ : Z = {z₀.val,z₁.val})
    (hdifferent : assignedLabel G M U₀ U₁ Z z₀.val ≠ assignedLabel G M U₀ U₁ Z z₁.val)
    (hregular : ∀ v, (residualGraph G N T).degree v = h) (herror : h-r ≤ D)
    (q : I → Fin r) (hq : Function.Injective q)
    (f : I → Fin h) (hf : Function.Injective f)
    (htrace : ∀ i, R.residualBoundary N T (q i) ∩
      joiningCopies (residualGraph G N T) (assignedLabel G M U₀ U₁ Z) = C.classes (f i))
    (P : ReserveExtension C (fun i => R.residualBoundary N T (q i)) f (Z.card+1))
    (hb : b ≤ D) (hD : 128*D ≤ h) (hs : 2*Fintype.card I ≤ h)
    (hweight₀ : ∀ j, starWeight (residualGraph G N T) z₀.val
      (if σ z₀ = 0 then U₀ else U₁) (C.classes j) ≤ h/8)
    (hweight₁ : ∀ j, starWeight (residualGraph G N T) z₁.val
      (if σ z₁ = 0 then U₀ else U₁) (C.classes j) ≤ h/8)
    (hparallel₀ : ∀ v ∈ (if σ z₁ = 0 then U₀ else U₁),
      ((residualGraph G N T).parallelEdges z₀.val v).card ≤ b)
    (hparallel₁ : ∀ v ∈ (if σ z₁ = 0 then U₀ else U₁),
      ((residualGraph G N T).parallelEdges z₁.val v).card ≤ b) :
    ∃ F : Fin h → Finset {e : E // e ∉ removedCopies N T},
      (∀ j, (residualGraph G N T).IsMatching (F j)) ∧
      Pairwise (fun i j => Disjoint (F i) (F j)) ∧
      univ.biUnion F =
        joiningCopies (residualGraph G N T) (assignedLabel G M U₀ U₁ Z) ∪
        univ.biUnion (fun i => R.residualBoundary N T (q i)) ∪
        exceptionCorePool (residualGraph G N T) z₀.val (if σ z₀ = 0 then U₀ else U₁) ∪
        exceptionCorePool (residualGraph G N T) z₁.val (if σ z₁ = 0 then U₀ else U₁) ∧
      (∀ i, F (f i) = R.residualBoundary N T (q i)) ∧
      (∀ j, Z ⊆ (residualGraph G N T).edgeSupport (F j)) ∧
      (∀ j i, (residualGraph G N T).cutOn (F j)
          (labelShore (assignedLabel G M U₀ U₁ Z) {i}) =
        (residualGraph G N T).cutOn (C.classes j)
          (labelShore (assignedLabel G M U₀ U₁ Z) {i})) ∧
      (∀ j, (F j).card ≤ max (3*L) (Z.card+1)+2) ∧
      (∀ j, ((residualGraph G N T).edgeSupport (F j)).card ≤
        2*max (3*L) (Z.card+1)+4) := by
  let H := residualGraph G N T
  let label := assignedLabel G M U₀ U₁ Z
  let Ux := if σ z₀ = 0 then U₀ else U₁
  let Uy := if σ z₁ = 0 then U₀ else U₁
  let S₀ := exceptionCorePool H z₀.val Ux
  let S₁ := exceptionCorePool H z₁.val Uy
  let Rsel := univ.biUnion (fun i => R.residualBoundary N T (q i))
  let A₀ := S₀ \ (Rsel ∩ S₀)
  let A₁ := S₁ \ (Rsel ∩ S₁)
  let F₀ := noBundleColors C f z₀.val
  let F₁ := noBundleColors C f z₁.val
  have hA₀ : A₀ ⊆ exceptionCorePool H z₀.val Ux := sdiff_subset
  have hA₁ : A₁ ⊆ exceptionCorePool H z₁.val Uy := sdiff_subset
  have hxy : z₀.val ≠ z₁.val := fun heq => hdifferent (congrArg label heq)
  have hyUx : z₁.val ∉ Ux := by
    dsimp only [Ux]
    split_ifs
    · exact fun hv => disjoint_left.mp h0Z hv z₁.property
    · exact fun hv => disjoint_left.mp h1Z hv z₁.property
  have hxUy : z₀.val ∉ Uy := by
    dsimp only [Uy]
    split_ifs
    · exact fun hv => disjoint_left.mp h0Z hv z₀.property
    · exact fun hv => disjoint_left.mp h1Z hv z₀.property
  have hI₀ : exceptionInternalPool H label Z z₀.val = ∅ :=
    (congrArg (fun X => exceptionInternalPool H label X z₀.val) hZ).trans
      (exceptionInternalPool_pair_eq_empty H label z₀.val z₁.val hdifferent)
  have hZ' : Z = {z₁.val,z₀.val} := by
    apply hZ.trans
    ext v
    simp only [mem_insert,mem_singleton,or_comm]
  have hI₁ : exceptionInternalPool H label Z z₁.val = ∅ :=
    (congrArg (fun X => exceptionInternalPool H label X z₁.val) hZ').trans
      (exceptionInternalPool_pair_eq_empty H label z₁.val z₀.val hdifferent.symm)
  obtain ⟨hcard₀,hlower₀⟩ := native_no_bundle_star_balance G hM U₀ U₁ Z h01 h0Z h1Z
    hcover σ hcode r R N T havoid C z₀ (hregular z₀.val) herror q hq f hf htrace hI₀
  obtain ⟨hcard₁,hlower₁⟩ := native_no_bundle_star_balance G hM U₀ U₁ Z h01 h0Z h1Z
    hcover σ hcode r R N T havoid C z₁ (hregular z₁.val) herror q hq f hf htrace hI₁
  have hAC₀ : ∀ j, Disjoint A₀ (P.classes j) := by
    intro j
    have hd := remaining_star_disjoint_reserve P S₀
      (native_star_disjoint_joining G hM U₀ U₁ Z h01 h0Z h1Z hcover σ hcode N T z₀) j
    apply disjoint_left.mpr
    intro e heA heP
    apply disjoint_left.mp hd ?_ heP
    simpa only [A₀,Rsel,mem_sdiff,mem_inter,mem_biUnion] using heA
  have hAC₁ : ∀ j, Disjoint A₁ (P.classes j) := by
    intro j
    have hd := remaining_star_disjoint_reserve P S₁
      (native_star_disjoint_joining G hM U₀ U₁ Z h01 h0Z h1Z hcover σ hcode N T z₁) j
    apply disjoint_left.mpr
    intro e heA heP
    apply disjoint_left.mp hd ?_ heP
    simpa only [A₁,Rsel,mem_sdiff,mem_inter,mem_biUnion] using heA
  obtain ⟨g₀,g₁,hm,hd,hcov,hsub,hcardF,hsupport,houtside,hcov₀,hcov₁,_hassign₀,_hassign₁⟩ :=
    exists_two_star_extension_on_available H P.classes z₀.val z₁.val Ux Uy A₀ A₁ F₀ F₁
      D b (Fintype.card I) hA₀ hA₁ hxy hyUx hxUy hcard₀ hcard₁ hlower₀ hlower₁
      hb hD hs P.matching P.disjoint hAC₀ hAC₁
      (reserve_free_on_noBundleColors P z₀.val) (reserve_free_on_noBundleColors P z₁.val)
      (fun v _ => reserve_available_load_le P z₀.val v)
      (fun v _ => reserve_available_load_le P z₁.val v)
      (reserve_available_weight_le P z₀.val Ux (h/8) hweight₀)
      (reserve_available_weight_le P z₁.val Uy (h/8) hweight₁)
      hparallel₀ hparallel₁
  let C₁ := starExtendedClasses P.classes A₀ (fun e => (g₀ e).val)
  let F := starExtendedClasses C₁ A₁ (fun e => (g₁ e).val)
  have hprotected (i : I) : f i ∉ F₀ ∪ F₁ := by
    intro hi
    rcases mem_union.mp hi with hi | hi
    · exact ((mem_remainingStarColors _ _ _ _).mp hi).1
        (mem_image_of_mem f (mem_univ i))
    · exact ((mem_remainingStarColors _ _ _ _).mp hi).1
        (mem_image_of_mem f (mem_univ i))
  have hinternal₀ : ∀ e ∈ A₀, label (H.firstEnd e) = label (H.secondEnd e) :=
    fun e he => native_star_internal G hM U₀ U₁ Z h01 h0Z h1Z hcover
      σ hcode N T z₀ e (hA₀ he)
  have hinternal₁ : ∀ e ∈ A₁, label (H.firstEnd e) = label (H.secondEnd e) :=
    fun e he => native_star_internal G hM U₀ U₁ Z h01 h0Z h1Z hcover
      σ hcode N T z₁ e (hA₁ he)
  have hcover₀ (j : Fin h) : z₀.val ∈ H.edgeSupport (F j) := by
    by_cases hj : j ∈ F₀
    · exact hcov₀ j hj
    · have hz := reserve_covers_not_noBundleColors P z₀.val
        (fun i => R.residualBoundary_covers_exceptional N T havoid (q i) z₀.property) j hj
      obtain ⟨e,he,hze⟩ := (H.mem_edgeSupport _ z₀.val).mp hz
      exact (H.mem_edgeSupport _ z₀.val).mpr ⟨e,hsub j he,hze⟩
  have hcover₁ (j : Fin h) : z₁.val ∈ H.edgeSupport (F j) := by
    by_cases hj : j ∈ F₁
    · exact hcov₁ j hj
    · have hz := reserve_covers_not_noBundleColors P z₁.val
        (fun i => R.residualBoundary_covers_exceptional N T havoid (q i) z₁.property) j hj
      obtain ⟨e,he,hze⟩ := (H.mem_edgeSupport _ z₁.val).mp hz
      exact (H.mem_edgeSupport _ z₁.val).mpr ⟨e,hsub j he,hze⟩
  refine ⟨F,hm,hd,?_,?_,?_,?_,?_,?_⟩
  · ext e
    have hcE : (∃ j, e ∈ F j) ↔ ((∃ j, e ∈ P.classes j) ∨ e ∈ A₀) ∨ e ∈ A₁ := by
      simpa only [F,C₁,mem_biUnion,mem_univ,true_and,mem_union] using Finset.ext_iff.mp hcov e
    have hpE : (∃ j, e ∈ P.classes j) ↔ e ∈ joiningCopies H label ∨
        ∃ i, e ∈ R.residualBoundary N T (q i) := by
      simpa only [mem_biUnion,mem_univ,true_and,mem_union] using Finset.ext_iff.mp P.cover e
    simp only [mem_biUnion,mem_univ,true_and,mem_union]
    rw [hcE,hpE]
    simp only [A₀,A₁,Rsel,S₀,S₁,mem_sdiff,mem_inter,mem_biUnion,mem_univ,true_and]
    constructor
    · rintro ((he | ⟨he,_⟩) | ⟨he,_⟩)
      · exact Or.inl (Or.inl he)
      · exact Or.inl (Or.inr he)
      · exact Or.inr he
    · rintro ((he | heS) | heS)
      · exact Or.inl (Or.inl he)
      · by_cases heR : ∃ i, e ∈ R.residualBoundary N T (q i)
        · exact Or.inl (Or.inl (Or.inr heR))
        · exact Or.inl (Or.inr ⟨heS,fun he => heR he.1⟩)
      · by_cases heR : ∃ i, e ∈ R.residualBoundary N T (q i)
        · exact Or.inl (Or.inl (Or.inr heR))
        · exact Or.inr ⟨heS,fun he => heR he.1⟩
  · intro i
    exact (houtside _ (hprotected i)).trans (P.prescribed i)
  · intro j v hv
    rw [hZ] at hv
    rcases mem_insert.mp hv with hv | hv
    · exact hv.symm ▸ hcover₀ j
    · exact (mem_singleton.mp hv).symm ▸ hcover₁ j
  · intro j i
    exact (starExtended_cut_eq H label C₁ A₁ _ hinternal₁ j i).trans
      ((starExtended_cut_eq H label P.classes A₀ _ hinternal₀ j i).trans (P.cut_eq j {i}))
  · intro j
    exact (hcardF j).trans (Nat.add_le_add_right (P.card_le j) 2)
  · intro j
    exact (hsupport j).trans (Nat.add_le_add_right (P.support_card_le j) 4)

end Overfull.NativeAssembly
