import Overfull.NativeWeighted.WeightedJoining
import Overfull.ExceptionalPalette.ReserveNative

/-!
# Native weighted joining colors with odd assigned cores

The actual surviving reserve crossings are forced primary pieces in the
original residual joining decomposition. Weighted grouping protects their
entire singleton colors and controls both exceptional star resources in the
full `h`-color palette. The crossings then recover their original reserve
indices, allowing the whole prescribed boundaries to be inserted.
-/

noncomputable section

namespace Overfull.NativeWeighted

open Finset Classical NativeReserve AssignedParts FourOdd WeightedPalette

variable {V E J κ : Type*} [Fintype V] [Fintype E] [Fintype κ]

/-- Construct an actual odd-core joining palette with weighted star
budgets, protecting half of the surviving native reserve crossings. -/
theorem exists_native_odd_weighted_joining_palette
    (G : Multigraph V E) (U₀ U₁ Z : Finset V) {M : Finset E}
    (hM : G.IsPerfectMatching M)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2)
    (r : ℕ) (R : BoundaryPacking G U₀ U₁ Z M r)
    (hodd : (corePart G M Z U₀).card % 2 = 1)
    (N : J → Finset E) (T : Finset J)
    (havoid : ∀ j ∈ T, Disjoint (N j) (removedCopies R.boundary univ))
    (h D b L : ℕ) (hregular : ∀ v, (residualGraph G N T).degree v = h)
    (hno : ∀ X : Finset V, ¬ (residualGraph G N T).IsOverfull h X)
    (hdegree : ∀ v, (joiningGraph (residualGraph G N T)
      (assignedLabel G M U₀ U₁ Z)).degree v ≤ D)
    (z : κ → V) (U : κ → Finset V) (hresources : Fintype.card κ ≤ 2)
    (hparallel : ∀ i, ∀ v ∈ U i,
      ((residualGraph G N T).parallelEdges (z i) v).card ≤ b)
    (hbD : b ≤ D) (hh : 0 < h) (hDh : 128 * D ≤ h)
    (hrh : r ≤ h) (hL : 0 < L)
    (hbudget : Fintype.card V * D ≤ 2 * L * (h - r/2 - 32 * D)) :
    ∃ (A : Finset (joiningCopies (residualGraph G N T) (assignedLabel G M U₀ U₁ Z)))
      (C : JoiningPalette (residualGraph G N T) (assignedLabel G M U₀ U₁ Z)
        h D L (fun i => if i=0 ∨ i=1 then 1 else 0)),
      A.card = r/2 ∧
      (∀ e ∈ A, e.val.val ∈ removedCopies R.boundary univ) ∧
      (∀ e ∈ A, (joiningQuotient (residualGraph G N T)
        (assignedLabel G M U₀ U₁ Z)).edge e = s(0,1)) ∧
      (∀ i j, starWeight (residualGraph G N T) (z i) (U i) (C.classes j) ≤ h/8) ∧
      ∃ f : A → Fin h, Function.Injective f ∧ ∀ e : A,
        C.classes (f e) = {e.val.val} := by
  let H := residualGraph G N T
  let label := assignedLabel G M U₀ U₁ Z
  have hfibers : ∀ i, (univ.filter (fun v => label v=i)).card % 2 =
      if i=0 ∨ i=1 then 1 else 0 := by
    intro i
    have hpar := assignedLabel_parity_eq_core_crossing G hM U₀ U₁ Z
      h01 h0Z h1Z hcover i
    rw [← corePart_card_parity G hM U₀ U₁ Z h01 h0Z h1Z hcover, hodd] at hpar
    exact hpar
  obtain ⟨A,hAcard,hsource,hpair⟩ := R.exists_half_residual_crossing_reserve
    hM h01 h0Z h1Z hcover hZ hodd N T havoid
  have hA : A.card ≤ h := by rw [hAcard]; omega
  have hD : D ≤ h-A.card := by rw [hAcard]; omega
  obtain ⟨P,hforced⟩ := exists_twoOddJoining_decomposition_with_reserved_primary
    H label 0 1 (by decide) h D (by decide) hregular hno hfibers
    A hpair hA hdegree hD
  let S := A.image (fun e => ({e.val} : Finset {e : E // e ∉ removedCopies N T}))
  have hScard : S.card = A.card := by
    apply card_image_of_injective
    intro e f hef
    exact Subtype.ext (singleton_inj.mp hef)
  have hSP : S ⊆ P.primary := by
    intro B hB
    obtain ⟨e,he,rfl⟩ := mem_image.mp hB
    exact hforced e he
  have hdegreeOn (v : V) : H.degreeOn (joiningCopies H label) v ≤ D := by
    rw [← joiningGraph_degree_eq]
    exact hdegree v
  obtain ⟨C,hweight,hprotected⟩ := P.exists_star_weighted_protected_palette
    H label S hSP z U hresources hdegreeOn hparallel
    (fun i => (hregular (z i)).le) hbD hh hDh hL
    (by rw [hScard,hAcard]; omega)
    (by rw [hScard,hAcard]; exact hbudget)
  have hex : ∀ e : A, ∃ j, C.classes j = {e.val.val} := by
    intro e
    exact hprotected {e.val.val} (mem_image.mpr ⟨e.val,e.property,rfl⟩)
  choose f hf using hex
  refine ⟨A,C,hAcard,hsource,hpair,hweight,f,?_,hf⟩
  intro e e' heq
  have hset : ({e.val.val} : Finset {e : E // e ∉ removedCopies N T}) = {e'.val.val} :=
    (hf e).symm.trans ((congrArg C.classes heq).trans (hf e'))
  exact Subtype.ext (Subtype.ext (singleton_inj.mp hset))

/-- Recover injective native reserve indices from the weighted protected
crossings and insert the exact prescribed full boundaries. Star-weight
control is retained on the original joining classes, for transfer to the
available colors after reserve insertion. -/
theorem exists_native_odd_weighted_reserved_palette
    (G : Multigraph V E) (U₀ U₁ Z : Finset V) {M : Finset E}
    (hM : G.IsPerfectMatching M)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2)
    (r : ℕ) (R : BoundaryPacking G U₀ U₁ Z M r)
    (hodd : (corePart G M Z U₀).card % 2 = 1)
    (N : J → Finset E) (T : Finset J)
    (havoid : ∀ j ∈ T, Disjoint (N j) (removedCopies R.boundary univ))
    (h D b L : ℕ) (hregular : ∀ v, (residualGraph G N T).degree v = h)
    (hno : ∀ X : Finset V, ¬ (residualGraph G N T).IsOverfull h X)
    (hdegree : ∀ v, (joiningGraph (residualGraph G N T)
      (assignedLabel G M U₀ U₁ Z)).degree v ≤ D)
    (z : κ → V) (U : κ → Finset V) (hresources : Fintype.card κ ≤ 2)
    (hparallel : ∀ i, ∀ v ∈ U i,
      ((residualGraph G N T).parallelEdges (z i) v).card ≤ b)
    (hbD : b ≤ D) (hh : 0 < h) (hDh : 128 * D ≤ h)
    (hrh : r ≤ h) (hL : 0 < L)
    (hbudget : Fintype.card V * D ≤ 2 * L * (h - r/2 - 32 * D)) :
    ∃ (A : Finset (joiningCopies (residualGraph G N T) (assignedLabel G M U₀ U₁ Z)))
      (C : JoiningPalette (residualGraph G N T) (assignedLabel G M U₀ U₁ Z)
        h D L (fun i => if i=0 ∨ i=1 then 1 else 0))
      (q : A → Fin r) (f : A → Fin h),
      A.card = r/2 ∧ Function.Injective q ∧ Function.Injective f ∧
      (∀ e : A, e.val.val.val ∈ R.boundary (q e)) ∧
      (∀ e : A, C.classes (f e) = {e.val.val}) ∧
      (∀ i j, starWeight (residualGraph G N T) (z i) (U i) (C.classes j) ≤ h/8) ∧
      (∀ e : A, R.residualBoundary N T (q e) ∩
        joiningCopies (residualGraph G N T) (assignedLabel G M U₀ U₁ Z) = C.classes (f e)) ∧
      ∃ P : ReserveExtension C (fun e => R.residualBoundary N T (q e)) f (Z.card+1),
        (∀ e : A, Z ⊆ (residualGraph G N T).edgeSupport (P.classes (f e))) ∧
        (∀ e : A,
          Even (U₀ \ (residualGraph G N T).edgeSupport (P.classes (f e))).card ∧
          Even (U₁ \ (residualGraph G N T).edgeSupport (P.classes (f e))).card) := by
  obtain ⟨A,C,hcard,hsource,_hpair,hweight,f,hf,hfclass⟩ :=
    exists_native_odd_weighted_joining_palette G U₀ U₁ Z hM h01 h0Z h1Z hcover hZ
      r R hodd N T havoid h D b L hregular hno hdegree z U hresources hparallel
      hbD hh hDh hrh hL hbudget
  have hex : ∀ e : A, ∃ i : Fin r, e.val.val.val ∈ R.boundary i := by
    intro e
    obtain ⟨i,_,hi⟩ := (mem_removedCopies R.boundary univ _).mp (hsource e.val e.property)
    exact ⟨i,hi⟩
  choose q hq using hex
  have htrace (e : A) : R.residualBoundary N T (q e) ∩
      joiningCopies (residualGraph G N T) (assignedLabel G M U₀ U₁ Z) = C.classes (f e) := by
    rw [hfclass e]
    exact R.residualBoundary_joining_singleton hM h01 h0Z h1Z hcover hZ hodd
      N T (q e) e.val (hq e)
  have hqinj : Function.Injective q := by
    intro e e' heq
    have hs := congrArg (fun i => R.residualBoundary N T i ∩
      joiningCopies (residualGraph G N T) (assignedLabel G M U₀ U₁ Z)) heq
    dsimp only at hs
    rw [htrace e,htrace e',hfclass e,hfclass e'] at hs
    exact Subtype.ext (Subtype.ext (singleton_inj.mp hs))
  let B : A → Finset {e : E // e ∉ removedCopies N T} :=
    fun e => R.residualBoundary N T (q e)
  have hBm : ∀ e, (residualGraph G N T).IsMatching (B e) :=
    fun e => R.residualBoundary_matching N T (q e)
  have hBd : Pairwise (fun e e' => Disjoint (B e) (B e')) := by
    intro e e' hee
    exact R.residualBoundary_disjoint N T (fun hqq => hee (hqinj hqq))
  have hBcard (e : A) : (B e).card ≤ Z.card+1 :=
    R.residualBoundary_card_le N T havoid (q e)
  let P := reserveExtension C B f hf hBm hBd
    (by
      intro e
      ext v
      simpa only [B,mem_inter] using (Finset.ext_iff.mp (htrace e) v)) hBcard
  refine ⟨A,C,q,f,hcard,hqinj,hf,hq,hfclass,hweight,htrace,P,?_,?_⟩
  · intro e
    rw [P.prescribed]
    exact R.residualBoundary_covers_exceptional N T havoid (q e)
  · intro e
    rw [P.prescribed]
    exact R.residualBoundary_uncovered_even N T havoid h01 h0Z h1Z hcover (q e)

end Overfull.NativeWeighted
