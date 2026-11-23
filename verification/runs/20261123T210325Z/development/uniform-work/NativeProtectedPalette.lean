import Overfull.ResidualPalette.ReservedPrimary
import Overfull.ResidualPalette.NativeReservedCrossings
import Overfull.ResidualPalette.ProtectedGrouping

/-!
# Actual protected singleton palette classes from the native reserve

Half of the surviving native reserve crossings are selected in their actual
residual copy type. They are forced to be singleton primary pieces and remain
entire singleton classes throughout the bounded palette grouping. Every
selected copy retains its original reserve membership.
-/

noncomputable section
namespace Overfull.NativeReserve
open Finset Classical AssignedParts FourOdd

variable {V E J : Type*} [Fintype V] [Fintype E]

/-- Construct a parity-correct joining palette with an injectively indexed
family of r/2 singleton classes, each consisting of an actual surviving
original reserved crossing. The remaining palette has all matching,
coverage, footprint and vertex-load certificates. -/
theorem exists_native_protected_joiningPalette
    (G : Multigraph V E) (U₀ U₁ Z : Finset V) {M : Finset E}
    (hM : G.IsPerfectMatching M)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2)
    (r : ℕ) (Q : BoundaryPacking G U₀ U₁ Z M r)
    (hodd : (corePart G M Z U₀).card % 2 = 1)
    (N : J → Finset E) (T : Finset J)
    (havoid : ∀ j ∈ T, Disjoint (N j) (removedCopies Q.boundary univ))
    (h D L : ℕ) (hregular : ∀ v, (residualGraph G N T).degree v = h)
    (hno : ∀ X : Finset V, ¬ (residualGraph G N T).IsOverfull h X)
    (hdegree : ∀ v, (joiningGraph (residualGraph G N T)
      (assignedLabel G M U₀ U₁ Z)).degree v ≤ D)
    (hL : 0 < L) (hmargin : 6*D+r/2 < h)
    (hbudget : Fintype.card V*D ≤ 2*L*(h-6*D-r/2)) :
    ∃ (A : Finset (joiningCopies (residualGraph G N T) (assignedLabel G M U₀ U₁ Z)))
      (C : JoiningPalette (residualGraph G N T) (assignedLabel G M U₀ U₁ Z)
        h D L (fun i => if i=0 ∨ i=1 then 1 else 0)),
      A.card = r/2 ∧
      (∀ e ∈ A, e.val.val ∈ removedCopies Q.boundary univ) ∧
      (∀ e ∈ A, (joiningQuotient (residualGraph G N T)
        (assignedLabel G M U₀ U₁ Z)).edge e = s(0,1)) ∧
      (∀ e ∈ A, ∃ j, C.classes j = {e.val}) ∧
      ∃ f : A → Fin h, Function.Injective f ∧ ∀ e : A,
        C.classes (f e) = {e.val.val} := by
  let H := residualGraph G N T
  let label := assignedLabel G M U₀ U₁ Z
  have hfibers : ∀ i, (univ.filter (fun v => label v=i)).card % 2 =
      if i=0 ∨ i=1 then 1 else 0 := by
    intro i
    have hh := assignedLabel_parity_eq_core_crossing G hM U₀ U₁ Z h01 h0Z h1Z hcover i
    rw [← corePart_card_parity G hM U₀ U₁ Z h01 h0Z h1Z hcover,hodd] at hh
    exact hh
  obtain ⟨A,hAcard,hsource,hpair⟩ := Q.exists_half_residual_crossing_reserve
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
  obtain ⟨C,hprotected⟩ := P.exists_protected_palette H label S hSP hdegreeOn hL
    (by rw [hScard,hAcard]; exact hmargin)
    (by rw [hScard,hAcard]; exact hbudget)
  have hsingle (e : joiningCopies H label) (he : e ∈ A) :
      ∃ j, C.classes j = {e.val} :=
    hprotected {e.val} (mem_image.mpr ⟨e,he,rfl⟩)
  have hex : ∀ e : A, ∃ j, C.classes j = {e.val.val} := fun e => hsingle e.val e.property
  choose f hf using hex
  refine ⟨A,C,hAcard,hsource,hpair,hsingle,f,?_,hf⟩
  intro e e' heq
  have hset : ({e.val.val} : Finset {e : E // e ∉ removedCopies N T}) = {e'.val.val} :=
    (hf e).symm.trans ((congrArg C.classes heq).trans (hf e'))
  exact Subtype.ext (Subtype.ext (singleton_inj.mp hset))

end Overfull.NativeReserve
