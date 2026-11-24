import Overfull.ExceptionalPalette.ReserveInsertion

/-!
# Actual native protected colors contain whole reserve boundaries

The selected surviving crossings recover injective original reserve indices.
The corresponding protected singleton colors are replaced by those entire
original boundaries. The resulting color family retains all joining copies
and colors exactly the selected internal reserve copies, covers every
exception in each protected color, and leaves even uncovered old cores.
-/

noncomputable section
namespace Overfull.NativeReserve
open Finset Classical AssignedParts FourOdd

variable {V E J : Type*} [Fintype V] [Fintype E]

/-- Complete the selected half-reserve colors with their actual original
compressed boundaries. The other colors and every joining-copy assignment
are unchanged; all newly inserted copies are internal to assigned fibers.
This theorem does not color other exceptional incidences or complete cores. -/
theorem exists_native_reserved_palette
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
        h D L (fun i => if i=0 ∨ i=1 then 1 else 0))
      (q : A → Fin r) (f : A → Fin h),
      A.card = r/2 ∧ Function.Injective q ∧ Function.Injective f ∧
      (∀ e : A, e.val.val.val ∈ Q.boundary (q e)) ∧
      (∀ e : A, C.classes (f e) = {e.val.val}) ∧
      ∃ P : ReserveExtension C (fun e => Q.residualBoundary N T (q e)) f (Z.card+1),
        (∀ e : A, Z ⊆ (residualGraph G N T).edgeSupport (P.classes (f e))) ∧
        (∀ e : A,
          Even (U₀ \ (residualGraph G N T).edgeSupport (P.classes (f e))).card ∧
          Even (U₁ \ (residualGraph G N T).edgeSupport (P.classes (f e))).card) := by
  obtain ⟨A,C,hcard,hsource,_hpair,_hsingle,f,hf,hfclass⟩ :=
    exists_native_protected_joiningPalette G U₀ U₁ Z hM h01 h0Z h1Z hcover hZ
      r Q hodd N T havoid h D L hregular hno hdegree hL hmargin hbudget
  have hex : ∀ e : A, ∃ i : Fin r, e.val.val.val ∈ Q.boundary i := by
    intro e
    obtain ⟨i,_,hi⟩ := (mem_removedCopies Q.boundary univ _).mp (hsource e.val e.property)
    exact ⟨i,hi⟩
  choose q hq using hex
  have htrace (e : A) : Q.residualBoundary N T (q e) ∩
      joiningCopies (residualGraph G N T) (assignedLabel G M U₀ U₁ Z) = C.classes (f e) := by
    rw [hfclass e]
    exact Q.residualBoundary_joining_singleton hM h01 h0Z h1Z hcover hZ hodd
      N T (q e) e.val (hq e)
  have hqinj : Function.Injective q := by
    intro e e' heq
    have hs := congrArg (fun i => Q.residualBoundary N T i ∩
      joiningCopies (residualGraph G N T) (assignedLabel G M U₀ U₁ Z)) heq
    dsimp only at hs
    rw [htrace e,htrace e',hfclass e,hfclass e'] at hs
    exact Subtype.ext (Subtype.ext (singleton_inj.mp hs))
  let B : A → Finset {e : E // e ∉ removedCopies N T} :=
    fun e => Q.residualBoundary N T (q e)
  have hBm : ∀ e, (residualGraph G N T).IsMatching (B e) :=
    fun e => Q.residualBoundary_matching N T (q e)
  have hBd : Pairwise (fun e e' => Disjoint (B e) (B e')) := by
    intro e e' hee
    exact Q.residualBoundary_disjoint N T (fun hqq => hee (hqinj hqq))
  have hBcard (e : A) : (B e).card ≤ Z.card+1 :=
    Q.residualBoundary_card_le N T havoid (q e)
  let P := reserveExtension C B f hf hBm hBd
    (by
      intro e
      ext z
      simpa only [B,mem_inter] using (Finset.ext_iff.mp (htrace e) z)) hBcard
  refine ⟨A,C,q,f,hcard,hqinj,hf,hq,hfclass,P,?_,?_⟩
  · intro e
    rw [P.prescribed]
    exact Q.residualBoundary_covers_exceptional N T havoid (q e)
  · intro e
    rw [P.prescribed]
    exact Q.residualBoundary_uncovered_even N T havoid h01 h0Z h1Z hcover (q e)

end Overfull.NativeReserve
