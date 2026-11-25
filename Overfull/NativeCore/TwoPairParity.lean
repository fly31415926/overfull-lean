import Overfull.NativeCore.Parity
import Overfull.AssignedParts.TwoPairs

/-!
# Original-core parity after the two-pair external assembly

The four actual assigned fibers retain their cut parity. Once the external
family covers every exception, uncovered vertices in either assigned core
are exactly the uncovered vertices of the corresponding original core.
-/

noncomputable section

namespace Overfull.NativeCore

open Finset Classical AssignedParts FourOdd NativeReserve

variable {V E F : Type*} [Fintype V]

/-- The actual four-fiber assignment transfers matching cut parity to
even uncovered original cores, including a possible fifth exception. -/
theorem uncovered_twoPair_old_cores_even (G : Multigraph V E) (H : Multigraph V F)
    {M : Finset E} (hM : G.IsPerfectMatching M) (U₀ U₁ Z : Finset V)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (e₀ e₁ : E) (he : e₀ ≠ e₁) (hpair : G.internalOn M Z = {e₀,e₁})
    (B : Finset F) (hB : H.IsMatching B) (hZ : Z ⊆ H.edgeSupport B)
    (hparity : ∀ i : Fin 4,
      (H.cutOn B (labelShore (twoPairAssignedLabel G M U₀ U₁ Z e₀) {i})).card % 2 =
        (univ.filter (fun v => twoPairAssignedLabel G M U₀ U₁ Z e₀ v = i)).card % 2) :
    Even (U₀ \ H.edgeSupport B).card ∧ Even (U₁ \ H.edgeSupport B).card := by
  have hfibers := twoPairAssignedLabel_fibers G hM U₀ U₁ Z
    h01 h0Z h1Z hcover e₀ e₁ he hpair
  have heven (i : Fin 4) :
      Even ((labelShore (twoPairAssignedLabel G M U₀ U₁ Z e₀) {i}) \
        H.edgeSupport B).card := by
    apply (hB.uncovered_even_iff_cut_parity H _).mpr
    simpa only [labelShore,mem_singleton] using (hparity i).symm
  have h₀ := heven 0
  have h₁ := heven 1
  rw [hfibers.1,uncovered_corePart_eq G H M U₀ Z B hZ] at h₀
  rw [hfibers.2.1,uncovered_corePart_eq G H M U₁ Z B hZ] at h₁
  exact ⟨h₀,h₁⟩

variable [Fintype F]

/-- Every externally completed color inherits old-core parity from the
constructed four-label palette once all exceptions are saturated. -/
theorem old_core_parity_of_twoPair_joining_cuts
    (G : Multigraph V E) (H : Multigraph V F)
    {M : Finset E} (hM : G.IsPerfectMatching M) (U₀ U₁ Z : Finset V)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (e₀ e₁ : E) (he : e₀ ≠ e₁) (hpair : G.internalOn M Z = {e₀,e₁})
    {h D L : ℕ}
    (C : JoiningPalette H (twoPairAssignedLabel G M U₀ U₁ Z e₀) h D L
      (fun i => (univ.filter (fun v => twoPairAssignedLabel G M U₀ U₁ Z e₀ v=i)).card % 2))
    (B : Fin h → Finset F) (hB : ∀ j, H.IsMatching (B j))
    (hZ : ∀ j, Z ⊆ H.edgeSupport (B j))
    (hcuts : ∀ j i,
      H.cutOn (B j) (labelShore (twoPairAssignedLabel G M U₀ U₁ Z e₀) {i}) =
      H.cutOn (C.classes j) (labelShore (twoPairAssignedLabel G M U₀ U₁ Z e₀) {i})) :
    ∀ j, Even (U₀ \ H.edgeSupport (B j)).card ∧
      Even (U₁ \ H.edgeSupport (B j)).card := by
  intro j
  apply uncovered_twoPair_old_cores_even G H hM U₀ U₁ Z h01 h0Z h1Z hcover
    e₀ e₁ he hpair (B j) (hB j) (hZ j)
  intro i
  rw [hcuts j i,C.cut_parity j i]

end Overfull.NativeCore
