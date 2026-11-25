import Overfull.AssignedParts.TwoPairs
import Overfull.ResidualPalette.FourTwoOddGrouping

/-!
# Native joining palettes for two separately labeled exceptional pairs

The original perfect-matching representative constructs the four labels and
their parity.  The regular host and its absence of overfull sets then furnish
an actual four-label joining decomposition and a bounded matching palette.
No joining decomposition or palette is supplied as a hypothesis.  The host
may be a residual multigraph on the same vertices; the original representative
need not survive there.
-/

noncomputable section

namespace Overfull.AssignedParts

open Finset Classical FourOdd NativeReserve

variable {V E : Type*} [Fintype V] (G : Multigraph V E)

/-- The actual two-pair assignment has all-even fibers or exactly the two
assigned-core fibers odd, with no separate parity hypothesis. -/
theorem twoPairAssignedLabel_parity {M : Finset E} (hM : G.IsPerfectMatching M)
    (U₀ U₁ Z : Finset V) (h01 : Disjoint U₀ U₁)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (e₀ e₁ : E) (he : e₀ ≠ e₁) (hpair : G.internalOn M Z = {e₀, e₁}) :
    (∀ i, (univ.filter (fun v => twoPairAssignedLabel G M U₀ U₁ Z e₀ v = i)).card % 2 = 0) ∨
      (∀ i, (univ.filter (fun v => twoPairAssignedLabel G M U₀ U₁ Z e₀ v = i)).card % 2 =
        if i = 0 ∨ i = 1 then 1 else 0) := by
  have hfibers := twoPairAssignedLabel_fibers G hM U₀ U₁ Z
    h01 h0Z h1Z hcover e₀ e₁ he hpair
  have h2 : Even (labelShore (twoPairAssignedLabel G M U₀ U₁ Z e₀) {2}).card := by
    rw [hfibers.2.2.1, exceptionalPairPart_card]
    decide
  have h3 : Even (labelShore (twoPairAssignedLabel G M U₀ U₁ Z e₀) {3}).card := by
    rw [hfibers.2.2.2, exceptionalPairPart_card]
    decide
  simpa only [labelShore, mem_singleton] using
    fiber_parity_cases_of_two_even_pairs (twoPairAssignedLabel G M U₀ U₁ Z e₀)
      (hM.even_card G) h2 h3

variable {F : Type*} [Fintype F] (H : Multigraph V F)

/-- Construct the complete actual-copy joining palette for the native
four-part assignment.  Regularity and no-overfull safety are properties of
the actual host; the original matching supplies the assigned vertex fibers. -/
theorem exists_twoPair_joiningPalette_in_host {M : Finset E}
    (hM : G.IsPerfectMatching M) (U₀ U₁ Z : Finset V)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (e₀ e₁ : E) (he : e₀ ≠ e₁) (hpair : G.internalOn M Z = {e₀, e₁})
    {h D L : ℕ} (hregular : ∀ v, H.degree v = h)
    (hno : ∀ X : Finset V, ¬ H.IsOverfull h X)
    (hdegree : ∀ v,
      H.degreeOn (joiningCopies H (twoPairAssignedLabel G M U₀ U₁ Z e₀)) v ≤ D)
    (hL : 0 < L) (hDh : 8*D < h)
    (hbudget : Fintype.card V*D ≤ 2*L*(h-8*D)) :
    Nonempty (JoiningPalette H (twoPairAssignedLabel G M U₀ U₁ Z e₀) h D (2*L)
      (fun i => (univ.filter (fun v => twoPairAssignedLabel G M U₀ U₁ Z e₀ v = i)).card % 2)) := by
  rcases twoPairAssignedLabel_parity G hM U₀ U₁ Z h01 h0Z h1Z hcover
      e₀ e₁ he hpair with heven | hodd
  · obtain ⟨P⟩ := exists_fourJoining_decomposition_of_even_fibers H
      (twoPairAssignedLabel G M U₀ U₁ Z e₀) (by decide) hregular hno heven
    obtain ⟨C⟩ := P.exists_palette H (twoPairAssignedLabel G M U₀ U₁ Z e₀)
      hdegree hL hDh hbudget
    exact ⟨C.congr_parity (fun i => (heven i).symm)⟩
  · obtain ⟨P⟩ := exists_fourTwoOddJoining_decomposition H
      (twoPairAssignedLabel G M U₀ U₁ Z e₀) 0 1 (by decide) h (by decide)
      hregular hno hodd
    obtain ⟨C⟩ := P.exists_palette H (twoPairAssignedLabel G M U₀ U₁ Z e₀)
      hdegree hL hDh hbudget
    exact ⟨C.congr_parity (fun i => (hodd i).symm)⟩

end Overfull.AssignedParts
