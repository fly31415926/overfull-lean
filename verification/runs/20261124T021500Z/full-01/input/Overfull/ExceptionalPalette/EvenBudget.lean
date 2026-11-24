import Overfull.ExceptionalPalette.EvenColors
import Overfull.ResidualPalette.ProtectedBudget

/-!
# Uniform footprint budgets with empty reserved colors

The same explicit margin that pays for protected singleton primary classes
also pays for prescribed empty classes in the all-even case. The capacity
is chosen before the palette, and bounds each whole palette footprint.
-/

noncomputable section

namespace Overfull.FourOdd

open Finset Classical NativeReserve

variable {V E K : Type*} [Fintype V] [Fintype E] [DecidableEq K]
    (G : Multigraph V E) (label : V → K)

/-- A uniform all-even palette construction leaves the prescribed colors
empty and bounds every whole class by the requested support tolerance. -/
theorem EvenJoiningDecomposition.exists_small_palette_avoiding_colors
    (P : EvenJoiningDecomposition G label) {h D : ℕ}
    (Q : Finset (Fin h)) (α δ ε : ℝ)
    (hdegree : ∀ v, G.degreeOn (joiningCopies G label) v ≤ D)
    (hα : 0 < α) (hε : 0 < ε) (hn : 0 < Fintype.card V)
    (hdensity : α*Fintype.card V/30 ≤ h)
    (hD : (D : ℝ) ≤ δ*Fintype.card V)
    (hδ : δ ≤ α/720) (hQ : Q.card ≤ h/2)
    (hδε : δ ≤ ε*α/720) (hlarge : 12/ε ≤ Fintype.card V) :
    let L := (Fintype.card V*D/2)/(h-6*D-Q.card)+1
    ∃ C : JoiningPalette G label h D L (fun _ => 0),
      (∀ j ∈ Q, C.classes j = ∅) ∧
      ∀ j, ((G.edgeSupport (C.classes j)).card : ℝ) ≤ ε*Fintype.card V := by
  dsimp only
  obtain ⟨hL,hmargin,hcapacity,hsupport⟩ :=
    uniform_protected_palette_budget α δ ε (Fintype.card V) h D Q.card
      hα hε hn hdensity hD hδ hQ hδε hlarge
  obtain ⟨C,hC⟩ := P.exists_palette_avoiding_colors G label Q
    hdegree hL hmargin hcapacity
  refine ⟨C,hC,?_⟩
  intro j
  exact (show ((G.edgeSupport (C.classes j)).card : ℝ) ≤
    (6*((Fintype.card V*D/2)/(h-6*D-Q.card)+1) : ℕ) by
      exact_mod_cast C.support_card_le j).trans (by exact_mod_cast hsupport)

end Overfull.FourOdd

namespace Overfull.AssignedParts

open Finset Classical NativeReserve FourOdd

variable {V E F : Type*} [Fintype V] [Fintype F]
    (G : Multigraph V E) (H : Multigraph V F)

/-- On the actual original representative assignment, uniform bounds
produce empty reserved colors, small whole-class supports, and the correct
even uncovered order in every assigned fiber. -/
theorem exists_small_assigned_even_joiningPalette_avoiding_colors_in_host
    (M : Finset E) (U₀ U₁ Z : Finset V) {h D : ℕ}
    (Q : Finset (Fin h)) (α δ ε : ℝ)
    (hregular : ∀ v, H.degree v = h)
    (hno : ∀ X : Finset V, ¬ H.IsOverfull h X)
    (heven : ∀ i, (univ.filter
      (fun v => assignedLabel G M U₀ U₁ Z v = i)).card % 2 = 0)
    (hdegree : ∀ v,
      H.degreeOn (joiningCopies H (assignedLabel G M U₀ U₁ Z)) v ≤ D)
    (hα : 0 < α) (hε : 0 < ε) (hn : 0 < Fintype.card V)
    (hdensity : α*Fintype.card V/30 ≤ h)
    (hD : (D : ℝ) ≤ δ*Fintype.card V)
    (hδ : δ ≤ α/720) (hQ : Q.card ≤ h/2)
    (hδε : δ ≤ ε*α/720) (hlarge : 12/ε ≤ Fintype.card V) :
    let L := (Fintype.card V*D/2)/(h-6*D-Q.card)+1
    ∃ C : JoiningPalette H (assignedLabel G M U₀ U₁ Z) h D L
      (fun i => (univ.filter
        (fun v => assignedLabel G M U₀ U₁ Z v = i)).card % 2),
      (∀ j ∈ Q, C.classes j = ∅) ∧
      (∀ j, ((H.edgeSupport (C.classes j)).card : ℝ) ≤ ε*Fintype.card V) ∧
      ∀ j i, Even ((univ.filter
        (fun v => assignedLabel G M U₀ U₁ Z v = i)) \
        H.edgeSupport (C.classes j)).card := by
  dsimp only
  obtain ⟨P⟩ := exists_evenJoining_decomposition H
    (assignedLabel G M U₀ U₁ Z) (by decide) hregular hno heven
  obtain ⟨B,hB,hsupport⟩ := P.exists_small_palette_avoiding_colors H
    (assignedLabel G M U₀ U₁ Z) Q α δ ε hdegree hα hε hn hdensity
    hD hδ hQ hδε hlarge
  let C := B.congr_parity (fun i => (heven i).symm)
  exact ⟨C,hB,hsupport,
    fun j i => assigned_joiningPalette_uncovered_even G H U₀ U₁ Z C j i⟩

end Overfull.AssignedParts
