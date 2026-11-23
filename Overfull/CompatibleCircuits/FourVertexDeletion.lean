import Overfull.CompatibleCircuits.Deletion
import Overfull.CompatibleCircuits.FourLabel

/-!
# Exact critical-cut test for deleting compatible circuits on at most four labels

The previous four-label deletion result gave a sufficient condition on `Fin 4`.
Here necessity and sufficiency hold for *any* finite vertex type of cardinality
at most four. A circuit can cross a shore in 0, 2, or 4 actual edge copies.
Compatibility implies at most one removed copy in a single incidence class.
Consequently a safe circuit may not cross a tight cut four times; if it
crosses a tight cut twice, it must meet the tight class. At slack two,
a four-crossing circuit must meet that class. These are exact constraints,
not a proof that a circuit satisfying them exists.
-/

namespace Overfull.Multigraph

open Finset Classical

variable {V E K : Type*} [Fintype V] (G : Multigraph V E)

/-- A circuit on at most four vertices crosses each cut in 0, 2, or 4
copies, even with parallel edges. -/
theorem IsCircuit.cutOn_card_zero_two_four_of_card_le_four
    {D : Finset E} (hD : G.IsCircuit D) (hV : Fintype.card V ≤ 4)
    (X : Finset V) :
    (G.cutOn D X).card = 0 ∨
      (G.cutOn D X).card = 2 ∨
      (G.cutOn D X).card = 4 := by
  have hsub : G.cutOn D X ⊆ D := Finset.filter_subset _ _
  have hbound := (Finset.card_le_card hsub).trans (hD.card_le.trans hV)
  have heven := Nat.even_iff.mp (IsCircuit.even_cutOn G hD X)
  omega

/-- The four-label critical-cut correction is necessary as well as
sufficient; it works for arbitrary finite label types of size at most four. -/
theorem admissibleOn_sdiff_iff_critical_cuts_of_card_le_four
    (hV : Fintype.card V ≤ 4) (classOf : V → E → K)
    {C D : Finset E} (hDC : D ⊆ C) (hD : G.IsCircuit D)
    (hadmissible : G.AdmissibleOn classOf C)
    (heven : ∀ v, Even (G.degreeOn C v)) :
    G.AdmissibleOn classOf (C \ D) ↔
      ∀ v k X,
        ((G.cutOn C X).card = 2 * (G.classCutOn classOf C v k X).card ∨
          (G.cutOn C X).card = 2 * (G.classCutOn classOf C v k X).card + 2) →
        2 * (G.classCutOn classOf C v k X).card + (G.cutOn D X).card ≤
          (G.cutOn C X).card + 2 * (G.classCutOn classOf D v k X).card := by
  rw [G.admissibleOn_sdiff_iff classOf hDC]
  constructor
  · intro h v k X _
    exact h v k X
  · intro h v k X
    by_cases hsmall :
        (G.cutOn C X).card < 2 * (G.classCutOn classOf C v k X).card + 4
    · exact h v k X
        (G.admissible_small_slack classOf hadmissible heven v k X hsmall)
    · have hcut : (G.cutOn D X).card ≤ 4 := by
        have hsub : G.cutOn D X ⊆ D := Finset.filter_subset _ _
        exact (Finset.card_le_card hsub).trans (hD.card_le.trans hV)
      omega

/-- Exact witness formulation for safely removing a *compatible* circuit.
At a tight cut, four crossing copies are forbidden outright. At a slack-two
cut, a four-crossing circuit must hit the relevant incidence class. -/
theorem admissibleOn_sdiff_iff_four_label_witnesses
    (hV : Fintype.card V ≤ 4) (classOf : V → E → K)
    {C D : Finset E} (hDC : D ⊆ C) (hD : G.IsCircuit D)
    (hcompatible : G.Compatible classOf D)
    (hadmissible : G.AdmissibleOn classOf C)
    (heven : ∀ v, Even (G.degreeOn C v)) :
    G.AdmissibleOn classOf (C \ D) ↔
      (∀ v k X,
        (G.cutOn C X).card = 2 * (G.classCutOn classOf C v k X).card →
          ((G.cutOn D X).card = 2 →
            1 ≤ (G.classCutOn classOf D v k X).card) ∧
          (G.cutOn D X).card ≠ 4) ∧
      (∀ v k X,
        (G.cutOn C X).card = 2 * (G.classCutOn classOf C v k X).card + 2 →
          (G.cutOn D X).card = 4 →
            1 ≤ (G.classCutOn classOf D v k X).card) := by
  rw [G.admissibleOn_sdiff_iff_critical_cuts_of_card_le_four
    hV classOf hDC hD hadmissible heven]
  constructor
  · intro h
    constructor
    · intro v k X htight
      have hh := h v k X (Or.inl htight)
      have hbound := Compatible.classCutOn_card_le_one G hcompatible v k X
      constructor
      · intro htwo
        omega
      · intro hfour
        omega
    · intro v k X hslack hfour
      have hh := h v k X (Or.inr hslack)
      omega
  · rintro ⟨htight, hslack⟩ v k X hcritical
    have hcut := hD.cutOn_card_zero_two_four_of_card_le_four G hV X
    rcases hcritical with hzero | htwo
    · rcases hcut with hcut | hcut | hcut
      · omega
      · have hreq := (htight v k X hzero).1 hcut
        omega
      · exact False.elim ((htight v k X hzero).2 hcut)
    · rcases hcut with hcut | hcut | hcut
      · omega
      · omega
      · have hreq := hslack v k X htwo hcut
        omega

end Overfull.Multigraph
