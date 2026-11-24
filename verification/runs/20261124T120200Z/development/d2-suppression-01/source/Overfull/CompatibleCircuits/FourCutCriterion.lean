import Overfull.CompatibleCircuits.Deletion

/-!
# Exact obstructions to removing a circuit on four labels

All counts refer to actual edge copies. A compatible circuit may cross a
four-label cut four times. A tight cut therefore both requires a copy from
its tight class and forbids four crossings; on a cut of slack two, four
crossings require a copy from that class. These conditions are necessary
and sufficient, including empty cuts. They are a deletion criterion, not
an assumed existence theorem for a circuit passing the criterion.
-/

namespace Overfull.Multigraph

open Finset Classical

variable {V E K : Type*} (G : Multigraph V E)

/-- Every circuit with at most four actual copies crosses a cut zero,
two, or four times. The ambient graph need not have four vertices. -/
theorem IsCircuit.cutOn_card_zero_two_four_of_card_le_four
    {D : Finset E} (hD : G.IsCircuit D) (hsmall : D.card ≤ 4)
    (X : Finset V) :
    (G.cutOn D X).card = 0 ∨ (G.cutOn D X).card = 2 ∨
      (G.cutOn D X).card = 4 := by
  have hbound := (card_le_card (filter_subset _ _ : G.cutOn D X ⊆ D)).trans hsmall
  have hparity := Nat.even_iff.mp (hD.even_cutOn G X)
  omega

/-- The exact witness form of safe deletion for a compatible circuit of
length at most four. The second clause is the additional obstruction that
is absent for pairs and triangles. -/
theorem admissibleOn_sdiff_iff_four_cut_witnesses
    (classOf : V → E → K) {C D : Finset E} (hDC : D ⊆ C)
    (hD : G.IsCircuit D) (hsmall : D.card ≤ 4)
    (hcomp : G.Compatible classOf D)
    (hadmissible : G.AdmissibleOn classOf C)
    (heven : ∀ v, Even (G.degreeOn C v)) :
    G.AdmissibleOn classOf (C \ D) ↔
      (∀ v k X,
        (G.cutOn C X).card = 2 * (G.classCutOn classOf C v k X).card →
        (G.cutOn D X).card ≤ 2 ∧
          ((G.cutOn D X).Nonempty → (G.classCutOn classOf D v k X).Nonempty)) ∧
      (∀ v k X,
        (G.cutOn C X).card = 2 * (G.classCutOn classOf C v k X).card + 2 →
        (G.cutOn D X).card = 4 → (G.classCutOn classOf D v k X).Nonempty) := by
  rw [G.admissibleOn_sdiff_iff classOf hDC]
  constructor
  · intro h
    constructor
    · intro v k X htight
      have hh := h v k X
      have hc := hcomp.classCutOn_card_le_one G v k X
      refine ⟨by omega, ?_⟩
      intro hcross
      have hp := card_pos.mpr hcross
      apply card_pos.mp
      omega
    · intro v k X htwo hfour
      have hh := h v k X
      apply card_pos.mp
      omega
  · rintro ⟨htight, htwo⟩ v k X
    have hbound := (card_le_card (filter_subset _ _ : G.cutOn D X ⊆ D)).trans hsmall
    have hle := hadmissible v k X
    have hparity := Nat.even_iff.mp (G.even_cutOn_of_even_degrees heven X)
    have hDparity := Nat.even_iff.mp (hD.even_cutOn G X)
    by_cases hzero :
        (G.cutOn C X).card = 2 * (G.classCutOn classOf C v k X).card
    · obtain ⟨hsmallcut, hmeet⟩ := htight v k X hzero
      by_cases hcross : (G.cutOn D X).Nonempty
      · have hc := card_pos.mpr (hmeet hcross)
        omega
      · have hc : (G.cutOn D X).card = 0 := card_eq_zero.mpr
          (not_nonempty_iff_eq_empty.mp hcross)
        omega
    · by_cases hslacktwo :
          (G.cutOn C X).card = 2 * (G.classCutOn classOf C v k X).card + 2
      · by_cases hfour : (G.cutOn D X).card = 4
        · have hc := card_pos.mpr (htwo v k X hslacktwo hfour)
          omega
        · omega
      · omega

/-- A pair or triangle is safely removable exactly when it meets each
tight class on every cut that it crosses, even in a larger ambient graph. -/
theorem admissibleOn_sdiff_iff_tight_classes_of_small_circuit
    (classOf : V → E → K) {C D : Finset E} (hDC : D ⊆ C)
    (hD : G.IsCircuit D) (hsmall : D.card ≤ 3)
    (hadmissible : G.AdmissibleOn classOf C)
    (heven : ∀ v, Even (G.degreeOn C v)) :
    G.AdmissibleOn classOf (C \ D) ↔
      ∀ v k X,
        (G.cutOn C X).card = 2 * (G.classCutOn classOf C v k X).card →
        (G.cutOn D X).Nonempty → (G.classCutOn classOf D v k X).Nonempty := by
  rw [G.admissibleOn_sdiff_iff classOf hDC]
  constructor
  · intro h v k X htight hcross
    have hh := h v k X
    have hp := card_pos.mpr hcross
    apply card_pos.mp
    omega
  · intro h v k X
    have hbound := (card_le_card (filter_subset _ _ : G.cutOn D X ⊆ D)).trans hsmall
    have hle := hadmissible v k X
    have hparity := Nat.even_iff.mp (G.even_cutOn_of_even_degrees heven X)
    have hDparity := Nat.even_iff.mp (hD.even_cutOn G X)
    by_cases htight :
        (G.cutOn C X).card = 2 * (G.classCutOn classOf C v k X).card
    · by_cases hcross : (G.cutOn D X).Nonempty
      · have hc := card_pos.mpr (h v k X htight hcross)
        omega
      · have hc : (G.cutOn D X).card = 0 := card_eq_zero.mpr
          (not_nonempty_iff_eq_empty.mp hcross)
        omega
    · omega

/-- The witness criterion for four named quotient labels. -/
theorem fourLabel_admissibleOn_sdiff_iff_cut_witnesses
    (Q : Multigraph (Fin 4) E) (classOf : Fin 4 → E → K)
    {C D : Finset E} (hDC : D ⊆ C) (hD : Q.IsCircuit D)
    (hcomp : Q.Compatible classOf D)
    (hadmissible : Q.AdmissibleOn classOf C)
    (heven : ∀ v, Even (Q.degreeOn C v)) :
    Q.AdmissibleOn classOf (C \ D) ↔
      (∀ v k X,
        (Q.cutOn C X).card = 2 * (Q.classCutOn classOf C v k X).card →
        (Q.cutOn D X).card ≤ 2 ∧
          ((Q.cutOn D X).Nonempty → (Q.classCutOn classOf D v k X).Nonempty)) ∧
      (∀ v k X,
        (Q.cutOn C X).card = 2 * (Q.classCutOn classOf C v k X).card + 2 →
        (Q.cutOn D X).card = 4 → (Q.classCutOn classOf D v k X).Nonempty) := by
  exact Q.admissibleOn_sdiff_iff_four_cut_witnesses classOf hDC hD
    (by simpa using hD.card_le) hcomp hadmissible heven

end Overfull.Multigraph
