import Overfull.CompatibleCircuits.Deletion

/-!
# Exact circuit deletion on at most three labels

Every circuit on at most three labels crosses each cut in zero or two
copies. Consequently, deleting a circuit from an admissible even-degree
graph preserves every half-cut inequality exactly when it meets each tight
incidence class on every tight cut that it crosses. No checks are needed
for positive-slack cuts.

This is an exact criterion on actual edge copies. It does not assume or
prove that a compatible circuit satisfying the criterion exists.
-/

namespace Overfull.Multigraph

open Finset Classical

variable {V E K : Type*} [Fintype V] (G : Multigraph V E)

/-- On at most three vertices, a circuit crosses any cut at most twice. -/
theorem IsCircuit.cutOn_card_le_two_of_card_le_three
    {D : Finset E} (hD : G.IsCircuit D) (hV : Fintype.card V ≤ 3)
    (X : Finset V) : (G.cutOn D X).card ≤ 2 := by
  have hsub : G.cutOn D X ⊆ D := filter_subset _ _
  have hbound := (card_le_card hsub).trans (hD.card_le.trans hV)
  have heven := Nat.even_iff.mp (IsCircuit.even_cutOn G hD X)
  omega

/-- The only possible circuit-cut sizes on at most three vertices. -/
theorem IsCircuit.cutOn_card_zero_or_two_of_card_le_three
    {D : Finset E} (hD : G.IsCircuit D) (hV : Fintype.card V ≤ 3)
    (X : Finset V) : (G.cutOn D X).card = 0 ∨ (G.cutOn D X).card = 2 := by
  have hbound := hD.cutOn_card_le_two_of_card_le_three G hV X
  have heven := Nat.even_iff.mp (IsCircuit.even_cutOn G hD X)
  omega

/-- A circuit is safely removable on at most three labels precisely when
its correction inequality holds on the tight cuts of the original graph.
All positive-slack cuts are automatically preserved. -/
theorem admissibleOn_sdiff_iff_tight_cuts_of_card_le_three
    (hV : Fintype.card V ≤ 3) (classOf : V → E → K)
    {C D : Finset E} (hDC : D ⊆ C) (hD : G.IsCircuit D)
    (hadmissible : G.AdmissibleOn classOf C)
    (heven : ∀ v, Even (G.degreeOn C v)) :
    G.AdmissibleOn classOf (C \ D) ↔
      ∀ v k X, (G.cutOn C X).card = 2 * (G.classCutOn classOf C v k X).card →
        (G.cutOn D X).card ≤ 2 * (G.classCutOn classOf D v k X).card := by
  rw [G.admissibleOn_sdiff_iff classOf hDC]
  constructor
  · intro h v k X htight
    have hh := h v k X
    omega
  · intro h v k X
    by_cases htight :
        (G.cutOn C X).card = 2 * (G.classCutOn classOf C v k X).card
    · have hh := h v k X htight
      omega
    · have hle := hadmissible v k X
      have hparity := Nat.even_iff.mp (G.even_cutOn_of_even_degrees heven X)
      have hsmall := hD.cutOn_card_le_two_of_card_le_three G hV X
      omega

/-- The tight-cut criterion as an actual incidence witness: whenever the
removed circuit crosses a tight cut, it must use a copy from that tight
class. This is equivalent to preservation of all half-cut inequalities. -/
theorem admissibleOn_sdiff_iff_meets_tight_classes_of_card_le_three
    (hV : Fintype.card V ≤ 3) (classOf : V → E → K)
    {C D : Finset E} (hDC : D ⊆ C) (hD : G.IsCircuit D)
    (hadmissible : G.AdmissibleOn classOf C)
    (heven : ∀ v, Even (G.degreeOn C v)) :
    G.AdmissibleOn classOf (C \ D) ↔
      ∀ v k X, (G.cutOn C X).card = 2 * (G.classCutOn classOf C v k X).card →
        (G.cutOn D X).Nonempty → (G.classCutOn classOf D v k X).Nonempty := by
  rw [G.admissibleOn_sdiff_iff_tight_cuts_of_card_le_three hV classOf hDC hD
    hadmissible heven]
  constructor
  · intro h v k X htight hcross
    have hle := h v k X htight
    have hpos := card_pos.mpr hcross
    apply card_pos.mp
    omega
  · intro h v k X htight
    by_cases hcross : (G.cutOn D X).Nonempty
    · have hpos := card_pos.mpr (h v k X htight hcross)
      have hsmall := hD.cutOn_card_le_two_of_card_le_three G hV X
      omega
    · rw [not_nonempty_iff_eq_empty.mp hcross, card_empty]
      exact Nat.zero_le _

/-- Specialization to an actual quotient on three named labels. -/
theorem threeLabel_admissibleOn_sdiff_iff_tight_classes
    (Q : Multigraph (Fin 3) E) (classOf : Fin 3 → E → K)
    {C D : Finset E} (hDC : D ⊆ C) (hD : Q.IsCircuit D)
    (hadmissible : Q.AdmissibleOn classOf C)
    (heven : ∀ v, Even (Q.degreeOn C v)) :
    Q.AdmissibleOn classOf (C \ D) ↔
      ∀ v k X, (Q.cutOn C X).card = 2 * (Q.classCutOn classOf C v k X).card →
        (Q.cutOn D X).Nonempty → (Q.classCutOn classOf D v k X).Nonempty :=
  Q.admissibleOn_sdiff_iff_meets_tight_classes_of_card_le_three
    (by simp) classOf hDC hD hadmissible heven

end Overfull.Multigraph
