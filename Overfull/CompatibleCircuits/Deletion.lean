import Overfull.CompatibleCircuits.Counting

/-!
# Exact admissibility after deleting actual copies

Deleting a compatible circuit does not automatically preserve the half-cut
inequalities.  This file records the exact condition.  On four labels only
cuts with slack zero or two can obstruct a deletion.
-/

namespace Overfull.Multigraph

open Finset Classical

variable {V E K : Type*} (G : Multigraph V E)

theorem cutOn_sdiff (C D : Finset E) (X : Finset V) :
    G.cutOn (C \ D) X = G.cutOn C X \ G.cutOn D X := by
  ext e
  simp only [mem_cutOn, Finset.mem_sdiff]
  tauto

theorem classCutOn_sdiff (classOf : V → E → K) (C D : Finset E)
    (v : V) (k : K) (X : Finset V) :
    G.classCutOn classOf (C \ D) v k X =
      G.classCutOn classOf C v k X \ G.classCutOn classOf D v k X := by
  ext e
  simp only [classCutOn, Finset.mem_filter, mem_cutOn, Finset.mem_sdiff]
  tauto

theorem cutOn_card_sdiff_add {C D : Finset E} (hDC : D ⊆ C) (X : Finset V) :
    (G.cutOn (C \ D) X).card + (G.cutOn D X).card = (G.cutOn C X).card := by
  rw [G.cutOn_sdiff]
  exact Finset.card_sdiff_add_card_eq_card (Finset.filter_subset_filter _ hDC)

theorem classCutOn_card_sdiff_add (classOf : V → E → K)
    {C D : Finset E} (hDC : D ⊆ C) (v : V) (k : K) (X : Finset V) :
    (G.classCutOn classOf (C \ D) v k X).card +
      (G.classCutOn classOf D v k X).card = (G.classCutOn classOf C v k X).card := by
  rw [G.classCutOn_sdiff]
  exact Finset.card_sdiff_add_card_eq_card
    (Finset.filter_subset_filter _ (Finset.filter_subset_filter _ hDC))

/-- The exact correction term required for admissibility after deletion. -/
theorem admissibleOn_sdiff_iff (classOf : V → E → K)
    {C D : Finset E} (hDC : D ⊆ C) :
    G.AdmissibleOn classOf (C \ D) ↔
      ∀ v k X, 2 * (G.classCutOn classOf C v k X).card + (G.cutOn D X).card ≤
        (G.cutOn C X).card + 2 * (G.classCutOn classOf D v k X).card := by
  constructor
  · intro h v k X
    have hcut := G.cutOn_card_sdiff_add hDC X
    have hclass := G.classCutOn_card_sdiff_add classOf hDC v k X
    have hh := h v k X
    omega
  · intro h v k X
    have hcut := G.cutOn_card_sdiff_add hDC X
    have hclass := G.classCutOn_card_sdiff_add classOf hDC v k X
    have hh := h v k X
    omega

/-- In an admissible even-degree graph, every cut with slack below four
has slack exactly zero or exactly two. -/
theorem admissible_small_slack (classOf : V → E → K) {C : Finset E}
    (hadmissible : G.AdmissibleOn classOf C) (heven : ∀ v, Even (G.degreeOn C v))
    (v : V) (k : K) (X : Finset V)
    (hsmall : (G.cutOn C X).card < 2 * (G.classCutOn classOf C v k X).card + 4) :
    (G.cutOn C X).card = 2 * (G.classCutOn classOf C v k X).card ∨
      (G.cutOn C X).card = 2 * (G.classCutOn classOf C v k X).card + 2 := by
  have hle := hadmissible v k X
  have hparity := Nat.even_iff.mp (G.even_cutOn_of_even_degrees heven X)
  omega

/-- On four labels, checking the exact correction only on slack-zero and
slack-two cuts suffices for deleting a circuit safely.  Finding a circuit
that passes these checks remains an additional existence problem. -/
theorem admissibleOn_sdiff_of_critical_cuts (Q : Multigraph (Fin 4) E)
    (classOf : Fin 4 → E → K) {C D : Finset E} (hDC : D ⊆ C)
    (hD : Q.IsCircuit D)
    (hadmissible : Q.AdmissibleOn classOf C)
    (heven : ∀ v, Even (Q.degreeOn C v))
    (hcritical : ∀ v k X,
      ((Q.cutOn C X).card = 2 * (Q.classCutOn classOf C v k X).card ∨
        (Q.cutOn C X).card = 2 * (Q.classCutOn classOf C v k X).card + 2) →
      2 * (Q.classCutOn classOf C v k X).card + (Q.cutOn D X).card ≤
        (Q.cutOn C X).card + 2 * (Q.classCutOn classOf D v k X).card) :
    Q.AdmissibleOn classOf (C \ D) := by
  apply (Q.admissibleOn_sdiff_iff classOf hDC).mpr
  intro v k X
  by_cases hsmall :
      (Q.cutOn C X).card < 2 * (Q.classCutOn classOf C v k X).card + 4
  · exact hcritical v k X
      (Q.admissible_small_slack classOf hadmissible heven v k X hsmall)
  · have hcut : (Q.cutOn D X).card ≤ 4 := by
      have hsubset : Q.cutOn D X ⊆ D := fun e he => (Q.mem_cutOn D X e |>.mp he).1
      exact (Finset.card_le_card hsubset).trans (by simpa using hD.card_le)
    omega

end Overfull.Multigraph
