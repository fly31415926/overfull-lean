import Overfull.CompatibleCircuits.FourDegreeTwo
import Overfull.CompatibleCircuits.FourAdmissibleRegular

/-!
# Compatible circuits with bounded four-label complexity

Degree-zero and degree-two suppression combine with the exact four-regular
construction. This gives every admissible even-degree instance whose degrees
are at most four, and every instance with at most eight actual copies.
The latter conclusion permits unequal degrees larger than four.

The final obstruction theorem records the precise remaining range: any
counterexample on four labels has degree at least four at every label,
degree at least six somewhere, and at least nine actual copies.
-/

namespace Overfull.Multigraph

open Finset Classical
open scoped BigOperators

variable {V E K : Type*}

/-- The handshake identity over the whole finite ambient vertex type. -/
theorem degreeOn_sum_univ [Fintype V] (G : Multigraph V E) (C : Finset E) :
    (∑ v, G.degreeOn C v) = 2 * C.card := by
  have hsum : (∑ v ∈ G.edgeSupport C, G.degreeOn C v) = ∑ v, G.degreeOn C v := by
    apply sum_subset (subset_univ _)
    intro v _ hv
    exact G.degreeOn_eq_zero_of_not_mem hv
  rw [← hsum]
  exact G.degreeOn_sum C

variable (Q : Multigraph (Fin 4) E)

/-- Complete four-label existence whenever every degree is at most four.
No connectedness or equality of degrees is required. -/
theorem exists_compatibleCircuitPartition_of_four_label_degree_le_four
    (classOf : Fin 4 → E → K) (C : Finset E)
    (hadmissible : Q.AdmissibleOn classOf C)
    (heven : ∀ v, Even (Q.degreeOn C v))
    (hbound : ∀ v, Q.degreeOn C v ≤ 4) :
    Nonempty (Q.CompatibleCircuitPartition classOf C) := by
  by_cases hsmall : ∃ v, Q.degreeOn C v ≤ 2
  · exact Q.exists_compatibleCircuitPartition_of_four_label_small_degree
      classOf C hadmissible heven hsmall
  · apply Q.exists_compatibleCircuitPartition_of_four_regular classOf C _ hadmissible
    intro v
    have hlarge : ¬ Q.degreeOn C v ≤ 2 := fun h => hsmall ⟨v, h⟩
    have hp := Nat.even_iff.mp (heven v)
    have hb := hbound v
    omega

/-- At most eight selected copies either have a low-degree label or form
an exactly four-regular graph. This is pure actual-copy degree counting. -/
theorem fourLabel_low_degree_or_four_regular_of_card_le_eight
    (C : Finset E) (heven : ∀ v, Even (Q.degreeOn C v)) (hsmall : C.card ≤ 8) :
    (∃ v, Q.degreeOn C v ≤ 2) ∨ (∀ v, Q.degreeOn C v = 4) := by
  by_cases hlow : ∃ v, Q.degreeOn C v ≤ 2
  · exact Or.inl hlow
  · right
    have hge (v : Fin 4) : 4 ≤ Q.degreeOn C v := by
      have hnot : ¬ Q.degreeOn C v ≤ 2 := fun h => hlow ⟨v, h⟩
      have hp := Nat.even_iff.mp (heven v)
      omega
    have hsum : Q.degreeOn C 0 + Q.degreeOn C 1 + Q.degreeOn C 2 +
        Q.degreeOn C 3 = 2 * C.card := by
      simpa only [Fin.sum_univ_succ, Fin.isValue, Fin.val_zero,
        Fin.zero_eta, Fin.eta, Nat.add_zero, Nat.add_assoc] using Q.degreeOn_sum_univ C
    have h0 := hge 0
    have h1 := hge 1
    have h2 := hge 2
    have h3 := hge 3
    intro v
    fin_cases v <;> omega

/-- Complete existence for every four-label admissible Eulerian graph
with at most eight actual copies, including unequal degree sequences. -/
theorem exists_compatibleCircuitPartition_of_four_label_card_le_eight
    (classOf : Fin 4 → E → K) (C : Finset E)
    (hadmissible : Q.AdmissibleOn classOf C)
    (heven : ∀ v, Even (Q.degreeOn C v)) (hsmall : C.card ≤ 8) :
    Nonempty (Q.CompatibleCircuitPartition classOf C) := by
  rcases Q.fourLabel_low_degree_or_four_regular_of_card_le_eight C heven hsmall with
      hlow | hregular
  · exact Q.exists_compatibleCircuitPartition_of_four_label_small_degree
      classOf C hadmissible heven hlow
  · exact Q.exists_compatibleCircuitPartition_of_four_regular classOf C hregular hadmissible

/-- Any unresolved four-label instance lies beyond both verified ranges. -/
theorem fourLabel_counterexample_degree_and_size
    (classOf : Fin 4 → E → K) (C : Finset E)
    (hadmissible : Q.AdmissibleOn classOf C)
    (heven : ∀ v, Even (Q.degreeOn C v))
    (hnone : ¬ Nonempty (Q.CompatibleCircuitPartition classOf C)) :
    (∀ v, 4 ≤ Q.degreeOn C v) ∧ (∃ v, 6 ≤ Q.degreeOn C v) ∧ 9 ≤ C.card := by
  have hlow : ¬ ∃ v, Q.degreeOn C v ≤ 2 := by
    intro h
    exact hnone (Q.exists_compatibleCircuitPartition_of_four_label_small_degree
      classOf C hadmissible heven h)
  have hmin (v : Fin 4) : 4 ≤ Q.degreeOn C v := by
    have hnot : ¬ Q.degreeOn C v ≤ 2 := fun h => hlow ⟨v, h⟩
    have hp := Nat.even_iff.mp (heven v)
    omega
  refine ⟨hmin, ?_, ?_⟩
  · by_contra! hsmall
    apply hnone
    apply Q.exists_compatibleCircuitPartition_of_four_label_degree_le_four
      classOf C hadmissible heven
    intro v
    have hh := hsmall v
    have hp := Nat.even_iff.mp (heven v)
    omega
  · by_contra h
    apply hnone
    exact Q.exists_compatibleCircuitPartition_of_four_label_card_le_eight
      classOf C hadmissible heven (by omega)

variable [Fintype V] (G : Multigraph V E)

/-- A low-degree label suffices on any finite vertex type of cardinality
at most four. Added labels are isolated and original copies are unchanged. -/
theorem exists_compatibleCircuitPartition_of_card_le_four_small_degree
    (hV : Fintype.card V ≤ 4) (classOf : V → E → K) (C : Finset E)
    (hadmissible : G.AdmissibleOn classOf C)
    (heven : ∀ v, Even (G.degreeOn C v)) (hlow : ∃ v, G.degreeOn C v ≤ 2) :
    Nonempty (G.CompatibleCircuitPartition classOf C) := by
  obtain ⟨φ⟩ : Nonempty (V ↪ Fin 4) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hV)
  obtain ⟨v, hv⟩ := hlow
  obtain ⟨P⟩ := (G.embedVertices φ).exists_compatibleCircuitPartition_of_four_label_small_degree
    (embedIncidenceClasses φ classOf) C
    ((G.embedVertices_admissibleOn φ classOf C).mpr hadmissible)
    (G.embedVertices_even_degrees φ heven)
    ⟨φ v, by simpa only [G.embedVertices_degreeOn] using hv⟩
  exact ⟨P.of_embedVertices G φ⟩

/-- Complete existence for maximum degree at most four and at most four
vertices, with no choice of a particular vertex labeling in the statement. -/
theorem exists_compatibleCircuitPartition_of_card_le_four_degree_le_four
    (hV : Fintype.card V ≤ 4) (classOf : V → E → K) (C : Finset E)
    (hadmissible : G.AdmissibleOn classOf C)
    (heven : ∀ v, Even (G.degreeOn C v)) (hbound : ∀ v, G.degreeOn C v ≤ 4) :
    Nonempty (G.CompatibleCircuitPartition classOf C) := by
  obtain ⟨φ⟩ : Nonempty (V ↪ Fin 4) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hV)
  have hbound' (w : Fin 4) : (G.embedVertices φ).degreeOn C w ≤ 4 := by
    by_cases hw : ∃ v, φ v = w
    · obtain ⟨v, rfl⟩ := hw
      simpa only [G.embedVertices_degreeOn] using hbound v
    · rw [G.embedVertices_degreeOn_zero φ C hw]
      omega
  obtain ⟨P⟩ := (G.embedVertices φ).exists_compatibleCircuitPartition_of_four_label_degree_le_four
    (embedIncidenceClasses φ classOf) C
    ((G.embedVertices_admissibleOn φ classOf C).mpr hadmissible)
    (G.embedVertices_even_degrees φ heven) hbound'
  exact ⟨P.of_embedVertices G φ⟩

/-- At most eight actual copies on at most four labels need no separate
maximum-degree bound. -/
theorem exists_compatibleCircuitPartition_of_card_le_four_eight_copies
    (hV : Fintype.card V ≤ 4) (classOf : V → E → K) (C : Finset E)
    (hadmissible : G.AdmissibleOn classOf C)
    (heven : ∀ v, Even (G.degreeOn C v)) (hsmall : C.card ≤ 8) :
    Nonempty (G.CompatibleCircuitPartition classOf C) := by
  obtain ⟨φ⟩ : Nonempty (V ↪ Fin 4) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hV)
  obtain ⟨P⟩ := (G.embedVertices φ).exists_compatibleCircuitPartition_of_four_label_card_le_eight
    (embedIncidenceClasses φ classOf) C
    ((G.embedVertices_admissibleOn φ classOf C).mpr hadmissible)
    (G.embedVertices_even_degrees φ heven) hsmall
  exact ⟨P.of_embedVertices G φ⟩

end Overfull.Multigraph
