import Overfull.CompatibleCircuits.JoiningPartitions
import Overfull.CompatibleCircuits.PairAugmentation

/-!
# The original-host quotient with two odd parts

Exactly two odd label fibers are repaired by one virtual parallel family.
Every class-cut inequality and every even quotient degree is derived from
the regular non-overfull original host. The small-quotient circuit theorem
then applies without an assumed selector or compatible partition.

The labels and their parity are inputs here. Constructing the manuscript's
assigned parts, reserves, palette and full factorization remains separate.
-/

noncomputable section

namespace Overfull.FourOdd

open Finset Classical

variable {V E I : Type*} [Fintype E] [DecidableEq I]
    (G : Multigraph V E) (label : V → I) (a b : I) (hab : a ≠ b) (h : ℕ)

/-- Augment the actual joining-copy quotient, without changing its labels. -/
def twoOddJoiningQuotient : Multigraph I ((joiningCopies G label) ⊕ Fin h) :=
  (joiningQuotient G label).pairAugmentation a b hab h

/-- Original classes record host endpoints; every virtual copy has one fresh class. -/
def twoOddJoiningClasses : I → ((joiningCopies G label) ⊕ Fin h) → V ⊕ Unit :=
  Multigraph.pairAugmentationClass h ((joiningGraph G label).endpointClass label)

variable [Fintype V]

/-- The original host supplies every augmented class-cut bound. No bound on
joining degrees or prior quotient admissibility is assumed. -/
theorem twoOddJoiningQuotient_admissible
    (hregular : ∀ v, G.degree v = h)
    (hno : ∀ X : Finset V, ¬ G.IsOverfull h X)
    (hfibers : ∀ i, (univ.filter (fun v => label v = i)).card % 2 =
      if i = a ∨ i = b then 1 else 0) :
    (twoOddJoiningQuotient G label a b hab h).AdmissibleOn
      (twoOddJoiningClasses G label h) univ := by
  apply (joiningQuotient G label).pairAugmentation_admissibleOn_univ a b hab h
    ((joiningGraph G label).endpointClass label)
  · intro A hclosed i v
    have hA : (labelShore label A).card % 2 = 0 := by
      rw [labelShore_card_parity_of_two_odd_fibers label a b hab hfibers]
      simp [hclosed]
    rw [joiningQuotient_classCutOn_card]
    by_cases hvi : label v = i
    · rw [if_pos hvi]
      change 2 * G.degreeOn (G.cutOn univ (labelShore label A)) v ≤
        (joiningCut G label A).card
      rw [joiningCut_card]
      exact regular_even_cut_twice_degree_le G hregular hno _ hA v
    · simp [hvi]
  · intro A hseparating
    have hA : (labelShore label A).card % 2 = 1 := by
      rw [labelShore_card_parity_of_two_odd_fibers label a b hab hfibers]
      simp [hseparating]
    constructor
    · change h ≤ (joiningCut G label A).card
      rw [joiningCut_card]
      exact regular_odd_cut_lower G hregular hno _ hA
    · intro i v
      exact (joiningQuotient_classCutOn_card_le_degree G label i v A).trans_eq
        (hregular v)

/-- The added family repairs the degree parity of precisely the two odd fibers. -/
theorem twoOddJoiningQuotient_even_degrees
    (hregular : ∀ v, G.degree v = h)
    (hfibers : ∀ i, (univ.filter (fun v => label v = i)).card % 2 =
      if i = a ∨ i = b then 1 else 0) (i : I) :
    Even ((twoOddJoiningQuotient G label a b hab h).degree i) := by
  change Even (((joiningQuotient G label).pairAugmentation a b hab h).degree i)
  rw [Nat.even_iff, Multigraph.pairAugmentation_degree]
  have hp := joiningQuotient_degree_parity_of_two_odd_fibers
    G label hregular a b hfibers i
  by_cases hi : i = a ∨ i = b <;> simp only [hi, if_true, if_false] at * <;> omega

/-- A compatible circuit partition is constructed on the actual augmented
joining copies of any regular non-overfull host with at most three labels
and exactly two odd label fibers. -/
theorem exists_twoOddJoining_circuitPartition [Fintype I]
    (hI : Fintype.card I ≤ 3)
    (hregular : ∀ v, G.degree v = h)
    (hno : ∀ X : Finset V, ¬ G.IsOverfull h X)
    (hfibers : ∀ i, (univ.filter (fun v => label v = i)).card % 2 =
      if i = a ∨ i = b then 1 else 0) :
    Nonempty ((twoOddJoiningQuotient G label a b hab h).CompatibleCircuitPartition
      (twoOddJoiningClasses G label h) univ) := by
  apply (twoOddJoiningQuotient G label a b hab h).
    exists_compatibleCircuitPartition_of_card_le_three hI (twoOddJoiningClasses G label h)
      univ (twoOddJoiningQuotient_admissible G label a b hab h hregular hno hfibers)
  exact twoOddJoiningQuotient_even_degrees G label a b hab h hregular hfibers

end Overfull.FourOdd
