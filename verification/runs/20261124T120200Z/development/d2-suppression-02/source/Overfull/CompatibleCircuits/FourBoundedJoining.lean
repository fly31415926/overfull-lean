import Overfull.CompatibleCircuits.FourBounded
import Overfull.CompatibleCircuits.TwoOddDecomposition

/-!
# Four-label joining decompositions with a small boundary

The regular original host supplies admissibility and parity. The low-degree
four-label theorem then constructs actual quotient circuits, and the existing
injective copy maps give exact original matching families. For two odd fibers,
one small even-fiber boundary suffices; the virtual family is still arbitrary.
These are circuit-stage results with explicit small-boundary hypotheses.
They do not claim the unrestricted terminal factorization proposition.
-/

noncomputable section

namespace Overfull.FourOdd

open Finset Classical

variable {V E I : Type*} [Fintype E] [DecidableEq I]
    (G : Multigraph V E) (label : V → I)

/-- A lifted compatible circuit meets each original fiber zero or twice. -/
theorem liftJoiningParts_cut_zero_or_two [Fintype V]
    {C : Finset (joiningCopies G label)}
    (P : (joiningQuotient G label).CompatibleCircuitPartition
      ((joiningGraph G label).endpointClass label) C)
    {M : Finset E} (hM : M ∈ liftJoiningParts G label P) (i : I) :
    (G.cutOn M (labelShore label {i})).card = 0 ∨
      (G.cutOn M (labelShore label {i})).card = 2 := by
  obtain ⟨D, hD, rfl⟩ := mem_image.mp hM
  rw [← joiningQuotient_degreeOn_eq_cut]
  by_cases hi : i ∈ (joiningQuotient G label).edgeSupport D
  · exact Or.inr ((P.circuit D hD).2.1 i hi)
  · exact Or.inl ((joiningQuotient G label).degreeOn_eq_zero_of_not_mem hi)

variable [Fintype V] [Fintype I]

/-- Exact original matching pieces for a four-label even-fiber circuit stage. -/
structure FourJoiningDecomposition where
  parts : Finset (Finset E)
  nonempty : ∀ M ∈ parts, M.Nonempty
  matching : ∀ M ∈ parts, G.IsMatching M
  card_le : ∀ M ∈ parts, M.card ≤ 4
  disjoint : ∀ M ∈ parts, ∀ N ∈ parts, M ≠ N → Disjoint M N
  cover : parts.biUnion id = joiningCopies G label
  fiber_cut : ∀ M ∈ parts, ∀ i,
    (G.cutOn M (labelShore label {i})).card = 0 ∨
      (G.cutOn M (labelShore label {i})).card = 2

/-- Exact original-copy transport of a constructed four-label partition. -/
def fourJoiningDecompositionOfPartition (hI : Fintype.card I ≤ 4)
    (P : (joiningQuotient G label).CompatibleCircuitPartition
      ((joiningGraph G label).endpointClass label) univ) :
    FourJoiningDecomposition G label where
  parts := liftJoiningParts G label P
  nonempty := fun _ hM => liftJoiningParts_nonempty G label P hM
  matching := fun _ hM => liftJoiningParts_isMatching G label P hM
  card_le := fun _ hM => (liftJoiningParts_card_le G label P hM).trans hI
  disjoint := fun _ hM _ hN hne => liftJoiningParts_disjoint G label P hM hN hne
  cover := liftJoiningParts_cover_univ G label P
  fiber_cut := fun _ hM i => liftJoiningParts_cut_zero_or_two G label P hM i

/-- On at most four even fibers, a boundary with at most two original
joining copies permits complete circuit-stage construction. Other joining
degrees and the regular degree are unrestricted. -/
theorem exists_fourJoining_decomposition_of_even_fibers_small_cut
    (hI : Fintype.card I ≤ 4) {h : ℕ}
    (hregular : ∀ v, G.degree v = h)
    (hno : ∀ X : Finset V, ¬ G.IsOverfull h X)
    (hfibers : ∀ i, (univ.filter (fun v => label v = i)).card % 2 = 0)
    (hsmall : ∃ i, (G.cutOn univ (labelShore label {i})).card ≤ 2) :
    Nonempty (FourJoiningDecomposition G label) := by
  obtain ⟨i, hi⟩ := hsmall
  have hlow : (joiningQuotient G label).degreeOn univ i ≤ 2 := by
    change (joiningQuotient G label).degree i ≤ 2
    rwa [joiningQuotient_degree_eq_cut]
  obtain ⟨P⟩ := (joiningQuotient G label).exists_compatibleCircuitPartition_of_card_le_four_small_degree
    hI ((joiningGraph G label).endpointClass label) univ
    (joiningQuotient_admissible_of_even_fibers G label hregular hno hfibers)
    (joiningQuotient_degree_even_of_even_fibers G label hregular hfibers) ⟨i, hlow⟩
  exact ⟨fourJoiningDecompositionOfPartition G label hI P⟩

/-- On at most four even fibers, boundaries of size at most four also
give an exact original-copy circuit-stage decomposition. -/
theorem exists_fourJoining_decomposition_of_even_fibers_bounded_cuts
    (hI : Fintype.card I ≤ 4) {h : ℕ}
    (hregular : ∀ v, G.degree v = h)
    (hno : ∀ X : Finset V, ¬ G.IsOverfull h X)
    (hfibers : ∀ i, (univ.filter (fun v => label v = i)).card % 2 = 0)
    (hbound : ∀ i, (G.cutOn univ (labelShore label {i})).card ≤ 4) :
    Nonempty (FourJoiningDecomposition G label) := by
  have hdegrees (i : I) : (joiningQuotient G label).degreeOn univ i ≤ 4 := by
    change (joiningQuotient G label).degree i ≤ 4
    simpa only [joiningQuotient_degree_eq_cut] using hbound i
  obtain ⟨P⟩ := (joiningQuotient G label).exists_compatibleCircuitPartition_of_card_le_four_degree_le_four
    hI ((joiningGraph G label).endpointClass label) univ
    (joiningQuotient_admissible_of_even_fibers G label hregular hno hfibers)
    (joiningQuotient_degree_even_of_even_fibers G label hregular hfibers) hdegrees
  exact ⟨fourJoiningDecompositionOfPartition G label hI P⟩

variable (a b : I) (hab : a ≠ b) (h : ℕ)

/-- Four-label version of the primary/surplus actual-copy output.
Primary pieces have at most three copies, and surplus pieces at most four. -/
structure FourTwoOddJoiningDecomposition where
  primary : Finset (Finset E)
  surplus : Finset (Finset E)
  primary_card : primary.card = h
  families_disjoint : Disjoint primary surplus
  nonempty : ∀ M ∈ primary ∪ surplus, M.Nonempty
  matching : ∀ M ∈ primary ∪ surplus, G.IsMatching M
  disjoint : ∀ M ∈ primary ∪ surplus, ∀ N ∈ primary ∪ surplus, M ≠ N → Disjoint M N
  cover : (primary ∪ surplus).biUnion id = joiningCopies G label
  primary_card_le : ∀ M ∈ primary, M.card ≤ 3
  surplus_card_le : ∀ M ∈ surplus, M.card ≤ 4
  primary_cut_eq_one : ∀ M ∈ primary, ∀ i, i = a ∨ i = b →
    (G.cutOn M (labelShore label {i})).card = 1
  primary_odd_cut_iff : ∀ M ∈ primary, ∀ i,
    Odd ((G.cutOn M (labelShore label {i})).card) ↔ i = a ∨ i = b
  surplus_even_cut : ∀ M ∈ surplus, ∀ i, Even ((G.cutOn M (labelShore label {i})).card)

/-- Four-label bounds for the primary and surplus original-copy families. -/
theorem twoOddParts_card_le_of_card_le_four
    (hI : Fintype.card I ≤ 4)
    (P : (twoOddJoiningQuotient G label a b hab h).CompatibleCircuitPartition
      (twoOddJoiningClasses G label h) univ) :
    (∀ M ∈ twoOddPrimaryParts G label a b hab h P, M.card ≤ 3) ∧
      (∀ M ∈ twoOddSurplusParts G label a b hab h P, M.card ≤ 4) := by
  constructor
  · intro M hM
    obtain ⟨D, hD, rfl⟩ := mem_image.mp hM
    obtain ⟨hDpart, hDvirtual⟩ := (P.mem_pairVirtualParts D).mp hD
    have hbound := (Multigraph.IsCircuit.one_pairVirtual_original
      (joiningQuotient G label) a b hab h (P.circuit D hDpart) hDvirtual).1
    change (D.toLeft.image Subtype.val).card ≤ 3
    rw [card_image_of_injective _ Subtype.val_injective]
    omega
  · intro M hM
    obtain ⟨D, hD, rfl⟩ := mem_image.mp hM
    have hcir := Multigraph.IsCircuit.no_pairVirtual_original
      (joiningQuotient G label) a b hab h (P.circuit D (mem_sdiff.mp hD).1)
      (twoOddSurplus_no_virtual G label a b hab h P hD)
    change (D.toLeft.image Subtype.val).card ≤ 4
    rw [card_image_of_injective _ Subtype.val_injective]
    exact hcir.card_le.trans hI

/-- Exact construction from the actual augmented quotient partition. -/
def fourTwoOddJoiningDecompositionOfPartition (hI : Fintype.card I ≤ 4)
    (P : (twoOddJoiningQuotient G label a b hab h).CompatibleCircuitPartition
      (twoOddJoiningClasses G label h) univ) :
    FourTwoOddJoiningDecomposition G label a b h where
  primary := twoOddPrimaryParts G label a b hab h P
  surplus := twoOddSurplusParts G label a b hab h P
  primary_card := twoOddPrimaryParts_card G label a b hab h P
  families_disjoint := twoOddParts_families_disjoint G label a b hab h P
  nonempty := fun _ hM => twoOddParts_nonempty G label a b hab h P hM
  matching := fun _ hM => twoOddParts_isMatching G label a b hab h P hM
  disjoint := fun _ hM _ hN hne => twoOddParts_disjoint G label a b hab h P hM hN hne
  cover := twoOddParts_cover G label a b hab h P
  primary_card_le := (twoOddParts_card_le_of_card_le_four G label a b hab h hI P).1
  surplus_card_le := (twoOddParts_card_le_of_card_le_four G label a b hab h hI P).2
  primary_cut_eq_one := fun _ hM i hi =>
    twoOddPrimaryParts_cut_eq_one G label a b hab h P hM i hi
  primary_odd_cut_iff := fun _ hM i =>
    twoOddPrimaryParts_odd_cut_iff G label a b hab h P hM i
  surplus_even_cut := fun _ hM i => twoOddSurplusParts_even_cut G label a b hab h P hM i

include hab in
/-- A small boundary at one of the even fibers suffices for the full
four-label two-odd circuit stage. The virtual multiplicity is unrestricted,
and exactly `h` distinct primary matching pieces are constructed. -/
theorem exists_fourTwoOddJoining_decomposition_of_small_even_cut
    (hI : Fintype.card I ≤ 4)
    (hregular : ∀ v, G.degree v = h)
    (hno : ∀ X : Finset V, ¬ G.IsOverfull h X)
    (hfibers : ∀ i, (univ.filter (fun v => label v = i)).card % 2 =
      if i = a ∨ i = b then 1 else 0)
    (hsmall : ∃ i, i ≠ a ∧ i ≠ b ∧
      (G.cutOn univ (labelShore label {i})).card ≤ 2) :
    Nonempty (FourTwoOddJoiningDecomposition G label a b h) := by
  obtain ⟨i, hia, hib, hi⟩ := hsmall
  have hlow : (twoOddJoiningQuotient G label a b hab h).degreeOn univ i ≤ 2 := by
    change ((joiningQuotient G label).pairAugmentation a b hab h).degree i ≤ 2
    rw [Multigraph.pairAugmentation_degree]
    simpa only [hia, hib, false_or, if_false, Nat.add_zero,
      joiningQuotient_degree_eq_cut] using hi
  obtain ⟨P⟩ := (twoOddJoiningQuotient G label a b hab h).exists_compatibleCircuitPartition_of_card_le_four_small_degree
    hI (twoOddJoiningClasses G label h) univ
    (twoOddJoiningQuotient_admissible G label a b hab h hregular hno hfibers)
    (twoOddJoiningQuotient_even_degrees G label a b hab h hregular hfibers) ⟨i, hlow⟩
  exact ⟨fourTwoOddJoiningDecompositionOfPartition G label a b hab h hI P⟩

end Overfull.FourOdd
