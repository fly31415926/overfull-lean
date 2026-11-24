import Overfull.CompatibleCircuits.TwoOddDecomposition

/-!
# Parity certificates retained through joining-piece grouping

The even-fiber decomposition retains the cut parity of each actual part.
Disjoint unions of pieces preserve even cuts, and a group with exactly one
primary piece preserves that primary's cut parity. These are certificates
for whole palette classes, including their actual parallel edge copies.
-/

noncomputable section

namespace Overfull.NativeReserve

open Finset Classical
open scoped BigOperators

variable {V E J I : Type*} (G : Multigraph V E)

/-- Actual cut cardinalities add across edge-disjoint pieces. -/
theorem cutOn_biUnion_card (A : Finset J) (M : J → Finset E)
    (hdisj : A.toSet.PairwiseDisjoint M) (X : Finset V) :
    (G.cutOn (A.biUnion M) X).card = ∑ j ∈ A, (G.cutOn (M j) X).card := by
  simp only [Multigraph.cutOn, filter_biUnion]
  apply card_biUnion
  intro j hj k hk hjk
  exact (hdisj hj hk hjk).mono (filter_subset _ _) (filter_subset _ _)

/-- Even cut certificates survive grouping disjoint original-copy pieces. -/
theorem cutOn_biUnion_even (A : Finset J) (M : J → Finset E)
    (hdisj : A.toSet.PairwiseDisjoint M) (X : Finset V)
    (heven : ∀ j ∈ A, Even ((G.cutOn (M j) X).card)) :
    Even ((G.cutOn (A.biUnion M) X).card) := by
  rw [cutOn_biUnion_card G A M hdisj X]
  apply Finset.even_sum
  exact heven

/-- With one primary and even surplus pieces, a group's cut has exactly
the primary's parity. No bound on the number of pieces is used here. -/
theorem cutOn_biUnion_mod_two_of_one_primary (A : Finset J) (M : J → Finset E)
    (hdisj : A.toSet.PairwiseDisjoint M) (X : Finset V) (p : J) (hp : p ∈ A)
    (heven : ∀ j ∈ A, j ≠ p → Even ((G.cutOn (M j) X).card)) :
    (G.cutOn (A.biUnion M) X).card % 2 = (G.cutOn (M p) X).card % 2 := by
  rw [cutOn_biUnion_card G A M hdisj X,
    ← sum_erase_add _ _ hp, Nat.add_mod]
  have hs : Even (∑ j ∈ A.erase p, (G.cutOn (M j) X).card) := by
    apply Finset.even_sum
    intro j hj
    exact heven j (mem_erase.mp hj).2 (mem_erase.mp hj).1
  rw [Nat.even_iff.mp hs]
  simp

end Overfull.NativeReserve

namespace Overfull.FourOdd

open Finset Classical

variable {V E I : Type*} [Fintype E] [DecidableEq I]
    (G : Multigraph V E) (label : V → I)

/-- Every lifted compatible circuit has even footprint in every fiber. -/
theorem liftJoiningParts_even_cut [Fintype V] {C : Finset (joiningCopies G label)}
    (P : (joiningQuotient G label).CompatibleCircuitPartition
      ((joiningGraph G label).endpointClass label) C)
    {M : Finset E} (hM : M ∈ liftJoiningParts G label P) (i : I) :
    Even ((G.cutOn M (labelShore label {i})).card) := by
  obtain ⟨D, hD, rfl⟩ := mem_image.mp hM
  rw [← joiningQuotient_degreeOn_eq_cut]
  exact Multigraph.IsCircuit.even_degreeOn (joiningQuotient G label) (P.circuit D hD) i

/-- The all-even joining decomposition retains all per-piece parity
certificates, as well as exact original-copy coverage and disjointness. -/
structure EvenJoiningDecomposition [Fintype V] where
  parts : Finset (Finset E)
  nonempty : ∀ M ∈ parts, M.Nonempty
  matching : ∀ M ∈ parts, G.IsMatching M
  card_le : ∀ M ∈ parts, M.card ≤ 3
  disjoint : ∀ M ∈ parts, ∀ N ∈ parts, M ≠ N → Disjoint M N
  cover : parts.biUnion id = joiningCopies G label
  even_cut : ∀ M ∈ parts, ∀ i, Even ((G.cutOn M (labelShore label {i})).card)

/-- Construct the parity-retaining all-even decomposition directly from
the original host conditions. -/
theorem exists_evenJoining_decomposition [Fintype V] [Fintype I]
    (hI : Fintype.card I ≤ 3) {h : ℕ}
    (hregular : ∀ v, G.degree v = h)
    (hno : ∀ X : Finset V, ¬ G.IsOverfull h X)
    (hfibers : ∀ i, (univ.filter (fun v => label v = i)).card % 2 = 0) :
    Nonempty (EvenJoiningDecomposition G label) := by
  obtain ⟨P⟩ := (joiningQuotient G label).exists_compatibleCircuitPartition_of_card_le_three
    hI ((joiningGraph G label).endpointClass label) univ
    (joiningQuotient_admissible_of_even_fibers G label hregular hno hfibers)
    (joiningQuotient_degree_even_of_even_fibers G label hregular hfibers)
  exact ⟨{
    parts := liftJoiningParts G label P
    nonempty := fun _ hM => liftJoiningParts_nonempty G label P hM
    matching := fun _ hM => liftJoiningParts_isMatching G label P hM
    card_le := fun _ hM => (liftJoiningParts_card_le G label P hM).trans hI
    disjoint := fun _ hM _ hN hne => liftJoiningParts_disjoint G label P hM hN hne
    cover := liftJoiningParts_cover_univ G label P
    even_cut := fun _ hM i => liftJoiningParts_even_cut G label P hM i
  }⟩

end Overfull.FourOdd
