import Overfull.SmallCuts
import Overfull.SafePrescription.Classification

/-!
# Removing the minority shores of a small cut

The input is the minority-sum inequality supplied by the small-cut lemma.
The removed vertices are constructed from the actual cores and the actual
cut shore. The surviving cores retain their labels and cover the vertices
outside the enlarged exceptional set.
-/

namespace Overfull.ForeignRefinement

open Finset Classical SafePrescription
open scoped BigOperators

variable {V I : Type*} [Fintype I]

/-- The vertices on the minority side of their core, with ties assigned
to the complement of the chosen cut shore. -/
noncomputable def minorityVertices (U : I → Finset V) (X : Finset V) : Finset V :=
  univ.biUnion (fun i =>
    if coreMajority U X i then U i \ X else X ∩ U i)

omit [Fintype I] in
private theorem minority_piece_card (U : I → Finset V) (X : Finset V) (i : I) :
    (if coreMajority U X i then U i \ X else X ∩ U i).card =
      min (X ∩ U i).card (U i \ X).card := by
  by_cases hi : coreMajority U X i
  · rw [if_pos hi]
    change (U i \ X).card < (X ∩ U i).card at hi
    exact (min_eq_right hi.le).symm
  · rw [if_neg hi]
    change ¬ (U i \ X).card < (X ∩ U i).card at hi
    exact (min_eq_left (Nat.le_of_not_gt hi)).symm

/-- The actual removed set is bounded by the total minority size. -/
theorem minorityVertices_card_le (U : I → Finset V) (X : Finset V) :
    (minorityVertices U X).card ≤
      ∑ i, min (X ∩ U i).card (U i \ X).card := by
  calc
    (minorityVertices U X).card ≤
        ∑ i, (if coreMajority U X i then U i \ X else X ∩ U i).card :=
      card_biUnion_le
    _ = _ := sum_congr rfl (fun i _ => minority_piece_card U X i)

/-- Every removed vertex belongs to an actual core. -/
theorem minorityVertices_subset (U : I → Finset V) (X : Finset V) :
    minorityVertices U X ⊆ univ.biUnion U := by
  intro v hv
  obtain ⟨i, hi, hvi⟩ := mem_biUnion.mp hv
  refine mem_biUnion.mpr ⟨i, hi, ?_⟩
  by_cases hmajority : coreMajority U X i
  · rw [if_pos hmajority] at hvi
    exact (mem_sdiff.mp hvi).1
  · rw [if_neg hmajority] at hvi
    exact (mem_inter.mp hvi).2

/-- Each surviving core vertex lies on the majority shore of its original core. -/
theorem surviving_core_membership (U : I → Finset V) (X : Finset V)
    (i : I) (v : V) (hv : v ∈ U i \ minorityVertices U X) :
    v ∈ X ↔ coreMajority U X i := by
  obtain ⟨hvi, hvW⟩ := mem_sdiff.mp hv
  by_cases hi : coreMajority U X i
  · refine ⟨fun _ => hi, fun _ => ?_⟩
    by_contra hvX
    apply hvW
    apply mem_biUnion.mpr
    exact ⟨i, mem_univ i, by simpa only [if_pos hi] using mem_sdiff.mpr ⟨hvi, hvX⟩⟩
  · refine ⟨?_, fun h => False.elim (hi h)⟩
    intro hvX
    exfalso
    apply hvW
    apply mem_biUnion.mpr
    exact ⟨i, mem_univ i, by simpa only [if_neg hi] using mem_inter.mpr ⟨hvX, hvi⟩⟩

/-- The minority-sum bound gives an actual deletion of at most one core
vertex. The resulting cores remain nonempty and disjoint, and together
with the enlarged exceptional set they still cover all vertices. -/
theorem minority_shore_deletion (U : I → Finset V) (Z X : Finset V)
    (hdisjoint : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hUZ : ∀ i, Disjoint (U i) Z)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (horder : ∀ i, 3 ≤ (U i).card)
    (hminority : (∑ i, min (X ∩ U i).card (U i \ X).card) ≤ 1) :
    ∃ W : Finset V,
      W ⊆ univ.biUnion U ∧
      W.card ≤ 1 ∧
      Disjoint W Z ∧
      (Z ∪ W).card ≤ Z.card + 1 ∧
      (∀ i, (U i).card ≤ (U i \ W).card + 1) ∧
      (∀ i, 2 ≤ (U i \ W).card) ∧
      (∀ i, (U i \ W).Nonempty) ∧
      Pairwise (fun i j => Disjoint (U i \ W) (U j \ W)) ∧
      (∀ i, Disjoint (U i \ W) (Z ∪ W)) ∧
      (∀ v, v ∈ Z ∪ W ∨ ∃ i, v ∈ U i \ W) ∧
      (∀ i v, v ∈ U i \ W → (v ∈ X ↔ coreMajority U X i)) := by
  let W := minorityVertices U X
  have hW : W.card ≤ 1 := (minorityVertices_card_le U X).trans hminority
  have hWsub : W ⊆ univ.biUnion U := minorityVertices_subset U X
  have hWZ : Disjoint W Z := by
    apply disjoint_left.mpr
    intro v hvW hvZ
    obtain ⟨i, _, hvi⟩ := mem_biUnion.mp (hWsub hvW)
    exact disjoint_left.mp (hUZ i) hvi hvZ
  have hZcard : (Z ∪ W).card ≤ Z.card + 1 :=
    (card_union_le Z W).trans (Nat.add_le_add_left hW Z.card)
  have hloss (i : I) : (U i).card ≤ (U i \ W).card + 1 := by
    have hsum := card_sdiff_add_card_inter (U i) W
    have hinter : (U i ∩ W).card ≤ W.card := card_le_card inter_subset_right
    omega
  have htwo (i : I) : 2 ≤ (U i \ W).card := by
    have hi := horder i
    have hl := hloss i
    omega
  have hnonempty (i : I) : (U i \ W).Nonempty :=
    card_pos.mp (by have hi := htwo i; omega)
  refine ⟨W, hWsub, hW, hWZ, hZcard, hloss, htwo, hnonempty, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact (hdisjoint hij).mono sdiff_subset sdiff_subset
  · intro i
    apply disjoint_left.mpr
    intro v hv hvZW
    obtain ⟨hvi, hvW⟩ := mem_sdiff.mp hv
    rcases mem_union.mp hvZW with hvZ | hvW'
    · exact disjoint_left.mp (hUZ i) hvi hvZ
    · exact hvW hvW'
  · intro v
    rcases hcover v with hvZ | ⟨i, hvi⟩
    · exact Or.inl (mem_union_left W hvZ)
    · by_cases hvW : v ∈ W
      · exact Or.inl (mem_union_right Z hvW)
      · exact Or.inr ⟨i, mem_sdiff.mpr ⟨hvi, hvW⟩⟩
  · intro i v hv
    exact surviving_core_membership U X i v hv

end Overfull.ForeignRefinement
