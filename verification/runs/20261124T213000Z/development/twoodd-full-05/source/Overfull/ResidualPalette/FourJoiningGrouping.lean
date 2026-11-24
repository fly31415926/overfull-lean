import Overfull.ResidualPalette.FourPaletteGrouping
import Overfull.ResidualPalette.JoiningGrouping
import Overfull.CompatibleCircuits.FourJoiningComplete

/-!
# Exact four-label joining palettes on original copies

The generic grouping gives `4*L` copies and `8*L` support vertices per class.
For compatibility with the existing completion interface, the result is
stored in `JoiningPalette` at capacity `2*L`; its weaker `6*L`/`12*L` bounds
follow explicitly. No edge copy or cut-parity certificate is discarded.
-/

noncomputable section

namespace Overfull.FourOdd

open Finset Classical NativeReserve

variable {V E K : Type*} [Fintype V] [Fintype E] [DecidableEq K]
    (G : Multigraph V E) (label : V → K)

theorem FourJoiningDecomposition.exists_palette
    (P : FourJoiningDecomposition G label) {h D L : ℕ}
    (hdegree : ∀ v, G.degreeOn (joiningCopies G label) v ≤ D)
    (hL : 0 < L) (hDh : 8*D < h)
    (hbudget : Fintype.card V*D ≤ 2*L*(h-8*D)) :
    Nonempty (JoiningPalette G label h D (2*L) (fun _ => 0)) := by
  let M : P.parts → Finset E := Subtype.val
  have hM : ∀ j, G.IsMatching (M j) := fun j => P.matching _ j.property
  have hsize : ∀ j, (M j).card ≤ 4 := fun j => P.card_le _ j.property
  have hdis : Pairwise (fun i j => Disjoint (M i) (M j)) := by
    intro i j hij
    exact P.disjoint _ i.property _ j.property (fun hh => hij (Subtype.ext hh))
  have hsubset : ∀ j, M j ⊆ joiningCopies G label := by
    intro j e he
    rw [← P.cover]
    exact mem_biUnion.mpr ⟨j.val, j.property, he⟩
  have hcount : Fintype.card P.parts ≤ L*(h-8*D) :=
    palette_capacity_of_incidence_budget_of_size (s := 4) G M (joiningCopies G label)
      (fun j => P.nonempty _ j.property) hdis hsubset hdegree hbudget
  have hpos : 0 < h := lt_of_le_of_lt (Nat.zero_le _) hDh
  obtain ⟨c, _, hcload, hmatching, hgroups, hcover, hcard, hsupport⟩ :=
    exists_bounded_matching_grouping_of_size G M (joiningCopies G label) ∅ (fun _ => ⟨0,hpos⟩)
      (by simp) hM hsize hdis hsubset hdegree hL hDh hcount
  have hcoverM : univ.biUnion M = joiningCopies G label := by
    rw [← P.cover]
    ext e
    simp only [mem_biUnion, mem_univ, true_and]
    exact ⟨fun ⟨j,hj⟩ => ⟨j.val,j.property,hj⟩,
      fun ⟨N,hN,he⟩ => ⟨⟨N,hN⟩,he⟩⟩
  refine ⟨{
    classes := groupedCopies M c
    matching := hmatching
    disjoint := hgroups
    cover := hcover.trans hcoverM
    cut_parity := ?_
    card_le := fun j => by have hh := hcard j; omega
    support_card_le := fun j => by have hh := hsupport j; omega
    vertex_load_le := groupedCopies_support_load_le G M c _ hdis hsubset hdegree
  }⟩
  intro j i
  apply Nat.even_iff.mp
  exact cutOn_biUnion_even G (univ.filter (fun q => c q = j)) M
    (fun a _ b _ hab => hdis hab) (labelShore label {i})
    (fun a _ => by
      rcases P.fiber_cut _ a.property i with hz | ht
      · rw [hz]; decide
      · rw [ht]; decide)

end Overfull.FourOdd
