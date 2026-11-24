import Overfull.Terminal.PrefixResult
import Overfull.Terminal.ResidualPools

/-!
# The actual residual joining profile

The finite family retained by the prefix is transported to the actual residual
edge type. In the even case there are no joining edges. In the two-odd case
there are exactly the residual degree number of disjoint primary matchings,
each crossing both odd cuts exactly once.
-/

noncomputable section

namespace Overfull.Terminal

open Finset Classical SimpleGraph ForeignPhase FourOdd

variable {V : Type*} [Fintype V]
variable {G : SimpleGraph V} {U : Fin 3 → Finset V}
variable {H : ∀ i, SimpleGraph (U i)} {h : ℕ} {a θ σ : ℝ}

theorem ThreeCorePrefix.residual_joining_empty
    (P : ThreeCorePrefix G U H h a θ σ) (hempty : P.remaining = ∅) :
    joiningCopies (Multigraph.ofSimpleGraph
      (afterDeletions G P.completion.full P.rounds)) (threeCoreLabel U) = ∅ := by
  have hh := residualFamily_union_joining G P.completion.full P.rounds
    (threeCoreLabel U) P.remaining id P.remaining_eq
  simpa only [hempty, Finset.biUnion_empty] using hh.symm

theorem ThreeCorePrefix.residual_cuts_empty
    (P : ThreeCorePrefix G U H h a θ σ)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hcover : ∀ v, ∃ i, v ∈ U i) (hempty : P.remaining = ∅) (i : Fin 3) :
    (Multigraph.ofSimpleGraph (afterDeletions G P.completion.full P.rounds)).cutEdges
      (U i) = ∅ := by
  simpa only [threeCoreLabel_shore U hdisjoint hcover] using
    fiber_cut_empty_of_joining_empty
      (Multigraph.ofSimpleGraph (afterDeletions G P.completion.full P.rounds))
      (threeCoreLabel U) (P.residual_joining_empty hempty) i

/-- The selected original primary pieces become an indexed family of actual
surviving copies, with exact cut union and singleton incidence at both odd
parts. No matching decomposition of the residual is assumed. -/
theorem ThreeCorePrefix.exists_residual_primary_family
    (P : ThreeCorePrefix G U H h a θ σ)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hcover : ∀ v, ∃ i, v ∈ U i) (x y : Fin 3) (hxy : x ≠ y)
    (hcard : P.remaining.card = h - P.rounds)
    (hcut : ∀ M ∈ P.remaining, ∀ i, i = x ∨ i = y →
      ((Multigraph.ofSimpleGraph G).cutOn M (U i)).card = 1) :
    ∃ M : Fin (h - P.rounds) → Finset (afterDeletions G P.completion.full P.rounds).edgeSet,
      (∀ j, (Multigraph.ofSimpleGraph
        (afterDeletions G P.completion.full P.rounds)).IsMatching (M j)) ∧
      Pairwise (fun i j => Disjoint (M i) (M j)) ∧
      univ.biUnion M =
        (Multigraph.ofSimpleGraph (afterDeletions G P.completion.full P.rounds)).cutEdges (U x) ∪
        (Multigraph.ofSimpleGraph (afterDeletions G P.completion.full P.rounds)).cutEdges (U y) ∧
      (∀ j, ((Multigraph.ofSimpleGraph
        (afterDeletions G P.completion.full P.rounds)).cutOn (M j) (U x)).card = 1) ∧
      (∀ j, ((Multigraph.ofSimpleGraph
        (afterDeletions G P.completion.full P.rounds)).cutOn (M j) (U y)).card = 1) := by
  let index : Fin (h - P.rounds) ≃ P.remaining :=
    Fintype.equivOfCardEq (by simpa only [Fintype.card_fin, Fintype.card_coe] using hcard.symm)
  let original : Fin (h - P.rounds) → Finset G.edgeSet := fun j => (index j).val
  have hmem (j : Fin (h - P.rounds)) : original j ∈ P.remaining := (index j).property
  have hinjective : Function.Injective original := by
    intro i j hij
    exact index.injective (Subtype.ext hij)
  have hindexed : univ.biUnion original = P.remaining.biUnion id := by
    ext e
    simp only [mem_biUnion, mem_univ, true_and]
    constructor
    · rintro ⟨j, hej⟩
      exact ⟨original j, hmem j, hej⟩
    · rintro ⟨M, hM, heM⟩
      obtain ⟨j, hj⟩ := index.surjective ⟨M, hM⟩
      refine ⟨j, ?_⟩
      simpa only [original, hj] using heM
  let M := fun j => residualPool G P.completion.full P.rounds (original j)
  refine ⟨M, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact residualPool_isMatching G P.completion.full P.rounds (original j)
      (P.remaining_matching _ (hmem j))
  · intro i j hij
    exact residualPool_disjoint G P.completion.full P.rounds (original i) (original j)
      (P.remaining_disjoint _ (hmem i) _ (hmem j) (fun hh => hij (hinjective hh)))
  · have hh := residualFamily_union_joining G P.completion.full P.rounds
      (threeCoreLabel U) univ original (P.remaining_eq.trans hindexed.symm)
    exact hh.trans (threeCoreLabel_joining _ U hdisjoint hcover x y hxy)
  · intro j
    rw [show M j = residualPool G P.completion.full P.rounds (original j) from rfl,
      residualPool_cutOn_card G P.completion.full P.rounds (original j) (U x)
        (fun _ he => P.remaining_survives (hmem j) he)]
    exact hcut _ (hmem j) x (Or.inl rfl)
  · intro j
    rw [show M j = residualPool G P.completion.full P.rounds (original j) from rfl,
      residualPool_cutOn_card G P.completion.full P.rounds (original j) (U y)
        (fun _ he => P.remaining_survives (hmem j) he)]
    exact hcut _ (hmem j) y (Or.inr rfl)

end Overfull.Terminal
