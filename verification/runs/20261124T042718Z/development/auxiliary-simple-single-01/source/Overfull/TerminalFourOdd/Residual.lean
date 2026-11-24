import Overfull.TerminalFourOdd.PrefixResult
import Overfull.TerminalFourOdd.ProfileCounts
import Overfull.Terminal.ResidualPools

/-!
# Exact surviving four-odd primary families

The constructed original-copy matchings are enumerated and transported to
the actual simple residual. Their forest profiles, cut counts and exact
number of singleton colors survive the transport.
-/

noncomputable section

namespace Overfull.TerminalFourOdd

open Finset Classical SimpleGraph ForeignPhase FourOdd Terminal

variable {V : Type*} [Fintype V]
variable {G : SimpleGraph V} {U : Fin 4 → Finset V}
variable {H : ∀ i, SimpleGraph (U i)} {label : V → Fin 4}
variable {h : ℕ} {a θ σ : ℝ}

theorem FourOddPrefix.exists_residual_primary_family
    (P : FourOddPrefix G U H label h a θ σ) :
    ∃ M : Fin (h-P.rounds) → Finset (afterDeletions G P.completion.full P.rounds).edgeSet,
      (∀ j, (Multigraph.ofSimpleGraph
        (afterDeletions G P.completion.full P.rounds)).IsMatching (M j)) ∧
      Pairwise (fun i j => Disjoint (M i) (M j)) ∧
      univ.biUnion M = joiningCopies (Multigraph.ofSimpleGraph
        (afterDeletions G P.completion.full P.rounds)) label ∧
      (∀ j, PrimaryProfile (Multigraph.ofSimpleGraph
        (afterDeletions G P.completion.full P.rounds)) label (M j)) ∧
      (∀ j, (M j).card ≤ 3) ∧
      (∀ i, (univ.filter (fun j => ((Multigraph.ofSimpleGraph
        (afterDeletions G P.completion.full P.rounds)).cutOn (M j)
          (labelShore label {i})).card = 1)).card =
        (singletonParts (Multigraph.ofSimpleGraph G) label P.remaining i).card) := by
  let index : Fin (h-P.rounds) ≃ P.remaining :=
    Fintype.equivOfCardEq (by simpa only [Fintype.card_fin, Fintype.card_coe]
      using P.remaining_card.symm)
  let original : Fin (h-P.rounds) → Finset G.edgeSet := fun j => (index j).val
  have hmem (j : Fin (h-P.rounds)) : original j ∈ P.remaining := (index j).property
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
      obtain ⟨j, hj⟩ := index.surjective ⟨M,hM⟩
      exact ⟨j, by simpa only [original, hj] using heM⟩
  let M := fun j => residualPool G P.completion.full P.rounds (original j)
  have hcuts (j : Fin (h-P.rounds)) (i : Fin 4) :
      ((Multigraph.ofSimpleGraph (afterDeletions G P.completion.full P.rounds)).cutOn
        (M j) (labelShore label {i})).card =
      ((Multigraph.ofSimpleGraph G).cutOn (original j) (labelShore label {i})).card :=
    residualPool_cutOn_card G P.completion.full P.rounds (original j) _
      (fun _ he => P.remaining_survives (hmem j) he)
  refine ⟨M, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact residualPool_isMatching G P.completion.full P.rounds (original j)
      (P.remaining_matching _ (hmem j))
  · intro i j hij
    exact residualPool_disjoint G P.completion.full P.rounds (original i) (original j)
      (P.remaining_disjoint _ (hmem i) _ (hmem j) (fun hh => hij (hinjective hh)))
  · have hh := residualFamily_union_joining G P.completion.full P.rounds
      label univ original (P.remaining_eq.trans hindexed.symm)
    have hinst : (fun e f : (afterDeletions G P.completion.full P.rounds).edgeSet =>
        propDecidable (e = f)) =
        (inferInstance : DecidableEq (afterDeletions G P.completion.full P.rounds).edgeSet) :=
      Subsingleton.elim _ _
    simpa only [hinst] using hh
  · intro j
    obtain ⟨F,hF,hprofile⟩ := P.remaining_profile _ (hmem j)
    exact ⟨F,hF, fun i => (hcuts j i).trans (hprofile i)⟩
  · intro j
    have hc := residualPool_card G P.completion.full P.rounds (original j)
      (fun _ he => P.remaining_survives (hmem j) he)
    exact hc.le.trans (P.remaining_card_le _ (hmem j))
  · intro i
    have himage : (univ.filter (fun j => ((Multigraph.ofSimpleGraph
        (afterDeletions G P.completion.full P.rounds)).cutOn (M j)
          (labelShore label {i})).card = 1)).image original =
        singletonParts (Multigraph.ofSimpleGraph G) label P.remaining i := by
      ext A
      simp only [mem_image, mem_filter, mem_univ, true_and, singletonParts]
      constructor
      · rintro ⟨j, hj, rfl⟩
        exact ⟨hmem j, (hcuts j i).symm.trans hj⟩
      · rintro ⟨hA, hc⟩
        obtain ⟨j,hj⟩ := index.surjective ⟨A,hA⟩
        have heq : original j = A := congrArg Subtype.val hj
        exact ⟨j, by rw [hcuts, heq]; exact hc, heq⟩
    rw [← himage, card_image_of_injective _ hinjective]

end Overfull.TerminalFourOdd
