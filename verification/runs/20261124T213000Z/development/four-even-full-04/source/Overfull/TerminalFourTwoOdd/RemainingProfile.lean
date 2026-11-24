import Overfull.TerminalFourTwoOdd.PrefixResult
import Overfull.Terminal.ResidualPools

/-! Every surviving joining copy, including even-to-even copies, is retained. -/

noncomputable section

namespace Overfull.TerminalFourTwoOdd

open Finset Classical SimpleGraph ForeignPhase FourOdd Terminal

variable {V : Type*} [Fintype V]
variable {G : SimpleGraph V} {U : Fin 4 → Finset V}
variable {H : ∀ i, SimpleGraph (U i)} {label : V → Fin 4} {x y : Fin 4}
variable {h : ℕ} {a θ σ : ℝ}

theorem FourTwoOddPrefix.exists_residual_primary_family
    (P : FourTwoOddPrefix G U H label x y h a θ σ)
    (hparts : ∀ i, labelShore label {i} = U i) :
    ∃ M : Fin (h-P.rounds) → Finset (afterDeletions G P.completion.full P.rounds).edgeSet,
      (∀ j, (Multigraph.ofSimpleGraph
        (afterDeletions G P.completion.full P.rounds)).IsMatching (M j)) ∧
      Pairwise (fun i j => Disjoint (M i) (M j)) ∧
      univ.biUnion M = joiningCopies (Multigraph.ofSimpleGraph
        (afterDeletions G P.completion.full P.rounds)) label ∧
      (∀ j i, i=x ∨ i=y → ((Multigraph.ofSimpleGraph
        (afterDeletions G P.completion.full P.rounds)).cutOn (M j) (U i)).card = 1) ∧
      (∀ j i, ((Multigraph.ofSimpleGraph
        (afterDeletions G P.completion.full P.rounds)).cutOn (M j) (U i)).card % 2 =
          (U i).card % 2) := by
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
  refine ⟨M, ?_, ?_, ?_, ?_, ?_⟩
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
  · intro j i hi
    have hc := hcuts j i
    rw [hparts] at hc
    exact hc.trans (P.remaining_cut _ (hmem j) i hi)
  · intro j i
    have hc := hcuts j i
    rw [hparts] at hc
    rw [hc]
    exact P.remaining_parity _ (hmem j) i

end Overfull.TerminalFourTwoOdd
