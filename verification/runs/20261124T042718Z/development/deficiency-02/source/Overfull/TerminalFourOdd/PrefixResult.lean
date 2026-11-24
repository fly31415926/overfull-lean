import Overfull.TerminalFourOdd.Palette
import Overfull.Terminal.PrefixCompletion
import Overfull.Terminal.Parameters

/-! The exact original-host result of a four-odd completed prefix. -/

noncomputable section

namespace Overfull.TerminalFourOdd

open Finset Classical SimpleGraph CircuitPatterns FourOdd NativeReserve Terminal

variable {V : Type*} [Fintype V]

/-- The surviving primary forests are actual original matchings. The
completed colors remove exactly their complement in the joining set. -/
structure FourOddPrefix (G : SimpleGraph V) (U : Fin 4 → Finset V)
    (H : ∀ i, SimpleGraph (U i)) (label : V → Fin 4) (h : ℕ) (a θ σ : ℝ) where
  rounds : ℕ
  rounds_eq : rounds = prefixRounds h
  rounds_le : rounds ≤ h
  boundary : ℕ → G.Subgraph
  completion : BoundaryCompletion G U H boundary rounds h a θ σ
  remaining : Finset (Finset G.edgeSet)
  remaining_card : remaining.card = h-rounds
  remaining_nonempty : ∀ M ∈ remaining, M.Nonempty
  remaining_card_le : ∀ M ∈ remaining, M.card ≤ 3
  remaining_matching : ∀ M ∈ remaining, (Multigraph.ofSimpleGraph G).IsMatching M
  remaining_disjoint : ∀ M ∈ remaining, ∀ N ∈ remaining, M ≠ N → Disjoint M N
  remaining_eq : joiningCopies (Multigraph.ofSimpleGraph G) label \
    removedCopies (matchingFamilyCopies G completion.full rounds) univ = remaining.biUnion id
  remaining_profile : ∀ M ∈ remaining, PrimaryProfile (Multigraph.ofSimpleGraph G) label M

theorem FourOddPrefix.remaining_survives {G : SimpleGraph V}
    {U : Fin 4 → Finset V} {H : ∀ i, SimpleGraph (U i)} {label : V → Fin 4}
    {h : ℕ} {a θ σ : ℝ} (P : FourOddPrefix G U H label h a θ σ)
    {M : Finset G.edgeSet} (hM : M ∈ P.remaining) {e : G.edgeSet} (he : e ∈ M) :
    e ∉ removedCopies (matchingFamilyCopies G P.completion.full P.rounds) univ := by
  have hm : e ∈ P.remaining.biUnion id := mem_biUnion.mpr ⟨M, hM, he⟩
  rw [← P.remaining_eq] at hm
  exact (mem_sdiff.mp hm).2

theorem FourOddPrefix.remaining_cut_one_or_three {G : SimpleGraph V}
    {U : Fin 4 → Finset V} {H : ∀ i, SimpleGraph (U i)} {label : V → Fin 4}
    {h : ℕ} {a θ σ : ℝ} (P : FourOddPrefix G U H label h a θ σ)
    (hparts : ∀ i, labelShore label {i} = U i)
    {M : Finset G.edgeSet} (hM : M ∈ P.remaining) (i : Fin 4) :
    ((Multigraph.ofSimpleGraph G).cutOn M (U i)).card = 1 ∨
      ((Multigraph.ofSimpleGraph G).cutOn M (U i)).card = 3 := by
  simpa only [hparts] using (P.remaining_profile M hM).cut_one_or_three i

end Overfull.TerminalFourOdd
