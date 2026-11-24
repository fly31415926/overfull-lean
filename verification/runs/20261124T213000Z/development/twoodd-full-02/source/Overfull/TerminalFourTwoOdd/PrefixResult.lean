import Overfull.Terminal.PrefixCompletion
import Overfull.Terminal.Parameters

/-! The original-copy result of the four-core two-odd prefix. -/

noncomputable section

namespace Overfull.TerminalFourTwoOdd

open Finset Classical SimpleGraph CircuitPatterns FourOdd NativeReserve Terminal

variable {V : Type*} [Fintype V]

structure FourTwoOddPrefix (G : SimpleGraph V) (U : Fin 4 → Finset V)
    (H : ∀ i, SimpleGraph (U i)) (label : V → Fin 4) (x y : Fin 4)
    (h : ℕ) (a θ σ : ℝ) where
  rounds : ℕ
  rounds_le : rounds ≤ h
  boundary : ℕ → G.Subgraph
  completion : BoundaryCompletion G U H boundary rounds h a θ σ
  remaining : Finset (Finset G.edgeSet)
  remaining_nonempty : ∀ M ∈ remaining, M.Nonempty
  remaining_matching : ∀ M ∈ remaining, (Multigraph.ofSimpleGraph G).IsMatching M
  remaining_disjoint : ∀ M ∈ remaining, ∀ N ∈ remaining, M ≠ N → Disjoint M N
  remaining_eq : joiningCopies (Multigraph.ofSimpleGraph G) label \
    removedCopies (matchingFamilyCopies G completion.full rounds) univ = remaining.biUnion id
  remaining_card : remaining.card = h-rounds
  remaining_cut : ∀ M ∈ remaining, ∀ i, i=x ∨ i=y →
    ((Multigraph.ofSimpleGraph G).cutOn M (U i)).card = 1
  remaining_parity : ∀ M ∈ remaining, ∀ i,
    ((Multigraph.ofSimpleGraph G).cutOn M (U i)).card % 2 = (U i).card % 2

theorem FourTwoOddPrefix.remaining_survives {G : SimpleGraph V}
    {U : Fin 4 → Finset V} {H : ∀ i, SimpleGraph (U i)} {label : V → Fin 4}
    {x y : Fin 4} {h : ℕ} {a θ σ : ℝ}
    (P : FourTwoOddPrefix G U H label x y h a θ σ)
    {M : Finset G.edgeSet} (hM : M ∈ P.remaining) {e : G.edgeSet} (he : e ∈ M) :
    e ∉ removedCopies (matchingFamilyCopies G P.completion.full P.rounds) univ := by
  have hm : e ∈ P.remaining.biUnion id := mem_biUnion.mpr ⟨M, hM, he⟩
  rw [← P.remaining_eq] at hm
  exact (mem_sdiff.mp hm).2

end Overfull.TerminalFourTwoOdd
