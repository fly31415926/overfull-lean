import Overfull.Terminal.PrefixCompletion

/-! Original-host output of the completed all-even four-core prefix. -/

noncomputable section

namespace Overfull.TerminalFourEven

open Finset Classical SimpleGraph CircuitPatterns FourOdd NativeReserve Terminal

variable {V : Type*} [Fintype V]

structure FourEvenPrefix (G : SimpleGraph V) (U : Fin 4 → Finset V)
    (H : ∀ i, SimpleGraph (U i)) (label : V → Fin 4)
    (h : ℕ) (a θ σ : ℝ) where
  rounds : ℕ
  rounds_le : rounds ≤ h
  boundary : ℕ → G.Subgraph
  completion : BoundaryCompletion G U H boundary rounds h a θ σ
  joining_removed : joiningCopies (Multigraph.ofSimpleGraph G) label \
    removedCopies (matchingFamilyCopies G completion.full rounds) univ = ∅

end Overfull.TerminalFourEven
