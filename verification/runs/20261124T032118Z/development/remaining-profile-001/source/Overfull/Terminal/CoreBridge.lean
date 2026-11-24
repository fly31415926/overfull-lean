import Overfull.CircuitPatterns.Completion
import Overfull.ForceMatching.Residual

/-!
# Actual residual robust cores after a completed boundary prefix

The residual cores are embedded into the simple residual's original edge-copy
multigraph. Their robustness and degree bounds are transported directly from
the completed adaptive matching transcript.
-/

noncomputable section

namespace Overfull.Terminal

open Finset Classical SimpleGraph ForeignPhase ForeignRuleCompletion
open ForceMatching CircuitPatterns ForeignIncidence

variable {V I : Type*} [Fintype V]
variable {G : SimpleGraph V} {U : I → Finset V}
variable {H : ∀ i, SimpleGraph (U i)} {F : ℕ → G.Subgraph}
variable {q h : ℕ} {a θ σ : ℝ}

/-- The actual remaining simple core, embedded into the actual simple residual
multigraph, retaining the original vertices and surviving edge copies. -/
def completionCore (D : BoundaryCompletion G U H F q h a θ σ)
    (s : ℕ) (hs : s ≤ q) (i : I) :
    SmallCuts.Core (Multigraph.ofSimpleGraph (afterDeletions G D.full s)) (U i) :=
  embeddedCore (afterDeletions G D.full s) (U i)
    (remainingCore (U i) (H i) (D.core i) (range s)) (D.core_embedded s hs i)

@[simp] theorem completionCore_graph
    (D : BoundaryCompletion G U H F q h a θ σ)
    (s : ℕ) (hs : s ≤ q) (i : I) :
    (completionCore D s hs i).graph =
      remainingCore (U i) (H i) (D.core i) (range s) := rfl

theorem completionCore_robust
    (D : BoundaryCompletion G U H F q h a θ σ)
    (s : ℕ) (hs : s ≤ q) (i : I) :
    IsRobustExpander (completionCore D s hs i).graph θ σ :=
  D.core_robust s hs i

/-- Natural residual degree and real degree error use the same subtraction;
the bound `s ≤ h` prevents a truncated natural subtraction. -/
theorem completionCore_degree
    (D : BoundaryCompletion G U H F q h a θ σ)
    (s : ℕ) (hs : s ≤ q) (hsh : s ≤ h) (i : I) (v : U i) :
    ((h - s : ℕ) : ℝ) - a ≤ ((completionCore D s hs i).graph.degree v : ℝ) ∧
      ((completionCore D s hs i).graph.degree v : ℝ) ≤ (h - s : ℕ) := by
  simpa only [completionCore_graph, Nat.cast_sub hsh] using D.core_degree s hs i v

theorem completionResidual_regular
    (D : BoundaryCompletion G U H F q h a θ σ)
    (s : ℕ) (hs : s ≤ q) :
    ∀ v, (Multigraph.ofSimpleGraph (afterDeletions G D.full s)).degree v = h - s := by
  intro v
  rw [Multigraph.ofSimpleGraph_degree]
  exact D.residual_regular s hs v

end Overfull.Terminal
