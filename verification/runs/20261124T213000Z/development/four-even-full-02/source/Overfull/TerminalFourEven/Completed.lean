import Overfull.TerminalFourEven.PrefixResult
import Overfull.Terminal.ClosedCores
import Overfull.Terminal.CoreBridge
import Overfull.Terminal.PartLabels
import Overfull.Terminal.ResidualPools
import Overfull.Terminal.Reassembly

/-! Close every residual core, factor it, and restore the original prefix. -/

noncomputable section

namespace Overfull.TerminalFourEven

open Finset Classical SimpleGraph Multigraph SmallCuts ForeignPhase FourOdd Terminal

variable {V : Type*} [Fintype V]
variable {G : SimpleGraph V} {U : Fin 4 → Finset V} {H : ∀ i, SimpleGraph (U i)}
variable {label : V → Fin 4} {h : ℕ} {a θ σ : ℝ}

theorem FourEvenPrefix.residual_joining_empty (P : FourEvenPrefix G U H label h a θ σ) :
    joiningCopies (Multigraph.ofSimpleGraph
      (afterDeletions G P.completion.full P.rounds)) label = ∅ := by
  have hh := residualFamily_union_joining G P.completion.full P.rounds
    label (∅ : Finset (Finset G.edgeSet)) id (by simpa using P.joining_removed)
  simpa only [Finset.biUnion_empty] using hh.symm

theorem FourEvenPrefix.residual_cuts_empty (P : FourEvenPrefix G U H label h a θ σ)
    (hparts : ∀ i, labelShore label {i} = U i) (i : Fin 4) :
    (Multigraph.ofSimpleGraph (afterDeletions G P.completion.full P.rounds)).cutEdges
      (U i) = ∅ := by
  simpa only [hparts] using fiber_cut_empty_of_joining_empty
    (Multigraph.ofSimpleGraph (afterDeletions G P.completion.full P.rounds))
    label P.residual_joining_empty i

/-- A uniform residual tolerance constructs component colorings and restores
all deleted matchings on their original edge copies. -/
theorem exists_uniform_completed_four_even_factorization (α ν τ : ℝ)
    (hα : 0 < α) (hν : 0 < ν) (hντ : ν ≤ τ) (hτ : τ ≤ min α 1/16) :
    ∃ η : ℝ, 0 < η ∧ ∃ m₀ : ℕ,
      ∀ (V : Type*) [Fintype V] (G : SimpleGraph V)
        (U : Fin 4 → Finset V) (H : ∀ i, SimpleGraph (U i))
        (label : V → Fin 4) (h : ℕ) (a : ℝ) (P : FourEvenPrefix G U H label h a ν τ),
        (∀ i, labelShore label {i} = U i) →
        Pairwise (fun i j => Disjoint (U i) (U j)) →
        (∀ v, ∃ i, v ∈ U i) →
        (∀ i, (U i).card % 2 = 0) →
        (∀ i, m₀ ≤ (U i).card) →
        (∀ i, α*(U i).card ≤ ((h-P.rounds : ℕ) : ℝ)) →
        (∀ i, a ≤ η*(U i).card) →
        Nonempty ((Multigraph.ofSimpleGraph G).EdgeColoring h) := by
  obtain ⟨η,hη,m₀,hfactor⟩ :=
    exists_uniform_closed_core_factorization α ν τ hα hν hντ hτ
  refine ⟨η,hη,m₀,?_⟩
  intro V _ G U H label h a P hparts hdisjoint hcover heven hm hk ha
  let R := afterDeletions G P.completion.full P.rounds
  let C : ∀ i, Core (Multigraph.ofSimpleGraph R) (U i) :=
    completionCore P.completion P.rounds le_rfl
  obtain ⟨c⟩ := hfactor V R.edgeSet (Fin 4) (Multigraph.ofSimpleGraph R) U C
    (h-P.rounds) a (fun i j hij => hdisjoint hij) hcover hm
    (fun i => Nat.even_iff.mpr (heven i)) (P.residual_cuts_empty hparts)
    (completionResidual_regular P.completion P.rounds le_rfl) hk
    (completionCore_robust P.completion P.rounds le_rfl) ha
    (fun i v => (completionCore_degree P.completion P.rounds le_rfl P.rounds_le i v).1)
  exact completion_restores_coloring P.completion P.rounds_le c

end Overfull.TerminalFourEven
