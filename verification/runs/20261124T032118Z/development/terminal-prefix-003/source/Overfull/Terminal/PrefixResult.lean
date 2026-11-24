import Overfull.Terminal.PrefixCompletion
import Overfull.Terminal.PartLabels

/-! The original-host result of the three-core terminal prefix. -/

noncomputable section

namespace Overfull.Terminal

open Finset Classical SimpleGraph CircuitPatterns FourOdd NativeReserve

variable {V : Type*} [Fintype V]

/-- Actual perfect deletions, robust residual cores, and the exact remaining
joining copies. The parity alternatives are derived from the original host. -/
structure ThreeCorePrefix (G : SimpleGraph V) (U : Fin 3 → Finset V)
    (H : ∀ i, SimpleGraph (U i)) (h : ℕ) (a θ σ : ℝ) where
  rounds : ℕ
  rounds_le : rounds ≤ h
  boundary : ℕ → G.Subgraph
  completion : BoundaryCompletion G U H boundary rounds h a θ σ
  remaining : Finset (Finset G.edgeSet)
  remaining_nonempty : ∀ M ∈ remaining, M.Nonempty
  remaining_matching : ∀ M ∈ remaining, (Multigraph.ofSimpleGraph G).IsMatching M
  remaining_disjoint : ∀ M ∈ remaining, ∀ N ∈ remaining, M ≠ N → Disjoint M N
  remaining_eq : joiningCopies (Multigraph.ofSimpleGraph G) (threeCoreLabel U) \
    removedCopies (matchingFamilyCopies G completion.full rounds) univ = remaining.biUnion id
  parity : ((∀ i, Even (U i).card) ∧ remaining = ∅) ∨
    ∃ x y : Fin 3, x ≠ y ∧
      (∀ i, (U i).card % 2 = if i=x ∨ i=y then 1 else 0) ∧
      remaining.card = h-rounds ∧
      ∀ M ∈ remaining, ∀ i, i=x ∨ i=y →
        ((Multigraph.ofSimpleGraph G).cutOn M (U i)).card = 1

theorem ThreeCorePrefix.remaining_survives {G : SimpleGraph V}
    {U : Fin 3 → Finset V} {H : ∀ i, SimpleGraph (U i)}
    {h : ℕ} {a θ σ : ℝ} (P : ThreeCorePrefix G U H h a θ σ)
    {M : Finset G.edgeSet} (hM : M ∈ P.remaining) {e : G.edgeSet} (he : e ∈ M) :
    e ∉ removedCopies (matchingFamilyCopies G P.completion.full P.rounds) univ := by
  have hm : e ∈ P.remaining.biUnion id := mem_biUnion.mpr ⟨M, hM, he⟩
  rw [← P.remaining_eq] at hm
  exact (mem_sdiff.mp hm).2

end Overfull.Terminal
