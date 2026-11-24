import Overfull.Absorption.SecondAbsorption
import Overfull.ForeignEdges.EpochState

/-!
# The actual bounded-exceptional-set absorption result

Every deleted matching is a matching in the original host. The core
enlargements change the distinguished partition only; the ambient graph
is exactly the residual of that matching sequence.
-/

namespace Overfull.Absorption

open Finset Classical SimpleGraph ForceMatching SafePrescription
open ForeignPhase ForeignIncidence

variable {V I : Type*} [Fintype V]

structure AbsorptionResult (G₀ : SimpleGraph V) (U₀ : I → Finset V)
    (Z₀ : Finset V) (h₀ T : ℕ) (f : ℕ → ℝ) (νout τout : ℝ) where
  G : SimpleGraph V
  h : ℕ
  N : ℕ → G₀.Subgraph
  rounds : ℕ
  graph_eq : G = afterDeletions G₀ N rounds
  degree_eq : h = h₀-rounds
  perfect : ∀ s < rounds, (N s).IsPerfectMatching
  present : ∀ s < rounds, (N s).spanningCoe ≤ afterDeletions G₀ N s
  regular : ∀ v, G.degree v = h
  no_overfull : ∀ X : Finset V, ¬ IsOverfull G h X
  degree_positive : 0 < h
  retained_degree : 3*(h₀ : ℝ)/4 ≤ (h : ℝ)
  U : I → Finset V
  H : ∀ i, SimpleGraph (U i)
  Z : Finset V
  error : ℝ
  error_nonneg : 0 ≤ error
  error_bound : error ≤ f Z.card*h
  exceptional_subset : Z ⊆ Z₀
  exceptional_card : Z.card ≤ T
  core_enlargement : ∀ i, U₀ i ⊆ U i
  core_disjoint : Pairwise (fun i j => Disjoint (U i) (U j))
  core_exceptional_disjoint : ∀ i, Disjoint (U i) Z
  cover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i
  core_embed : ∀ i, H i ≤ G.induce (U i : Set V)
  core_degree : ∀ i v, (h : ℝ)-error ≤ ((H i).degree v : ℝ)
  core_robust : ∀ i, IsRobustExpander (H i) νout τout

namespace AbsorptionResult

variable {G₀ : SimpleGraph V} {U₀ : I → Finset V} {Z₀ : Finset V}
variable {h₀ T : ℕ} {f : ℕ → ℝ} {νout τout : ℝ}

theorem graph_le_original (R : AbsorptionResult G₀ U₀ Z₀ h₀ T f νout τout) :
    R.G ≤ G₀ := by
  rw [R.graph_eq]
  exact sdiff_le

theorem pairwise_disjoint (R : AbsorptionResult G₀ U₀ Z₀ h₀ T f νout τout) :
    ∀ s ∈ range R.rounds, ∀ t ∈ range R.rounds, s ≠ t →
      Disjoint (R.N s).spanningCoe (R.N t).spanningCoe :=
  deletion_sequence_pairwise G₀ R.N R.rounds R.present

end AbsorptionResult
end Overfull.Absorption
