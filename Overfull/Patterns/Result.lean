import Overfull.Patterns.ReservedEdges
import Overfull.Patterns.AbsorptionParity

/-!
# The frequent-pattern reduction result

The record contains the actual original-host deletion sequence, the exact
regular residual, enlarged robust cores covering every vertex, and actual
joining-edge and cut supplies for the retained forest.
-/

noncomputable section
namespace Overfull.Patterns

open Finset Classical SimpleGraph Compression
open ForeignPhase MatchingProbability

variable {V I : Type*} [Fintype V] [Fintype I]

structure FrequentPatternResult (G₀ : SimpleGraph V) (U₀ : I → Finset V)
    (k t : ℕ) (δ νout τout : ℝ) where
  G : SimpleGraph V
  h : ℕ
  N : ℕ → G₀.Subgraph
  rounds : ℕ
  graph_eq : G = afterDeletions G₀ N rounds
  degree_eq : h = k-rounds
  perfect : ∀ j < rounds, (N j).IsPerfectMatching
  present : ∀ j < rounds, (N j).spanningCoe ≤ afterDeletions G₀ N j
  regular : ∀ v, G.degree v = h
  safe_prefixes : ∀ s ≤ rounds, ∀ X : Finset V,
    ¬ IsOverfull (afterDeletions G₀ N s) (k-s) X
  no_overfull : ∀ X : Finset V, ¬ IsOverfull G h X
  degree_positive : 0 < h
  retained_degree : (k : ℝ)/(3*patternBound t) ≤ h
  U : I → Finset V
  H : ∀ i, SimpleGraph (U i)
  core_enlargement : ∀ i, U₀ i ⊆ U i
  core_disjoint : Pairwise (fun i j => Disjoint (U i) (U j))
  cover : ∀ v, ∃ i, v ∈ U i
  core_embed : ∀ i, H i ≤ G.induce (U i : Set V)
  error : ℝ
  error_nonneg : 0 ≤ error
  error_bound : error ≤ δ*h
  core_degree : ∀ i v, (h : ℝ)-error ≤ ((H i).degree v : ℝ)
  core_robust : ∀ i, IsRobustExpander (H i) νout τout
  reserve : ℕ
  reserve_le : reserve ≤ h
  reserve_error : (h : ℝ)-reserve ≤ δ*h
  code : I ↪ Fin 4
  forest : Finset LabelPair
  forest_isForest : LeafForest forest
  forest_shape : Fintype.card I = 4 → (∀ i, Odd (U i).card) → LabelForestShape forest
  pair_supply : ∀ p ∈ forest, reserve ≤ (partPairEdges G U code p).card
  cut_supply : ∀ J : Finset I,
    reserve*forestCutCount forest (J.image code) ≤ graphCutCount G (J.biUnion U)

end Overfull.Patterns
