import Overfull.OrdinaryFactorization.CutReserve
import Overfull.OrdinaryFactorization.MatchingBridge
import Overfull.OrdinaryFactorization.Residual

/-!
# Actual data after completing the first group of colors

The geometric cut, sampled reserve, original complementary classes,
internal coloring, and repaired matchings all refer to the same embedded
core and the same original edge copies.
-/

noncomputable section

namespace Overfull.OrdinaryFactorization

open Finset Classical SmallCuts SimpleGraph
open BipartitePackingAccounting

variable {V E : Type*} [Fintype V] [Fintype E]

/-- The constructed first group of colors in the ordinary-core argument.
Factorization of the exact remaining regular graph is a later obligation. -/
structure FirstHalfData (G : Multigraph V E) (U : Finset V) (C : Core G U)
    (k : ℕ) (α ν τ ξ p σ κ δ μ : ℝ) where
  pairing : Fin (U.card / 2) × Bool ≃ U
  geometry : CutReserveData C.graph pairing (α / 2) τ ξ p
    (min ν (α * σ / 4)) σ δ
  count : ℕ
  count_eq : count = geometry.internal.maxDegree + 1 + Nat.ceil (κ * U.card)
  count_pos : 0 < count
  count_le : count ≤ k
  count_upper : (count : ℝ) ≤ 3 * k / 5
  count_lower : (α / 8) * U.card ≤ (count : ℝ)
  exteriorColor : (G.restrictEdges (OneCore.coreEdges C)ᶜ).EdgeColoring k
  labels : Fin count ↪ Fin k
  internalColor : (Multigraph.ofSimpleGraph geometry.internal).EdgeColoring count
  avoids : internalColor.AvoidsVertices (selectedFootprint C exteriorColor labels)
  matchings : Fin count → C.graph.Subgraph
  matching : ∀ i, (matchings i).IsMatching
  verts : ∀ i, (matchings i).verts = (selectedFootprint C exteriorColor labels i : Set U)ᶜ
  support : ∀ i, (matchings i).spanningCoe ≤
    (colorMatching C.graph geometry.internal geometry.internal_le internalColor i).spanningCoe ⊔
      geometry.reserve
  disjoint : Pairwise (fun i j => Disjoint (matchings i).spanningCoe (matchings j).spanningCoe)
  reserve_used : ∀ v,
    ((edgeUnion (fun i => (matchings i).spanningCoe ⊓ geometry.reserve) univ).degree v : ℝ) ≤
      μ * U.card
  internal_released : ∀ v,
    ((edgeUnion (fun i =>
      (colorMatching C.graph geometry.internal geometry.internal_le internalColor i).spanningCoe \
        (matchings i).spanningCoe) univ).degree v : ℝ) ≤ μ * U.card

namespace FirstHalfData

variable {G : Multigraph V E} {U : Finset V} {C : Core G U} {k : ℕ}
variable {α ν τ ξ p σ κ δ μ : ℝ}
variable (D : FirstHalfData G U C k α ν τ ξ p σ κ δ μ)

/-- The actual completed classes in the original multigraph. -/
def completed (i : Fin D.count) : Finset E :=
  completedClass C D.exteriorColor D.labels D.matchings i

theorem completed_perfect (hregular : ∀ v, G.degree v = k) (i : Fin D.count) :
    G.IsPerfectMatching (D.completed i) :=
  completedClass_isPerfectMatching C D.exteriorColor D.labels D.matchings
    D.matching D.verts hregular i

theorem completed_disjoint : Pairwise (fun i j => Disjoint (D.completed i) (D.completed j)) :=
  completedClass_pairwiseDisjoint C D.exteriorColor D.labels D.matchings D.disjoint

/-- The precise original-edge residual after removing the completed classes. -/
def remaining : Multigraph V ↥((deleted C D.exteriorColor D.labels D.matchings)ᶜ) :=
  residualGraph C D.exteriorColor D.labels D.matchings

theorem remaining_regular (hregular : ∀ v, G.degree v = k) (v : V) :
    D.remaining.degree v = k - D.count :=
  residualGraph_regular C D.exteriorColor D.labels D.matchings
    D.matching D.verts D.disjoint hregular v

theorem remaining_degree_lower : (2 : ℝ) * k / 5 ≤ ((k - D.count : ℕ) : ℝ) := by
  have hsub : ((k - D.count : ℕ) : ℝ) = k - D.count := Nat.cast_sub D.count_le
  rw [hsub]
  linarith only [D.count_upper]

end FirstHalfData

end Overfull.OrdinaryFactorization
