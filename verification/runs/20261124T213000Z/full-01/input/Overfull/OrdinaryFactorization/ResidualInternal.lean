import Overfull.OrdinaryFactorization.FirstHalfData
import Overfull.OrdinaryFactorization.CutReserveBounds

/-!
# Degree of the internal graph after the first color group

Every surviving internal edge is either an internal reserve edge or an
edge released by its original color matching. The inclusion concerns the
original core vertex type and yields the required actual degree bound.
-/

noncomputable section

namespace Overfull.OrdinaryFactorization.FirstHalfData

open Finset Classical SmallCuts SimpleGraph
open BipartitePackingAccounting

variable {V E : Type*} [Fintype V] [Fintype E]
variable {G : Multigraph V E} {U : Finset V} {C : Core G U} {k : ℕ}
variable {α ν τ ξ p σ κ δ μ : ℝ}
variable (D : FirstHalfData G U C k α ν τ ξ p σ κ δ μ)

/-- The actual core edges used by the completed first-group matchings. -/
def usedCore : SimpleGraph U :=
  edgeUnion (fun i => (D.matchings i).spanningCoe) univ

/-- Original internal color-class edges released during reserve repair. -/
def releasedInternal : SimpleGraph U :=
  edgeUnion (fun i =>
    (colorMatching C.graph D.geometry.internal D.geometry.internal_le
      D.internalColor i).spanningCoe \ (D.matchings i).spanningCoe) univ

/-- Original same-side core edges surviving all completed matchings. -/
def remainingInside : SimpleGraph U :=
  insideGraph C.graph D.geometry.left \ D.usedCore

@[simp] theorem usedCore_adj (v w : U) :
    D.usedCore.Adj v w ↔ ∃ i, (D.matchings i).Adj v w := by
  simp only [usedCore, edgeUnion_adj, mem_univ, true_and,
    SimpleGraph.Subgraph.spanningCoe_adj]

@[simp] theorem remainingInside_adj (v w : U) :
    D.remainingInside.Adj v w ↔
      C.graph.Adj v w ∧ ((v ∈ D.geometry.left) ↔ (w ∈ D.geometry.left)) ∧
        ∀ i, ¬ (D.matchings i).Adj v w := by
  simp only [remainingInside, SimpleGraph.sdiff_adj, insideGraph_adj,
    D.usedCore_adj, not_exists]
  tauto

theorem remainingInside_le_core : D.remainingInside ≤ C.graph := by
  intro v w hvw
  exact ((D.remainingInside_adj v w).mp hvw).1

/-- The color classes cover the original internal graph exactly. Thus an
internal edge that is not in the reserve and survives all matchings is
released by its own original color class. -/
theorem remainingInside_le_reserve_sup_released :
    D.remainingInside ≤
      insideGraph D.geometry.reserve D.geometry.left ⊔ D.releasedInternal := by
  intro v w hvw
  obtain ⟨hcore, hside, hnotUsed⟩ := (D.remainingInside_adj v w).mp hvw
  by_cases hreserve : D.geometry.reserve.Adj v w
  · exact Or.inl ⟨hreserve, hside⟩
  · have hinternal : D.geometry.internal.Adj v w :=
      (D.geometry.internal_adj v w).mpr ⟨hcore, hreserve, hside⟩
    have hunion := colorMatching_edgeUnion C.graph D.geometry.internal
      D.geometry.internal_le D.internalColor
    rw [← hunion] at hinternal
    obtain ⟨i, _hi, hcolor⟩ := hinternal
    exact Or.inr ⟨i, mem_univ i, hcolor, hnotUsed i⟩

/-- The remaining internal degree is controlled by the internal part of
the reserve and the actual released-edge load. -/
theorem remainingInside_degree_le_insideReserve (v : U) :
    (D.remainingInside.degree v : ℝ) ≤
      (insideGraph D.geometry.reserve D.geometry.left).degree v + μ * U.card := by
  have hmono := SimpleGraph.degree_le_of_le
    D.remainingInside_le_reserve_sup_released (v := v)
  have hsum := degree_sup_add_degree_inf
    (insideGraph D.geometry.reserve D.geometry.left) D.releasedInternal v
  have hnat : D.remainingInside.degree v ≤
      (insideGraph D.geometry.reserve D.geometry.left).degree v +
        D.releasedInternal.degree v := by
    simp only [← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] at hmono hsum ⊢
    omega
  have hreal : (D.remainingInside.degree v : ℝ) ≤
      (insideGraph D.geometry.reserve D.geometry.left).degree v +
        D.releasedInternal.degree v := by exact_mod_cast hnat
  have hreleased : (D.releasedInternal.degree v : ℝ) ≤ μ * U.card :=
    D.internal_released v
  linarith only [hreal, hreleased]

theorem remainingInside_degree_le_reserve (v : U) :
    (D.remainingInside.degree v : ℝ) ≤ D.geometry.reserve.degree v + μ * U.card := by
  have hmono : (insideGraph D.geometry.reserve D.geometry.left).degree v ≤
      D.geometry.reserve.degree v :=
    SimpleGraph.degree_le_of_le (insideGraph_le D.geometry.reserve D.geometry.left)
  have hreal : ((insideGraph D.geometry.reserve D.geometry.left).degree v : ℝ) ≤
      D.geometry.reserve.degree v := by exact_mod_cast hmono
  exact (D.remainingInside_degree_le_insideReserve v).trans (add_le_add_right hreal _)

/-- Total reserve-degree control gives the direct manuscript-scale bound. -/
theorem remainingInside_degree_le (hp : 0 ≤ p)
    (hcore : ∀ v : U, (C.graph.degree v : ℝ) ≤ k) (v : U) :
    (D.remainingInside.degree v : ℝ) ≤ p * k + 4 * δ * U.card + μ * U.card := by
  have herror : (D.geometry.reserve.degree v : ℝ) - p * C.graph.degree v ≤
      4 * δ * U.card := by
    simpa only [Fintype.card_coe] using (abs_le.mp (D.geometry.reserve_degree_error v)).2
  have hmul := mul_le_mul_of_nonneg_left (hcore v) hp
  have hremaining := D.remainingInside_degree_le_reserve v
  linarith only [herror, hmul, hremaining]

/-- Simplicity also gives a bound in terms of the core order without any
ambient regular-degree hypothesis. -/
theorem remainingInside_degree_le_order (hp : 0 ≤ p) (v : U) :
    (D.remainingInside.degree v : ℝ) ≤ p * U.card + 4 * δ * U.card + μ * U.card := by
  have hcore : (C.graph.degree v : ℝ) ≤ U.card := by
    exact_mod_cast (show C.graph.degree v ≤ U.card by
      simpa only [Fintype.card_coe] using (C.graph.degree_lt_card_verts v).le)
  have herror : (D.geometry.reserve.degree v : ℝ) - p * C.graph.degree v ≤
      4 * δ * U.card := by
    simpa only [Fintype.card_coe] using (abs_le.mp (D.geometry.reserve_degree_error v)).2
  have hmul := mul_le_mul_of_nonneg_left hcore hp
  have hremaining := D.remainingInside_degree_le_reserve v
  linarith only [herror, hmul, hremaining]

/-- Keeping the side estimate gives the sharper half-degree bound. -/
theorem remainingInside_degree_le_half (hp : 0 ≤ p)
    (hcore : ∀ v : U, (C.graph.degree v : ℝ) ≤ k) (v : U) :
    (D.remainingInside.degree v : ℝ) ≤ p * k / 2 + 2 * δ * U.card + μ * U.card := by
  have hside : ((insideGraph D.geometry.reserve D.geometry.left).degree v : ℝ) ≤
      p * C.graph.degree v / 2 + 2 * δ * U.card := by
    rw [insideGraph_degree D.geometry.reserve D.geometry.left D.geometry.right
      D.geometry.disjoint D.geometry.cover v]
    split_ifs with hv
    · have hh := (abs_le.mp (D.geometry.reserve_side_degree_estimate v).1).2
      simp only [Fintype.card_coe] at hh
      linarith only [hh]
    · have hh := (abs_le.mp (D.geometry.reserve_side_degree_estimate v).2).2
      simp only [Fintype.card_coe] at hh
      linarith only [hh]
  have hmul := mul_le_mul_of_nonneg_left (hcore v) hp
  have hremaining := D.remainingInside_degree_le_insideReserve v
  linarith only [hside, hmul, hremaining]

end Overfull.OrdinaryFactorization.FirstHalfData
