import Overfull.OrdinaryFactorization.Geometry
import Overfull.PairedCut.Quantitative
import Overfull.OrdinaryRandomReserveSides

/-!
# A simultaneous balanced cut, robust reserve, and internal leftover

The positive robust crossing constant is chosen before the reserve
probability and the degree tolerance. A single actual cut and sample give
all conclusions, including the near-regular internal graph to be colored.
-/

namespace Overfull.OrdinaryFactorization

open Finset Classical
open OrdinaryRandomReserve PairedCut

variable {V I : Type*} [Fintype V] [Fintype I] [DecidableEq V]

/-- Concrete data for the first geometric step of ordinary-core
factorization. Both derived graphs retain the original vertices and edges. -/
structure CutReserveData (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : I × Bool ≃ V) (α τ ξ p νR σ δ : ℝ) where
  left : Finset V
  right : Finset V
  sample : Sym2 V → Bool
  disjoint : Disjoint left right
  cover : left ∪ right = univ
  left_card : left.card = Fintype.card I
  right_card : right.card = Fintype.card I
  split_pairs : ∀ i, (e (i, false) ∈ left ∧ e (i, true) ∈ right) ∨
    (e (i, true) ∈ left ∧ e (i, false) ∈ right)
  crossing_degree : ∀ v,
    α * Fintype.card V / 3 ≤ ((crossingGraph G left).degree v : ℝ)
  crossing_robust : IsBipartiteRobustExpander (cutSidesGraph G left right) ξ (4 * τ)
  original_degrees : ∀ v,
    |((G.neighborFinset v ∩ left).card : ℝ) - G.degree v / 2| ≤ δ * Fintype.card V ∧
    |((G.neighborFinset v ∩ right).card : ℝ) - G.degree v / 2| ≤ δ * Fintype.card V
  reserve_le : sampledGraph G sample ≤ G
  reserve_robust : IsRobustExpander (sampledGraph G sample) (p * νR / 4) σ
  reserve_degrees : ∀ v,
    |(((sampledGraph G sample).neighborFinset v ∩ left).card : ℝ) - p * G.degree v / 2| ≤
      2 * δ * Fintype.card V ∧
    |(((sampledGraph G sample).neighborFinset v ∩ right).card : ℝ) - p * G.degree v / 2| ≤
      2 * δ * Fintype.card V
  internal_degree : ∀ v,
    |((internalLeftover G (sampledGraph G sample) left).degree v : ℝ) -
      (1 - p) * G.degree v / 2| ≤ 3 * δ * Fintype.card V

namespace CutReserveData

variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {e : I × Bool ≃ V} {α τ ξ p νR σ δ : ℝ}

/-- The actual sampled reserve on the original vertex set. -/
def reserve (D : CutReserveData G e α τ ξ p νR σ δ) : SimpleGraph V :=
  sampledGraph G D.sample

/-- Exactly the original internal edges outside the reserve. -/
def internal (D : CutReserveData G e α τ ξ p νR σ δ) : SimpleGraph V :=
  internalLeftover G D.reserve D.left

theorem internal_le (D : CutReserveData G e α τ ξ p νR σ δ) : D.internal ≤ G :=
  internalLeftover_le G D.reserve D.left

theorem internal_disjoint (D : CutReserveData G e α τ ξ p νR σ δ) :
    Disjoint D.internal D.reserve := internalLeftover_disjoint G D.reserve D.left

@[simp] theorem internal_adj (D : CutReserveData G e α τ ξ p νR σ δ) (v w : V) :
    D.internal.Adj v w ↔
      G.Adj v w ∧ ¬ D.reserve.Adj v w ∧ ((v ∈ D.left) ↔ (w ∈ D.left)) :=
  internalLeftover_adj G D.reserve D.left v w

end CutReserveData

/-- Combine two robustness guarantees on the same host. The first fixes
the crossing robust parameter; the second controls the sampled reserve.
All reserve parameters follow the choice of the crossing parameter. -/
theorem exists_cut_reserve_of_two_robust_parameters
    (α ν τ : ℝ) (hα : 0 < α) (hν : 0 < ν)
    (hντ : ν ≤ τ) (hτ : τ ≤ 1 / 8) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∀ p νR σ δ : ℝ, 0 < p → p ≤ 1 → 0 < νR → 0 < δ →
      ∃ n₀ : ℕ, ∀ (V I : Type*) [Fintype V] [Fintype I] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj] (e : I × Bool ≃ V),
        n₀ ≤ Fintype.card V →
        (∀ v, α * Fintype.card V ≤ (G.degree v : ℝ)) →
        IsRobustExpander G ν τ →
        IsRobustExpander G νR σ →
        Nonempty (CutReserveData G e α τ ξ p νR σ δ) := by
  obtain ⟨ξ, hξ, hcut⟩ := paired_cut_quantitative α ν τ hα hν hντ hτ
  refine ⟨ξ, hξ, ?_⟩
  intro p νR σ δ hp hp1 hνR hδ
  obtain ⟨nCut, hCut⟩ := hcut δ hδ
  let ε := min δ p
  have hε : 0 < ε := lt_min hδ hp
  obtain ⟨nReserve, hReserve⟩ := exists_reserve_with_side_degree_control
    p νR ε hp hp1 hνR hε (min_le_right _ _)
  refine ⟨max nCut nReserve, ?_⟩
  intro V I _ _ _ G _ e hn hdegree hG hGReserve
  obtain ⟨A, B, hAB, hcover, hAcard, hBcard, hpair, hcross, hprecision, hrob⟩ :=
    hCut V I G e ((le_max_left nCut nReserve).trans hn) hdegree hG
  obtain ⟨ω, hRG, hRrob, hsample⟩ := hReserve V G σ A B
    ((le_max_right nCut nReserve).trans hn) hGReserve
  have hcoefficient : ε + p * δ ≤ 2 * δ := by
    have hεδ : ε ≤ δ := min_le_left _ _
    have hpδ := mul_le_mul_of_nonneg_right hp1 hδ.le
    linarith
  have herror : (ε + p * δ) * Fintype.card V ≤ 2 * δ * Fintype.card V :=
    mul_le_mul_of_nonneg_right hcoefficient (Nat.cast_nonneg _)
  have hreserve (v : V) :
      |(((sampledGraph G ω).neighborFinset v ∩ A).card : ℝ) - p * G.degree v / 2| ≤
        2 * δ * Fintype.card V ∧
      |(((sampledGraph G ω).neighborFinset v ∩ B).card : ℝ) - p * G.degree v / 2| ≤
        2 * δ * Fintype.card V := by
    constructor
    · have h := side_degree_deviation_from_target G ω v A p ε δ
        ((G.degree v : ℝ) / 2) hp.le (hsample v).1 (hprecision v).1
      simpa only [mul_div_assoc] using h.le.trans herror
    · have h := side_degree_deviation_from_target G ω v B p ε δ
        ((G.degree v : ℝ) / 2) hp.le (hsample v).2 (hprecision v).2
      simpa only [mul_div_assoc] using h.le.trans herror
  have hinternal (v : V) :
      |((internalLeftover G (sampledGraph G ω) A).degree v : ℝ) -
        (1 - p) * G.degree v / 2| ≤ 3 * δ * Fintype.card V := by
    have h := internalLeftover_degree_error G (sampledGraph G ω) hRG A B hAB hcover
      v ((G.degree v : ℝ) / 2) (p * G.degree v / 2)
      (δ * Fintype.card V) (2 * δ * Fintype.card V) (hprecision v) (hreserve v)
    have htarget : (G.degree v : ℝ) / 2 - p * G.degree v / 2 =
        (1 - p) * G.degree v / 2 := by ring
    rw [htarget, show δ * Fintype.card V + 2 * δ * Fintype.card V =
      3 * δ * Fintype.card V by ring] at h
    exact h
  exact ⟨{
    left := A
    right := B
    sample := ω
    disjoint := hAB
    cover := hcover
    left_card := hAcard
    right_card := hBcard
    split_pairs := hpair
    crossing_degree := hcross
    crossing_robust := hrob
    original_degrees := hprecision
    reserve_le := hRG
    reserve_robust := hRrob
    reserve_degrees := hreserve
    internal_degree := hinternal
  }⟩

/-- Prescribe a smaller reserve range after choosing the reserve density.
Range reduction is applied to the original dense host before sampling;
the crossing robust parameter remains independent of all later choices. -/
theorem exists_cut_reserve (α ν τ : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτα : τ ≤ α / 4) (hτ : τ ≤ 1 / 8) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∀ p : ℝ, 0 < p → p ≤ 1 →
      ∀ σ : ℝ, 0 < σ → σ ≤ τ → ∀ δ : ℝ, 0 < δ →
      ∃ n₀ : ℕ, ∀ (V I : Type*) [Fintype V] [Fintype I] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj] (e : I × Bool ≃ V),
        n₀ ≤ Fintype.card V →
        (∀ v, α * Fintype.card V ≤ (G.degree v : ℝ)) →
        IsRobustExpander G ν τ →
        Nonempty (CutReserveData G e α τ ξ p (min ν (α * σ / 2)) σ δ) := by
  obtain ⟨ξ, hξ, hconstruct⟩ :=
    exists_cut_reserve_of_two_robust_parameters α ν τ hα hν hντ hτ
  refine ⟨ξ, hξ, ?_⟩
  intro p hp hp1 σ hσ hστ δ hδ
  have hνR : 0 < min ν (α * σ / 2) := lt_min hν (by positivity)
  obtain ⟨n₀, hn₀⟩ := hconstruct p (min ν (α * σ / 2)) σ δ hp hp1 hνR hδ
  refine ⟨n₀, ?_⟩
  intro V I _ _ _ G _ e hn hdegree hG
  exact hn₀ V I G e hn hdegree hG
    (robust_range_reduction G α ν τ σ hα hα1 hν hτα hσ hστ hdegree hG)

end Overfull.OrdinaryFactorization
