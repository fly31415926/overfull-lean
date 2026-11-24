import Overfull.OrdinaryFactorization.CutReserve
import Overfull.PairedCut.BalancedFootprints

/-!
# Simultaneous cut, reserve, and bounded balanced footprints

The paired cut balances a positive proportion of any prescribed family of
bounded even footprints. Sampling the reserve after that cut preserves the
same concrete shores and their balanced-footprint count. The robustness
constant is fixed before the reserve and error parameters.
-/

namespace Overfull.OrdinaryFactorization

open Finset Classical
open OrdinaryRandomReserve PairedCut

/-- Combine two robustness guarantees on the same host. The first fixes
the crossing robust parameter; the second controls the sampled reserve.
All reserve parameters follow the choice of the crossing parameter. -/
theorem exists_cut_reserve_of_two_robust_parameters_with_bounded_footprints
    (α ν τ : ℝ) (s : ℕ) (hα : 0 < α) (hν : 0 < ν)
    (hντ : ν ≤ τ) (hτ : τ ≤ 1 / 8) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∀ p νR σ δ : ℝ, 0 < p → p ≤ 1 → 0 < νR → 0 < δ →
      ∃ n₀ : ℕ, ∀ (V I : Type*) [Fintype V] [Fintype I] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj] (e : I × Bool ≃ V)
        (k : ℕ) (X : Fin k → Finset V),
        n₀ ≤ Fintype.card V →
        (∀ v, α * Fintype.card V ≤ (G.degree v : ℝ)) →
        IsRobustExpander G ν τ →
        IsRobustExpander G νR σ →
        (∀ i, Even (X i).card) → (∀ i, (X i).card ≤ s) →
        ∃ D : CutReserveData G e α τ ξ p νR σ δ,
          k ≤ 2 ^ (s + 1) * (univ.filter (fun i =>
            (X i ∩ D.left).card = (X i ∩ D.right).card)).card := by
  obtain ⟨ξ, hξ, hcut⟩ := paired_cut_quantitative_balanced_footprints α ν τ s hα hν hντ hτ
  refine ⟨ξ, hξ, ?_⟩
  intro p νR σ δ hp hp1 hνR hδ
  obtain ⟨nCut, hCut⟩ := hcut δ hδ
  let ε := min δ p
  have hε : 0 < ε := lt_min hδ hp
  obtain ⟨nReserve, hReserve⟩ := exists_reserve_with_side_degree_control
    p νR ε hp hp1 hνR hε (min_le_right _ _)
  refine ⟨max nCut nReserve, ?_⟩
  intro V I _ _ _ G _ e k X hn hdegree hG hGReserve hXeven hXsize
  obtain ⟨A, B, hAB, hcover, hAcard, hBcard, hpair, hcross, hprecision, hrob, hmany⟩ :=
    hCut V I G e k X ((le_max_left nCut nReserve).trans hn) hdegree hG hXeven hXsize
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
  }, hmany⟩

/-- Prescribe a smaller reserve range after choosing the reserve density.
Range reduction is applied to the original dense host before sampling;
the crossing robust parameter remains independent of all later choices. -/
theorem exists_cut_reserve_with_bounded_footprints (α ν τ : ℝ) (s : ℕ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτα : τ ≤ α / 4) (hτ : τ ≤ 1 / 8) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∀ p : ℝ, 0 < p → p ≤ 1 →
      ∀ σ : ℝ, 0 < σ → σ ≤ τ → ∀ δ : ℝ, 0 < δ →
      ∃ n₀ : ℕ, ∀ (V I : Type*) [Fintype V] [Fintype I] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj] (e : I × Bool ≃ V)
        (k : ℕ) (X : Fin k → Finset V),
        n₀ ≤ Fintype.card V →
        (∀ v, α * Fintype.card V ≤ (G.degree v : ℝ)) →
        IsRobustExpander G ν τ →
        (∀ i, Even (X i).card) → (∀ i, (X i).card ≤ s) →
        ∃ D : CutReserveData G e α τ ξ p (min ν (α * σ / 2)) σ δ,
          k ≤ 2 ^ (s + 1) * (univ.filter (fun i =>
            (X i ∩ D.left).card = (X i ∩ D.right).card)).card := by
  obtain ⟨ξ, hξ, hconstruct⟩ :=
    exists_cut_reserve_of_two_robust_parameters_with_bounded_footprints
      α ν τ s hα hν hντ hτ
  refine ⟨ξ, hξ, ?_⟩
  intro p hp hp1 σ hσ hστ δ hδ
  have hνR : 0 < min ν (α * σ / 2) := lt_min hν (by positivity)
  obtain ⟨n₀, hn₀⟩ := hconstruct p (min ν (α * σ / 2)) σ δ hp hp1 hνR hδ
  refine ⟨n₀, ?_⟩
  intro V I _ _ _ G _ e k X hn hdegree hG hXeven hXsize
  exact hn₀ V I G e k X hn hdegree hG
    (robust_range_reduction G α ν τ σ hα hα1 hν hτα hσ hστ hdegree hG)
    hXeven hXsize

end Overfull.OrdinaryFactorization
