import Overfull.TerminalFour.Theorem
import Overfull.TerminalFour.PatternTransport
import Overfull.Terminal.ThreeCore

/-! The complete terminal proposition for the actual frequent-pattern result. -/

noncomputable section
namespace Overfull
open Finset Classical SimpleGraph FourOdd CircuitPatterns Compression TerminalFour
universe u v

/-- Proposition 4.16. The actual residual produced by the frequent-pattern
reduction has a one-factorization for three or four cores in every parity case.
Even order is derived internally; no coloring or decomposition is an input. -/
theorem frequent_pattern_result_one_factorization (α ν τ : ℝ)
    (hα : 0 < α) (hν : 0 < ν) (hντ : ν ≤ τ) (hτ : τ ≤ min α 1 / 64) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ n₀ : ℕ, 0 < n₀ ∧
      ∀ (V : Type u) [Fintype V] (I : Type v) [Fintype I]
        (G₀ : SimpleGraph V) (U₀ : I → Finset V) (k t : ℕ)
        (R : FrequentPatternResult G₀ U₀ k t δ ν τ),
        (Fintype.card I = 3 ∨ Fintype.card I = 4) → n₀ ≤ Fintype.card V →
        α * Fintype.card V ≤ (R.h : ℝ) →
        (∀ i, α * Fintype.card V ≤ ((R.U i).card : ℝ)) →
        ∃ M : Fin R.h → Finset R.G.edgeSet,
          (∀ i, (Multigraph.ofSimpleGraph R.G).IsPerfectMatching (M i)) ∧
          Pairwise (fun i j => Disjoint (M i) (M j)) ∧ univ.biUnion M = univ := by
  obtain ⟨ε₃,hε₃,n₃,hn₃,hthree⟩ := three_core_terminal_one_factorization α ν τ hα hν hντ hτ
  obtain ⟨ε₄,hε₄,n₄,_hn₄,hfour⟩ := four_core_terminal_one_factorization α ν τ hα hν hντ hτ
  let ε := min ε₃ ε₄
  have hε : 0 < ε := lt_min hε₃ hε₄
  let n₀ := max (max n₃ n₄) ⌈2 / ε⌉₊
  have hn₀ : 0 < n₀ := hn₃.trans_le ((le_max_left _ _).trans (le_max_left _ _))
  refine ⟨ε/2, by positivity, n₀, hn₀, ?_⟩
  intro V _ I _ G₀ U₀ k t R hI hn hdensity hsize
  have heven := even_order_of_positive_regular R.G R.h R.degree_positive R.regular R.no_overfull
  obtain ⟨v₀⟩ := Fintype.card_pos_iff.mp (hn₀.trans_le hn)
  have hhn : (R.h : ℝ) ≤ Fintype.card V := by
    have ht := R.G.degree_lt_card_verts v₀
    rw [R.regular] at ht
    exact_mod_cast ht.le
  have hceil : (⌈2 / ε⌉₊ : ℝ) ≤ Fintype.card V := by
    exact_mod_cast (le_max_right (max n₃ n₄) ⌈2 / ε⌉₊).trans hn
  have htwo : 2 ≤ ε * Fintype.card V := by
    have hh := (div_le_iff₀ hε).mp ((Nat.le_ceil (2 / ε)).trans hceil)
    linarith
  have hbudget : R.error + 1 ≤ ε * Fintype.card V := by
    have hh := mul_le_mul_of_nonneg_left hhn (by positivity : 0 ≤ ε/2)
    linarith only [R.error_bound, hh, htwo]
  have hreserve : (R.h : ℝ) - R.reserve ≤ ε * Fintype.card V := by
    have hh := mul_le_mul_of_nonneg_left hhn (by positivity : 0 ≤ ε/2)
    have hnnonneg : 0 ≤ ε * Fintype.card V := mul_nonneg hε.le (Nat.cast_nonneg _)
    linarith only [R.reserve_error, hh, hnnonneg]
  rcases hI with hI | hI
  · let e := Fintype.equivFinOfCardEq hI
    have hd : Pairwise (fun i j : Fin 3 => Disjoint (R.U (e.symm i)) (R.U (e.symm j))) := by
      intro i j hij
      exact R.core_disjoint (fun heq => hij (e.symm.injective heq))
    have hc (v : V) : ∃ i : Fin 3, v ∈ R.U (e.symm i) := by
      obtain ⟨i,hi⟩ := R.cover v
      exact ⟨e i, by simpa only [e.symm_apply_apply] using hi⟩
    exact hthree V R.G (fun i => R.U (e.symm i)) (fun i => R.H (e.symm i)) R.h R.error
      ((le_max_left _ _).trans ((le_max_left _ _).trans hn)) heven R.regular hdensity R.no_overfull
      hd hc (fun i => hsize _) (fun i => R.core_embed _) (fun i => R.core_robust _)
      (fun i => R.core_degree _) R.error_nonneg
      (hbudget.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _)))
  · let e := fourCodeEquiv R.code hI
    let label := coreLabel R.U R.code
    have hp (i : Fin 4) : labelShore label {i} = R.U (e.symm i) :=
      codeEquiv_shore R.U R.code hI R.core_disjoint R.cover i
    have hd : Pairwise (fun i j : Fin 4 => Disjoint (R.U (e.symm i)) (R.U (e.symm j))) := by
      intro i j hij
      exact R.core_disjoint (fun heq => hij (e.symm.injective heq))
    have hc (v : V) : ∃ i : Fin 4, v ∈ R.U (e.symm i) := by
      obtain ⟨i,hi⟩ := R.cover v
      exact ⟨e i, by simpa only [e.symm_apply_apply] using hi⟩
    have hf (hodd : ∀ i : Fin 4, (R.U (e.symm i)).card % 2 = 1) : LabelForestShape R.forest := by
      apply R.forest_shape hI
      intro i
      apply Nat.odd_iff.mpr
      simpa only [e.symm_apply_apply] using hodd (e i)
    have hs (p : LabelPair) (hpF : p ∈ R.forest) :
        R.reserve ≤ (pairPool (joiningQuotient (Multigraph.ofSimpleGraph R.G) label) p).card := by
      rw [joining_pairPool_card R.G R.U R.code p]
      exact R.pair_supply p hpF
    exact hfour V R.G (fun i => R.U (e.symm i)) (fun i => R.H (e.symm i)) label R.h R.reserve
      R.error R.forest ((le_max_right _ _).trans ((le_max_left _ _).trans hn)) heven hp
      R.regular hdensity R.no_overfull hd hc (fun i => hsize _) (fun i => R.core_embed _)
      (fun i => R.core_robust _) (fun i => R.core_degree _) R.error_nonneg
      (hbudget.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg _))) hf hs
      (hreserve.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg _)))

end Overfull
