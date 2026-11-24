import Overfull.TerminalFour.Parity
import Overfull.TerminalFourEven.Theorem
import Overfull.TerminalFourTwoOdd.Theorem
import Overfull.TerminalFourOdd.Theorem

/-! A uniform terminal theorem covering all parity profiles of four cores. -/

noncomputable section
namespace Overfull
open Finset Classical SimpleGraph FourOdd CircuitPatterns TerminalFour
universe u

/-- All constants precede the host. The actual forest supply is used only
when all four cores are odd; all three parity constructions preserve copies. -/
theorem four_core_terminal_one_factorization (α ν τ : ℝ)
    (hα : 0 < α) (hν : 0 < ν) (hντ : ν ≤ τ) (hτ : τ ≤ min α 1 / 64) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, 0 < n₀ ∧
      ∀ (V : Type u) [Fintype V] (G : SimpleGraph V)
        (U : Fin 4 → Finset V) (H : ∀ i, SimpleGraph (U i))
        (label : V → Fin 4) (h r₀ : ℕ) (a : ℝ) (F : Finset LabelPair),
        n₀ ≤ Fintype.card V → Even (Fintype.card V) →
        (∀ i, labelShore label {i} = U i) →
        (∀ v, G.degree v = h) → α * Fintype.card V ≤ (h : ℝ) →
        (∀ X : Finset V, ¬ IsOverfull G h X) →
        Pairwise (fun i j => Disjoint (U i) (U j)) →
        (∀ v, ∃ i, v ∈ U i) →
        (∀ i, α * Fintype.card V ≤ ((U i).card : ℝ)) →
        (∀ i, H i ≤ G.induce (U i : Set V)) →
        (∀ i, IsRobustExpander (H i) ν τ) →
        (∀ i v, (h : ℝ) - a ≤ ((H i).degree v : ℝ)) →
        0 ≤ a → a + 1 ≤ ε * Fintype.card V →
        ((∀ i, (U i).card % 2 = 1) → LabelForestShape F) →
        (∀ p ∈ F, r₀ ≤ (pairPool (joiningQuotient (Multigraph.ofSimpleGraph G) label) p).card) →
        (h : ℝ) - r₀ ≤ ε * Fintype.card V →
        ∃ M : Fin h → Finset G.edgeSet,
          (∀ i, (Multigraph.ofSimpleGraph G).IsPerfectMatching (M i)) ∧
          Pairwise (fun i j => Disjoint (M i) (M j)) ∧ univ.biUnion M = univ := by
  obtain ⟨εE, hεE, nE, hnE, hE⟩ := four_even_terminal_one_factorization α ν τ hα hν hντ hτ
  obtain ⟨εT, hεT, nT, _hnT, hT⟩ := four_two_odd_terminal_one_factorization α ν τ hα hν hντ hτ
  obtain ⟨εO, hεO, nO, _hnO, hO⟩ := four_odd_terminal_one_factorization α ν τ hα hν hντ hτ
  let ε := min εE (min εT εO)
  let n₀ := max nE (max nT nO)
  refine ⟨ε, lt_min hεE (lt_min hεT hεO), n₀, hnE.trans_le (le_max_left _ _), ?_⟩
  intro V _ G U H label h r₀ a F hn heven hparts hregular hdensity hno hdisj hcover
    hsize hembed hrobust hdegree ha herror hforest hsupply hreserve
  have hεE' : ε ≤ εE := min_le_left _ _
  have hεT' : ε ≤ εT := (min_le_right _ _).trans (min_le_left _ _)
  have hεO' : ε ≤ εO := (min_le_right _ _).trans (min_le_right _ _)
  have herrorE := herror.trans (mul_le_mul_of_nonneg_right hεE' (Nat.cast_nonneg _))
  have herrorT := herror.trans (mul_le_mul_of_nonneg_right hεT' (Nat.cast_nonneg _))
  have herrorO := herror.trans (mul_le_mul_of_nonneg_right hεO' (Nat.cast_nonneg _))
  rcases four_core_parity U label hparts heven with hpar | ⟨x,y,hxy,hpar⟩ | hpar
  · exact hE V G U H label h a ((le_max_left _ _).trans hn) hparts hpar
      hregular hdensity hno hdisj hcover hsize hembed hrobust hdegree ha herrorE
  · exact hT V G U H label x y h a ((le_max_left _ _).trans ((le_max_right _ _).trans hn))
      hparts hxy hpar hregular hdensity hno hdisj hcover hsize hembed hrobust hdegree ha herrorT
  · exact hO V G U H label h r₀ a F ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
      hparts hpar hregular hdensity hno hdisj hcover hsize hembed hrobust hdegree ha herrorO
      (hforest hpar) hsupply (hreserve.trans
        (mul_le_mul_of_nonneg_right hεO' (Nat.cast_nonneg _)))

end Overfull
