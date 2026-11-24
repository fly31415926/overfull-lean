import Overfull.TerminalFourOdd.Prefix
import Overfull.TerminalFourOdd.Completed

/-!
# Uniform terminal one-factorization for four odd robust parts

This proves the all-four-odd subcase of terminal Proposition 4.16 from
the original simple host and actual forest pair supplies. The primary
decomposition, selected prefix, completed matchings, residual geometry,
local colorings and original-copy reconstruction are all constructed.
The four-even and exactly-two-odd cases are not asserted here.
-/

noncomputable section

namespace Overfull

open Finset Classical SimpleGraph FourOdd Compression CircuitPatterns Terminal TerminalFourOdd

universe u

theorem four_odd_terminal_one_factorization (α ν τ : ℝ)
    (hα : 0 < α) (hν : 0 < ν) (hντ : ν ≤ τ) (hτ : τ ≤ min α 1/64) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, 0 < n₀ ∧
      ∀ (V : Type u) [Fintype V] (G : SimpleGraph V)
        (U : Fin 4 → Finset V) (H : ∀ i, SimpleGraph (U i))
        (label : V → Fin 4) (h r₀ : ℕ) (a : ℝ) (F : Finset LabelPair),
        n₀ ≤ Fintype.card V →
        (∀ i, labelShore label {i} = U i) → (∀ i, (U i).card % 2 = 1) →
        (∀ v, G.degree v = h) → α*Fintype.card V ≤ (h : ℝ) →
        (∀ X : Finset V, ¬ IsOverfull G h X) →
        Pairwise (fun i j => Disjoint (U i) (U j)) →
        (∀ v, ∃ i, v ∈ U i) →
        (∀ i, α*Fintype.card V ≤ ((U i).card : ℝ)) →
        (∀ i, H i ≤ G.induce (U i : Set V)) →
        (∀ i, IsRobustExpander (H i) ν τ) →
        (∀ i v, (h : ℝ)-a ≤ ((H i).degree v : ℝ)) →
        0 ≤ a → a+1 ≤ ε*Fintype.card V → LabelForestShape F →
        (∀ p ∈ F, r₀ ≤ (pairPool (joiningQuotient (Multigraph.ofSimpleGraph G) label) p).card) →
        (h : ℝ)-r₀ ≤ ε*Fintype.card V →
        ∃ M : Fin h → Finset G.edgeSet,
          (∀ i, (Multigraph.ofSimpleGraph G).IsPerfectMatching (M i)) ∧
          Pairwise (fun i j => Disjoint (M i) (M j)) ∧ univ.biUnion M = univ := by
  let β := min α 1
  have hβ : 0 < β := lt_min hα zero_lt_one
  have hβ1 : β ≤ 1 := min_le_right _ _
  have hτβ : τ ≤ β/64 := hτ
  have hτprefix : τ ≤ β/8 := by linarith
  obtain ⟨θ,hθ,hθτ,hprefix⟩ := exists_uniform_four_odd_prefix β ν τ
    hβ hβ1 hν hντ hτprefix
  have hτresidual : τ/2 ≤ min (β/2) 1/16 := by
    rw [min_eq_left (by linarith : β/2 ≤ 1)]
    linarith
  obtain ⟨η,hη,m₀,hcomplete⟩ := exists_uniform_completed_four_odd_factorization
    (β/2) (β/100) θ (τ/2) (by positivity) (by linarith) (by positivity)
    hθ hθτ hτresidual
  obtain ⟨ε,hε,n₀,hn₀,hconstruct⟩ := hprefix η hη m₀
  refine ⟨ε,hε,n₀,hn₀,?_⟩
  intro V _ G U H label h r₀ a F hn hparts hodd hregular hdensity hno hdisj hcover
    hsize hembed hrobust hdegree ha herror hF hsupply hreserve
  have hdensity' : β*Fintype.card V ≤ (h : ℝ) :=
    (mul_le_mul_of_nonneg_right (min_le_left α 1) (Nat.cast_nonneg _)).trans hdensity
  have hsize' (i : Fin 4) : β*Fintype.card V ≤ ((U i).card : ℝ) :=
    (mul_le_mul_of_nonneg_right (min_le_left α 1) (Nat.cast_nonneg _)).trans (hsize i)
  obtain ⟨P,hm,hk,hsmall⟩ := hconstruct V G U H label h r₀ a F hn hparts hodd
    hregular hdensity' hno hdisj hcover hsize' hembed hrobust hdegree
    ha herror hF hsupply hreserve
  have hpalette (i : Fin 4) : (β/100)*(U i).card ≤ (P.rounds : ℝ) := by
    have hUn : ((U i).card : ℝ) ≤ Fintype.card V := by exact_mod_cast card_le_univ (U i)
    have hcore := (mul_le_mul_of_nonneg_left hUn hβ.le).trans hdensity'
    have hr : h < 100*P.rounds := by rw [P.rounds_eq]; unfold prefixRounds; omega
    have hrR : (h : ℝ) < 100*(P.rounds : ℝ) := by exact_mod_cast hr
    linarith
  exact hcomplete V G U H label h a P hparts hodd hm hk ha hsmall hpalette

end Overfull
