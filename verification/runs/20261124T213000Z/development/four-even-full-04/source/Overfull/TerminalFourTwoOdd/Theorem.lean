import Overfull.TerminalFourTwoOdd.Prefix
import Overfull.TerminalFourTwoOdd.Completed

/-! The unrestricted exactly-two-odd four-core terminal conclusion on original copies. -/

noncomputable section

namespace Overfull

open Finset Classical SimpleGraph FourOdd CircuitPatterns Terminal TerminalFourTwoOdd

universe u

theorem four_two_odd_terminal_one_factorization (α ν τ : ℝ)
    (hα : 0 < α) (hν : 0 < ν) (hντ : ν ≤ τ) (hτ : τ ≤ min α 1/64) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, 0 < n₀ ∧
      ∀ (V : Type u) [Fintype V] (G : SimpleGraph V)
        (U : Fin 4 → Finset V) (H : ∀ i, SimpleGraph (U i))
        (label : V → Fin 4) (x y : Fin 4) (h : ℕ) (a : ℝ),
        n₀ ≤ Fintype.card V →
        (∀ i, labelShore label {i} = U i) → x ≠ y →
        (∀ i, (U i).card % 2 = if i=x ∨ i=y then 1 else 0) →
        (∀ v, G.degree v = h) → α*Fintype.card V ≤ (h : ℝ) →
        (∀ X : Finset V, ¬ IsOverfull G h X) →
        Pairwise (fun i j => Disjoint (U i) (U j)) →
        (∀ v, ∃ i, v ∈ U i) →
        (∀ i, α*Fintype.card V ≤ ((U i).card : ℝ)) →
        (∀ i, H i ≤ G.induce (U i : Set V)) →
        (∀ i, IsRobustExpander (H i) ν τ) →
        (∀ i v, (h : ℝ)-a ≤ ((H i).degree v : ℝ)) →
        0 ≤ a → a+1 ≤ ε*Fintype.card V →
        ∃ M : Fin h → Finset G.edgeSet,
          (∀ i, (Multigraph.ofSimpleGraph G).IsPerfectMatching (M i)) ∧
          Pairwise (fun i j => Disjoint (M i) (M j)) ∧ univ.biUnion M = univ := by
  let β := min α 1
  have hβ : 0 < β := lt_min hα zero_lt_one
  have hβ1 : β ≤ 1 := min_le_right _ _
  have hτβ : τ ≤ β/64 := hτ
  obtain ⟨θ,hθ,hθτ,hprefix⟩ := exists_uniform_four_two_odd_prefix β ν τ
    hβ hβ1 hν hντ (by linarith)
  obtain ⟨η,hη,m₀,hcomplete⟩ := exists_uniform_completed_four_two_odd_factorization
    (β/2) θ (τ/2) (by positivity) (by linarith) hθ hθτ (by linarith)
  obtain ⟨ε,hε,n₀,hn₀,hconstruct⟩ := hprefix η hη m₀
  refine ⟨ε,hε,n₀,hn₀,?_⟩
  intro V _ G U H label x y h a hn hparts hxy hparity hregular hdensity hno hdisj hcover
    hsize hembed hrobust hdegree ha herror
  have hdensity' : β*Fintype.card V ≤ (h : ℝ) :=
    (mul_le_mul_of_nonneg_right (min_le_left α 1) (Nat.cast_nonneg _)).trans hdensity
  have hsize' (i : Fin 4) : β*Fintype.card V ≤ ((U i).card : ℝ) :=
    (mul_le_mul_of_nonneg_right (min_le_left α 1) (Nat.cast_nonneg _)).trans (hsize i)
  obtain ⟨P,hm,hk,hsmall⟩ := hconstruct V G U H label x y h a hn hparts hxy hparity
    hregular hdensity' hno hdisj hcover hsize' hembed hrobust hdegree ha herror
  obtain ⟨c⟩ := hcomplete V G U H label x y h a P hparts hxy hparity hdisj hcover hm hk
    (fun i => (mul_le_mul_of_nonneg_right (by linarith : β/2 ≤ β)
      (Nat.cast_nonneg _)).trans (hsize' i)) hsmall
  exact BoundedExterior.exists_oneFactorization_of_coloring (Multigraph.ofSimpleGraph G) h
    (by simpa only [Multigraph.ofSimpleGraph_degree] using hregular) c

end Overfull
