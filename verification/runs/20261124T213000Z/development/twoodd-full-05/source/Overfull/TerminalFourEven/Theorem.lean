import Overfull.TerminalFourEven.Prefix
import Overfull.TerminalFourEven.Completed

/-! Uniform original-copy one-factorization for four even robust cores. -/

noncomputable section

namespace Overfull

open Finset Classical SimpleGraph FourOdd Terminal TerminalFourEven

universe u

/-- Every joining piece, perfect prefix, residual component coloring and final
matching family is constructed from the original host. The tolerance and order
threshold are fixed before the host and its core data. -/
theorem four_even_terminal_one_factorization (α ν τ : ℝ)
    (hα : 0 < α) (hν : 0 < ν) (hντ : ν ≤ τ) (hτ : τ ≤ min α 1/64) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, 0 < n₀ ∧
      ∀ (V : Type u) [Fintype V] (G : SimpleGraph V)
        (U : Fin 4 → Finset V) (H : ∀ i, SimpleGraph (U i))
        (label : V → Fin 4) (h : ℕ) (a : ℝ),
        n₀ ≤ Fintype.card V →
        (∀ i, labelShore label {i} = U i) → (∀ i, (U i).card % 2 = 0) →
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
  have hτprefix : τ ≤ β/8 := by linarith
  obtain ⟨θ,hθ,hθτ,hprefix⟩ := exists_uniform_four_even_prefix β ν τ
    hβ hβ1 hν hντ hτprefix
  have hτresidual : τ/2 ≤ min (β/2) 1/16 := by
    rw [min_eq_left (by linarith : β/2 ≤ 1)]
    linarith
  obtain ⟨η,hη,m₀,hcomplete⟩ := exists_uniform_completed_four_even_factorization
    (β/2) θ (τ/2) (by positivity) hθ hθτ hτresidual
  obtain ⟨ε,hε,n₀,hn₀,hconstruct⟩ := hprefix η hη m₀
  refine ⟨ε,hε,n₀,hn₀,?_⟩
  intro V _ G U H label h a hn hparts heven hregular hdensity hno hdisj hcover
    hsize hembed hrobust hdegree ha herror
  have hdensity' : β*Fintype.card V ≤ (h : ℝ) :=
    (mul_le_mul_of_nonneg_right (min_le_left α 1) (Nat.cast_nonneg _)).trans hdensity
  have hsize' (i : Fin 4) : β*Fintype.card V ≤ ((U i).card : ℝ) :=
    (mul_le_mul_of_nonneg_right (min_le_left α 1) (Nat.cast_nonneg _)).trans (hsize i)
  obtain ⟨P,hm,hk,hsmall⟩ := hconstruct V G U H label h a hn hparts heven
    hregular hdensity' hno hdisj hcover hsize' hembed hrobust hdegree ha herror
  have hk' (i : Fin 4) : (β/2)*(U i).card ≤ ((h-P.rounds : ℕ) : ℝ) := by
    have hUn : ((U i).card : ℝ) ≤ Fintype.card V := by exact_mod_cast card_le_univ (U i)
    exact (mul_le_mul_of_nonneg_left hUn (by positivity)).trans hk
  obtain ⟨c⟩ := hcomplete V G U H label h a P hparts hdisj hcover heven hm hk' hsmall
  have hregularM : ∀ v, (Multigraph.ofSimpleGraph G).degree v = h := by
    simpa only [Multigraph.ofSimpleGraph_degree] using hregular
  have hinst : (fun e f : G.edgeSet => propDecidable (e = f)) =
      (inferInstance : DecidableEq G.edgeSet) := Subsingleton.elim _ _
  simpa only [hinst] using
    BoundedExterior.exists_oneFactorization_of_coloring (Multigraph.ofSimpleGraph G) h hregularM c

end Overfull
