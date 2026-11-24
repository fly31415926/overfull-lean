import Overfull.SmallCuts

/-!
# Cuts in the auxiliary simple graph

Every cut with at least two vertices on each side has more than `k` edges.
Small shores are handled by the minimum degree and simplicity; the other
shores are handled by robust expansion.
-/

namespace Overfull.AuxiliaryCompletion

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Sufficient numerical conditions for every nontrivial auxiliary cut to
have more than `k` edges.  Both sides of the cut must have at least two
vertices. -/
theorem core_cut_gt_of_ranges (k b ν τ : ℝ)
    (hν : 0 ≤ ν)
    (hb : b ≤ k / 8) (hsmall : τ * Fintype.card V ≤ k / 8)
    (hlarge : k < ν ^ 2 * (Fintype.card V : ℝ) ^ 2)
    (hdegree : ∀ v, k - b ≤ (G.degree v : ℝ))
    (hrobust : IsRobustExpander G ν τ) (X : Finset V)
    (hX : 2 ≤ X.card) (hcompl : 2 ≤ Xᶜ.card) :
    k < ((Multigraph.ofSimpleGraph G).cutSize X : ℝ) := by
  classical
  let S := SmallCuts.smallerShore X
  have htwo : (2 : ℝ) ≤ S.card := by
    have : 2 ≤ S.card := by
      rw [show S = SmallCuts.smallerShore X from rfl, SmallCuts.smallerShore_card]
      exact le_min hX hcompl
    exact_mod_cast this
  have hhalf : (2 : ℝ) * S.card ≤ Fintype.card V := by
    exact_mod_cast SmallCuts.smallerShore_card_le_half X
  have hcut : (Multigraph.ofSimpleGraph G).cutSize S =
      (Multigraph.ofSimpleGraph G).cutSize X :=
    SmallCuts.smallerShore_cut (Multigraph.ofSimpleGraph G) X
  rw [← hcut]
  by_cases hsmallshore : (S.card : ℝ) < τ * Fintype.card V
  · have hr : (S.card : ℝ) < k / 8 := lt_of_lt_of_le hsmallshore hsmall
    have hpositive : 0 < k - b - S.card + 1 := by linarith
    have hproduct := mul_le_mul_of_nonneg_right htwo hpositive.le
    have hstrict : k < 2 * (k - b - S.card + 1) := by linarith
    exact lt_of_lt_of_le (lt_of_lt_of_le hstrict hproduct)
      (SmallCuts.cut_lower_bound_degree G (k - b) hdegree S)
  · have hlower : τ * Fintype.card V ≤ (S.card : ℝ) := le_of_not_gt hsmallshore
    have hupper : (S.card : ℝ) ≤ (1 - τ) * Fintype.card V := by
      nlinarith
    exact lt_of_lt_of_le hlarge
      (SmallCuts.robust_cut_lower_bound G ν τ hν hrobust S hlower hupper)

/-- The numerical hypotheses used for the auxiliary graph in Lemma 2.22
imply the cut bound.  Its order is at most three times the original order. -/
theorem core_cut_gt (n k : ℕ) (b α ν τ : ℝ)
    (hτ : 0 ≤ τ) (hτα : τ < α / 24)
    (hν : 0 ≤ ν) (horder : (Fintype.card V : ℝ) ≤ 3 * n)
    (hk : α * n ≤ k) (hb : b ≤ k / 8)
    (hlarge : (k : ℝ) < ν ^ 2 * (Fintype.card V : ℝ) ^ 2)
    (hdegree : ∀ v, (k : ℝ) - b ≤ (G.degree v : ℝ))
    (hrobust : IsRobustExpander G ν τ) (X : Finset V)
    (hX : 2 ≤ X.card) (hcompl : 2 ≤ Xᶜ.card) :
    k < (Multigraph.ofSimpleGraph G).cutSize X := by
  have hsmall : τ * Fintype.card V ≤ (k : ℝ) / 8 := by
    have horder' := mul_le_mul_of_nonneg_left horder hτ
    have hscale := mul_le_mul_of_nonneg_right hτα.le (Nat.cast_nonneg n)
    nlinarith
  have h := core_cut_gt_of_ranges G k b ν τ hν
    hb hsmall hlarge hdegree hrobust X hX hcompl
  exact_mod_cast h

end Overfull.AuxiliaryCompletion
