import Overfull.CompatibleCircuits.FourStrictTriangles
import Overfull.CompatibleCircuits.FourAdmissibleClassification

/-!
# Complete support forces a short compatible circuit

The six bundle sizes are unrestricted natural numbers counting actual
copies.  Local corner bounds and strict opposite-shore bounds rule out
all choices of a monochromatic blocker for each of the four triangles.
-/

namespace Overfull.CompatibleCircuits

/-- Finite arithmetic form of the four triangle-blocker contradiction.
Repeated blockers and cyclic blocker assignments fail the local bounds;
the remaining opposite-pair assignments fail strict two-shore bounds. -/
theorem four_positive_triangle_corner_bounds_false
    (a b c d e f : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f)
    (h012 : (a + b ≤ c ∧ a + b < e + f) ∨
      (a + d ≤ e ∧ a + d < c + f) ∨ (b + d ≤ f ∧ b + d < c + e))
    (h013 : (a + c ≤ b ∧ a + c < d + f) ∨
      (a + e ≤ d ∧ a + e < b + f) ∨ (c + e ≤ f ∧ c + e < b + d))
    (h023 : (b + c ≤ a ∧ b + c < d + e) ∨
      (b + f ≤ d ∧ b + f < a + e) ∨ (c + f ≤ e ∧ c + f < a + d))
    (h123 : (d + e ≤ a ∧ d + e < b + c) ∨
      (d + f ≤ b ∧ d + f < a + c) ∨ (e + f ≤ c ∧ e + f < a + b)) : False := by
  rcases h012 with h012 | h012 | h012 <;>
    rcases h013 with h013 | h013 | h013 <;>
      rcases h023 with h023 | h023 | h023 <;>
        rcases h123 with h123 | h123 | h123 <;> omega

end Overfull.CompatibleCircuits

namespace Overfull.Multigraph

open Finset Classical Overfull.CompatibleCircuits

variable {E K : Type*} (Q : Multigraph (Fin 4) E)

/-- All actual cut copies are counted in their unique unordered bundle. -/
theorem fourLabel_cut_bundle_sum (C : Finset E) (X : Finset (Fin 4)) :
    (Q.cutOn C X).card = ∑ i : Fin 6,
      if (((FourRegular.pairs i).toFinset ∩ X).card = 1)
      then (FourRegular.bundle Q C i).card else 0 := by
  have hlocal : ∀ (x y : Fin 4) (Y : Finset (Fin 4)), x ≠ y →
      (if (x ∈ Y) ≠ (y ∈ Y) then 1 else 0 : ℕ) =
        ∑ i : Fin 6, if ((FourRegular.pairs i).toFinset ∩ Y).card = 1 ∧
          s(x, y) = FourRegular.pairs i then 1 else 0 := by decide
  calc
    (Q.cutOn C X).card =
        ∑ e ∈ C, if (Q.firstEnd e ∈ X) ≠ (Q.secondEnd e ∈ X) then 1 else 0 := by
      simp only [cutOn, card_eq_sum_ones, sum_filter]
    _ = ∑ e ∈ C, ∑ i : Fin 6,
        if ((FourRegular.pairs i).toFinset ∩ X).card = 1 ∧
          Q.edge e = FourRegular.pairs i then 1 else 0 := by
      apply sum_congr rfl
      intro e _
      rw [← Q.edge_eq e]
      exact hlocal _ _ _ (Q.endpoints_distinct e)
    _ = ∑ i : Fin 6, ∑ e ∈ C,
        if ((FourRegular.pairs i).toFinset ∩ X).card = 1 ∧
          Q.edge e = FourRegular.pairs i then 1 else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro i _
      by_cases hi : ((FourRegular.pairs i).toFinset ∩ X).card = 1
      · simp only [hi, true_and, ite_true, FourRegular.bundle,
          card_eq_sum_ones, sum_filter]
      · simp only [hi, false_and, ite_false, sum_const_zero]

/-- Explicit local degree identities in the original bundle API. -/
theorem fourLabel_degree_bundle_counts (C : Finset E) :
    Q.degreeOn C 0 = (Q.edgeBundleOn C 0 1).card +
      (Q.edgeBundleOn C 0 2).card + (Q.edgeBundleOn C 0 3).card ∧
    Q.degreeOn C 1 = (Q.edgeBundleOn C 0 1).card +
      (Q.edgeBundleOn C 1 2).card + (Q.edgeBundleOn C 1 3).card ∧
    Q.degreeOn C 2 = (Q.edgeBundleOn C 0 2).card +
      (Q.edgeBundleOn C 1 2).card + (Q.edgeBundleOn C 2 3).card ∧
    Q.degreeOn C 3 = (Q.edgeBundleOn C 0 3).card +
      (Q.edgeBundleOn C 1 3).card + (Q.edgeBundleOn C 2 3).card := by
  have h0 := FourRegular.degree_bundle_sum Q C 0
  have h1 := FourRegular.degree_bundle_sum Q C 1
  have h2 := FourRegular.degree_bundle_sum Q C 2
  have h3 := FourRegular.degree_bundle_sum Q C 3
  norm_num [Fin.sum_univ_succ, FourRegular.pairs, FourRegular.bundle, edgeBundleOn,
    Sym2.mem_iff, Fin.ext_iff, Fin.succ] at h0 h1 h2 h3
  exact ⟨by simpa only [edgeBundleOn, add_assoc] using h0,
    by simpa only [edgeBundleOn, add_assoc] using h1,
    by simpa only [edgeBundleOn, add_assoc] using h2,
    by simpa only [edgeBundleOn, add_assoc] using h3⟩

/-- The three opposite-shore cut sizes, with no regularity assumption. -/
theorem fourLabel_two_shore_bundle_counts (C : Finset E) :
    (Q.cutOn C {0, 1}).card = (Q.edgeBundleOn C 0 2).card +
      (Q.edgeBundleOn C 0 3).card + (Q.edgeBundleOn C 1 2).card +
      (Q.edgeBundleOn C 1 3).card ∧
    (Q.cutOn C {0, 2}).card = (Q.edgeBundleOn C 0 1).card +
      (Q.edgeBundleOn C 0 3).card + (Q.edgeBundleOn C 1 2).card +
      (Q.edgeBundleOn C 2 3).card ∧
    (Q.cutOn C {0, 3}).card = (Q.edgeBundleOn C 0 1).card +
      (Q.edgeBundleOn C 0 2).card + (Q.edgeBundleOn C 1 3).card +
      (Q.edgeBundleOn C 2 3).card := by
  have h01 := Q.fourLabel_cut_bundle_sum C {0, 1}
  have h02 := Q.fourLabel_cut_bundle_sum C {0, 2}
  have h03 := Q.fourLabel_cut_bundle_sum C {0, 3}
  norm_num [Fin.sum_univ_succ, FourRegular.pairs, FourRegular.bundle,
    Sym2.toFinset_mk, Fin.succ, Fin.ext_iff] at h01 h02 h03
  exact ⟨by simpa only [edgeBundleOn, add_assoc] using h01,
    by simpa only [edgeBundleOn, add_assoc] using h02,
    by simpa only [edgeBundleOn, add_assoc] using h03⟩

end Overfull.Multigraph
