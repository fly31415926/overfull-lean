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
    (a b c d e f : ℕ) (ha : 0 < a) (_hb : 0 < b) (hc : 0 < c)
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
      apply sum_congr rfl
      intro e _
      split_ifs <;> rfl
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

theorem fourLabel_bundle_eq_named (C : Finset E) (i : Fin 6) (u v : Fin 4)
    (h : FourRegular.pairs i = s(u, v)) :
    FourRegular.bundle Q C i = Q.edgeBundleOn C u v := by
  ext e
  simp [FourRegular.bundle, edgeBundleOn, h]

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
  norm_num [Fin.sum_univ_succ, FourRegular.pairs,
    Sym2.mem_iff, Fin.ext_iff, Fin.succ] at h0 h1 h2 h3
  change Q.degreeOn C 0 = (FourRegular.bundle Q C 0).card +
    ((FourRegular.bundle Q C 1).card + (FourRegular.bundle Q C 2).card) at h0
  change Q.degreeOn C 1 = (FourRegular.bundle Q C 0).card +
    ((FourRegular.bundle Q C 3).card + (FourRegular.bundle Q C 4).card) at h1
  change Q.degreeOn C 2 = (FourRegular.bundle Q C 1).card +
    ((FourRegular.bundle Q C 3).card + (FourRegular.bundle Q C 5).card) at h2
  change Q.degreeOn C 3 = (FourRegular.bundle Q C 2).card +
    ((FourRegular.bundle Q C 4).card + (FourRegular.bundle Q C 5).card) at h3
  simp only [Q.fourLabel_bundle_eq_named C 0 0 1 rfl,
    Q.fourLabel_bundle_eq_named C 1 0 2 rfl,
    Q.fourLabel_bundle_eq_named C 2 0 3 rfl,
    Q.fourLabel_bundle_eq_named C 3 1 2 rfl,
    Q.fourLabel_bundle_eq_named C 4 1 3 rfl,
    Q.fourLabel_bundle_eq_named C 5 2 3 rfl] at h0 h1 h2 h3
  exact ⟨by omega, by omega, by omega, by omega⟩

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
  norm_num [Fin.sum_univ_succ, FourRegular.pairs, Fin.succ, Fin.ext_iff] at h01 h02 h03
  change (Q.cutOn C {0, 1}).card = (FourRegular.bundle Q C 1).card +
    ((FourRegular.bundle Q C 2).card + ((FourRegular.bundle Q C 3).card +
      (FourRegular.bundle Q C 4).card)) at h01
  change (Q.cutOn C {0, 2}).card = (FourRegular.bundle Q C 0).card +
    ((FourRegular.bundle Q C 2).card + ((FourRegular.bundle Q C 3).card +
      (FourRegular.bundle Q C 5).card)) at h02
  change (Q.cutOn C {0, 3}).card = (FourRegular.bundle Q C 0).card +
    ((FourRegular.bundle Q C 1).card + ((FourRegular.bundle Q C 4).card +
      (FourRegular.bundle Q C 5).card)) at h03
  simp only [Q.fourLabel_bundle_eq_named C 0 0 1 rfl,
    Q.fourLabel_bundle_eq_named C 1 0 2 rfl,
    Q.fourLabel_bundle_eq_named C 2 0 3 rfl,
    Q.fourLabel_bundle_eq_named C 3 1 2 rfl,
    Q.fourLabel_bundle_eq_named C 4 1 3 rfl,
    Q.fourLabel_bundle_eq_named C 5 2 3 rfl] at h01 h02 h03
  exact ⟨by omega, by omega, by omega⟩

/-- Every complete four-label support has an actual compatible pair or
triangle under the original admissibility and strict nonlocal cut bounds. -/
theorem exists_short_compatible_circuit_of_four_complete_support
    (classOf : Fin 4 → E → K) (C : Finset E)
    (hadmissible : Q.AdmissibleOn classOf C)
    (hstrict : Q.StrictNonlocalOn classOf C)
    (h01 : (Q.edgeBundleOn C 0 1).Nonempty)
    (h02 : (Q.edgeBundleOn C 0 2).Nonempty)
    (h03 : (Q.edgeBundleOn C 0 3).Nonempty)
    (h12 : (Q.edgeBundleOn C 1 2).Nonempty)
    (h13 : (Q.edgeBundleOn C 1 3).Nonempty)
    (h23 : (Q.edgeBundleOn C 2 3).Nonempty) :
    ∃ D : Finset E, D ⊆ C ∧ Q.IsCircuit D ∧ Q.Compatible classOf D ∧ D.card ≤ 3 := by
  by_contra hnone
  let a := (Q.edgeBundleOn C 0 1).card
  let b := (Q.edgeBundleOn C 0 2).card
  let c := (Q.edgeBundleOn C 0 3).card
  let d := (Q.edgeBundleOn C 1 2).card
  let e := (Q.edgeBundleOn C 1 3).card
  let f := (Q.edgeBundleOn C 2 3).card
  obtain ⟨hd0, hd1, hd2, hd3⟩ := Q.fourLabel_degree_bundle_counts C
  obtain ⟨hc01, hc02, hc03⟩ := Q.fourLabel_two_shore_bundle_counts C
  have hc12 : (Q.cutOn C {1, 2}).card = a + b + e + f := by
    have hcomp : Q.cutOn C {1, 2} = Q.cutOn C {0, 3} := by
      ext e
      have hmem (v : Fin 4) : v ∈ ({1, 2} : Finset (Fin 4)) ↔
          v ∉ ({0, 3} : Finset (Fin 4)) := by fin_cases v <;> decide
      simp only [mem_cutOn, hmem]
      tauto
    rw [hcomp]
    exact hc03
  have hc13 : (Q.cutOn C {1, 3}).card = a + c + d + f := by
    have hcomp : Q.cutOn C {1, 3} = Q.cutOn C {0, 2} := by
      ext e
      have hmem (v : Fin 4) : v ∈ ({1, 3} : Finset (Fin 4)) ↔
          v ∉ ({0, 2} : Finset (Fin 4)) := by fin_cases v <;> decide
      simp only [mem_cutOn, hmem]
      tauto
    rw [hcomp]
    exact hc02
  have hc23 : (Q.cutOn C {2, 3}).card = b + c + d + e := by
    have hcomp : Q.cutOn C {2, 3} = Q.cutOn C {0, 1} := by
      ext e
      have hmem (v : Fin 4) : v ∈ ({2, 3} : Finset (Fin 4)) ↔
          v ∉ ({0, 1} : Finset (Fin 4)) := by fin_cases v <;> decide
      simp only [mem_cutOn, hmem]
      tauto
    rw [hcomp]
    exact hc01
  have hcorner (v u w : Fin 4) (hvu : v ≠ u) (hvw : v ≠ w) (huw : u ≠ w)
      (h : CommonClassOn (Q.edgeBundleOn C v u) (Q.edgeBundleOn C v w) (classOf v)) :
      2 * ((Q.edgeBundleOn C v u).card + (Q.edgeBundleOn C v w).card) ≤
        Q.degreeOn C v ∧
      2 * ((Q.edgeBundleOn C v u).card + (Q.edgeBundleOn C v w).card) <
        (Q.cutOn C {u, w}).card := by
    refine ⟨Q.common_corner_local_bound classOf hadmissible hvw huw h, ?_⟩
    apply Q.common_corner_strict_cut_bound classOf hstrict hvw huw {u, w}
      (by simp [hvu, hvw]) (by simp) (by simp) ?_ h
    have hn : ∀ (v u w : Fin 4), v ≠ u → v ≠ w → u ≠ w → NonlocalShore v {u, w} := by
      unfold NonlocalShore
      decide
    exact hn v u w hvu hvw huw
  have h012 : (a + b ≤ c ∧ a + b < e + f) ∨
      (a + d ≤ e ∧ a + d < c + f) ∨
      (b + d ≤ f ∧ b + d < c + e) := by
    rcases Q.triangle_common_corner_of_no_short_circuit classOf C hnone
      (u := 0) (v := 1) (w := 2) (by decide) (by decide) (by decide)
      h01 h02 h12 with h | h | h
    · have hb := hcorner 0 1 2 (by decide) (by decide) (by decide)
        h
      simp only [hd0, hc12] at hb
      exact Or.inl ⟨by omega, by omega⟩
    · have hb := hcorner 1 0 2 (by decide) (by decide) (by decide)
        (by simpa only [Q.edgeBundleOn_swap C 1 0] using h)
      simp only [Q.edgeBundleOn_swap C 1 0, hd1, hc02] at hb
      exact Or.inr (Or.inl ⟨by omega, by omega⟩)
    · have hb := hcorner 2 0 1 (by decide) (by decide) (by decide)
        (by simpa only [Q.edgeBundleOn_swap C 2 0, Q.edgeBundleOn_swap C 2 1] using h)
      simp only [Q.edgeBundleOn_swap C 2 0, Q.edgeBundleOn_swap C 2 1, hd2, hc01] at hb
      exact Or.inr (Or.inr ⟨by omega, by omega⟩)
  have h013 : (a + c ≤ b ∧ a + c < d + f) ∨
      (a + e ≤ d ∧ a + e < b + f) ∨
      (c + e ≤ f ∧ c + e < b + d) := by
    rcases Q.triangle_common_corner_of_no_short_circuit classOf C hnone
      (u := 0) (v := 1) (w := 3) (by decide) (by decide) (by decide)
      h01 h03 h13 with h | h | h
    · have hb := hcorner 0 1 3 (by decide) (by decide) (by decide)
        h
      simp only [hd0, hc13] at hb
      exact Or.inl ⟨by omega, by omega⟩
    · have hb := hcorner 1 0 3 (by decide) (by decide) (by decide)
        (by simpa only [Q.edgeBundleOn_swap C 1 0] using h)
      simp only [Q.edgeBundleOn_swap C 1 0, hd1, hc03] at hb
      exact Or.inr (Or.inl ⟨by omega, by omega⟩)
    · have hb := hcorner 3 0 1 (by decide) (by decide) (by decide)
        (by simpa only [Q.edgeBundleOn_swap C 3 0, Q.edgeBundleOn_swap C 3 1] using h)
      simp only [Q.edgeBundleOn_swap C 3 0, Q.edgeBundleOn_swap C 3 1, hd3, hc01] at hb
      exact Or.inr (Or.inr ⟨by omega, by omega⟩)
  have h023 : (b + c ≤ a ∧ b + c < d + e) ∨
      (b + f ≤ d ∧ b + f < a + e) ∨
      (c + f ≤ e ∧ c + f < a + d) := by
    rcases Q.triangle_common_corner_of_no_short_circuit classOf C hnone
      (u := 0) (v := 2) (w := 3) (by decide) (by decide) (by decide)
      h02 h03 h23 with h | h | h
    · have hb := hcorner 0 2 3 (by decide) (by decide) (by decide)
        h
      simp only [hd0, hc23] at hb
      exact Or.inl ⟨by omega, by omega⟩
    · have hb := hcorner 2 0 3 (by decide) (by decide) (by decide)
        (by simpa only [Q.edgeBundleOn_swap C 2 0] using h)
      simp only [Q.edgeBundleOn_swap C 2 0, hd2, hc03] at hb
      exact Or.inr (Or.inl ⟨by omega, by omega⟩)
    · have hb := hcorner 3 0 2 (by decide) (by decide) (by decide)
        (by simpa only [Q.edgeBundleOn_swap C 3 0, Q.edgeBundleOn_swap C 3 2] using h)
      simp only [Q.edgeBundleOn_swap C 3 0, Q.edgeBundleOn_swap C 3 2, hd3, hc02] at hb
      exact Or.inr (Or.inr ⟨by omega, by omega⟩)
  have h123 : (d + e ≤ a ∧ d + e < b + c) ∨
      (d + f ≤ b ∧ d + f < a + c) ∨
      (e + f ≤ c ∧ e + f < a + b) := by
    rcases Q.triangle_common_corner_of_no_short_circuit classOf C hnone
      (u := 1) (v := 2) (w := 3) (by decide) (by decide) (by decide)
      h12 h13 h23 with h | h | h
    · have hb := hcorner 1 2 3 (by decide) (by decide) (by decide)
        h
      simp only [hd1, hc23] at hb
      exact Or.inl ⟨by omega, by omega⟩
    · have hb := hcorner 2 1 3 (by decide) (by decide) (by decide)
        (by simpa only [Q.edgeBundleOn_swap C 2 1] using h)
      simp only [Q.edgeBundleOn_swap C 2 1, hd2, hc13] at hb
      exact Or.inr (Or.inl ⟨by omega, by omega⟩)
    · have hb := hcorner 3 1 2 (by decide) (by decide) (by decide)
        (by simpa only [Q.edgeBundleOn_swap C 3 1, Q.edgeBundleOn_swap C 3 2] using h)
      simp only [Q.edgeBundleOn_swap C 3 1, Q.edgeBundleOn_swap C 3 2, hd3, hc12] at hb
      exact Or.inr (Or.inr ⟨by omega, by omega⟩)
  exact four_positive_triangle_corner_bounds_false a b c d e f
    (card_pos.mpr h01) (card_pos.mpr h02) (card_pos.mpr h03)
    (card_pos.mpr h12) (card_pos.mpr h13) (card_pos.mpr h23)
    h012 h013 h023 h123

end Overfull.Multigraph
