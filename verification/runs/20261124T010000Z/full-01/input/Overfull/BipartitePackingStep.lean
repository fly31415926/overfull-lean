import Overfull.MatchingExtension
import Overfull.BipartitePackingDeficiency

/-!
# A large matching covering the saturated vertices

This is the matching component of Step 2 of adaptive packing. The ambient
order bound may exceed the current side sizes after a balanced vertex deletion.
-/

namespace Overfull.BipartitePackingStep

open Finset Classical SimpleGraph
open scoped BigOperators

/-- Rescale the degree-deficiency estimate using the manuscript's ambient
side-size parameter. -/
theorem deficiency_scale (h m : ℕ) (d ε γ c₀ t : ℝ)
    (hm : 0 < m) (hd : 0 < d) (hγ : 0 < γ)
    (hdlower : γ * m / 2 ≤ d) (ht : t ≤ c₀ * ε * (m : ℝ) ^ 2)
    (hbound : (h : ℝ) ≤ (8 * ε * (m : ℝ) ^ 2 + t) / d) :
    (h : ℝ) ≤ (16 + 2 * c₀) * ε * m / γ := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmul := (le_div_iff₀ hd).mp hbound
  have hlower := mul_le_mul_of_nonneg_right hdlower (Nat.cast_nonneg h)
  apply (le_div_iff₀ hγ).mpr
  apply (mul_le_mul_iff_left₀ hmR).mp
  nlinarith

/-- The total nonnegative load controls the size of the actual set of
vertices that have reached a positive capacity. -/
theorem saturated_set_bound {V : Type*} [Fintype V]
    (u : V → ℝ) (r t : ℝ) (hu : ∀ v, 0 ≤ u v)
    (hload : ∑ v, u v ≤ t) :
    r * ((univ.filter (fun v => r ≤ u v)).card : ℝ) ≤ t := by
  calc
    _ = ∑ _v ∈ univ.filter (fun v => r ≤ u v), r := by simp; ring
    _ ≤ ∑ v ∈ univ.filter (fun v => r ≤ u v), u v :=
      Finset.sum_le_sum (fun v hv => (Finset.mem_filter.mp hv).2)
    _ ≤ ∑ v : V, u v := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _) (fun v _ _ => hu v)
    _ ≤ t := hload

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
variable (G : SimpleGraph (A ⊕ B)) [DecidableRel G.Adj]

/-- From actual degree and load data, construct a maximum matching that
covers the prescribed vertices and satisfies the Hall-deficiency estimate. -/
theorem exists_maximum_matching_with_deficiency
    (hbip : G.IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr))
    (Z : Finset (A ⊕ B)) (m : ℕ) (d a t : ℝ) (u : A ⊕ B → ℝ)
    (hd : 0 < d) (ha : 0 ≤ a) (hu : ∀ v, 0 ≤ u v)
    (hA : Fintype.card A ≤ m) (hB : Fintype.card B ≤ m)
    (hlower : ∀ v, d - a ≤ (G.degree v : ℝ))
    (hupper : ∀ v, (G.degree v : ℝ) ≤ d + a + u v)
    (hload : ∑ v, u v ≤ t) (hsmall : (2 : ℝ) * Z.card < d - a) :
    ∃ M : G.Subgraph, M.IsMatching ∧ (↑Z : Set (A ⊕ B)) ⊆ M.verts ∧
      (∀ N : G.Subgraph, N.IsMatching →
        N.spanningCoe.edgeFinset.card ≤ M.spanningCoe.edgeFinset.card) ∧
      ((uncoveredLeft M).card : ℝ) ≤ (2 * a * m + t) / d := by
  have hdegreeZ : ∀ v ∈ Z, 2 * Z.card < G.degree v := by
    intro v _
    have h := hsmall.trans_le (hlower v)
    exact_mod_cast h
  obtain ⟨M, hM, hcover, hmax⟩ :=
    MatchingExtension.exists_maximum_covering_small_set G Z hdegreeZ
  exact ⟨M, hM, hcover, hmax,
    BipartitePackingDeficiency.maximum_matching_deficiency G hbip M hM hmax
      m d a t u hd ha hu hA hB hlower hupper hload⟩

/-- A positive capacity and the total load bound supply the required
small saturated set; no matching or Hall witness is assumed. -/
theorem exists_matching_covering_saturated_load
    (hbip : G.IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr))
    (m : ℕ) (d a r t : ℝ) (u : A ⊕ B → ℝ)
    (hd : 0 < d) (ha : 0 ≤ a) (hr : 0 < r) (hu : ∀ v, 0 ≤ u v)
    (hA : Fintype.card A ≤ m) (hB : Fintype.card B ≤ m)
    (hlower : ∀ v, d - a ≤ (G.degree v : ℝ))
    (hupper : ∀ v, (G.degree v : ℝ) ≤ d + a + u v)
    (hload : ∑ v, u v ≤ t) (hbudget : 2 * t < r * (d - a)) :
    ∃ M : G.Subgraph, M.IsMatching ∧ (∀ v, r ≤ u v → v ∈ M.verts) ∧
      (∀ N : G.Subgraph, N.IsMatching →
        N.spanningCoe.edgeFinset.card ≤ M.spanningCoe.edgeFinset.card) ∧
      ((uncoveredLeft M).card : ℝ) ≤ (2 * a * m + t) / d := by
  let Z : Finset (A ⊕ B) := univ.filter (fun v => r ≤ u v)
  have hsize : r * (Z.card : ℝ) ≤ t := saturated_set_bound u r t hu hload
  have hsmall : (2 : ℝ) * Z.card < d - a := by nlinarith
  obtain ⟨M, hM, hcover, hmax, hdef⟩ := exists_maximum_matching_with_deficiency G hbip
    Z m d a t u hd ha hu hA hB hlower hupper hload hsmall
  refine ⟨M, hM, ?_, hmax, hdef⟩
  intro v hv
  exact hcover (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩)

/-- The numerical Step 2 bound in the manuscript. The current balanced
side sizes may be smaller than the ambient `m` used in the degree errors. -/
theorem exists_packing_matching
    (hbip : G.IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr))
    (hbalance : Fintype.card A = Fintype.card B)
    (Z : Finset (A ⊕ B)) (m : ℕ) (d ε γ c₀ : ℝ) (u : A ⊕ B → ℝ)
    (hm : 0 < m) (hε : 0 ≤ ε) (hγ : 0 < γ) (hu : ∀ v, 0 ≤ u v)
    (hA : Fintype.card A ≤ m) (hB : Fintype.card B ≤ m)
    (hdlower : γ * m / 2 ≤ d)
    (hlower : ∀ v, d - 4 * ε * m ≤ (G.degree v : ℝ))
    (hupper : ∀ v, (G.degree v : ℝ) ≤ d + 4 * ε * m + u v)
    (hload : ∑ v, u v ≤ c₀ * ε * (m : ℝ) ^ 2)
    (hsmall : (2 : ℝ) * Z.card < d - 4 * ε * m) :
    ∃ M : G.Subgraph, M.IsMatching ∧ (↑Z : Set (A ⊕ B)) ⊆ M.verts ∧
      (∀ N : G.Subgraph, N.IsMatching →
        N.spanningCoe.edgeFinset.card ≤ M.spanningCoe.edgeFinset.card) ∧
      (uncoveredLeft M).card =
        (univ.filter (fun b : B => (.inr b : A ⊕ B) ∉ M.verts)).card ∧
      ((uncoveredLeft M).card : ℝ) ≤ (16 + 2 * c₀) * ε * m / γ := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hd : 0 < d := (by positivity : 0 < γ * (m : ℝ) / 2).trans_le hdlower
  have ha : 0 ≤ 4 * ε * (m : ℝ) := by positivity
  obtain ⟨M, hM, hcover, hmax, hdef⟩ := exists_maximum_matching_with_deficiency G hbip
    Z m d (4 * ε * m) (c₀ * ε * (m : ℝ) ^ 2) u hd ha hu hA hB hlower hupper hload hsmall
  have hdef' : ((uncoveredLeft M).card : ℝ) ≤
      (8 * ε * (m : ℝ) ^ 2 + c₀ * ε * (m : ℝ) ^ 2) / d := by
    convert hdef using 1
    congr 1
    ring
  refine ⟨M, hM, hcover, hmax,
    BipartitePackingDeficiency.matching_uncovered_sides_eq G hbip hbalance M hM, ?_⟩
  exact deficiency_scale (uncoveredLeft M).card m d ε γ c₀
    (c₀ * ε * (m : ℝ) ^ 2) hm hd hγ hdlower le_rfl hdef'

end Overfull.BipartitePackingStep
