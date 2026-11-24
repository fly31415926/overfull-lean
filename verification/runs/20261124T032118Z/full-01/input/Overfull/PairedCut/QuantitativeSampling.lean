import Overfull.PairedCut.Uniform

/-!
# Quantitative degree balance for prescribed pair orientations

The neighborhood tolerance may be chosen independently of the fixed
regularity-cluster tolerance. One orientation simultaneously satisfies
both requirements and retains the existing crossing minimum-degree bound.
-/

namespace Overfull.PairedCut

open Finset Classical
open scoped BigOperators

variable {I : Type*} [Fintype I]

/-- A neighborhood deviation bound with an arbitrary relative tolerance. -/
theorem degree_failure_probability_quantitative
    (G : SimpleGraph (I × Bool)) [DecidableRel G.Adj]
    (α κ c : ℝ) (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1 / 2)
    (hc : c ≤ 2 * κ ^ 2 * α / 3)
    (hdegree : ∀ v, α * Fintype.card (I × Bool) ≤ (G.degree v : ℝ)) :
    Bernoulli.probability (1 / 2) (fun ω => ∃ v,
      κ * (G.neighborFinset v).card ≤
        |(splitCount (G.neighborFinset v) ω : ℝ) - (G.neighborFinset v).card / 2|) ≤
      2 * Fintype.card (I × Bool) * Real.exp (-c * Fintype.card (I × Bool)) := by
  let P := fun (v : I × Bool) (ω : I → Bool) =>
    κ * (G.neighborFinset v).card ≤
      |(splitCount (G.neighborFinset v) ω : ℝ) - (G.neighborFinset v).card / 2|
  have hsingle (v : I × Bool) : Bernoulli.probability (1 / 2) (P v) ≤
      2 * Real.exp (-c * Fintype.card (I × Bool)) := by
    have h := splitCount_concentration (G.neighborFinset v) κ
      (G.neighborFinset v).card hκ hκ1 le_rfl
    apply h.trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
    apply Real.exp_le_exp.mpr
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    have hn := mul_le_mul_of_nonneg_right hc
      (Nat.cast_nonneg (Fintype.card (I × Bool)))
    have hd := mul_le_mul_of_nonneg_left (hdegree v) (sq_nonneg κ)
    nlinarith
  calc
    _ ≤ ∑ v : I × Bool, Bernoulli.probability (1 / 2) (P v) := by
      simpa only [Finset.mem_univ, true_and] using
        Bernoulli.probability_exists_le_sum (1 / 2) (by norm_num) (by norm_num) univ P
    _ ≤ ∑ _v : I × Bool, 2 * Real.exp (-c * Fintype.card (I × Bool)) :=
      Finset.sum_le_sum (fun v _ => hsingle v)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- The same outcome controls relative neighborhood errors and all fixed
cluster errors. A tolerance at most one sixth retains the degree bound. -/
theorem exists_orientation_quantitative_of_error_bound {J : Type*} [Fintype J]
    (G : SimpleGraph (I × Bool)) [DecidableRel G.Adj] (C : J → Finset (I × Bool))
    (α κ ε β c : ℝ) (hκ : 0 ≤ κ) (hκ6 : κ ≤ 1 / 6)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1 / 2)
    (hcα : c ≤ 2 * κ ^ 2 * α / 3) (hcε : c ≤ 2 * ε ^ 2 * β / 3)
    (hdegree : ∀ v, α * Fintype.card (I × Bool) ≤ (G.degree v : ℝ))
    (hsize : ∀ j, β * Fintype.card (I × Bool) ≤ ((C j).card : ℝ))
    (herror : 2 * ((Fintype.card (I × Bool) : ℝ) + Fintype.card J) *
      Real.exp (-c * Fintype.card (I × Bool)) < 1) :
    ∃ ω : I → Bool,
      (∀ v, α * Fintype.card (I × Bool) / 3 ≤ ((cutGraph G ω).degree v : ℝ)) ∧
      (∀ v,
        |((G.neighborFinset v ∩ leftVertices ω).card : ℝ) - G.degree v / 2| <
          κ * G.degree v ∧
        |((G.neighborFinset v ∩ rightVertices ω).card : ℝ) - G.degree v / 2| <
          κ * G.degree v) ∧
      ∀ j,
        |(((C j) ∩ leftVertices ω).card : ℝ) - (C j).card / 2| < ε * (C j).card ∧
        |(((C j) ∩ rightVertices ω).card : ℝ) - (C j).card / 2| < ε * (C j).card := by
  let P := fun (ω : I → Bool) => ∃ v,
    κ * (G.neighborFinset v).card ≤
      |(splitCount (G.neighborFinset v) ω : ℝ) - (G.neighborFinset v).card / 2|
  let Q := fun (ω : I → Bool) => ∃ j,
    ε * (C j).card ≤ |(splitCount (C j) ω : ℝ) - (C j).card / 2|
  have hbad : Bernoulli.probability (1 / 2) (fun ω => P ω ∨ Q ω) < 1 := by
    have hu := Bernoulli.probability_union_le (1 / 2) (by norm_num) (by norm_num) P Q
    have hp := degree_failure_probability_quantitative G α κ c hκ (by linarith) hcα hdegree
    have hq := cluster_failure_probability C ε β c hε hε1 hcε hsize
    change Bernoulli.probability (1 / 2) P ≤ _ at hp
    change Bernoulli.probability (1 / 2) Q ≤ _ at hq
    nlinarith
  obtain ⟨ω, hω⟩ := Bernoulli.exists_not_of_probability_lt_one (1 / 2)
    (fun ω => P ω ∨ Q ω) hbad
  have hdev (v : I × Bool) :
      |((G.neighborFinset v ∩ leftVertices ω).card : ℝ) - G.degree v / 2| <
        κ * G.degree v := by
    have h : |(splitCount (G.neighborFinset v) ω : ℝ) -
        (G.neighborFinset v).card / 2| < κ * (G.neighborFinset v).card :=
      lt_of_not_ge (fun h => hω (Or.inl ⟨v, h⟩))
    simpa only [splitCount_eq_inter, SimpleGraph.card_neighborFinset_eq_degree] using h
  have hsum (v : I × Bool) :
      ((G.neighborFinset v ∩ leftVertices ω).card : ℝ) +
        (G.neighborFinset v ∩ rightVertices ω).card = G.degree v := by
    exact_mod_cast (side_count_sum (G.neighborFinset v) ω).trans
      (G.card_neighborFinset_eq_degree v)
  have hneighbor (v : I × Bool) :
      α * Fintype.card (I × Bool) / 3 ≤
        ((G.neighborFinset v ∩ leftVertices ω).card : ℝ) ∧
      α * Fintype.card (I × Bool) / 3 ≤
        ((G.neighborFinset v ∩ rightVertices ω).card : ℝ) := by
    obtain ⟨hl, hu⟩ := abs_lt.mp (hdev v)
    have hκd := mul_le_mul_of_nonneg_right hκ6 (Nat.cast_nonneg (G.degree v))
    have hd := hdegree v
    have hs := hsum v
    constructor <;> linarith
  refine ⟨ω, ?_, ?_, ?_⟩
  · intro v
    rw [cutGraph_degree]
    split_ifs
    · exact (hneighbor v).2
    · exact (hneighbor v).1
  · intro v
    refine ⟨hdev v, ?_⟩
    have heq : ((G.neighborFinset v ∩ rightVertices ω).card : ℝ) - G.degree v / 2 =
        -(((G.neighborFinset v ∩ leftVertices ω).card : ℝ) - G.degree v / 2) := by
      linarith [hsum v]
    rw [heq, abs_neg]
    exact hdev v
  · intro j
    have h : |(splitCount (C j) ω : ℝ) - (C j).card / 2| < ε * (C j).card :=
      lt_of_not_ge (fun h => hω (Or.inr ⟨j, h⟩))
    rw [splitCount_eq_inter] at h
    refine ⟨h, ?_⟩
    have hs : (((C j) ∩ leftVertices ω).card : ℝ) +
        ((C j) ∩ rightVertices ω).card = (C j).card := by
      exact_mod_cast side_count_sum (C j) ω
    have heq : (((C j) ∩ rightVertices ω).card : ℝ) - (C j).card / 2 =
        -((((C j) ∩ leftVertices ω).card : ℝ) - (C j).card / 2) := by linarith
    rw [heq, abs_neg]
    exact h

/-- The order threshold is uniform over the graph, prescribed pairing,
and fixed clusters. Only the neighborhood error is measured against the
whole vertex count; the cluster tolerance remains independent. -/
theorem exists_orientation_quantitative (α δ ε β : ℝ) (K : ℕ)
    (hα : 0 < α) (hδ : 0 < δ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) (hβ : 0 < β) :
    ∃ n₀ : ℕ, ∀ (I J : Type*) [Fintype I] [Fintype J]
      (G : SimpleGraph (I × Bool)) [DecidableRel G.Adj] (C : J → Finset (I × Bool)),
      Fintype.card J ≤ K → n₀ ≤ Fintype.card (I × Bool) →
      (∀ v, α * Fintype.card (I × Bool) ≤ (G.degree v : ℝ)) →
      (∀ j, β * Fintype.card (I × Bool) ≤ ((C j).card : ℝ)) →
      ∃ ω : I → Bool,
        (∀ v, α * Fintype.card (I × Bool) / 3 ≤ ((cutGraph G ω).degree v : ℝ)) ∧
        (∀ v,
          |((G.neighborFinset v ∩ leftVertices ω).card : ℝ) - G.degree v / 2| ≤
            δ * Fintype.card (I × Bool) ∧
          |((G.neighborFinset v ∩ rightVertices ω).card : ℝ) - G.degree v / 2| ≤
            δ * Fintype.card (I × Bool)) ∧
        ∀ j,
          |(((C j) ∩ leftVertices ω).card : ℝ) - (C j).card / 2| < ε * (C j).card ∧
          |(((C j) ∩ rightVertices ω).card : ℝ) - (C j).card / 2| < ε * (C j).card := by
  let κ := min δ (1 / 6)
  have hκ : 0 < κ := lt_min hδ (by norm_num)
  let c := min (2 * κ ^ 2 * α / 3) (2 * ε ^ 2 * β / 3)
  have hc : 0 < c := lt_min (by positivity) (by positivity)
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (max (1 : ℝ) (16 * ((K : ℝ) + 1) / c ^ 2))
  refine ⟨n₀, ?_⟩
  intro I J _ _ G _ C hK hn hdegree hsize
  have hnR : max (1 : ℝ) (16 * ((K : ℝ) + 1) / c ^ 2) < Fintype.card (I × Bool) :=
    hn₀.trans_le (by exact_mod_cast hn)
  have hn1 : 1 ≤ Fintype.card (I × Bool) := by
    have h := (le_max_left (1 : ℝ) (16 * ((K : ℝ) + 1) / c ^ 2)).trans_lt hnR
    exact_mod_cast h.le
  have hlarge : 16 * ((K : ℝ) + 1) ≤ c ^ 2 * Fintype.card (I × Bool) := by
    have h := (le_max_right (1 : ℝ) (16 * ((K : ℝ) + 1) / c ^ 2)).trans_lt hnR
    have h' := (div_lt_iff₀ (sq_pos_of_pos hc)).mp h
    nlinarith
  have herr := orientation_error_lt_one c hc K (Fintype.card (I × Bool)) hn1 hlarge
  have herror : 2 * ((Fintype.card (I × Bool) : ℝ) + Fintype.card J) *
      Real.exp (-c * Fintype.card (I × Bool)) < 1 := by
    have hKR : (Fintype.card J : ℝ) ≤ K := by exact_mod_cast hK
    have hmono := mul_le_mul_of_nonneg_right
      (show 2 * ((Fintype.card (I × Bool) : ℝ) + Fintype.card J) ≤
        2 * ((Fintype.card (I × Bool) : ℝ) + K) by linarith)
      (Real.exp_pos (-c * Fintype.card (I × Bool))).le
    exact hmono.trans_lt herr
  obtain ⟨ω, hcut, hdev, hcluster⟩ := exists_orientation_quantitative_of_error_bound
    G C α κ ε β c hκ.le (min_le_right _ _) hε.le hε1
    (min_le_left _ _) (min_le_right _ _) hdegree hsize herror
  refine ⟨ω, hcut, ?_, hcluster⟩
  intro v
  have hd : (G.degree v : ℝ) ≤ Fintype.card (I × Bool) := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    exact_mod_cast (Finset.card_le_univ (G.neighborFinset v))
  have hbound : κ * G.degree v ≤ δ * Fintype.card (I × Bool) :=
    mul_le_mul (min_le_left _ _) hd (Nat.cast_nonneg _) hδ.le
  exact ⟨(hdev v).1.le.trans hbound, (hdev v).2.le.trans hbound⟩

end Overfull.PairedCut
