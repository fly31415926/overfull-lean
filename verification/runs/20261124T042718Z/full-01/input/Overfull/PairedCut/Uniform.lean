import Overfull.PairedCut.Sampling

/-!
# Simultaneous degree and cluster control for a prescribed pairing

The order threshold is chosen before the graph, pairing and cluster sets.
One actual pair orientation gives the crossing minimum degree and balances
each of the fixed clusters. Robust expansion is a separate deterministic
step and is not asserted here.
-/

namespace Overfull.PairedCut

open Finset Classical
open scoped BigOperators

variable {I : Type*} [Fintype I]

theorem degree_failure_probability (G : SimpleGraph (I × Bool)) [DecidableRel G.Adj]
    (α c : ℝ) (hc : c ≤ α / 54)
    (hdegree : ∀ v, α * Fintype.card (I × Bool) ≤ (G.degree v : ℝ)) :
    Bernoulli.probability (1 / 2) (fun ω => ∃ v,
      (1 / 6 : ℝ) * (G.neighborFinset v).card ≤
        |(splitCount (G.neighborFinset v) ω : ℝ) - (G.neighborFinset v).card / 2|) ≤
      2 * Fintype.card (I × Bool) * Real.exp (-c * Fintype.card (I × Bool)) := by
  let P := fun (v : I × Bool) (ω : I → Bool) =>
    (1 / 6 : ℝ) * (G.neighborFinset v).card ≤
      |(splitCount (G.neighborFinset v) ω : ℝ) - (G.neighborFinset v).card / 2|
  have hsingle (v : I × Bool) : Bernoulli.probability (1 / 2) (P v) ≤
      2 * Real.exp (-c * Fintype.card (I × Bool)) := by
    have h := splitCount_concentration (G.neighborFinset v) (1 / 6)
      (G.neighborFinset v).card (by norm_num) (by norm_num) le_rfl
    apply h.trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
    apply Real.exp_le_exp.mpr
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    have hn := mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg (Fintype.card (I × Bool)))
    have hd := hdegree v
    nlinarith
  calc
    _ ≤ ∑ v : I × Bool, Bernoulli.probability (1 / 2) (P v) := by
      simpa only [Finset.mem_univ,true_and] using
        Bernoulli.probability_exists_le_sum (1 / 2) (by norm_num) (by norm_num) univ P
    _ ≤ ∑ _v : I × Bool, 2 * Real.exp (-c * Fintype.card (I × Bool)) :=
      Finset.sum_le_sum (fun v _ => hsingle v)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

theorem cluster_failure_probability {J : Type*} [Fintype J]
    (C : J → Finset (I × Bool)) (ε β c : ℝ)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) (hc : c ≤ 2 * ε ^ 2 * β / 3)
    (hsize : ∀ j, β * Fintype.card (I × Bool) ≤ ((C j).card : ℝ)) :
    Bernoulli.probability (1 / 2) (fun ω => ∃ j,
      ε * (C j).card ≤ |(splitCount (C j) ω : ℝ) - (C j).card / 2|) ≤
      2 * Fintype.card J * Real.exp (-c * Fintype.card (I × Bool)) := by
  let P := fun (j : J) (ω : I → Bool) =>
    ε * (C j).card ≤ |(splitCount (C j) ω : ℝ) - (C j).card / 2|
  have hsingle (j : J) : Bernoulli.probability (1 / 2) (P j) ≤
      2 * Real.exp (-c * Fintype.card (I × Bool)) := by
    have h := splitCount_concentration (C j) ε (C j).card hε hε1 le_rfl
    apply h.trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
    apply Real.exp_le_exp.mpr
    have hn := mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg (Fintype.card (I × Bool)))
    have hs := mul_le_mul_of_nonneg_left (hsize j) (sq_nonneg ε)
    nlinarith
  calc
    _ ≤ ∑ j : J, Bernoulli.probability (1 / 2) (P j) := by
      simpa only [Finset.mem_univ,true_and] using
        Bernoulli.probability_exists_le_sum (1 / 2) (by norm_num) (by norm_num) univ P
    _ ≤ ∑ _j : J, 2 * Real.exp (-c * Fintype.card (I × Bool)) :=
      Finset.sum_le_sum (fun j _ => hsingle j)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

theorem exists_orientation_of_error_bound {J : Type*} [Fintype J]
    (G : SimpleGraph (I × Bool)) [DecidableRel G.Adj] (C : J → Finset (I × Bool))
    (α ε β c : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1 / 2)
    (hcα : c ≤ α / 54) (hcε : c ≤ 2 * ε ^ 2 * β / 3)
    (hdegree : ∀ v, α * Fintype.card (I × Bool) ≤ (G.degree v : ℝ))
    (hsize : ∀ j, β * Fintype.card (I × Bool) ≤ ((C j).card : ℝ))
    (herror : 2 * ((Fintype.card (I × Bool) : ℝ) + Fintype.card J) *
      Real.exp (-c * Fintype.card (I × Bool)) < 1) :
    ∃ ω : I → Bool,
      (∀ v, α * Fintype.card (I × Bool) / 3 ≤ ((cutGraph G ω).degree v : ℝ)) ∧
      ∀ j,
        |(((C j) ∩ leftVertices ω).card : ℝ) - (C j).card / 2| < ε * (C j).card ∧
        |(((C j) ∩ rightVertices ω).card : ℝ) - (C j).card / 2| < ε * (C j).card := by
  let P := fun (ω : I → Bool) => ∃ v,
    (1 / 6 : ℝ) * (G.neighborFinset v).card ≤
      |(splitCount (G.neighborFinset v) ω : ℝ) - (G.neighborFinset v).card / 2|
  let Q := fun (ω : I → Bool) => ∃ j,
    ε * (C j).card ≤ |(splitCount (C j) ω : ℝ) - (C j).card / 2|
  have hbad : Bernoulli.probability (1 / 2) (fun ω => P ω ∨ Q ω) < 1 := by
    have hu := Bernoulli.probability_union_le (1 / 2) (by norm_num) (by norm_num) P Q
    have hp := degree_failure_probability G α c hcα hdegree
    have hq := cluster_failure_probability C ε β c hε hε1 hcε hsize
    change Bernoulli.probability (1 / 2) P ≤ _ at hp
    change Bernoulli.probability (1 / 2) Q ≤ _ at hq
    nlinarith
  obtain ⟨ω,hω⟩ := Bernoulli.exists_not_of_probability_lt_one (1 / 2)
    (fun ω => P ω ∨ Q ω) hbad
  have hneighbor (v : I × Bool) :
      α * Fintype.card (I × Bool) / 3 ≤
        ((G.neighborFinset v ∩ leftVertices ω).card : ℝ) ∧
      α * Fintype.card (I × Bool) / 3 ≤
        ((G.neighborFinset v ∩ rightVertices ω).card : ℝ) := by
    have hdev : |(splitCount (G.neighborFinset v) ω : ℝ) -
        (G.neighborFinset v).card / 2| < (1 / 6 : ℝ) * (G.neighborFinset v).card :=
      lt_of_not_ge (fun h => hω (Or.inl ⟨v,h⟩))
    rw [splitCount_eq_inter] at hdev
    obtain ⟨hl,hu⟩ := abs_lt.mp hdev
    have hsum : ((G.neighborFinset v ∩ leftVertices ω).card : ℝ) +
        (G.neighborFinset v ∩ rightVertices ω).card = (G.neighborFinset v).card := by
      exact_mod_cast side_count_sum (G.neighborFinset v) ω
    have hd : α * Fintype.card (I × Bool) ≤ ((G.neighborFinset v).card : ℝ) := by
      simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hdegree v
    constructor <;> linarith
  refine ⟨ω,?_,?_⟩
  · intro v
    rw [cutGraph_degree]
    split_ifs
    · exact (hneighbor v).2
    · exact (hneighbor v).1
  · intro j
    have hdev : |(splitCount (C j) ω : ℝ) - (C j).card / 2| < ε * (C j).card :=
      lt_of_not_ge (fun h => hω (Or.inr ⟨j,h⟩))
    rw [splitCount_eq_inter] at hdev
    refine ⟨hdev,?_⟩
    have hsum : (((C j) ∩ leftVertices ω).card : ℝ) +
        ((C j) ∩ rightVertices ω).card = (C j).card := by
      exact_mod_cast side_count_sum (C j) ω
    have heq : (((C j) ∩ rightVertices ω).card : ℝ) - (C j).card / 2 =
        -((((C j) ∩ leftVertices ω).card : ℝ) - (C j).card / 2) := by linarith
    rw [heq,abs_neg]
    exact hdev

/-- A uniform elementary bound for the total sampling error. -/
theorem orientation_error_lt_one (c : ℝ) (hc : 0 < c) (K n : ℕ)
    (hn : 1 ≤ n) (hlarge : 16 * ((K : ℝ) + 1) ≤ c ^ 2 * n) :
    2 * ((n : ℝ) + K) * Real.exp (-c * n) < 1 := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hhalf : c * (n : ℝ) / 2 ≤ Real.exp (c * n / 2) := by
    linarith [Real.add_one_le_exp (c * (n : ℝ) / 2)]
  have hsq := pow_le_pow_left₀ (show 0 ≤ c * (n : ℝ) / 2 by positivity) hhalf 2
  have heq : Real.exp (c * (n : ℝ) / 2) ^ 2 = Real.exp (c * n) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [heq] at hsq
  have hlarge' := mul_le_mul_of_nonneg_right hlarge hn0
  have hlow : 4 * ((K : ℝ) + 1) * n ≤ Real.exp (c * n) := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hlow (Real.exp_pos (-c * n)).le
  have hcancel : Real.exp (c * (n : ℝ)) * Real.exp (-c * n) = 1 := by
    rw [← Real.exp_add,show c * (n : ℝ) + -c * n = 0 by ring,Real.exp_zero]
  rw [hcancel] at hmul
  have hcoeff : (n : ℝ) + K ≤ ((K : ℝ) + 1) * n := by
    nlinarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)]
  have hcoeff' := mul_le_mul_of_nonneg_right hcoeff (Real.exp_pos (-c * n)).le
  nlinarith

/-- One pair orientation controls every crossing degree and all fixed
clusters simultaneously. The threshold precedes all finite types and sets. -/
theorem exists_orientation (α ε β : ℝ) (K : ℕ)
    (hα : 0 < α) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) (hβ : 0 < β) :
    ∃ n₀ : ℕ, ∀ (I J : Type*) [Fintype I] [Fintype J]
      (G : SimpleGraph (I × Bool)) [DecidableRel G.Adj] (C : J → Finset (I × Bool)),
      Fintype.card J ≤ K → n₀ ≤ Fintype.card (I × Bool) →
      (∀ v, α * Fintype.card (I × Bool) ≤ (G.degree v : ℝ)) →
      (∀ j, β * Fintype.card (I × Bool) ≤ ((C j).card : ℝ)) →
      ∃ ω : I → Bool,
        (∀ v, α * Fintype.card (I × Bool) / 3 ≤ ((cutGraph G ω).degree v : ℝ)) ∧
        ∀ j,
          |(((C j) ∩ leftVertices ω).card : ℝ) - (C j).card / 2| < ε * (C j).card ∧
          |(((C j) ∩ rightVertices ω).card : ℝ) - (C j).card / 2| < ε * (C j).card := by
  let c := min (α / 54) (2 * ε ^ 2 * β / 3)
  have hc : 0 < c := lt_min (by positivity) (by positivity)
  obtain ⟨n₀,hn₀⟩ := exists_nat_gt (max (1 : ℝ) (16 * ((K : ℝ) + 1) / c ^ 2))
  refine ⟨n₀,?_⟩
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
  apply exists_orientation_of_error_bound G C α ε β c hε.le hε1
    (min_le_left _ _) (min_le_right _ _) hdegree hsize
  have hKR : (Fintype.card J : ℝ) ≤ K := by exact_mod_cast hK
  have hmono := mul_le_mul_of_nonneg_right
    (show 2 * ((Fintype.card (I × Bool) : ℝ) + Fintype.card J) ≤
      2 * ((Fintype.card (I × Bool) : ℝ) + K) by linarith)
    (Real.exp_pos (-c * Fintype.card (I × Bool))).le
  exact hmono.trans_lt herr

end Overfull.PairedCut
