import Overfull.PairedCut.Quantitative

/-!
# Quantitative paired cuts balancing many bounded even footprints

A prescribed pair orientation balances any fixed even footprint of size at
most `s` with probability at least `2⁻ˢ`. Linearity of expectation, after
discarding the small set of orientations failing the degree and cluster
bounds, gives one admissible cut balancing at least a `2⁻⁽ˢ⁺¹⁾` fraction
of an arbitrary finite family. No disjointness of the footprints is used.
-/

namespace Overfull.PairedCut

open Finset Classical
open scoped BigOperators

variable {I : Type*} [Fintype I]

/-- An even footprint admits a balanced assignment of its single-end pairs.
The probability of this one assignment already gives the uniform lower bound. -/
theorem balanced_footprint_probability (S : Finset (I × Bool)) (s : ℕ)
    (heven : Even S.card) (hsize : S.card ≤ s) :
    (1 / 2 : ℝ) ^ s ≤ Bernoulli.probability (1 / 2) (fun ω =>
      (S ∩ leftVertices ω).card = (S ∩ rightVertices ω).card) := by
  classical
  have hsingle := (singlePairs_card_le S).trans hsize
  have hhalf : 2 * ((singlePairs S).card / 2) = (singlePairs S).card := by
    obtain ⟨r, hr⟩ := heven
    have hc := set_card_identity S
    omega
  obtain ⟨T, hT, hTc⟩ := Finset.exists_subset_card_eq
    (Nat.div_le_self (singlePairs S).card 2)
  let σ : I → Bool := fun i => decide (i ∈ T)
  let Q : (I → Bool) → Prop := fun ω =>
    Bernoulli.retainedCount (singlePairs S) ω = (singlePairs S).card / 2
  have hassign (ω : I → Bool) (hω : ∀ i ∈ singlePairs S, ω i = σ i) : Q ω := by
    have hfilter : (singlePairs S).filter (fun i => ω i = true) = T := by
      ext i
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hi, htrue⟩
        have h := hω i hi
        simp only [σ, htrue, true_eq_decide_iff] at h
        exact h
      · intro hi
        refine ⟨hT hi, ?_⟩
        rw [hω i (hT hi)]
        simp [σ, hi]
    simpa only [Q, Bernoulli.retainedCount, hfilter] using hTc
  have hp : (1 / 2 : ℝ) ^ (singlePairs S).card ≤
      Bernoulli.probability (1 / 2) Q := by
    have h := Bernoulli.probability_mono (1 / 2) (by norm_num) (by norm_num) hassign
    rw [Bernoulli.probability_assignment] at h
    simpa only [fair_mass, Finset.prod_const] using h
  have heq : (fun ω => (S ∩ leftVertices ω).card = (S ∩ rightVertices ω).card) =
      (fun ω => Q (flip S ω)) := by
    funext ω
    apply propext
    have hsum := side_count_sum S ω
    have hid := splitCount_identity S ω
    rw [splitCount_eq_inter] at hid
    have hc := set_card_identity S
    dsimp only [Q]
    omega
  rw [heq, probability_flip S Q]
  exact (pow_le_pow_of_le_one (by norm_num) (by norm_num) hsingle).trans hp

/-- Averaging survives the removal of an exceptional event of probability
less than half the individual footprint lower bound. -/
theorem exists_balanced_footprints_outside (s k : ℕ)
    (X : Fin k → Finset (I × Bool))
    (heven : ∀ i, Even (X i).card) (hsize : ∀ i, (X i).card ≤ s)
    (Bad : (I → Bool) → Prop)
    (hbad : Bernoulli.probability (1 / 2) Bad < (1 / 2 : ℝ) ^ (s + 1)) :
    ∃ ω : I → Bool, ¬ Bad ω ∧
      k ≤ 2 ^ (s + 1) * (univ.filter (fun i =>
        ((X i) ∩ leftVertices ω).card = ((X i) ∩ rightVertices ω).card)).card := by
  classical
  let P := fun (i : Fin k) (ω : I → Bool) =>
    ((X i) ∩ leftVertices ω).card = ((X i) ∩ rightVertices ω).card
  let N := fun ω => (univ.filter (fun i => P i ω)).card
  let q : ℝ := (1 / 2) ^ (s + 1)
  have hq : 0 < q := by dsimp [q]; positivity
  have hq1 : q ≤ 1 := by
    dsimp [q]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  by_cases hk : k = 0
  · obtain ⟨ω, hω⟩ := Bernoulli.exists_not_of_probability_lt_one (1 / 2) Bad
      (hbad.trans_le hq1)
    exact ⟨ω, hω, by simp [hk]⟩
  have hkR : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hNle (ω : I → Bool) : N ω ≤ k := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      (Finset.card_filter_le (univ : Finset (Fin k)) (fun i => P i ω))
  have hcount (ω : I → Bool) :
      (N ω : ℝ) = ∑ i : Fin k, if P i ω then (1 : ℝ) else 0 := by
    exact Finset.natCast_card_filter (fun i => P i ω) univ
  have hexpect : (∑ ω : I → Bool, Bernoulli.weight (1 / 2) ω * (N ω : ℝ)) =
      ∑ i : Fin k, Bernoulli.probability (1 / 2) (P i) := by
    simp_rw [hcount, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Bernoulli.probability, MatchingProbability.probability, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro ω _
    by_cases h : P i ω <;> simp [h]
  have hlower : (k : ℝ) * (1 / 2) ^ s ≤
      ∑ ω : I → Bool, Bernoulli.weight (1 / 2) ω * (N ω : ℝ) := by
    rw [hexpect]
    calc
      _ = ∑ _i : Fin k, (1 / 2 : ℝ) ^ s := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i _ =>
        balanced_footprint_probability (X i) s (heven i) (hsize i))
  by_contra hnone
  have hsmall (ω : I → Bool) (hω : ¬ Bad ω) :
      (N ω : ℝ) ≤ (k : ℝ) * q := by
    have hnot : ¬ k ≤ 2 ^ (s + 1) * N ω := fun h => hnone ⟨ω, hω, h⟩
    have hn : (2 : ℝ) ^ (s + 1) * (N ω : ℝ) < k := by
      exact_mod_cast Nat.lt_of_not_ge hnot
    have hscale : (2 : ℝ) ^ (s + 1) * q = 1 := by
      dsimp [q]
      rw [← mul_pow]
      norm_num
    have hm := mul_le_mul_of_nonneg_right hn.le hq.le
    nlinarith
  have hpoint (ω : I → Bool) :
      (N ω : ℝ) ≤ (k : ℝ) * q + if Bad ω then (k : ℝ) else 0 := by
    by_cases h : Bad ω
    · rw [if_pos h]
      have hn : (N ω : ℝ) ≤ k := by exact_mod_cast hNle ω
      linarith [mul_nonneg hkR.le hq.le]
    · simpa [h] using hsmall ω h
  have hupper : (∑ ω : I → Bool, Bernoulli.weight (1 / 2) ω * (N ω : ℝ)) ≤
      (k : ℝ) * q + (k : ℝ) * Bernoulli.probability (1 / 2) Bad := by
    calc
      _ ≤ ∑ ω : I → Bool, Bernoulli.weight (1 / 2) ω *
          ((k : ℝ) * q + if Bad ω then (k : ℝ) else 0) :=
        Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (hpoint ω)
          (Bernoulli.weight_nonneg (1 / 2) (by norm_num) (by norm_num) ω))
      _ = _ := by
        simp only [mul_add, Finset.sum_add_distrib]
        have hconst : (∑ ω : I → Bool, Bernoulli.weight (1 / 2) ω * ((k : ℝ) * q)) =
            (k : ℝ) * q := by
          rw [← Finset.sum_mul, Bernoulli.sum_weight, one_mul]
        rw [hconst]
        congr 1
        simp only [Bernoulli.probability, MatchingProbability.probability,
          Finset.sum_filter, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ω _
        by_cases h : Bad ω <;> simp [h, mul_comm]
  have hdouble : (1 / 2 : ℝ) ^ s = 2 * q := by
    dsimp [q]
    rw [pow_succ]
    ring
  have hstrict := mul_lt_mul_of_pos_left hbad hkR
  rw [hdouble] at hlower
  change (k : ℝ) * Bernoulli.probability (1 / 2) Bad < (k : ℝ) * q at hstrict
  linarith

/-- The sampling error can be made smaller than any positive constant. -/
theorem orientation_error_lt_positive (c q : ℝ) (hc : 0 < c) (hq : 0 < q)
    (K n : ℕ) (hn : 1 ≤ n)
    (hlarge : 16 * ((K : ℝ) + 1) ≤ q * c ^ 2 * n) :
    2 * ((n : ℝ) + K) * Real.exp (-c * n) < q := by
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
  have hsq' := mul_le_mul_of_nonneg_left hsq hq.le
  have hlow : 4 * ((K : ℝ) + 1) * n ≤ q * Real.exp (c * n) := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hlow (Real.exp_pos (-c * n)).le
  have hcancel : Real.exp (c * (n : ℝ)) * Real.exp (-c * n) = 1 := by
    rw [← Real.exp_add, show c * (n : ℝ) + -c * n = 0 by ring, Real.exp_zero]
  rw [mul_assoc q, hcancel, mul_one] at hmul
  have hcoeff : (n : ℝ) + K ≤ ((K : ℝ) + 1) * n := by
    nlinarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)]
  have hcoeff' := mul_le_mul_of_nonneg_right hcoeff (Real.exp_pos (-c * n)).le
  nlinarith


/-- Simultaneous neighborhood, cluster, and bounded-footprint control. -/
theorem exists_orientation_balanced_footprints_of_error_bound {J : Type*} [Fintype J]
    (G : SimpleGraph (I × Bool)) [DecidableRel G.Adj] (C : J → Finset (I × Bool))
    (s k : ℕ) (X : Fin k → Finset (I × Bool))
    (heven : ∀ i, Even (X i).card) (hXsize : ∀ i, (X i).card ≤ s)
    (α κ ε β c : ℝ) (hκ : 0 ≤ κ) (hκ6 : κ ≤ 1 / 6)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1 / 2)
    (hcα : c ≤ 2 * κ ^ 2 * α / 3) (hcε : c ≤ 2 * ε ^ 2 * β / 3)
    (hdegree : ∀ v, α * Fintype.card (I × Bool) ≤ (G.degree v : ℝ))
    (hsize : ∀ j, β * Fintype.card (I × Bool) ≤ ((C j).card : ℝ))
    (herror : 2 * ((Fintype.card (I × Bool) : ℝ) + Fintype.card J) *
      Real.exp (-c * Fintype.card (I × Bool)) < (1 / 2 : ℝ) ^ (s + 1)) :
    ∃ ω : I → Bool,
      (∀ v, α * Fintype.card (I × Bool) / 3 ≤ ((cutGraph G ω).degree v : ℝ)) ∧
      (∀ v,
        |((G.neighborFinset v ∩ leftVertices ω).card : ℝ) - G.degree v / 2| <
          κ * G.degree v ∧
        |((G.neighborFinset v ∩ rightVertices ω).card : ℝ) - G.degree v / 2| <
          κ * G.degree v) ∧
      (∀ j,
        |(((C j) ∩ leftVertices ω).card : ℝ) - (C j).card / 2| < ε * (C j).card ∧
        |(((C j) ∩ rightVertices ω).card : ℝ) - (C j).card / 2| < ε * (C j).card) ∧
      k ≤ 2 ^ (s + 1) * (univ.filter (fun i =>
        ((X i) ∩ leftVertices ω).card = ((X i) ∩ rightVertices ω).card)).card := by
  let P := fun (ω : I → Bool) => ∃ v,
    κ * (G.neighborFinset v).card ≤
      |(splitCount (G.neighborFinset v) ω : ℝ) - (G.neighborFinset v).card / 2|
  let Q := fun (ω : I → Bool) => ∃ j,
    ε * (C j).card ≤ |(splitCount (C j) ω : ℝ) - (C j).card / 2|
  have hbad : Bernoulli.probability (1 / 2) (fun ω => P ω ∨ Q ω) < (1 / 2 : ℝ) ^ (s + 1) := by
    have hu := Bernoulli.probability_union_le (1 / 2) (by norm_num) (by norm_num) P Q
    have hp := degree_failure_probability_quantitative G α κ c hκ (by linarith) hcα hdegree
    have hq := cluster_failure_probability C ε β c hε hε1 hcε hsize
    change Bernoulli.probability (1 / 2) P ≤ _ at hp
    change Bernoulli.probability (1 / 2) Q ≤ _ at hq
    nlinarith
  obtain ⟨ω, hω, hmany⟩ := exists_balanced_footprints_outside s k X heven hXsize
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
  refine ⟨ω, ?_, ?_, ?_, hmany⟩
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


/-- Uniform thresholds precede the number and positions of all footprints. -/
theorem exists_orientation_balanced_footprints (α δ ε β : ℝ) (K s : ℕ)
    (hα : 0 < α) (hδ : 0 < δ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) (hβ : 0 < β) :
    ∃ n₀ : ℕ, ∀ (I J : Type*) [Fintype I] [Fintype J]
      (G : SimpleGraph (I × Bool)) [DecidableRel G.Adj] (C : J → Finset (I × Bool))
      (k : ℕ) (X : Fin k → Finset (I × Bool)),
      Fintype.card J ≤ K → n₀ ≤ Fintype.card (I × Bool) →
      (∀ v, α * Fintype.card (I × Bool) ≤ (G.degree v : ℝ)) →
      (∀ j, β * Fintype.card (I × Bool) ≤ ((C j).card : ℝ)) →
      (∀ i, Even (X i).card) → (∀ i, (X i).card ≤ s) →
      ∃ ω : I → Bool,
        (∀ v, α * Fintype.card (I × Bool) / 3 ≤ ((cutGraph G ω).degree v : ℝ)) ∧
        (∀ v,
          |((G.neighborFinset v ∩ leftVertices ω).card : ℝ) - G.degree v / 2| ≤
            δ * Fintype.card (I × Bool) ∧
          |((G.neighborFinset v ∩ rightVertices ω).card : ℝ) - G.degree v / 2| ≤
            δ * Fintype.card (I × Bool)) ∧
        (∀ j,
          |(((C j) ∩ leftVertices ω).card : ℝ) - (C j).card / 2| < ε * (C j).card ∧
          |(((C j) ∩ rightVertices ω).card : ℝ) - (C j).card / 2| < ε * (C j).card) ∧
        k ≤ 2 ^ (s + 1) * (univ.filter (fun i =>
          ((X i) ∩ leftVertices ω).card = ((X i) ∩ rightVertices ω).card)).card := by
  let κ := min δ (1 / 6)
  have hκ : 0 < κ := lt_min hδ (by norm_num)
  let c := min (2 * κ ^ 2 * α / 3) (2 * ε ^ 2 * β / 3)
  have hc : 0 < c := lt_min (by positivity) (by positivity)
  let q : ℝ := (1 / 2) ^ (s + 1)
  have hq : 0 < q := by dsimp [q]; positivity
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (max (1 : ℝ) (16 * ((K : ℝ) + 1) / (q * c ^ 2)))
  refine ⟨n₀, ?_⟩
  intro I J _ _ G _ C k X hK hn hdegree hsize heven hXsize
  have hnR : max (1 : ℝ) (16 * ((K : ℝ) + 1) / (q * c ^ 2)) < Fintype.card (I × Bool) :=
    hn₀.trans_le (by exact_mod_cast hn)
  have hn1 : 1 ≤ Fintype.card (I × Bool) := by
    have h := (le_max_left (1 : ℝ) (16 * ((K : ℝ) + 1) / (q * c ^ 2))).trans_lt hnR
    exact_mod_cast h.le
  have hlarge : 16 * ((K : ℝ) + 1) ≤ q * c ^ 2 * Fintype.card (I × Bool) := by
    have h := (le_max_right (1 : ℝ) (16 * ((K : ℝ) + 1) / (q * c ^ 2))).trans_lt hnR
    have h' := (div_lt_iff₀ (mul_pos hq (sq_pos_of_pos hc))).mp h
    nlinarith
  have herr := orientation_error_lt_positive c q hc hq K (Fintype.card (I × Bool)) hn1 hlarge
  have herror : 2 * ((Fintype.card (I × Bool) : ℝ) + Fintype.card J) *
      Real.exp (-c * Fintype.card (I × Bool)) < q := by
    have hKR : (Fintype.card J : ℝ) ≤ K := by exact_mod_cast hK
    have hmono := mul_le_mul_of_nonneg_right
      (show 2 * ((Fintype.card (I × Bool) : ℝ) + Fintype.card J) ≤
        2 * ((Fintype.card (I × Bool) : ℝ) + K) by linarith)
      (Real.exp_pos (-c * Fintype.card (I × Bool))).le
    exact hmono.trans_lt herr
  obtain ⟨ω, hcut, hdev, hcluster, hmany⟩ := exists_orientation_balanced_footprints_of_error_bound
    G C s k X heven hXsize α κ ε β c hκ.le (min_le_right _ _) hε.le hε1
    (min_le_left _ _) (min_le_right _ _) hdegree hsize herror
  refine ⟨ω, hcut, ?_, hcluster, hmany⟩
  intro v
  have hd : (G.degree v : ℝ) ≤ Fintype.card (I × Bool) := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    exact_mod_cast (Finset.card_le_univ (G.neighborFinset v))
  have hbound : κ * G.degree v ≤ δ * Fintype.card (I × Bool) :=
    mul_le_mul (min_le_left _ _) hd (Nat.cast_nonneg _) hδ.le
  exact ⟨(hdev v).1.le.trans hbound, (hdev v).2.le.trans hbound⟩



/-- Transport the same quantitative orientation and footprint count to arbitrary labels. -/
theorem exists_prescribed_pair_cut_balanced_footprints (α δ ε β : ℝ) (K s : ℕ)
    (hα : 0 < α) (hδ : 0 < δ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) (hβ : 0 < β) :
    ∃ n₀ : ℕ, ∀ (V I J : Type*) [Fintype V] [Fintype I] [Fintype J]
      (G : SimpleGraph V) [DecidableRel G.Adj] (e : I × Bool ≃ V)
      (C : J → Finset V) (k : ℕ) (X : Fin k → Finset V),
      Fintype.card J ≤ K → n₀ ≤ Fintype.card V →
      (∀ v, α * Fintype.card V ≤ (G.degree v : ℝ)) →
      (∀ j, β * Fintype.card V ≤ ((C j).card : ℝ)) →
      (∀ i, Even (X i).card) → (∀ i, (X i).card ≤ s) →
      ∃ A B : Finset V,
        Disjoint A B ∧ A ∪ B = univ ∧
        A.card = Fintype.card I ∧ B.card = Fintype.card I ∧
        (∀ i, (e (i, false) ∈ A ∧ e (i, true) ∈ B) ∨
          (e (i, true) ∈ A ∧ e (i, false) ∈ B)) ∧
        (∀ v, α * Fintype.card V / 3 ≤ ((crossingGraph G A).degree v : ℝ)) ∧
        (∀ v,
          |((G.neighborFinset v ∩ A).card : ℝ) - G.degree v / 2| ≤ δ * Fintype.card V ∧
          |((G.neighborFinset v ∩ B).card : ℝ) - G.degree v / 2| ≤ δ * Fintype.card V) ∧
        (∀ j,
          |(((C j) ∩ A).card : ℝ) - (C j).card / 2| < ε * (C j).card ∧
          |(((C j) ∩ B).card : ℝ) - (C j).card / 2| < ε * (C j).card) ∧
        k ≤ 2 ^ (s + 1) * (univ.filter (fun i =>
          ((X i) ∩ A).card = ((X i) ∩ B).card)).card := by
  obtain ⟨n₀, hn₀⟩ := exists_orientation_balanced_footprints α δ ε β K s hα hδ hε hε1 hβ
  refine ⟨n₀, ?_⟩
  intro V I J _ _ _ G _ e C k X hK hn hdegree hsize heven hXsize
  let C' := fun j => (C j).map e.symm.toEmbedding
  let X' := fun i => (X i).map e.symm.toEmbedding
  have hcard : Fintype.card (I × Bool) = Fintype.card V := Fintype.card_congr e
  have hdegree' (v : I × Bool) :
      α * Fintype.card (I × Bool) ≤ ((G.comap e).degree v : ℝ) := by
    have hd := Overfull.iso_degree_eq (SimpleGraph.Iso.comap e G) v
    change (G.comap e).degree v = G.degree (e v) at hd
    rw [hcard, hd]
    exact hdegree (e v)
  have hsize' (j : J) : β * Fintype.card (I × Bool) ≤ ((C' j).card : ℝ) := by
    simpa only [C', Finset.card_map, hcard] using hsize j
  obtain ⟨ω, hcut, hprecision, hbalance, hmany⟩ := hn₀ I J (G.comap e) C' k X' hK
    (by simpa [hcard] using hn) hdegree' hsize'
    (by simpa only [X', Finset.card_map] using heven)
    (by simpa only [X', Finset.card_map] using hXsize)
  let A := (leftVertices ω).map e.toEmbedding
  let B := (rightVertices ω).map e.toEmbedding
  refine ⟨A, B, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply Finset.disjoint_left.mpr
    intro v hvA hvB
    change v ∈ (leftVertices ω).map e.toEmbedding at hvA
    change v ∈ (rightVertices ω).map e.toEmbedding at hvB
    rw [Finset.mem_map_equiv] at hvA hvB
    exact Finset.disjoint_left.mp (sides_disjoint ω) hvA hvB
  · ext v
    change (v ∈ (leftVertices ω).map e.toEmbedding ∪
      (rightVertices ω).map e.toEmbedding) ↔ v ∈ univ
    simp only [Finset.mem_union, Finset.mem_map_equiv, Finset.mem_univ, iff_true]
    have h : e.symm v ∈ leftVertices ω ∪ rightVertices ω := by rw [sides_union]; simp
    exact Finset.mem_union.mp h
  · simp only [A, Finset.card_map, leftVertices_card]
  · simp only [B, Finset.card_map, rightVertices_card]
  · intro i
    cases hω : ω i <;>
      simp [A, B, Finset.mem_map_equiv, mem_leftVertices, mem_rightVertices, hω]
  · intro v
    obtain ⟨u, rfl⟩ := e.surjective v
    have h := hcut u
    rw [hcard, Overfull.iso_degree_eq (pairCutIso G e ω)] at h
    exact h
  · intro v
    obtain ⟨u, rfl⟩ := e.surjective v
    have h := hprecision u
    have hneighbor : (G.comap e).neighborFinset u =
        (G.neighborFinset (e u)).map e.symm.toEmbedding := by
      ext w
      simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.comap_adj,
        Finset.mem_map_equiv, Equiv.symm_symm]
    have hd := Overfull.iso_degree_eq (SimpleGraph.Iso.comap e G) u
    change (G.comap e).degree u = G.degree (e u) at hd
    rw [hneighbor, inverse_inter_card e (G.neighborFinset (e u)) (leftVertices ω),
      inverse_inter_card e (G.neighborFinset (e u)) (rightVertices ω), hd, hcard] at h
    exact h
  · intro j
    have h := hbalance j
    dsimp only [C'] at h
    rw [inverse_inter_card e (C j) (leftVertices ω),
      inverse_inter_card e (C j) (rightVertices ω), Finset.card_map] at h
    exact h

  · simpa only [X', inverse_inter_card] using hmany


/-- Cluster regularity turns the same cut into a robust bipartite graph. -/
theorem exists_prescribed_pair_cut_from_clusters_balanced_footprints
    (α δ ε β d γ τ : ℝ) (K s : ℕ)
    (hα : 0 < α) (hδ : 0 < δ) (hε : 0 < ε) (hεγ : ε ≤ γ / 100) (hβ : 0 < β)
    (hd : 0 < d) (hd1 : d ≤ 1) (hγ : 0 < γ) (hγτ : γ ≤ τ) (hτ : τ ≤ 1 / 8) :
    ∃ n₀ : ℕ, ∀ (V I J : Type*) [Fintype V] [Fintype I] [Fintype J]
      [DecidableEq V] [DecidableEq J]
      (G : SimpleGraph V) [DecidableRel G.Adj] (e : I × Bool ≃ V)
      (R : SimpleGraph J) [DecidableRel R.Adj] (C : J → Finset V) (w k : ℕ) (X : Fin k → Finset V),
      Fintype.card J ≤ K → n₀ ≤ Fintype.card V →
      (∀ v, α * Fintype.card V ≤ (G.degree v : ℝ)) →
      (∀ j, β * Fintype.card V ≤ ((C j).card : ℝ)) →
      0 < w → 1 ≤ γ * Fintype.card J → IsRobustExpander R (2 * γ) (2 * τ) →
      (∀ i j, i ≠ j → Disjoint (C i) (C j)) → (∀ i, (C i).card = w) →
      (((univ.biUnion C)ᶜ).card : ℝ) ≤ ε * Fintype.card V →
      LowerRegularPairs G R C ε d w →
      (∀ i, Even (X i).card) → (∀ i, (X i).card ≤ s) →
      ∃ A B : Finset V,
        Disjoint A B ∧ A ∪ B = univ ∧ A.card = Fintype.card I ∧ B.card = Fintype.card I ∧
        (∀ i, (e (i, false) ∈ A ∧ e (i, true) ∈ B) ∨
          (e (i, true) ∈ A ∧ e (i, false) ∈ B)) ∧
        (∀ v, α * Fintype.card V / 3 ≤ ((crossingGraph G A).degree v : ℝ)) ∧
        (∀ v,
          |((G.neighborFinset v ∩ A).card : ℝ) - G.degree v / 2| ≤ δ * Fintype.card V ∧
          |((G.neighborFinset v ∩ B).card : ℝ) - G.degree v / 2| ≤ δ * Fintype.card V) ∧
        IsBipartiteRobustExpander (cutSidesGraph G A B) (d * γ ^ 2 / 100) (4 * τ) ∧
        k ≤ 2 ^ (s + 1) * (univ.filter (fun i =>
          ((X i) ∩ A).card = ((X i) ∩ B).card)).card := by
  have hε1 : ε ≤ 1 / 2 := by linarith
  obtain ⟨n₀, hn₀⟩ := exists_prescribed_pair_cut_balanced_footprints α δ ε β K s hα hδ hε hε1 hβ
  refine ⟨n₀, ?_⟩
  intro V I J _ _ _ _ _ G _ e R _ C w k X hK hn hdegree hlarge hw ht hR
    hdisjoint hsize hexception hregular heven hXsize
  obtain ⟨A, B, hAB, hunion, hAcard, hBcard, hpair, hcut, hprecision, hcluster, hmany⟩ :=
    hn₀ V I J G e C k X hK hn hdegree hlarge heven hXsize
  have hunion' : A ∪ B = univ := by
    ext v
    have h := Finset.ext_iff.mp hunion v
    simpa only [Finset.mem_union, Finset.mem_univ] using h
  have hinter (X Y : Finset V) :
      (letI : DecidableEq V := Classical.decEq V; X ∩ Y) = X ∩ Y := by
    ext v
    simp only [Finset.mem_inter]
  simp only [hinter] at hcluster hprecision hmany
  refine ⟨A, B, hAB, hunion', hAcard, hBcard, hpair, hcut, hprecision, ?_, hmany⟩
  apply balanced_cluster_cut_expands G R C ε d γ τ w hd hd1 hγ hγτ hτ hε.le hεγ
    hw ht hR hdisjoint hsize hexception hregular A B hAB hunion' (hAcard.trans hBcard.symm)
  · intro j
    have h := (abs_lt.mp (hcluster j).1).2
    rw [hsize j, Finset.inter_comm] at h
    linarith
  · intro j
    have h := (abs_lt.mp (hcluster j).2).1
    rw [hsize j, Finset.inter_comm] at h
    linarith


/-- A single robust quantitative paired cut balances a fixed positive fraction
of all bounded even footprints. The robust constant precedes the degree tolerance,
and the order threshold precedes the graph, pairing, and footprint family. -/
theorem paired_cut_quantitative_balanced_footprints (α ν τ : ℝ) (s : ℕ) (hα : 0 < α) (hν : 0 < ν)
    (hντ : ν ≤ τ) (hτ : τ ≤ 1 / 8) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ,
      ∀ (V I : Type*) [Fintype V] [Fintype I] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj] (e : I × Bool ≃ V)
        (k : ℕ) (X : Fin k → Finset V),
        n₀ ≤ Fintype.card V →
        (∀ v, α * Fintype.card V ≤ (G.degree v : ℝ)) →
        IsRobustExpander G ν τ →
        (∀ i, Even (X i).card) → (∀ i, (X i).card ≤ s) →
        ∃ A B : Finset V,
          Disjoint A B ∧ A ∪ B = univ ∧ A.card = Fintype.card I ∧ B.card = Fintype.card I ∧
          (∀ i, (e (i, false) ∈ A ∧ e (i, true) ∈ B) ∨
            (e (i, true) ∈ A ∧ e (i, false) ∈ B)) ∧
          (∀ v, α * Fintype.card V / 3 ≤ ((crossingGraph G A).degree v : ℝ)) ∧
          (∀ v,
            |((G.neighborFinset v ∩ A).card : ℝ) - G.degree v / 2| ≤ δ * Fintype.card V ∧
            |((G.neighborFinset v ∩ B).card : ℝ) - G.degree v / 2| ≤ δ * Fintype.card V) ∧
          IsBipartiteRobustExpander (cutSidesGraph G A B) ξ (4 * τ) ∧
          k ≤ 2 ^ (s + 1) * (univ.filter (fun i =>
            ((X i) ∩ A).card = ((X i) ∩ B).card)).card := by
  let γ := ν / 4
  let ε := γ / 200
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεγ : ε ≤ γ / 100 := by dsimp [ε]; linarith
  have hγτ : γ ≤ τ := by dsimp [γ]; linarith
  have hν1 : ν ≤ 1 := by linarith
  have hτ0 : 0 ≤ τ := hν.le.trans hντ
  obtain ⟨K, hK, d, hd, hd1, nReg, hReg⟩ :=
    exists_robust_regular_clusters ν τ ε hν hν1 hτ0 hε
  let β := 1 / (2 * (K : ℝ))
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hβ : 0 < β := by dsimp [β]; positivity
  refine ⟨d * γ ^ 2 / 100, by positivity, ?_⟩
  intro δ hδ
  obtain ⟨nCut, hCut⟩ := exists_prescribed_pair_cut_from_clusters_balanced_footprints α δ ε β d γ τ K s
    hα hδ hε hεγ hβ hd hd1 hγ hγτ hτ
  refine ⟨max nReg nCut, ?_⟩
  intro V I _ _ _ G _ e k X hn hdegree hG heven hXsize
  obtain ⟨P, w, C, R, hK', ht, hw, hsize, hdisjoint, hexception, hlarge, hR, hregular⟩ :=
    hReg V G ((le_max_left nReg nCut).trans hn) hG
  apply hCut V I P.parts G e R C w k X
  · simpa only [Fintype.card_coe] using hK'
  · exact (le_max_right nReg nCut).trans hn
  · exact hdegree
  · intro j
    rw [hsize j]
    exact hlarge
  · exact hw
  · simpa only [γ, Fintype.card_coe] using ht
  · have heq : 2 * γ = ν / 2 := by dsimp [γ]; ring
    simpa only [heq] using hR
  · exact hdisjoint
  · exact hsize
  · simpa only [Finset.compl_eq_univ_sdiff] using hexception
  · exact hregular

  · exact heven
  · exact hXsize

end Overfull.PairedCut
