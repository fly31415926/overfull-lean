import Overfull.Probability.IndependentBernoulli
import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# Uniform sampling without replacement

A sample is an actual subset of a finite population. All subsets of the
prescribed size have the same probability, and the number of selected
members of a fixed set is the hypergeometric random variable.
-/

namespace Overfull.Hypergeometric

open Finset Classical
open scoped BigOperators

variable {E : Type*} [Fintype E]

noncomputable def weight (k : ℕ) (T : Finset E) : ℝ :=
  if T.card = k then 1 / (Nat.choose (Fintype.card E) k : ℝ) else 0

noncomputable def probability (k : ℕ) (P : Finset E → Prop) : ℝ :=
  MatchingProbability.probability (weight (E := E) k) P

noncomputable def count (S T : Finset E) : ℕ := (S ∩ T).card

theorem weight_nonneg (k : ℕ) (T : Finset E) : 0 ≤ weight k T := by
  unfold weight
  split_ifs <;> positivity

private theorem all_samples (k : ℕ) :
    (univ : Finset (Finset E)).filter (fun T => T.card = k) =
      (univ : Finset E).powersetCard k := by
  classical
  ext T
  simp

theorem sum_weight (k : ℕ) (hk : k ≤ Fintype.card E) :
    (∑ T : Finset E, weight k T) = 1 := by
  classical
  unfold weight
  rw [← Finset.sum_filter, all_samples]
  simp only [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
    nsmul_eq_mul]
  have hp : (0 : ℝ) < Nat.choose (Fintype.card E) k := by
    exact_mod_cast Nat.choose_pos hk
  field_simp

theorem probability_eq_card (k : ℕ) (P : Finset E → Prop) :
    probability k P =
      (((univ : Finset E).powersetCard k).filter P).card /
        (Nat.choose (Fintype.card E) k : ℝ) := by
  classical
  unfold probability MatchingProbability.probability weight
  rw [← Finset.sum_filter]
  have heq : ((univ : Finset (Finset E)).filter P).filter (fun T => T.card = k) =
      ((univ : Finset E).powersetCard k).filter P := by
    ext T
    simp [and_comm]
  rw [heq]
  simp [div_eq_mul_inv]

/-- Counting samples which contain a prescribed set, by deleting that set. -/
theorem containing_samples_card (S : Finset E) (k : ℕ) (hSk : S.card ≤ k) :
    (((univ : Finset E).powersetCard k).filter (fun T => S ⊆ T)).card =
      Nat.choose (Fintype.card E - S.card) (k - S.card) := by
  classical
  let U := (univ : Finset E) \ S
  have heq : ((univ : Finset E).powersetCard k).filter (fun T => S ⊆ T) =
      (U.powersetCard (k - S.card)).image (fun T => S ∪ T) := by
    ext T
    constructor
    · intro hT
      obtain ⟨hT, hST⟩ := Finset.mem_filter.mp hT
      have hcard := (Finset.mem_powersetCard.mp hT).2
      apply Finset.mem_image.mpr
      refine ⟨T \ S, ?_, Finset.union_sdiff_of_subset hST⟩
      apply Finset.mem_powersetCard.mpr
      constructor
      · intro e he
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ e, (Finset.mem_sdiff.mp he).2⟩
      · rw [Finset.card_sdiff_of_subset hST, hcard]
    · intro hT
      obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp hT
      obtain ⟨hRU, hRcard⟩ := Finset.mem_powersetCard.mp hR
      have hd : Disjoint S R := by
        apply Finset.disjoint_left.mpr
        intro e heS heR
        exact (Finset.mem_sdiff.mp (hRU heR)).2 heS
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩,
        Finset.subset_union_left⟩
      rw [Finset.card_union_of_disjoint hd, hRcard, Nat.add_sub_of_le hSk]
  have hinj : Set.InjOn (fun T : Finset E => S ∪ T)
      (U.powersetCard (k - S.card)) := by
    intro T hT R hR heq
    have hTU := (Finset.mem_powersetCard.mp hT).1
    have hRU := (Finset.mem_powersetCard.mp hR).1
    ext e
    by_cases heS : e ∈ S
    · have heT : e ∉ T := fun h => (Finset.mem_sdiff.mp (hTU h)).2 heS
      have heR : e ∉ R := fun h => (Finset.mem_sdiff.mp (hRU h)).2 heS
      simp [heT, heR]
    · have h := congrArg (fun Q : Finset E => e ∈ Q) heq
      simpa [heS] using h
  rw [heq, Finset.card_image_of_injOn hinj, Finset.card_powersetCard]
  simp [U, Finset.card_sdiff_of_subset (Finset.subset_univ S)]

/-- Sampling without replacement makes simultaneous inclusion no more
likely than independent inclusion with the same marginal probability. -/
theorem choose_ratio_le_pow (N k r : ℕ) (hN : 0 < N) (hk : k ≤ N) (hr : r ≤ k) :
    (Nat.choose k r : ℝ) / Nat.choose N r ≤ ((k : ℝ) / N) ^ r := by
  have hNr : r ≤ N := hr.trans hk
  have hden : (Nat.choose N r : ℝ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero hNr
  have hf : (r.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  have hratio : (Nat.choose k r : ℝ) / Nat.choose N r =
      (k.descFactorial r : ℝ) / N.descFactorial r := by
    rw [Nat.descFactorial_eq_factorial_mul_choose,
      Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    field_simp
  rw [hratio, Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_prod_range]
  push_cast
  rw [← Finset.prod_div_distrib]
  calc
    _ ≤ ∏ _i ∈ Finset.range r, (k : ℝ) / N := by
      apply Finset.prod_le_prod
      · intro i _
        positivity
      · intro i hi
        have hir : i < r := Finset.mem_range.mp hi
        have hik : i ≤ k := by omega
        have hiN : i < N := by omega
        have hpos : (0 : ℝ) < (N : ℝ) - i := by
          exact sub_pos.mpr (by exact_mod_cast hiN)
        have hposN : (0 : ℝ) < N := by exact_mod_cast hN
        rw [Nat.cast_sub hik, Nat.cast_sub hiN.le]
        apply (div_le_div_iff₀ hpos hposN).2
        have hmul := mul_le_mul_of_nonneg_left
          (show (k : ℝ) ≤ N by exact_mod_cast hk) (Nat.cast_nonneg i : (0 : ℝ) ≤ i)
        nlinarith
    _ = _ := by simp [div_pow]

/-- Exact probability of containing a prescribed set. -/
theorem probability_containing (S : Finset E) (k : ℕ) (hSk : S.card ≤ k) :
    probability k (fun T => S ⊆ T) =
      (Nat.choose (Fintype.card E - S.card) (k - S.card) : ℝ) /
        Nat.choose (Fintype.card E) k := by
  classical
  rw [probability_eq_card]
  congr 2
  convert containing_samples_card S k hSk using 1
  congr 1
  ext T
  simp

theorem probability_containing_le (k : ℕ) (hN : 0 < Fintype.card E)
    (hk : k ≤ Fintype.card E) (S : Finset E) :
    probability k (fun T => S ⊆ T) ≤
      ((k : ℝ) / Fintype.card E) ^ S.card := by
  classical
  by_cases hSk : S.card ≤ k
  · rw [probability_containing S k hSk]
    have hchoose := Nat.choose_mul hk hSk
    have hNchoose : (Nat.choose (Fintype.card E) k : ℝ) ≠ 0 := by
      exact_mod_cast Nat.choose_ne_zero hk
    have hSchoose : (Nat.choose (Fintype.card E) S.card : ℝ) ≠ 0 := by
      exact_mod_cast Nat.choose_ne_zero (hSk.trans hk)
    have heq : (Nat.choose (Fintype.card E - S.card) (k - S.card) : ℝ) /
        Nat.choose (Fintype.card E) k =
        (Nat.choose k S.card : ℝ) / Nat.choose (Fintype.card E) S.card := by
      apply (div_eq_div_iff hNchoose hSchoose).2
      have hc : (Nat.choose (Fintype.card E) k : ℝ) * Nat.choose k S.card =
          (Nat.choose (Fintype.card E) S.card : ℝ) *
            Nat.choose (Fintype.card E - S.card) (k - S.card) := by
        exact_mod_cast hchoose
      nlinarith
    rw [heq]
    exact choose_ratio_le_pow _ k S.card hN hk hSk
  · have hzero : probability k (fun T => S ⊆ T) = 0 := by
      unfold probability MatchingProbability.probability
      apply Finset.sum_eq_zero
      intro T hT
      have hST : S ⊆ T := by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hT
      unfold weight
      apply if_neg
      intro hTk
      exact hSk (hTk ▸ Finset.card_le_card hST)
    rw [hzero]
    positivity

theorem weight_compl (k : ℕ) (hk : k ≤ Fintype.card E) (T : Finset E) :
    weight k T = weight (Fintype.card E - k) Tᶜ := by
  classical
  have hT : T.card ≤ Fintype.card E := Finset.card_le_univ T
  have heq : Tᶜ.card = Fintype.card E - k ↔ T.card = k := by
    rw [Finset.card_compl]
    omega
  unfold weight
  simp only [Nat.choose_symm hk, heq]

theorem expectation_compl (k : ℕ) (hk : k ≤ Fintype.card E)
    (f : Finset E → ℝ) :
    (∑ T : Finset E, weight k T * f T) =
      ∑ T : Finset E, weight (Fintype.card E - k) T * f Tᶜ := by
  classical
  apply Fintype.sum_bijective (fun T : Finset E => Tᶜ)
    (show Function.Bijective (fun T : Finset E => Tᶜ) from
      ⟨compl_injective, fun T => ⟨Tᶜ, compl_compl T⟩⟩)
  intro T
  rw [weight_compl k hk T, compl_compl]

theorem probability_compl (k : ℕ) (hk : k ≤ Fintype.card E)
    (P : Finset E → Prop) :
    probability k P = probability (Fintype.card E - k) (fun T => P Tᶜ) := by
  classical
  have h := expectation_compl k hk (fun T => if P T then 1 else 0)
  simpa only [probability, MatchingProbability.probability, Finset.sum_filter,
    mul_ite, mul_one, mul_zero] using h

theorem probability_disjoint_le (k : ℕ) (hN : 0 < Fintype.card E)
    (hk : k ≤ Fintype.card E) (S : Finset E) :
    probability k (fun T => Disjoint S T) ≤
      (1 - (k : ℝ) / Fintype.card E) ^ S.card := by
  classical
  rw [probability_compl k hk]
  have heq : (fun T : Finset E => Disjoint S Tᶜ) = (fun T => S ⊆ T) := by
    funext T
    simp [Finset.disjoint_left, Finset.subset_iff]
  rw [heq]
  have h := probability_containing_le (Fintype.card E - k) hN (Nat.sub_le _ _) S
  have he : ((Fintype.card E - k : ℕ) : ℝ) / Fintype.card E =
      1 - (k : ℝ) / Fintype.card E := by
    rw [Nat.cast_sub hk, sub_div]
    have hne : (Fintype.card E : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    rw [div_self hne]
  simpa only [he] using h

private theorem product_moment_le {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (P : E → Ω → Prop) (S : Finset E) (a b p : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hjoint : ∀ U ⊆ S,
      MatchingProbability.probability w (fun ω => ∀ e ∈ U, P e ω) ≤ p ^ U.card) :
    (∑ ω : Ω, w ω * ∏ e ∈ S, ((if P e ω then b else 0) + a)) ≤
      (b * p + a) ^ S.card := by
  classical
  calc
    _ = ∑ U ∈ S.powerset,
        (b ^ U.card * a ^ (S \ U).card) *
          MatchingProbability.probability w (fun ω => ∀ e ∈ U, P e ω) := by
      simp_rw [Finset.prod_add (fun e => if P e _ then b else 0) (fun _ => a),
        Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro U _
      simp only [Finset.prod_ite_zero, Finset.prod_const,
        MatchingProbability.probability, Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ω _
      by_cases h : ∀ e ∈ U, P e ω <;> simp [h, mul_comm, mul_left_comm]
    _ ≤ ∑ U ∈ S.powerset, (b ^ U.card * a ^ (S \ U).card) * p ^ U.card := by
      apply Finset.sum_le_sum
      intro U hU
      exact mul_le_mul_of_nonneg_left (hjoint U (Finset.mem_powerset.mp hU))
        (mul_nonneg (pow_nonneg hb _) (pow_nonneg ha _))
    _ = _ := by
      have h := Finset.prod_add (fun _ : E => b * p) (fun _ => a) S
      simp only [Finset.prod_const] at h
      rw [h]
      apply Finset.sum_congr rfl
      intro U _
      rw [mul_pow]
      ring

omit [Fintype E] in
theorem count_eq_retainedCount (S T : Finset E) :
    count S T = Bernoulli.retainedCount S (fun e => decide (e ∈ T)) := by
  classical
  unfold count Bernoulli.retainedCount
  congr 1
  ext e
  simp

theorem exp_count_product (S T : Finset E) (t : ℝ) :
    Real.exp (t * (count S T : ℝ)) =
      ∏ e ∈ S, if e ∈ T then Real.exp t else 1 := by
  classical
  rw [count_eq_retainedCount, Bernoulli.exp_count_product]
  calc
    _ = ∏ e : E, if e ∈ S then (if e ∈ T then Real.exp t else 1) else 1 := by
      apply Finset.prod_congr rfl
      intro e _
      by_cases heS : e ∈ S <;> by_cases heT : e ∈ T <;> simp [heS, heT]
    _ = _ := by rw [← Finset.prod_filter]; simp

/-- The exponential moment of the actual fixed-size sample is no larger
than the independent Bernoulli moment, for either sign of the exponent. -/
theorem exponential_moment_le_binomial (k : ℕ) (hN : 0 < Fintype.card E)
    (hk : k ≤ Fintype.card E) (S : Finset E) (t : ℝ) :
    (∑ T : Finset E, weight k T * Real.exp (t * (count S T : ℝ))) ≤
      (1 - (k : ℝ) / Fintype.card E +
        ((k : ℝ) / Fintype.card E) * Real.exp t) ^ S.card := by
  classical
  by_cases ht : 0 ≤ t
  · have hb : 0 ≤ Real.exp t - 1 := by
      have h := Real.exp_le_exp.mpr ht
      simpa only [Real.exp_zero] using sub_nonneg.mpr h
    have h := product_moment_le (weight (E := E) k) (fun e T => e ∈ T)
      S 1 (Real.exp t - 1) ((k : ℝ) / Fintype.card E) (by norm_num) hb
      (fun U _ => probability_containing_le k hN hk U)
    convert h using 1
    · apply Finset.sum_congr rfl
      intro T _
      congr 1
      rw [exp_count_product]
      apply Finset.prod_congr rfl
      intro e _
      by_cases he : e ∈ T <;> simp [he]
    · congr 1
      ring
  · have ht' : t ≤ 0 := le_of_lt (lt_of_not_ge ht)
    have hb : 0 ≤ 1 - Real.exp t := by
      have h := Real.exp_le_exp.mpr ht'
      simpa only [Real.exp_zero] using sub_nonneg.mpr h
    have hjoint (U : Finset E) (_ : U ⊆ S) :
        MatchingProbability.probability (weight (E := E) k)
          (fun T => ∀ e ∈ U, e ∉ T) ≤
            (1 - (k : ℝ) / Fintype.card E) ^ U.card := by
      have heq : (fun T : Finset E => ∀ e ∈ U, e ∉ T) =
          (fun T => Disjoint U T) := by
        funext T
        exact propext Finset.disjoint_left.symm
      rw [heq]
      exact probability_disjoint_le k hN hk U
    have h := product_moment_le (weight (E := E) k) (fun e T => e ∉ T)
      S (Real.exp t) (1 - Real.exp t) (1 - (k : ℝ) / Fintype.card E)
      (Real.exp_pos _).le hb hjoint
    convert h using 1
    · apply Finset.sum_congr rfl
      intro T _
      congr 1
      rw [exp_count_product]
      apply Finset.prod_congr rfl
      intro e _
      by_cases he : e ∈ T <;> simp [he]
    · congr 1
      ring

theorem exponential_moment_le (k : ℕ) (hN : 0 < Fintype.card E)
    (hk : k ≤ Fintype.card E) (S : Finset E) (t : ℝ) :
    (∑ T : Finset E, weight k T * Real.exp (t * (count S T : ℝ))) ≤
      Real.exp (((k : ℝ) / Fintype.card E) * S.card * (Real.exp t - 1)) := by
  have hp : 0 ≤ (k : ℝ) / Fintype.card E := by positivity
  have hp1 : (k : ℝ) / Fintype.card E ≤ 1 := by
    apply (div_le_one (by exact_mod_cast hN : (0 : ℝ) < Fintype.card E)).2
    exact_mod_cast hk
  have hbase : 1 - (k : ℝ) / Fintype.card E +
      ((k : ℝ) / Fintype.card E) * Real.exp t ≤
        Real.exp (((k : ℝ) / Fintype.card E) * (Real.exp t - 1)) := by
    have h := Real.add_one_le_exp (((k : ℝ) / Fintype.card E) * (Real.exp t - 1))
    nlinarith
  have hnonneg : 0 ≤ 1 - (k : ℝ) / Fintype.card E +
      ((k : ℝ) / Fintype.card E) * Real.exp t :=
    add_nonneg (sub_nonneg.mpr hp1) (mul_nonneg hp (Real.exp_pos _).le)
  calc
    _ ≤ (1 - (k : ℝ) / Fintype.card E +
        ((k : ℝ) / Fintype.card E) * Real.exp t) ^ S.card :=
      exponential_moment_le_binomial k hN hk S t
    _ ≤ Real.exp (((k : ℝ) / Fintype.card E) * (Real.exp t - 1)) ^ S.card :=
      pow_le_pow_left₀ hnonneg hbase _
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

theorem probability_member (k : ℕ) (hN : 0 < Fintype.card E)
    (hk : k ≤ Fintype.card E) (e : E) :
    probability k (fun T => e ∈ T) = (k : ℝ) / Fintype.card E := by
  classical
  by_cases hk0 : k = 0
  · subst k
    simp [probability_eq_card]
  · have hkpos : 1 ≤ k := by omega
    have heq : (fun T : Finset E => e ∈ T) = (fun T => {e} ⊆ T) := by
      funext T
      simp
    rw [heq, probability_containing {e} k (by simpa using hkpos)]
    simp only [Finset.card_singleton]
    have hc := Nat.choose_mul hk hkpos
    simp only [Nat.choose_one_right] at hc
    have hNchoose : (Nat.choose (Fintype.card E) k : ℝ) ≠ 0 := by
      exact_mod_cast Nat.choose_ne_zero hk
    have hNr : (Fintype.card E : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    apply (div_eq_div_iff hNchoose hNr).2
    have hc' : (Nat.choose (Fintype.card E) k : ℝ) * k =
        (Fintype.card E : ℝ) * Nat.choose (Fintype.card E - 1) (k - 1) := by
      exact_mod_cast hc
    nlinarith

omit [Fintype E] in
theorem count_eq_sum (S T : Finset E) :
    (count S T : ℝ) = ∑ e ∈ S, if e ∈ T then 1 else 0 := by
  classical
  have heq : S ∩ T = S.filter (fun e => e ∈ T) := by
    ext e
    simp
  simp [count, heq]

/-- The expectation is computed from the actual uniform sample. -/
theorem expected_count_nonempty (k : ℕ) (hN : 0 < Fintype.card E)
    (hk : k ≤ Fintype.card E) (S : Finset E) :
    (∑ T : Finset E, weight k T * (count S T : ℝ)) =
      ((k : ℝ) / Fintype.card E) * S.card := by
  classical
  simp_rw [count_eq_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ e ∈ S, probability k (fun T => e ∈ T) := by
      apply Finset.sum_congr rfl
      intro e _
      simp only [probability, MatchingProbability.probability, Finset.sum_filter,
        mul_ite, mul_one, mul_zero]
      apply Finset.sum_congr rfl
      intro T _
      by_cases he : e ∈ T <;> simp [he]
    _ = _ := by simp [probability_member k hN hk, mul_comm]

theorem exponential_tail (k : ℕ) (hN : 0 < Fintype.card E)
    (hk : k ≤ Fintype.card E) (S : Finset E) (t a : ℝ)
    (P : Finset E → Prop)
    (hP : ∀ T, P T → t * a ≤ t * (count S T : ℝ)) :
    probability k P ≤ Real.exp
      (((k : ℝ) / Fintype.card E) * S.card * (Real.exp t - 1) - t * a) := by
  have hm := MatchingProbability.probability_markov (weight (E := E) k)
    (weight_nonneg k) (fun T => Real.exp (t * (count S T : ℝ)))
    (fun _ => (Real.exp_pos _).le) (Real.exp (t * a)) P
    (fun T h => Real.exp_le_exp.mpr (hP T h))
  have hb := exponential_moment_le k hN hk S t
  change Real.exp (t * a) * probability k P ≤ _ at hm
  have hmul := mul_le_mul_of_nonneg_left (hm.trans hb) (Real.exp_pos (-t * a)).le
  have hc : Real.exp (-t * a) * Real.exp (t * a) = 1 := by
    rw [← Real.exp_add, show -t * a + t * a = 0 by ring, Real.exp_zero]
  rw [← mul_assoc, hc, one_mul, ← Real.exp_add] at hmul
  convert hmul using 1
  congr 1
  ring

theorem chernoff_upper (k : ℕ) (δ : ℝ) (hN : 0 < Fintype.card E)
    (hk : k ≤ Fintype.card E) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (S : Finset E) :
    probability k (fun T => (1 + δ) * (((k : ℝ) / Fintype.card E) * S.card) ≤
      (count S T : ℝ)) ≤
      Real.exp (-δ ^ 2 * (((k : ℝ) / Fintype.card E) * S.card) / 3) := by
  have hμ : 0 ≤ ((k : ℝ) / Fintype.card E) * S.card := by positivity
  have ht : 0 ≤ δ / 2 := by positivity
  have htail := exponential_tail k hN hk S (δ / 2)
    ((1 + δ) * (((k : ℝ) / Fintype.card E) * S.card))
    (fun T => (1 + δ) * (((k : ℝ) / Fintype.card E) * S.card) ≤ (count S T : ℝ))
    (fun _ h => mul_le_mul_of_nonneg_left h ht)
  refine htail.trans (Real.exp_le_exp.mpr ?_)
  have hq := Bernoulli.exp_quadratic_bound (δ / 2)
    (by rw [abs_of_nonneg ht]; linarith)
  have hmul := mul_le_mul_of_nonneg_left hq hμ
  nlinarith

theorem chernoff_lower (k : ℕ) (δ : ℝ) (hN : 0 < Fintype.card E)
    (hk : k ≤ Fintype.card E) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (S : Finset E) :
    probability k (fun T => (count S T : ℝ) ≤
      (1 - δ) * (((k : ℝ) / Fintype.card E) * S.card)) ≤
      Real.exp (-δ ^ 2 * (((k : ℝ) / Fintype.card E) * S.card) / 3) := by
  have hμ : 0 ≤ ((k : ℝ) / Fintype.card E) * S.card := by positivity
  have ht : -δ / 2 ≤ 0 := by linarith
  have htail := exponential_tail k hN hk S (-δ / 2)
    ((1 - δ) * (((k : ℝ) / Fintype.card E) * S.card))
    (fun T => (count S T : ℝ) ≤ (1 - δ) * (((k : ℝ) / Fintype.card E) * S.card))
    (fun _ h => mul_le_mul_of_nonpos_left h ht)
  refine htail.trans (Real.exp_le_exp.mpr ?_)
  have hq := Bernoulli.exp_quadratic_bound (-δ / 2)
    (by rw [abs_of_nonpos ht]; linarith)
  have hmul := mul_le_mul_of_nonneg_left hq hμ
  nlinarith

/-- Two-sided Chernoff bound for a uniform sample of size `k`, without
replacement, from a finite nonempty population. -/
theorem chernoff_nonempty (k : ℕ) (δ : ℝ) (hN : 0 < Fintype.card E)
    (hk : k ≤ Fintype.card E) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (S : Finset E) :
    probability k (fun T => δ * (((k : ℝ) / Fintype.card E) * S.card) ≤
      |(count S T : ℝ) - ((k : ℝ) / Fintype.card E) * S.card|) ≤
      2 * Real.exp (-δ ^ 2 * (((k : ℝ) / Fintype.card E) * S.card) / 3) := by
  classical
  have hupper := chernoff_upper k δ hN hk hδ hδ1 S
  have hlower := chernoff_lower k δ hN hk hδ hδ1 S
  calc
    _ ≤ probability k (fun T =>
        (1 + δ) * (((k : ℝ) / Fintype.card E) * S.card) ≤ (count S T : ℝ) ∨
        (count S T : ℝ) ≤ (1 - δ) * (((k : ℝ) / Fintype.card E) * S.card)) := by
      apply MatchingProbability.probability_mono _ (weight_nonneg k)
      intro T hT
      rcases le_abs.mp hT with h | h
      · left; nlinarith
      · right; nlinarith
    _ ≤ probability k (fun T =>
        (1 + δ) * (((k : ℝ) / Fintype.card E) * S.card) ≤ (count S T : ℝ)) +
        probability k (fun T => (count S T : ℝ) ≤
          (1 - δ) * (((k : ℝ) / Fintype.card E) * S.card)) :=
      MatchingProbability.probability_union_le _ (weight_nonneg k) _ _
    _ ≤ _ := by linarith

/-- The expectation formula also includes the empty population. -/
theorem expected_count (k : ℕ) (hk : k ≤ Fintype.card E) (S : Finset E) :
    (∑ T : Finset E, weight k T * (count S T : ℝ)) =
      ((k : ℝ) / Fintype.card E) * S.card := by
  classical
  by_cases hN : 0 < Fintype.card E
  · exact expected_count_nonempty k hN hk S
  · have hS : S = ∅ := by
      apply Finset.card_eq_zero.mp
      have hcard := Finset.card_le_univ S
      omega
    simp [hS, count]

/-- Chernoff's two-sided estimate for every valid uniform fixed-size sample,
including the degenerate empty population. -/
theorem chernoff (k : ℕ) (δ : ℝ) (hk : k ≤ Fintype.card E)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (S : Finset E) :
    probability k (fun T => δ * (((k : ℝ) / Fintype.card E) * S.card) ≤
      |(count S T : ℝ) - ((k : ℝ) / Fintype.card E) * S.card|) ≤
      2 * Real.exp (-δ ^ 2 * (((k : ℝ) / Fintype.card E) * S.card) / 3) := by
  classical
  by_cases hN : 0 < Fintype.card E
  · exact chernoff_nonempty k δ hN hk hδ hδ1 S
  · have hS : S = ∅ := by
      apply Finset.card_eq_zero.mp
      have hcard := Finset.card_le_univ S
      omega
    have hprob : probability k (fun _ : Finset E => True) = 1 := by
      simpa only [probability, MatchingProbability.probability, Finset.filter_true]
        using sum_weight (E := E) k hk
    simpa [hS, count] using hprob.le.trans (by norm_num : (1 : ℝ) ≤ 2)

end Overfull.Hypergeometric
