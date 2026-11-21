import Overfull.Probability.Bernoulli

/-!
# Concentration for the finite independent sampling model

The two-sided bound has the constant used in the manuscript. It is proved
for the actual finite Bernoulli product distribution; the hypergeometric
part of the manuscript's concentration lemma is a separate assertion.
-/

namespace Overfull.Bernoulli

open Finset Classical
open scoped BigOperators

variable {E : Type*} [Fintype E]

theorem expected_retainedCount (p : ℝ) (S : Finset E) :
    (∑ ω : E → Bool, weight p ω * (retainedCount S ω : ℝ)) = p * S.card := by
  classical
  simp_rw [retainedCount_eq_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ e : E, if e ∈ S then p else 0 := by
      apply Finset.sum_congr rfl
      intro e _
      by_cases he : e ∈ S
      · simp only [he, true_and, if_true]
        calc
          _ = probability p (fun ω => ω e = true) := by
            simp only [probability, MatchingProbability.probability, Finset.sum_filter,
              mul_ite, mul_one, mul_zero]
            apply Finset.sum_congr rfl
            intro ω _
            by_cases hω : ω e = true <;> simp [hω]
          _ = p := probability_retained p e
      · simp [he]
    _ = _ := by rw [← Finset.sum_filter]; simp; ring

theorem exp_count_product (S : Finset E) (ω : E → Bool) (t : ℝ) :
    Real.exp (t * (retainedCount S ω : ℝ)) =
      ∏ e : E, if e ∈ S ∧ ω e = true then Real.exp t else 1 := by
  classical
  rw [retainedCount_eq_sum, Finset.mul_sum, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro e _
  split_ifs <;> simp

theorem exponential_moment_general (p : ℝ) (S : Finset E) (t : ℝ) :
    (∑ ω : E → Bool, weight p ω * Real.exp (t * (retainedCount S ω : ℝ))) =
      (1 - p + p * Real.exp t) ^ S.card := by
  classical
  simp only [exp_count_product]
  rw [expectation_product p (fun e b => if e ∈ S ∧ b = true then Real.exp t else 1)]
  calc
    _ = ∏ e : E, if e ∈ S then 1 - p + p * Real.exp t else 1 := by
      apply Finset.prod_congr rfl
      intro e _
      by_cases he : e ∈ S <;> simp [he, mass]
    _ = _ := by rw [← Finset.prod_filter]; simp

theorem exponential_moment_general_le (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (S : Finset E) (t : ℝ) :
    (∑ ω : E → Bool, weight p ω * Real.exp (t * (retainedCount S ω : ℝ))) ≤
      Real.exp (p * S.card * (Real.exp t - 1)) := by
  rw [exponential_moment_general]
  have hbase : 1 - p + p * Real.exp t ≤ Real.exp (p * (Real.exp t - 1)) := by
    have h := Real.add_one_le_exp (p * (Real.exp t - 1))
    nlinarith
  have hnonneg : 0 ≤ 1 - p + p * Real.exp t :=
    add_nonneg (sub_nonneg.mpr hp1) (mul_nonneg hp (Real.exp_pos _).le)
  calc
    _ ≤ Real.exp (p * (Real.exp t - 1)) ^ S.card :=
      pow_le_pow_left₀ hnonneg hbase _
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

/-- A Taylor bound on the small interval needed by both tails. -/
theorem exp_quadratic_bound (t : ℝ) (ht : |t| ≤ 1 / 2) :
    Real.exp t ≤ 1 + t + (2 / 3 : ℝ) * t ^ 2 := by
  have ht1 : |t| ≤ 1 := by linarith
  have h := Real.exp_bound ht1 (n := 3) (by decide)
  norm_num [Finset.sum_range_succ] at h
  have hupper := (abs_le.mp h).2
  have habs := abs_nonneg t
  have hsq := sq_nonneg t
  have hcube : |t| ^ 3 ≤ t ^ 2 / 2 := by
    have hm := mul_le_mul_of_nonneg_right ht hsq
    rw [pow_succ, sq_abs]
    nlinarith
  nlinarith

theorem exponential_tail (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (S : Finset E) (t a : ℝ) (P : (E → Bool) → Prop)
    (hP : ∀ ω, P ω → t * a ≤ t * (retainedCount S ω : ℝ)) :
    probability p P ≤ Real.exp (p * S.card * (Real.exp t - 1) - t * a) := by
  have hm := MatchingProbability.probability_markov (weight p)
    (weight_nonneg p hp hp1)
    (fun ω => Real.exp (t * (retainedCount S ω : ℝ)))
    (fun _ => (Real.exp_pos _).le) (Real.exp (t * a)) P
    (fun ω h => Real.exp_le_exp.mpr (hP ω h))
  have hb := exponential_moment_general_le p hp hp1 S t
  change Real.exp (t * a) * probability p P ≤ _ at hm
  have hmul := mul_le_mul_of_nonneg_left (hm.trans hb) (Real.exp_pos (-t * a)).le
  have hc : Real.exp (-t * a) * Real.exp (t * a) = 1 := by
    rw [← Real.exp_add, show -t * a + t * a = 0 by ring, Real.exp_zero]
  rw [← mul_assoc, hc, one_mul, ← Real.exp_add] at hmul
  convert hmul using 1
  congr 1
  ring

theorem chernoff_upper (p δ : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (S : Finset E) :
    probability p (fun ω => (1 + δ) * (p * S.card) ≤ (retainedCount S ω : ℝ)) ≤
      Real.exp (-δ ^ 2 * (p * S.card) / 3) := by
  have hμ : 0 ≤ p * (S.card : ℝ) := mul_nonneg hp (Nat.cast_nonneg _)
  have ht : 0 ≤ δ / 2 := by positivity
  have htail := exponential_tail p hp hp1 S (δ / 2) ((1 + δ) * (p * S.card))
    (fun ω => (1 + δ) * (p * S.card) ≤ (retainedCount S ω : ℝ))
    (fun _ h => mul_le_mul_of_nonneg_left h ht)
  refine htail.trans (Real.exp_le_exp.mpr ?_)
  have hq := exp_quadratic_bound (δ / 2) (by rw [abs_of_nonneg ht]; linarith)
  have hmul := mul_le_mul_of_nonneg_left hq hμ
  nlinarith

theorem chernoff_lower (p δ : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (S : Finset E) :
    probability p (fun ω => (retainedCount S ω : ℝ) ≤ (1 - δ) * (p * S.card)) ≤
      Real.exp (-δ ^ 2 * (p * S.card) / 3) := by
  have hμ : 0 ≤ p * (S.card : ℝ) := mul_nonneg hp (Nat.cast_nonneg _)
  have ht : -δ / 2 ≤ 0 := by linarith
  have htail := exponential_tail p hp hp1 S (-δ / 2) ((1 - δ) * (p * S.card))
    (fun ω => (retainedCount S ω : ℝ) ≤ (1 - δ) * (p * S.card))
    (fun _ h => mul_le_mul_of_nonpos_left h ht)
  refine htail.trans (Real.exp_le_exp.mpr ?_)
  have hq := exp_quadratic_bound (-δ / 2) (by rw [abs_of_nonpos ht]; linarith)
  have hmul := mul_le_mul_of_nonneg_left hq hμ
  nlinarith

/-- Two-sided multiplicative Chernoff bound for an actual sampled edge set. -/
theorem chernoff (p δ : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (S : Finset E) :
    probability p (fun ω => δ * (p * S.card) ≤
      |(retainedCount S ω : ℝ) - p * S.card|) ≤
      2 * Real.exp (-δ ^ 2 * (p * S.card) / 3) := by
  classical
  have hupper := chernoff_upper p δ hp hp1 hδ hδ1 S
  have hlower := chernoff_lower p δ hp hp1 hδ hδ1 S
  calc
    _ ≤ probability p (fun ω =>
        (1 + δ) * (p * S.card) ≤ (retainedCount S ω : ℝ) ∨
        (retainedCount S ω : ℝ) ≤ (1 - δ) * (p * S.card)) := by
      apply probability_mono p hp hp1
      intro ω hω
      rcases le_abs.mp hω with h | h
      · left; nlinarith
      · right; nlinarith
    _ ≤ probability p (fun ω => (1 + δ) * (p * S.card) ≤ (retainedCount S ω : ℝ)) +
        probability p (fun ω => (retainedCount S ω : ℝ) ≤ (1 - δ) * (p * S.card)) :=
      MatchingProbability.probability_union_le _ (weight_nonneg p hp hp1) _ _
    _ ≤ _ := by linarith

/-- An additive tail estimate normalized by any upper bound on the number
of sampled coordinates. This is used for simultaneous reserve degrees. -/
theorem additive_chernoff (p a m : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (ha : 0 ≤ a) (hap : a ≤ p) (S : Finset E) (hSm : (S.card : ℝ) ≤ m) :
    probability p (fun ω => a * m ≤ |(retainedCount S ω : ℝ) - p * S.card|) ≤
      2 * Real.exp (-a ^ 2 * m / (3 * p)) := by
  classical
  let t := a / (2 * p)
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hthalf : t ≤ 1 / 2 := by
    dsimp [t]
    apply (div_le_iff₀ (by positivity : 0 < 2 * p)).2
    linarith
  have hm : 0 ≤ m := (Nat.cast_nonneg S.card).trans hSm
  have hμ : 0 ≤ p * (S.card : ℝ) := mul_nonneg hp.le (Nat.cast_nonneg _)
  have hcalc : (2 / 3 : ℝ) * p * m * t ^ 2 - t * a * m =
      -a ^ 2 * m / (3 * p) := by
    dsimp [t]
    field_simp
    ring
  have hupper : probability p (fun ω => p * S.card + a * m ≤
      (retainedCount S ω : ℝ)) ≤ Real.exp (-a ^ 2 * m / (3 * p)) := by
    have htail := exponential_tail p hp.le hp1 S t (p * S.card + a * m)
      (fun ω => p * S.card + a * m ≤ (retainedCount S ω : ℝ))
      (fun _ h => mul_le_mul_of_nonneg_left h ht)
    refine htail.trans (Real.exp_le_exp.mpr ?_)
    have hq := exp_quadratic_bound t (by rwa [abs_of_nonneg ht])
    have hmul := mul_le_mul_of_nonneg_left hq hμ
    have hsize := mul_le_mul_of_nonneg_left hSm
      (show 0 ≤ (2 / 3 : ℝ) * p * t ^ 2 by positivity)
    nlinarith
  have hlower : probability p (fun ω => (retainedCount S ω : ℝ) ≤
      p * S.card - a * m) ≤ Real.exp (-a ^ 2 * m / (3 * p)) := by
    have htail := exponential_tail p hp.le hp1 S (-t) (p * S.card - a * m)
      (fun ω => (retainedCount S ω : ℝ) ≤ p * S.card - a * m)
      (fun _ h => mul_le_mul_of_nonpos_left h (neg_nonpos.mpr ht))
    refine htail.trans (Real.exp_le_exp.mpr ?_)
    have hq := exp_quadratic_bound (-t) (by simpa only [abs_neg, abs_of_nonneg ht] using hthalf)
    have hmul := mul_le_mul_of_nonneg_left hq hμ
    have hsize := mul_le_mul_of_nonneg_left hSm
      (show 0 ≤ (2 / 3 : ℝ) * p * t ^ 2 by positivity)
    nlinarith
  calc
    _ ≤ probability p (fun ω => p * S.card + a * m ≤ (retainedCount S ω : ℝ) ∨
        (retainedCount S ω : ℝ) ≤ p * S.card - a * m) := by
      apply probability_mono p hp.le hp1
      intro ω hω
      rcases le_abs.mp hω with h | h
      · left; linarith
      · right; linarith
    _ ≤ probability p (fun ω => p * S.card + a * m ≤ (retainedCount S ω : ℝ)) +
        probability p (fun ω => (retainedCount S ω : ℝ) ≤ p * S.card - a * m) :=
      MatchingProbability.probability_union_le _ (weight_nonneg p hp.le hp1) _ _
    _ ≤ _ := by linarith

end Overfull.Bernoulli
