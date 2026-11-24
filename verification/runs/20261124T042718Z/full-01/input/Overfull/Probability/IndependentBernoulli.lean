import Overfull.Probability.Concentration

/-!
# Chernoff bounds for independent Bernoulli variables

Each coordinate has its own success probability. The finite product mass is
normalized, its joint assignment probabilities factor, and the exponential
moment is calculated from that mass before the tail estimate is applied.
-/

namespace Overfull.IndependentBernoulli

open Finset Classical
open scoped BigOperators

variable {E : Type*} [Fintype E]

noncomputable def weight (p : E → ℝ) (ω : E → Bool) : ℝ :=
  ∏ e, Bernoulli.mass (p e) (ω e)

noncomputable def probability (p : E → ℝ) (P : (E → Bool) → Prop) : ℝ :=
  MatchingProbability.probability (weight p) P

theorem weight_nonneg (p : E → ℝ) (hp : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    (ω : E → Bool) : 0 ≤ weight p ω := by
  classical
  apply Finset.prod_nonneg
  intro e _
  unfold Bernoulli.mass
  split_ifs <;> linarith [hp e, hp1 e]

theorem sum_weight (p : E → ℝ) : (∑ ω : E → Bool, weight p ω) = 1 := by
  classical
  unfold weight
  rw [Bernoulli.sum_product]
  simp [Bernoulli.mass]

theorem expectation_product (p : E → ℝ) (f : E → Bool → ℝ) :
    (∑ ω : E → Bool, weight p ω * ∏ e, f e (ω e)) =
      ∏ e, (Bernoulli.mass (p e) false * f e false +
        Bernoulli.mass (p e) true * f e true) := by
  classical
  simp only [weight, ← Finset.prod_mul_distrib]
  exact Bernoulli.sum_product (fun e b => Bernoulli.mass (p e) b * f e b)

/-- Exact joint probabilities verify independence of the coordinates. -/
theorem probability_assignment (p : E → ℝ) (S : Finset E) (σ : E → Bool) :
    probability p (fun ω => ∀ e ∈ S, ω e = σ e) =
      ∏ e ∈ S, Bernoulli.mass (p e) (σ e) := by
  classical
  let f := fun (e : E) (b : Bool) => if e ∈ S → b = σ e then (1 : ℝ) else 0
  calc
    _ = ∑ ω : E → Bool, weight p ω * ∏ e, f e (ω e) := by
      simp only [probability, MatchingProbability.probability, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro ω _
      by_cases hω : ∀ e ∈ S, ω e = σ e
      · rw [if_pos hω]
        have hprod : (∏ e : E, f e (ω e)) = 1 := by
          apply Finset.prod_eq_one
          intro e _
          exact if_pos (hω e)
        rw [hprod, mul_one]
      · rw [if_neg hω]
        push_neg at hω
        obtain ⟨e, he, hne⟩ := hω
        have hprod : (∏ e : E, f e (ω e)) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ e) (by simp [f, he, hne])
        rw [hprod, mul_zero]
    _ = ∏ e, (Bernoulli.mass (p e) false * f e false +
        Bernoulli.mass (p e) true * f e true) := expectation_product p f
    _ = ∏ e : E, if e ∈ S then Bernoulli.mass (p e) (σ e) else 1 := by
      apply Finset.prod_congr rfl
      intro e _
      by_cases he : e ∈ S <;> cases hσ : σ e <;>
        simp [f, he, hσ, Bernoulli.mass]
    _ = _ := by rw [← Finset.prod_filter]; simp

theorem probability_retained (p : E → ℝ) (e : E) :
    probability p (fun ω => ω e = true) = p e := by
  classical
  simpa [Bernoulli.mass] using probability_assignment p {e} (fun _ => true)

theorem probability_nonneg (p : E → ℝ) (hp : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    (P : (E → Bool) → Prop) : 0 ≤ probability p P :=
  MatchingProbability.probability_nonneg _ (weight_nonneg p hp hp1) P

theorem probability_mono (p : E → ℝ) (hp : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    {P Q : (E → Bool) → Prop} (h : ∀ ω, P ω → Q ω) :
    probability p P ≤ probability p Q :=
  MatchingProbability.probability_mono _ (weight_nonneg p hp hp1) h

theorem expected_retainedCount (p : E → ℝ) (S : Finset E) :
    (∑ ω : E → Bool, weight p ω * (Bernoulli.retainedCount S ω : ℝ)) =
      ∑ e ∈ S, p e := by
  classical
  simp_rw [Bernoulli.retainedCount_eq_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ e : E, if e ∈ S then p e else 0 := by
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
          _ = p e := probability_retained p e
      · simp [he]
    _ = _ := by rw [← Finset.sum_filter]; simp

theorem exponential_moment (p : E → ℝ) (S : Finset E) (t : ℝ) :
    (∑ ω : E → Bool, weight p ω * Real.exp (t * (Bernoulli.retainedCount S ω : ℝ))) =
      ∏ e ∈ S, (1 - p e + p e * Real.exp t) := by
  classical
  simp only [Bernoulli.exp_count_product]
  rw [expectation_product p (fun e b => if e ∈ S ∧ b = true then Real.exp t else 1)]
  calc
    _ = ∏ e : E, if e ∈ S then 1 - p e + p e * Real.exp t else 1 := by
      apply Finset.prod_congr rfl
      intro e _
      by_cases he : e ∈ S <;> simp [he, Bernoulli.mass]
    _ = _ := by rw [← Finset.prod_filter]; simp

theorem exponential_moment_le (p : E → ℝ) (hp : ∀ e, 0 ≤ p e)
    (hp1 : ∀ e, p e ≤ 1) (S : Finset E) (t : ℝ) :
    (∑ ω : E → Bool, weight p ω * Real.exp (t * (Bernoulli.retainedCount S ω : ℝ))) ≤
      Real.exp ((∑ e ∈ S, p e) * (Real.exp t - 1)) := by
  classical
  rw [exponential_moment]
  calc
    _ ≤ ∏ e ∈ S, Real.exp (p e * (Real.exp t - 1)) := by
      apply Finset.prod_le_prod
      · intro e _
        exact add_nonneg (sub_nonneg.mpr (hp1 e))
          (mul_nonneg (hp e) (Real.exp_pos _).le)
      · intro e _
        have h := Real.add_one_le_exp (p e * (Real.exp t - 1))
        nlinarith
    _ = _ := by rw [← Real.exp_sum, ← Finset.sum_mul]

theorem exponential_tail (p : E → ℝ) (hp : ∀ e, 0 ≤ p e)
    (hp1 : ∀ e, p e ≤ 1) (S : Finset E) (t a : ℝ) (P : (E → Bool) → Prop)
    (hP : ∀ ω, P ω → t * a ≤ t * (Bernoulli.retainedCount S ω : ℝ)) :
    probability p P ≤ Real.exp ((∑ e ∈ S, p e) * (Real.exp t - 1) - t * a) := by
  have hm := MatchingProbability.probability_markov (weight p)
    (weight_nonneg p hp hp1)
    (fun ω => Real.exp (t * (Bernoulli.retainedCount S ω : ℝ)))
    (fun _ => (Real.exp_pos _).le) (Real.exp (t * a)) P
    (fun ω h => Real.exp_le_exp.mpr (hP ω h))
  have hb := exponential_moment_le p hp hp1 S t
  change Real.exp (t * a) * probability p P ≤ _ at hm
  have hmul := mul_le_mul_of_nonneg_left (hm.trans hb) (Real.exp_pos (-t * a)).le
  have hc : Real.exp (-t * a) * Real.exp (t * a) = 1 := by
    rw [← Real.exp_add, show -t * a + t * a = 0 by ring, Real.exp_zero]
  rw [← mul_assoc, hc, one_mul, ← Real.exp_add] at hmul
  convert hmul using 1
  congr 1
  ring

theorem chernoff_upper (p : E → ℝ) (δ : ℝ) (hp : ∀ e, 0 ≤ p e)
    (hp1 : ∀ e, p e ≤ 1) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (S : Finset E) :
    probability p (fun ω => (1 + δ) * (∑ e ∈ S, p e) ≤
      (Bernoulli.retainedCount S ω : ℝ)) ≤
      Real.exp (-δ ^ 2 * (∑ e ∈ S, p e) / 3) := by
  have hμ : 0 ≤ ∑ e ∈ S, p e := Finset.sum_nonneg (fun e _ => hp e)
  have ht : 0 ≤ δ / 2 := by positivity
  have htail := exponential_tail p hp hp1 S (δ / 2) ((1 + δ) * (∑ e ∈ S, p e))
    (fun ω => (1 + δ) * (∑ e ∈ S, p e) ≤ (Bernoulli.retainedCount S ω : ℝ))
    (fun _ h => mul_le_mul_of_nonneg_left h ht)
  refine htail.trans (Real.exp_le_exp.mpr ?_)
  have hq := Bernoulli.exp_quadratic_bound (δ / 2)
    (by rw [abs_of_nonneg ht]; linarith)
  have hmul := mul_le_mul_of_nonneg_left hq hμ
  nlinarith

theorem chernoff_lower (p : E → ℝ) (δ : ℝ) (hp : ∀ e, 0 ≤ p e)
    (hp1 : ∀ e, p e ≤ 1) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (S : Finset E) :
    probability p (fun ω => (Bernoulli.retainedCount S ω : ℝ) ≤
      (1 - δ) * (∑ e ∈ S, p e)) ≤
      Real.exp (-δ ^ 2 * (∑ e ∈ S, p e) / 3) := by
  have hμ : 0 ≤ ∑ e ∈ S, p e := Finset.sum_nonneg (fun e _ => hp e)
  have ht : -δ / 2 ≤ 0 := by linarith
  have htail := exponential_tail p hp hp1 S (-δ / 2) ((1 - δ) * (∑ e ∈ S, p e))
    (fun ω => (Bernoulli.retainedCount S ω : ℝ) ≤ (1 - δ) * (∑ e ∈ S, p e))
    (fun _ h => mul_le_mul_of_nonpos_left h ht)
  refine htail.trans (Real.exp_le_exp.mpr ?_)
  have hq := Bernoulli.exp_quadratic_bound (-δ / 2)
    (by rw [abs_of_nonpos ht]; linarith)
  have hmul := mul_le_mul_of_nonneg_left hq hμ
  nlinarith

/-- The two-sided Chernoff bound, without an identical-distribution assumption. -/
theorem chernoff (p : E → ℝ) (δ : ℝ) (hp : ∀ e, 0 ≤ p e)
    (hp1 : ∀ e, p e ≤ 1) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (S : Finset E) :
    probability p (fun ω => δ * (∑ e ∈ S, p e) ≤
      |(Bernoulli.retainedCount S ω : ℝ) - ∑ e ∈ S, p e|) ≤
      2 * Real.exp (-δ ^ 2 * (∑ e ∈ S, p e) / 3) := by
  classical
  have hupper := chernoff_upper p δ hp hp1 hδ hδ1 S
  have hlower := chernoff_lower p δ hp hp1 hδ hδ1 S
  calc
    _ ≤ probability p (fun ω =>
        (1 + δ) * (∑ e ∈ S, p e) ≤ (Bernoulli.retainedCount S ω : ℝ) ∨
        (Bernoulli.retainedCount S ω : ℝ) ≤ (1 - δ) * (∑ e ∈ S, p e)) := by
      apply probability_mono p hp hp1
      intro ω hω
      rcases le_abs.mp hω with h | h
      · left; nlinarith
      · right; nlinarith
    _ ≤ probability p (fun ω => (1 + δ) * (∑ e ∈ S, p e) ≤
        (Bernoulli.retainedCount S ω : ℝ)) +
        probability p (fun ω => (Bernoulli.retainedCount S ω : ℝ) ≤
          (1 - δ) * (∑ e ∈ S, p e)) :=
      MatchingProbability.probability_union_le _ (weight_nonneg p hp hp1) _ _
    _ ≤ _ := by linarith

/-- A finite family with the product joint law has the same expectation as
its canonical Boolean product model, for every real-valued function. -/
theorem expectation_of_joint_law {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (X : Ω → E → Bool) (p : E → ℝ)
    (hjoint : ∀ σ : E → Bool,
      MatchingProbability.probability w (fun ω => X ω = σ) = weight p σ)
    (f : (E → Bool) → ℝ) :
    (∑ ω : Ω, w ω * f (X ω)) = ∑ σ : E → Bool, weight p σ * f σ := by
  classical
  symm
  simp_rw [← hjoint, MatchingProbability.probability, Finset.sum_filter,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp only [ite_mul, zero_mul]
  simp

/-- The mean of the sum is unchanged when transported by the joint law. -/
theorem expected_count_of_joint_law {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (X : Ω → E → Bool) (p : E → ℝ)
    (hjoint : ∀ σ : E → Bool,
      MatchingProbability.probability w (fun ω => X ω = σ) = weight p σ)
    (S : Finset E) :
    (∑ ω : Ω, w ω * (Bernoulli.retainedCount S (X ω) : ℝ)) = ∑ e ∈ S, p e := by
  exact (expectation_of_joint_law w X p hjoint
    (fun σ => (Bernoulli.retainedCount S σ : ℝ))).trans (expected_retainedCount p S)

/-- Event probabilities transfer from the actual joint law. -/
theorem probability_of_joint_law {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (X : Ω → E → Bool) (p : E → ℝ)
    (hjoint : ∀ σ : E → Bool,
      MatchingProbability.probability w (fun ω => X ω = σ) = weight p σ)
    (P : (E → Bool) → Prop) :
    MatchingProbability.probability w (fun ω => P (X ω)) = probability p P := by
  classical
  have h := expectation_of_joint_law w X p hjoint (fun σ => if P σ then 1 else 0)
  simpa only [probability, MatchingProbability.probability, Finset.sum_filter,
    mul_ite, mul_one, mul_zero] using h

/-- The Chernoff bound for an arbitrary finite probability space whose
indicator variables have the independent Bernoulli joint probabilities. -/
theorem chernoff_of_independent_indicators {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (X : Ω → E → Bool) (p : E → ℝ) (δ : ℝ)
    (hp : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    (hindependent : ∀ (S : Finset E) (σ : E → Bool),
      MatchingProbability.probability w (fun ω => ∀ e ∈ S, X ω e = σ e) =
        ∏ e ∈ S, Bernoulli.mass (p e) (σ e))
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (S : Finset E) :
    MatchingProbability.probability w (fun ω => δ * (∑ e ∈ S, p e) ≤
      |(Bernoulli.retainedCount S (X ω) : ℝ) - ∑ e ∈ S, p e|) ≤
      2 * Real.exp (-δ ^ 2 * (∑ e ∈ S, p e) / 3) := by
  classical
  have hjoint (σ : E → Bool) :
      MatchingProbability.probability w (fun ω => X ω = σ) = weight p σ := by
    have h := hindependent univ σ
    simpa only [Finset.mem_univ, forall_const, ← funext_iff, weight] using h
  rw [probability_of_joint_law w X p hjoint (fun σ =>
    δ * (∑ e ∈ S, p e) ≤ |(Bernoulli.retainedCount S σ : ℝ) - ∑ e ∈ S, p e|)]
  exact chernoff p δ hp hp1 hδ hδ1 S

end Overfull.IndependentBernoulli
