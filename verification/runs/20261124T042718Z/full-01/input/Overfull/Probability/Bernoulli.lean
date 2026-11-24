import Overfull.MatchingProbability
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Finite independent edge sampling

The sample space is the set of all Boolean choices on a finite edge type.
Its probability mass is the product of the Bernoulli masses. All probabilities
below are finite sums of these masses.
-/

namespace Overfull.Bernoulli

open Finset Classical
open scoped BigOperators

variable {E : Type*} [Fintype E]

noncomputable def mass (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

noncomputable def weight (p : ℝ) (ω : E → Bool) : ℝ := ∏ e, mass p (ω e)

noncomputable def probability (p : ℝ) (P : (E → Bool) → Prop) : ℝ :=
  MatchingProbability.probability (weight p) P

noncomputable def retainedCount (S : Finset E) (ω : E → Bool) : ℕ :=
  (S.filter (fun e => ω e = true)).card

theorem sum_product (f : E → Bool → ℝ) :
    (∑ ω : E → Bool, ∏ e, f e (ω e)) =
      ∏ e, (f e false + f e true) := by
  classical
  simpa [Fintype.sum_bool, add_comm] using
    (Finset.prod_univ_sum (fun _ : E => (univ : Finset Bool)) f).symm

theorem weight_nonneg (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (ω : E → Bool) :
    0 ≤ weight p ω := by
  classical
  apply Finset.prod_nonneg
  intro e _
  unfold mass
  split_ifs <;> linarith

theorem sum_weight (p : ℝ) : (∑ ω : E → Bool, weight p ω) = 1 := by
  classical
  unfold weight
  rw [sum_product]
  simp [mass]

/-- Coordinate products factor under the explicitly defined probability mass. -/
theorem expectation_product (p : ℝ) (f : E → Bool → ℝ) :
    (∑ ω : E → Bool, weight p ω * ∏ e, f e (ω e)) =
      ∏ e, (mass p false * f e false + mass p true * f e true) := by
  classical
  simp only [weight, ← Finset.prod_mul_distrib]
  exact sum_product (fun e b => mass p b * f e b)

/-- The joint probabilities of any prescribed coordinate values are the
products of their Bernoulli masses. This verifies independence, not just
the normalization of the sample weights. -/
theorem probability_assignment (p : ℝ) (S : Finset E) (σ : E → Bool) :
    probability p (fun ω => ∀ e ∈ S, ω e = σ e) = ∏ e ∈ S, mass p (σ e) := by
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
    _ = ∏ e, (mass p false * f e false + mass p true * f e true) :=
      expectation_product p f
    _ = ∏ e : E, if e ∈ S then mass p (σ e) else 1 := by
      apply Finset.prod_congr rfl
      intro e _
      by_cases he : e ∈ S <;> cases hσ : σ e <;> simp [f, he, hσ, mass]
    _ = _ := by rw [← Finset.prod_filter]; simp

theorem probability_retained (p : ℝ) (e : E) :
    probability p (fun ω => ω e = true) = p := by
  classical
  simpa [mass] using probability_assignment p {e} (fun _ => true)

theorem probability_nonneg (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (P : (E → Bool) → Prop) : 0 ≤ probability p P :=
  MatchingProbability.probability_nonneg _ (weight_nonneg p hp hp1) P

theorem probability_compl (p : ℝ) (P : (E → Bool) → Prop) :
    probability p (fun ω => ¬ P ω) = 1 - probability p P := by
  classical
  have h : probability p P + probability p (fun ω => ¬ P ω) = 1 := by
    calc
      _ = ∑ ω : E → Bool, weight p ω := by
        simp only [probability, MatchingProbability.probability, Finset.sum_filter,
          ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro ω _
        by_cases hω : P ω <;> simp [hω]
      _ = 1 := sum_weight p
  linarith

theorem probability_mono (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    {P Q : (E → Bool) → Prop} (h : ∀ ω, P ω → Q ω) :
    probability p P ≤ probability p Q :=
  MatchingProbability.probability_mono _ (weight_nonneg p hp hp1) h

theorem probability_union_le (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (P Q : (E → Bool) → Prop) :
    probability p (fun ω => P ω ∨ Q ω) ≤ probability p P + probability p Q :=
  MatchingProbability.probability_union_le _ (weight_nonneg p hp hp1) P Q

theorem exists_not_of_probability_lt_one (p : ℝ) (P : (E → Bool) → Prop)
    (h : probability p P < 1) : ∃ ω, ¬ P ω := by
  classical
  by_contra hnot
  push_neg at hnot
  have hall : probability p P = 1 := by
    unfold probability MatchingProbability.probability
    rw [Finset.sum_filter]
    calc
      _ = ∑ ω : E → Bool, weight p ω := by
        apply Finset.sum_congr rfl
        intro ω _
        exact if_pos (hnot ω)
      _ = 1 := sum_weight p
  linarith

theorem probability_exists_le_sum {I : Type*} (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (S : Finset I) (P : I → (E → Bool) → Prop) :
    probability p (fun ω => ∃ i ∈ S, P i ω) ≤
      ∑ i ∈ S, probability p (P i) :=
  MatchingProbability.probability_exists_le_sum _ (weight_nonneg p hp hp1) S P

theorem retainedCount_eq_sum (S : Finset E) (ω : E → Bool) :
    (retainedCount S ω : ℝ) = ∑ e : E, if e ∈ S ∧ ω e = true then 1 else 0 := by
  classical
  have heq : S.filter (fun e => ω e = true) =
      univ.filter (fun e => e ∈ S ∧ ω e = true) := by
    ext e
    simp
  simp [retainedCount, heq, Finset.sum_boole]

theorem exp_neg_half_count (S : Finset E) (ω : E → Bool) :
    Real.exp (-(retainedCount S ω : ℝ) / 2) =
      ∏ e : E, if e ∈ S ∧ ω e = true then Real.exp (-(1 : ℝ) / 2) else 1 := by
  classical
  rw [retainedCount_eq_sum]
  have hsum : -(∑ e : E, if e ∈ S ∧ ω e = true then (1 : ℝ) else 0) / 2 =
      ∑ e : E, if e ∈ S ∧ ω e = true then -(1 : ℝ) / 2 else 0 := by
    rw [← Finset.sum_neg_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro e _
    split_ifs <;> norm_num
  rw [hsum, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro e _
  split_ifs <;> simp

/-- Factorization of the exponential moment follows from the actual
product probability mass, including all unused coordinates. -/
theorem exponential_moment (p : ℝ) (S : Finset E) :
    (∑ ω : E → Bool, weight p ω * Real.exp (-(retainedCount S ω : ℝ) / 2)) =
      (1 - p + p * Real.exp (-(1 : ℝ) / 2)) ^ S.card := by
  classical
  simp only [weight, exp_neg_half_count, ← Finset.prod_mul_distrib]
  rw [sum_product (fun e b => mass p b *
    (if e ∈ S ∧ b = true then Real.exp (-(1 : ℝ) / 2) else 1))]
  have heq (e : E) :
      mass p false * (if e ∈ S ∧ false = true then Real.exp (-(1 : ℝ) / 2) else 1) +
        mass p true * (if e ∈ S ∧ true = true then Real.exp (-(1 : ℝ) / 2) else 1) =
      if e ∈ S then 1 - p + p * Real.exp (-(1 : ℝ) / 2) else 1 := by
    by_cases he : e ∈ S <;> simp [he, mass]
  calc
    _ = ∏ e : E, if e ∈ S then 1 - p + p * Real.exp (-(1 : ℝ) / 2) else 1 := by
      apply Finset.prod_congr rfl
      intro e _
      exact heq e
    _ = _ := by rw [← Finset.prod_filter]; simp

theorem exp_neg_half_le : Real.exp (-(1 : ℝ) / 2) ≤ 2 / 3 := by
  classical
  have h := Real.add_one_le_exp ((1 : ℝ) / 2)
  have hp := Real.exp_pos ((1 : ℝ) / 2)
  rw [show -(1 : ℝ) / 2 = -((1 : ℝ) / 2) by ring, Real.exp_neg]
  rw [inv_eq_one_div]
  apply (div_le_iff₀ hp).2
  linarith

theorem exponential_moment_le (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (S : Finset E) :
    (∑ ω : E → Bool, weight p ω * Real.exp (-(retainedCount S ω : ℝ) / 2)) ≤
      Real.exp (-p * S.card / 3) := by
  classical
  rw [exponential_moment]
  have hbase : 1 - p + p * Real.exp (-(1 : ℝ) / 2) ≤ Real.exp (-p / 3) := by
    have h := mul_le_mul_of_nonneg_left exp_neg_half_le hp
    have he := Real.add_one_le_exp (-p / 3)
    linarith
  have hnonneg : 0 ≤ 1 - p + p * Real.exp (-(1 : ℝ) / 2) :=
    add_nonneg (sub_nonneg.mpr hp1) (mul_nonneg hp (Real.exp_pos _).le)
  calc
    _ ≤ Real.exp (-p / 3) ^ S.card := pow_le_pow_left₀ hnonneg hbase _
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

/-- A direct half-mean lower-tail bound. The constant is sufficient for
the manuscript's random-reserve lemma. -/
theorem half_mean_lower_tail (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (S : Finset E) :
    probability p (fun ω => (retainedCount S ω : ℝ) < p * S.card / 2) ≤
      Real.exp (-p * S.card / 12) := by
  classical
  have hm := MatchingProbability.probability_markov (weight p)
    (weight_nonneg p hp hp1)
    (fun ω => Real.exp (-(retainedCount S ω : ℝ) / 2))
    (fun _ => (Real.exp_pos _).le)
    (Real.exp (-p * S.card / 4))
    (fun ω => (retainedCount S ω : ℝ) < p * S.card / 2)
    (fun ω h => Real.exp_le_exp.mpr (by linarith))
  have hmoment := exponential_moment_le p hp hp1 S
  change Real.exp (-p * S.card / 4) * probability p _ ≤ _ at hm
  have hprod := le_trans hm hmoment
  have hmul := mul_le_mul_of_nonneg_left hprod (Real.exp_pos (p * S.card / 4)).le
  have hcancel : Real.exp (p * S.card / 4) * Real.exp (-p * S.card / 4) = 1 := by
    rw [← Real.exp_add]
    rw [show p * S.card / 4 + -p * S.card / 4 = 0 by ring, Real.exp_zero]
  rw [← mul_assoc, hcancel, one_mul, ← Real.exp_add] at hmul
  have harg : p * S.card / 4 + -p * S.card / 3 = -p * S.card / 12 := by ring
  simpa only [harg] using hmul

end Overfull.Bernoulli
