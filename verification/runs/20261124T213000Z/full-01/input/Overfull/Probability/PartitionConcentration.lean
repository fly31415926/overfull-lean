import Overfull.Probability.ProductMoments

/-!
# Exponential lower tails for independent fixed-size part samples

Every coordinate is sampled uniformly at its prescribed integer size. The
exponential moment factors under the actual product weights, including empty
coordinate populations. No independence of individual vertices within a part
is assumed.
-/

noncomputable section

namespace Overfull.PartitionConcentration

open Finset Classical FiniteProbability

private theorem part_exponential_moment_le {E : Type*} [Fintype E]
    (s : ℕ) (hs : s ≤ Fintype.card E) (R : Finset E) (t : ℝ) :
    mean (Hypergeometric.weight s)
      (fun T => Real.exp (t * (Hypergeometric.count R T : ℝ))) ≤
        Real.exp (((s : ℝ) / Fintype.card E) * R.card * (Real.exp t - 1)) := by
  classical
  by_cases hE : 0 < Fintype.card E
  · exact Hypergeometric.exponential_moment_le s hE hs R t
  · have hR : R = ∅ := by
      apply Finset.card_eq_zero.mp
      have hcard := Finset.card_le_univ R
      omega
    have hmean := mean_const (Hypergeometric.weight (E := E) s)
      (Hypergeometric.sum_weight s hs) 1
    simpa [hR, Hypergeometric.count] using hmean.le

variable {ι : Type*} [Fintype ι] {κ : ι → Type*} [∀ i, Fintype (κ i)]

/-- Total selected representatives across the independent coordinate samples. -/
def count (R : ∀ i, Finset (κ i)) (T : ∀ i, Finset (κ i)) : ℝ :=
  ∑ i, (Hypergeometric.count (R i) (T i) : ℝ)

/-- The sum of the actual hypergeometric coordinate means. -/
def expectedCount (s : ι → ℕ) (R : ∀ i, Finset (κ i)) : ℝ :=
  ∑ i, ((s i : ℝ) / Fintype.card (κ i)) * (R i).card

theorem expectedCount_nonneg (s : ι → ℕ) (R : ∀ i, Finset (κ i)) :
    0 ≤ expectedCount s R :=
  Finset.sum_nonneg (fun _ _ => by positivity)

/-- Product factorization of the actual coordinate laws gives the exponential
moment bound for the total selected representative count. -/
theorem exponential_moment_le (s : ι → ℕ)
    (hs : ∀ i, s i ≤ Fintype.card (κ i)) (R : ∀ i, Finset (κ i)) (t : ℝ) :
    mean (piWeight (fun i => Hypergeometric.weight (E := κ i) (s i)))
      (fun T => Real.exp (t * count R T)) ≤
        Real.exp (expectedCount s R * (Real.exp t - 1)) := by
  classical
  have hfun : (fun T => Real.exp (t * count R T)) =
      (fun T => ∏ i, Real.exp (t * (Hypergeometric.count (R i) (T i) : ℝ))) := by
    funext T
    rw [count, Finset.mul_sum, Real.exp_sum]
  rw [hfun, mean_pi_product
    (fun i => Hypergeometric.weight (E := κ i) (s i))
    (fun i T => Real.exp (t * (Hypergeometric.count (R i) T : ℝ)))]
  calc
    _ ≤ ∏ i, Real.exp (((s i : ℝ) / Fintype.card (κ i)) * (R i).card *
        (Real.exp t - 1)) := by
      apply Finset.prod_le_prod
      · intro i _
        exact mean_nonneg _ (Hypergeometric.weight_nonneg _) _
          (fun _ => (Real.exp_pos _).le)
      · intro i _
        exact part_exponential_moment_le (s i) (hs i) (R i) t
    _ = _ := by rw [← Real.exp_sum, ← Finset.sum_mul]; rfl

/-- Markov's inequality applied to the derived exponential moment. -/
theorem exponential_tail (s : ι → ℕ)
    (hs : ∀ i, s i ≤ Fintype.card (κ i)) (R : ∀ i, Finset (κ i))
    (t a : ℝ) (P : (∀ i, Finset (κ i)) → Prop)
    (hP : ∀ T, P T → t * a ≤ t * count R T) :
    MatchingProbability.probability
      (piWeight (fun i => Hypergeometric.weight (E := κ i) (s i))) P ≤
        Real.exp (expectedCount s R * (Real.exp t - 1) - t * a) := by
  have hm := MatchingProbability.probability_markov
    (piWeight (fun i => Hypergeometric.weight (E := κ i) (s i)))
    (piWeight_nonneg _ (fun i => Hypergeometric.weight_nonneg _))
    (fun T => Real.exp (t * count R T)) (fun _ => (Real.exp_pos _).le)
    (Real.exp (t * a)) P (fun T h => Real.exp_le_exp.mpr (hP T h))
  have hb := exponential_moment_le s hs R t
  change Real.exp (t * a) * MatchingProbability.probability _ P ≤ _ at hm
  have hmul := mul_le_mul_of_nonneg_left (hm.trans hb) (Real.exp_pos (-t * a)).le
  have hc : Real.exp (-t * a) * Real.exp (t * a) = 1 := by
    rw [← Real.exp_add, show -t * a + t * a = 0 by ring, Real.exp_zero]
  rw [← mul_assoc, hc, one_mul, ← Real.exp_add] at hmul
  convert hmul using 1
  congr 1
  ring

/-- A lower Chernoff bound for the sum of independent without-replacement
coordinate counts, with their actual total mean. -/
theorem chernoff_lower (s : ι → ℕ)
    (hs : ∀ i, s i ≤ Fintype.card (κ i)) (R : ∀ i, Finset (κ i))
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    MatchingProbability.probability
      (piWeight (fun i => Hypergeometric.weight (E := κ i) (s i)))
      (fun T => count R T ≤ (1 - δ) * expectedCount s R) ≤
        Real.exp (-δ ^ 2 * expectedCount s R / 3) := by
  have hμ := expectedCount_nonneg s R
  have ht : -δ / 2 ≤ 0 := by linarith
  have htail := exponential_tail s hs R (-δ / 2)
    ((1 - δ) * expectedCount s R)
    (fun T => count R T ≤ (1 - δ) * expectedCount s R)
    (fun _ h => mul_le_mul_of_nonpos_left h ht)
  refine htail.trans (Real.exp_le_exp.mpr ?_)
  have hq := Bernoulli.exp_quadratic_bound (-δ / 2)
    (by rw [abs_of_nonpos ht]; linarith)
  have hmul := mul_le_mul_of_nonneg_left hq hμ
  nlinarith

/-- The exponential half-mean tail needed when the number of ordinary
vertices grows with the graph order. -/
theorem half_mean_lower_tail (s : ι → ℕ)
    (hs : ∀ i, s i ≤ Fintype.card (κ i)) (R : ∀ i, Finset (κ i)) :
    MatchingProbability.probability
      (piWeight (fun i => Hypergeometric.weight (E := κ i) (s i)))
      (fun T => count R T < expectedCount s R / 2) ≤
        Real.exp (-expectedCount s R / 12) := by
  apply le_trans (MatchingProbability.probability_mono _
    (piWeight_nonneg _ (fun i => Hypergeometric.weight_nonneg _))
    (fun T hT => show count R T ≤ (1 - (1 / 2 : ℝ)) * expectedCount s R by
      linarith))
  have h := chernoff_lower s hs R (1 / 2) (by norm_num) (by norm_num)
  convert h using 1
  congr 1
  ring

end Overfull.PartitionConcentration
