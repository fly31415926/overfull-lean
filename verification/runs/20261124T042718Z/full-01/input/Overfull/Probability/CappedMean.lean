import Overfull.Probability.WeightedSampling

/-!
# Lower bounds for capped finite means

A nonnegative random variable with variance at most its mean times `a`
retains a quantitative mean after truncation. The proof is finite
Cauchy--Schwarz; no concentration assertion is assumed.
-/

noncomputable section

namespace Overfull.FiniteProbability

open Finset Classical

variable {Ω : Type*} [Fintype Ω]

/-- A harmonic lower bound for the cap at a positive level. -/
theorem harmonic_le_cap (x ω ell : ℝ) (hx : 0 ≤ x)
    (hω : 0 < ω) (hell : 0 < ell) :
    ell * x / (ell / ω + x) ≤ min (ω * x) ell := by
  have hq : 0 < ell / ω := div_pos hell hω
  have hd : 0 < ell / ω + x := add_pos_of_pos_of_nonneg hq hx
  apply le_min
  · apply (div_le_iff₀ hd).mpr
    calc
      ell * x = (ω * x) * (ell / ω) := by field_simp
      _ ≤ (ω * x) * (ell / ω + x) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hx) (mul_nonneg hω.le hx)
  · apply (div_le_iff₀ hd).mpr
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hq.le) hell.le

/-- Finite Cauchy--Schwarz with the ratio and second-moment factors
needed for a capped expectation. Normalization is unnecessary here. -/
theorem mean_sq_le_ratio_second_moment (p : Ω → ℝ) (hp : ∀ i, 0 ≤ p i)
    (X : Ω → ℝ) (hX : ∀ i, 0 ≤ X i) (q : ℝ) (hq : 0 < q) :
    (mean p X) ^ 2 ≤
      mean p (fun i => X i / (q + X i)) * mean p (fun i => X i * (q + X i)) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul univ
    (r := fun i => p i * X i)
    (f := fun i => p i * (X i / (q + X i)))
    (g := fun i => p i * (X i * (q + X i)))
  · intro i _
    exact mul_nonneg (hp i) (div_nonneg (hX i) (add_nonneg hq.le (hX i)))
  · intro i _
    exact mul_nonneg (hp i) (mul_nonneg (hX i) (add_nonneg hq.le (hX i)))
  · intro i _
    have hd : q + X i ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg hq (hX i))
    field_simp

/-- A second-moment bound gives a lower bound for the capped mean,
including the zero-mean case. -/
theorem capped_mean_lower_of_second_moment
    (p : Ω → ℝ) (hp : ∀ i, 0 ≤ p i)
    (X : Ω → ℝ) (hX : ∀ i, 0 ≤ X i) (ω ell a : ℝ)
    (hω : 0 < ω) (hell : 0 < ell) (ha : 0 ≤ a)
    (hsecond : mean p (fun i => X i ^ 2) ≤ (mean p X) ^ 2 + a * mean p X) :
    ell * mean p X / (ell / ω + mean p X + a) ≤
      mean p (fun i => min (ω * X i) ell) := by
  let μ := mean p X
  let q := ell / ω
  let M := mean p (fun i => min (ω * X i) ell)
  have hμ0 : 0 ≤ μ := mean_nonneg p hp X hX
  have hq : 0 < q := div_pos hell hω
  have hM0 : 0 ≤ M := mean_nonneg p hp _ (fun i =>
    le_min (mul_nonneg hω.le (hX i)) hell.le)
  change ell * μ / (q + μ + a) ≤ M
  by_cases hμ : μ = 0
  · simpa only [hμ, mul_zero, zero_div] using hM0
  have hμpos : 0 < μ := lt_of_le_of_ne hμ0 (Ne.symm hμ)
  have hden : 0 < q + μ + a := by positivity
  have hg0 : 0 ≤ mean p (fun i => X i * (q + X i)) :=
    mean_nonneg p hp _ (fun i => mul_nonneg (hX i) (add_nonneg hq.le (hX i)))
  have hgeq : mean p (fun i => X i * (q + X i)) =
      q * μ + mean p (fun i => X i ^ 2) := by
    dsimp [μ]
    simp only [mean, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hgb : mean p (fun i => X i * (q + X i)) ≤ μ * (q + μ + a) := by
    rw [hgeq]
    change mean p (fun i => X i ^ 2) ≤ μ ^ 2 + a * μ at hsecond
    nlinarith only [hsecond]
  have hcap : ell * mean p (fun i => X i / (q + X i)) ≤ M := by
    rw [← mean_mul_left]
    exact mean_mono p hp (fun i => by
      simpa only [q, mul_div_assoc] using harmonic_le_cap (X i) ω ell (hX i) hω hell)
  have hcs := mean_sq_le_ratio_second_moment p hp X hX q hq
  have hmain : ell * μ ^ 2 ≤ M * (μ * (q + μ + a)) := by
    calc
      ell * μ ^ 2 ≤ ell *
          (mean p (fun i => X i / (q + X i)) *
            mean p (fun i => X i * (q + X i))) :=
        mul_le_mul_of_nonneg_left hcs hell.le
      _ = (ell * mean p (fun i => X i / (q + X i))) *
          mean p (fun i => X i * (q + X i)) := by ring
      _ ≤ M * mean p (fun i => X i * (q + X i)) :=
        mul_le_mul_of_nonneg_right hcap hg0
      _ ≤ M * (μ * (q + μ + a)) := mul_le_mul_of_nonneg_left hgb hM0
  apply (div_le_iff₀ hden).mpr
  apply (mul_le_mul_iff_left₀ hμpos).mp
  nlinarith only [hmain]

/-- The capped-mean estimate from a normalized finite variance bound. -/
theorem capped_mean_lower_of_variance
    (p : Ω → ℝ) (hp : ∀ i, 0 ≤ p i) (hpsum : (∑ i, p i) = 1)
    (X : Ω → ℝ) (hX : ∀ i, 0 ≤ X i) (ω ell a : ℝ)
    (hω : 0 < ω) (hell : 0 < ell) (ha : 0 ≤ a)
    (hvar : variance p X ≤ a * mean p X) :
    ell * mean p X / (ell / ω + mean p X + a) ≤
      mean p (fun i => min (ω * X i) ell) := by
  apply capped_mean_lower_of_second_moment p hp X hX ω ell a hω hell ha
  rw [variance_eq_mean_sq_sub p hpsum X] at hvar
  linarith

/-- The explicit numerical margin used for one exceptional correction
row. All quantities are real; in particular the mean is `p₀ * d`. -/
theorem correction_capped_mean_lower
    (p : Ω → ℝ) (hp : ∀ i, 0 ≤ p i) (hpsum : (∑ i, p i) = 1)
    (X : Ω → ℝ) (hX : ∀ i, 0 ≤ X i) (p₀ d c lam ω ell a : ℝ)
    (hp₀ : 0 < p₀) (hd : 0 ≤ d) (hc : 0 < c) (hlam : 0 ≤ lam)
    (hω : 0 < ω) (hell : 0 < ell) (ha : 0 ≤ a)
    (hmean : mean p X = p₀ * d)
    (hvar : variance p X ≤ a * mean p X)
    (hdc : d ≤ c / 2)
    (hell_lower : (59 / 64 : ℝ) * lam * c ≤ ell)
    (hell_ratio : ell / ω ≤ (15 / 1024 : ℝ) * p₀ * c)
    (ha_upper : a ≤ p₀ * c / 4096) :
    (7 / 4 : ℝ) * lam * d ≤ mean p (fun i => min (ω * X i) ell) := by
  have hcap := capped_mean_lower_of_variance p hp hpsum X hX ω ell a hω hell ha hvar
  rw [hmean] at hcap
  apply le_trans ?_ hcap
  have hden : 0 < ell / ω + p₀ * d + a := by positivity
  apply (le_div_iff₀ hden).mpr
  have hden_upper : ell / ω + p₀ * d + a ≤ (2109 / 4096 : ℝ) * p₀ * c := by
    have := mul_le_mul_of_nonneg_left hdc hp₀.le
    linarith
  have hleft := mul_le_mul_of_nonneg_left hden_upper
    (show 0 ≤ (7 / 4 : ℝ) * lam * d by positivity)
  have hright := mul_le_mul_of_nonneg_right hell_lower (mul_nonneg hp₀.le hd)
  have hprod : 0 ≤ lam * d * p₀ * c := by positivity
  nlinarith only [hleft, hright, hprod]

/-- A finite lower-tail bound when a numerical lower bound for the
mean is available. The statistic need not be nonnegative. -/
theorem lower_tail_of_mean_lower (p : Ω → ℝ) (hp : ∀ i, 0 ≤ p i)
    (X : Ω → ℝ) (b t : ℝ) (hbt : t < b) (hb : b ≤ mean p X) :
    MatchingProbability.probability p (fun i => X i < t) ≤
      variance p X / (b - t) ^ 2 := by
  apply le_trans (MatchingProbability.probability_mono p hp (fun i hi =>
    show b - t ≤ |X i - mean p X| from by
      have h := neg_le_abs (X i - mean p X)
      linarith))
  exact chebyshev p hp X (b - t) (sub_pos.mpr hbt)

/-- The numerical Chebyshev bound used for the capped correction score.
The mean and variance estimates remain explicit premises here; their
finite analytic ingredients are proved separately. -/
theorem correction_score_lower_tail
    (p : Ω → ℝ) (hp : ∀ i, 0 ≤ p i) (X : Ω → ℝ)
    (p₀ lam a M : ℝ) (hp₀ : 0 < p₀) (hlam : 0 < lam)
    (hM : 0 < M)
    (hmean : (7 / 4 : ℝ) * lam * M ≤ mean p X)
    (hvar : variance p X ≤ 8 * p₀ * (64 * lam / p₀ ^ 2) ^ 2 * a * M) :
    MatchingProbability.probability p (fun i => X i < (13 / 8 : ℝ) * lam * M) ≤
      (2 : ℝ) ^ 21 * a / (p₀ ^ 3 * M) := by
  have hgap : (13 / 8 : ℝ) * lam * M < (7 / 4 : ℝ) * lam * M := by
    nlinarith [mul_pos hlam hM]
  have htail := lower_tail_of_mean_lower p hp X
    ((7 / 4 : ℝ) * lam * M) ((13 / 8 : ℝ) * lam * M) hgap hmean
  apply htail.trans
  calc
    variance p X / ((7 / 4 : ℝ) * lam * M - (13 / 8 : ℝ) * lam * M) ^ 2 ≤
        (8 * p₀ * (64 * lam / p₀ ^ 2) ^ 2 * a * M) /
          ((7 / 4 : ℝ) * lam * M - (13 / 8 : ℝ) * lam * M) ^ 2 :=
      div_le_div_of_nonneg_right hvar (sq_nonneg _)
    _ = (2 : ℝ) ^ 21 * a / (p₀ ^ 3 * M) := by
      field_simp
      ring

end Overfull.FiniteProbability
