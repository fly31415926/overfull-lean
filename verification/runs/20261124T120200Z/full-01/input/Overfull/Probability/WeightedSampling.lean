import Overfull.Probability.Hypergeometric

/-!
# Finite weighted moments and sampling without replacement

Expectation and variance are finite sums with explicit normalized weights.
The weighted sample bounds use the actual uniform fixed-size subset law,
including the empty population and both endpoint sample sizes.
-/

noncomputable section

namespace Overfull.FiniteProbability

open Finset Classical

variable {Ω ι : Type*} [Fintype Ω]

/-- Expectation under finite real weights. -/
def mean (p : Ω → ℝ) (f : Ω → ℝ) : ℝ := ∑ ω, p ω * f ω

/-- Centered second moment under finite real weights. -/
def variance (p : Ω → ℝ) (f : Ω → ℝ) : ℝ :=
  mean p (fun ω => (f ω - mean p f) ^ 2)

theorem mean_nonneg (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω)
    (f : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω) : 0 ≤ mean p f :=
  Finset.sum_nonneg (fun ω _ => mul_nonneg (hp ω) (hf ω))

theorem mean_mono (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω)
    {f g : Ω → ℝ} (hfg : ∀ ω, f ω ≤ g ω) : mean p f ≤ mean p g :=
  Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (hfg ω) (hp ω))

theorem mean_const (p : Ω → ℝ) (hp : (∑ ω, p ω) = 1) (c : ℝ) :
    mean p (fun _ => c) = c := by
  rw [mean, ← Finset.sum_mul, hp, one_mul]

theorem mean_eq_const_of_support (p : Ω → ℝ) (hp : (∑ ω, p ω) = 1)
    (f : Ω → ℝ) (c : ℝ) (hf : ∀ ω, p ω ≠ 0 → f ω = c) : mean p f = c := by
  calc
    _ = mean p (fun _ => c) := by
      apply Finset.sum_congr rfl
      intro ω _
      by_cases hω : p ω = 0
      · simp only [hω, zero_mul]
      · rw [hf ω hω]
    _ = c := mean_const p hp c

theorem nonempty_of_sum_eq_one (p : Ω → ℝ) (hp : (∑ ω, p ω) = 1) : Nonempty Ω := by
  by_contra h
  haveI : IsEmpty Ω := not_nonempty_iff.mp h
  simp at hp

theorem mean_add (p : Ω → ℝ) (f g : Ω → ℝ) :
    mean p (fun ω => f ω + g ω) = mean p f + mean p g := by
  simp only [mean, mul_add, Finset.sum_add_distrib]

theorem mean_sub (p : Ω → ℝ) (f g : Ω → ℝ) :
    mean p (fun ω => f ω - g ω) = mean p f - mean p g := by
  simp only [mean, mul_sub, Finset.sum_sub_distrib]

theorem mean_mul_left (p : Ω → ℝ) (c : ℝ) (f : Ω → ℝ) :
    mean p (fun ω => c * f ω) = c * mean p f := by
  simp only [mean, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

theorem mean_sum [Fintype ι] (p : Ω → ℝ) (f : ι → Ω → ℝ) :
    mean p (fun ω => ∑ i, f i ω) = ∑ i, mean p (f i) := by
  simp only [mean, Finset.mul_sum]
  exact Finset.sum_comm

theorem mean_indicator (p : Ω → ℝ) (P : Ω → Prop) [DecidablePred P] :
    mean p (fun ω => if P ω then 1 else 0) = MatchingProbability.probability p P := by
  simp only [mean, MatchingProbability.probability, Finset.sum_filter,
    mul_ite, mul_one, mul_zero]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : P ω <;> simp only [h, if_true, if_false]

theorem variance_nonneg (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (f : Ω → ℝ) :
    0 ≤ variance p f := mean_nonneg p hp _ (fun _ => sq_nonneg _)

theorem variance_eq_zero_of_support (p : Ω → ℝ) (hp : (∑ ω, p ω) = 1)
    (f : Ω → ℝ) (c : ℝ) (hf : ∀ ω, p ω ≠ 0 → f ω = c) :
    variance p f = 0 := by
  rw [variance, mean_eq_const_of_support p hp f c hf]
  apply Finset.sum_eq_zero
  intro ω _
  by_cases hω : p ω = 0
  · simp only [hω, zero_mul]
  · simp only [hf ω hω, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, mul_zero]

theorem variance_const (p : Ω → ℝ) (hp : (∑ ω, p ω) = 1) (c : ℝ) :
    variance p (fun _ => c) = 0 :=
  variance_eq_zero_of_support p hp _ c (fun _ _ => rfl)

/-- The centered second moment equals the second moment minus the square
of the mean for every normalized finite distribution. -/
theorem variance_eq_mean_sq_sub (p : Ω → ℝ) (hp : (∑ ω, p ω) = 1)
    (f : Ω → ℝ) :
    variance p f = mean p (fun ω => f ω ^ 2) - (mean p f) ^ 2 := by
  unfold variance
  have hpoint : (fun ω => (f ω - mean p f) ^ 2) =
      (fun ω => (f ω ^ 2 - (2 * mean p f) * f ω) + (mean p f) ^ 2) := by
    funext ω
    ring
  rw [hpoint, mean_add, mean_sub, mean_mul_left, mean_const p hp]
  ring

/-- The square of an average is at most the average square. -/
theorem mean_sq_le (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω)
    (hpsum : (∑ ω, p ω) = 1) (f : Ω → ℝ) :
    (mean p f) ^ 2 ≤ mean p (fun ω => f ω ^ 2) := by
  have h := variance_nonneg p hp f
  rw [variance_eq_mean_sq_sub p hpsum f] at h
  linarith

/-- Finite Chebyshev inequality with an explicit positive deviation. -/
theorem chebyshev (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω)
    (f : Ω → ℝ) (t : ℝ) (ht : 0 < t) :
    MatchingProbability.probability p (fun ω => t ≤ |f ω - mean p f|) ≤
      variance p f / t ^ 2 := by
  have h := MatchingProbability.probability_markov p hp
    (fun ω => (f ω - mean p f) ^ 2) (fun _ => sq_nonneg _) (t ^ 2)
    (fun ω => t ≤ |f ω - mean p f|) (by
      intro ω hω
      have habs := abs_nonneg (f ω - mean p f)
      have hsq := sq_abs (f ω - mean p f)
      nlinarith)
  apply (le_div_iff₀ (sq_pos_of_pos ht)).mpr
  simpa only [variance, mean, mul_comm] using h

section Product

variable {Λ : Type*} [Fintype Λ]

/-- Reindexing the actual outcomes by an equivalence preserves the mean. -/
theorem mean_equiv (e : Ω ≃ Λ) (p : Λ → ℝ) (f : Λ → ℝ) :
    mean (fun x => p (e x)) (fun x => f (e x)) = mean p f :=
  e.sum_comp (fun y => p y * f y)

/-- Reindexing outcomes preserves the centered second moment. -/
theorem variance_equiv (e : Ω ≃ Λ) (p : Λ → ℝ) (f : Λ → ℝ) :
    variance (fun x => p (e x)) (fun x => f (e x)) = variance p f := by
  unfold variance
  rw [mean_equiv e p f]
  exact mean_equiv e p (fun y => (f y - mean p f) ^ 2)

/-- Interchange two finite weighted averages. -/
theorem mean_comm (p : Ω → ℝ) (q : Λ → ℝ) (f : Ω → Λ → ℝ) :
    mean p (fun x => mean q (f x)) =
      mean q (fun y => mean p (fun x => f x y)) := by
  simp only [mean, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- The expectation for an actual product law is its iterated expectation. -/
theorem mean_prod (p : Ω → ℝ) (q : Λ → ℝ) (f : Ω → Λ → ℝ) :
    mean (fun z : Ω × Λ => p z.1 * q z.2) (fun z => f z.1 z.2) =
      mean p (fun x => mean q (f x)) := by
  simp only [mean, Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

/-- Law of total variance for two independent finite coordinates. The
statistic itself may depend nonlinearly on both coordinates. -/
theorem variance_prod (p : Ω → ℝ) (q : Λ → ℝ)
    (hp : (∑ x, p x) = 1) (hq : (∑ y, q y) = 1) (f : Ω → Λ → ℝ) :
    variance (fun z : Ω × Λ => p z.1 * q z.2) (fun z => f z.1 z.2) =
      mean p (fun x => variance q (f x)) +
        variance p (fun x => mean q (f x)) := by
  have hprod : (∑ z : Ω × Λ, p z.1 * q z.2) = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, hq, mul_one, hp]
  rw [variance_eq_mean_sq_sub _ hprod,
    mean_prod p q (fun x y => f x y ^ 2), mean_prod p q f,
    variance_eq_mean_sq_sub p hp]
  simp_rw [variance_eq_mean_sq_sub q hq]
  rw [mean_sub]
  ring

/-- Averaging a nonlinear statistic over an independent coordinate cannot
increase the variance in the other coordinate beyond the average of its
conditional variances. -/
theorem variance_mean_le (p : Ω → ℝ) (q : Λ → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ y, 0 ≤ q y) (hqsum : (∑ y, q y) = 1)
    (f : Ω → Λ → ℝ) :
    variance p (fun x => mean q (f x)) ≤
      mean q (fun y => variance p (fun x => f x y)) := by
  unfold variance
  rw [mean_comm p q f]
  calc
    _ ≤ mean p (fun x => mean q
        (fun y => (f x y - mean p (fun z => f z y)) ^ 2)) := by
      apply mean_mono p hp
      intro x
      have h := mean_sq_le q hq hqsum (fun y => f x y - mean p (fun z => f z y))
      rw [mean_sub] at h
      exact h
    _ = _ := mean_comm p q _

/-- Two-coordinate variance tensorization. This applies to a general
nonlinear statistic, not only to sums of independent statistics. -/
theorem variance_prod_le (p : Ω → ℝ) (q : Λ → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ y, 0 ≤ q y)
    (hpsum : (∑ x, p x) = 1) (hqsum : (∑ y, q y) = 1) (f : Ω → Λ → ℝ) :
    variance (fun z : Ω × Λ => p z.1 * q z.2) (fun z => f z.1 z.2) ≤
      mean p (fun x => variance q (f x)) +
        mean q (fun y => variance p (fun x => f x y)) := by
  rw [variance_prod p q hpsum hqsum f]
  exact add_le_add_left (variance_mean_le p q hp hq hqsum f) _

end Product

end Overfull.FiniteProbability

namespace Overfull.Hypergeometric

open Finset Classical FiniteProbability

variable {E : Type*} [Fintype E]

/-- A zero-size sample is deterministic, even for an empty population. -/
theorem variance_zero_sample (f : Finset E → ℝ) : variance (weight 0) f = 0 := by
  apply variance_eq_zero_of_support _ (sum_weight 0 (Nat.zero_le _)) f (f ∅)
  intro T hT
  have hcard : T.card = 0 := by
    by_contra hn
    exact hT (by simp only [weight, if_neg hn])
  rw [Finset.card_eq_zero.mp hcard]

/-- Sampling the entire population is deterministic. -/
theorem variance_full_sample (f : Finset E → ℝ) :
    variance (weight (Fintype.card E)) f = 0 := by
  apply variance_eq_zero_of_support _ (sum_weight _ le_rfl) f (f univ)
  intro T hT
  have hcard : T.card = Fintype.card E := by
    by_contra hn
    exact hT (by simp only [weight, if_neg hn])
  rw [Finset.eq_univ_of_card T hcard]

/-- The total prescribed weight in an actual sampled subset. -/
def weightedSum (w : E → ℝ) (T : Finset E) : ℝ := ∑ e ∈ T, w e

theorem weightedSum_eq_indicators (w : E → ℝ) (T : Finset E) :
    weightedSum w T = ∑ e, w e * (if e ∈ T then 1 else 0) := by
  simp only [weightedSum, mul_ite, mul_one, mul_zero]
  simp

/-- The inclusion indicator has the same mean for every population
member; its existence itself supplies nonemptiness of the population. -/
theorem mean_member_indicator (s : ℕ) (hs : s ≤ Fintype.card E) (e : E) :
    mean (weight s) (fun T => if e ∈ T then 1 else 0) =
      (s : ℝ) / Fintype.card E := by
  rw [mean_indicator]
  exact probability_member s (Fintype.card_pos_iff.mpr ⟨e⟩) hs e

/-- Weighted expectation under the actual uniform subset law. It also
covers an empty population, since the finite member sum is then empty. -/
theorem mean_weightedSum (s : ℕ) (hs : s ≤ Fintype.card E) (w : E → ℝ) :
    mean (weight s) (weightedSum w) =
      ((s : ℝ) / Fintype.card E) * ∑ e, w e := by
  change mean (weight s) (fun T => weightedSum w T) = _
  simp_rw [weightedSum_eq_indicators, mean_sum, mean_mul_left,
    mean_member_indicator s hs]
  rw [← Finset.sum_mul, mul_comm]

/-- Distinct membership indicators have nonpositive covariance. The
diagonal term is retained as a separate nonnegative error. -/
theorem mean_pair_indicator_le (s : ℕ) (hs : s ≤ Fintype.card E) (x y : E) :
    mean (weight s) (fun T => if x ∈ T ∧ y ∈ T then 1 else 0) ≤
      ((s : ℝ) / Fintype.card E) ^ 2 +
        if x = y then (s : ℝ) / Fintype.card E else 0 := by
  by_cases hxy : x = y
  · subst y
    simp only [and_self, if_true, mean_member_indicator s hs]
    nlinarith [sq_nonneg ((s : ℝ) / Fintype.card E)]
  · rw [if_neg hxy, add_zero]
    have h := probability_containing_le s (Fintype.card_pos_iff.mpr ⟨x⟩) hs {x, y}
    simpa only [Finset.card_pair hxy, Finset.insert_subset_iff,
      Finset.singleton_subset_iff, mean, probability, MatchingProbability.probability,
      Finset.sum_filter, mul_ite, mul_one, mul_zero] using h

theorem weightedSum_sq (w : E → ℝ) (T : Finset E) :
    weightedSum w T ^ 2 = ∑ x, ∑ y,
      (w x * w y) * (if x ∈ T ∧ y ∈ T then 1 else 0) := by
  rw [weightedSum_eq_indicators, pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hx : x ∈ T <;> by_cases hy : y ∈ T <;> simp [hx, hy]

/-- The second moment bound is obtained by summing actual one- and
two-member inclusion probabilities over all weighted pairs. -/
theorem mean_weightedSum_sq_le (s : ℕ) (hs : s ≤ Fintype.card E)
    (w : E → ℝ) (hw : ∀ e, 0 ≤ w e) :
    mean (weight s) (fun T => weightedSum w T ^ 2) ≤
      (((s : ℝ) / Fintype.card E) * ∑ e, w e) ^ 2 +
        ((s : ℝ) / Fintype.card E) * ∑ e, w e ^ 2 := by
  let p : ℝ := (s : ℝ) / Fintype.card E
  have hfirst : (∑ x, ∑ y, (w x * w y) * p ^ 2) = p ^ 2 * (∑ e, w e) ^ 2 := by
    simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
    rw [← Finset.sum_mul]
    ring
  have hdiag : (∑ x, ∑ y, (w x * w y) * (if x = y then p else 0)) =
      p * ∑ e, w e ^ 2 := by
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    simp only [pow_two, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  calc
    _ = ∑ x, ∑ y, (w x * w y) *
        mean (weight s) (fun T => if x ∈ T ∧ y ∈ T then 1 else 0) := by
      simp_rw [weightedSum_sq, mean_sum, mean_mul_left]
    _ ≤ ∑ x, ∑ y, (w x * w y) * (p ^ 2 + if x = y then p else 0) := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro y _
      exact mul_le_mul_of_nonneg_left (mean_pair_indicator_le s hs x y)
        (mul_nonneg (hw x) (hw y))
    _ = _ := by
      simp_rw [mul_add, Finset.sum_add_distrib]
      rw [hfirst, hdiag]
      dsimp only [p]
      ring

/-- Weighted sampling without replacement has variance at most the
sampling proportion times the sum of squared nonnegative weights. -/
theorem variance_weightedSum_le (s : ℕ) (hs : s ≤ Fintype.card E)
    (w : E → ℝ) (hw : ∀ e, 0 ≤ w e) :
    variance (weight s) (weightedSum w) ≤
      ((s : ℝ) / Fintype.card E) * ∑ e, w e ^ 2 := by
  rw [variance_eq_mean_sq_sub _ (sum_weight s hs), mean_weightedSum s hs]
  have h := mean_weightedSum_sq_le s hs w hw
  linarith

/-- A uniform bound on individual weights gives the variance bound
`maximum weight × mean` used for palette pools and exceptional rows. -/
theorem variance_weightedSum_le_max_mul_mean (s : ℕ) (hs : s ≤ Fintype.card E)
    (w : E → ℝ) (M : ℝ) (hw : ∀ e, 0 ≤ w e) (hM : ∀ e, w e ≤ M) :
    variance (weight s) (weightedSum w) ≤ M * mean (weight s) (weightedSum w) := by
  rw [mean_weightedSum s hs]
  apply (variance_weightedSum_le s hs w hw).trans
  have hsquares : (∑ e, w e ^ 2) ≤ M * ∑ e, w e := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e _
    simpa only [pow_two] using mul_le_mul_of_nonneg_right (hM e) (hw e)
  have h := mul_le_mul_of_nonneg_left hsquares
    (show (0 : ℝ) ≤ (s : ℝ) / Fintype.card E by positivity)
  nlinarith

end Overfull.Hypergeometric

namespace Overfull.FiniteProbability

open Finset Classical

/-- The actual product weight of finitely many finite coordinate laws. -/
def piWeight {ι : Type*} [Fintype ι] {κ : ι → Type*}
    (p : ∀ i, κ i → ℝ) (x : ∀ i, κ i) : ℝ := ∏ i, p i (x i)

theorem piWeight_nonneg {ι : Type*} [Fintype ι] {κ : ι → Type*}
    (p : ∀ i, κ i → ℝ) (hp : ∀ i x, 0 ≤ p i x) (x : ∀ i, κ i) :
    0 ≤ piWeight p x := Finset.prod_nonneg (fun i _ => hp i (x i))

theorem sum_piWeight {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)]
    (p : ∀ i, κ i → ℝ) (hp : ∀ i, (∑ x, p i x) = 1) :
    (∑ x : ∀ i, κ i, piWeight p x) = 1 := by
  classical
  unfold piWeight
  rw [← Fintype.prod_sum]
  simp only [hp, Finset.prod_const_one]

theorem piWeight_cons {n : ℕ} {κ : Fin (n + 1) → Type*}
    (p : ∀ i, κ i → ℝ) (x : κ 0) (y : ∀ i : Fin n, κ i.succ) :
    piWeight p (Fin.cons x y) = p 0 x * piWeight (fun i : Fin n => p i.succ) y := by
  simp only [piWeight, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]

/-- Tensorization for a finite tuple: a uniform bound on every
one-coordinate section variance bounds the variance of any statistic. -/
theorem variance_pi_fin_le :
    ∀ (n : ℕ) (κ : Fin n → Type*) [∀ i, Fintype (κ i)]
      (p : ∀ i, κ i → ℝ) (_hp : ∀ i x, 0 ≤ p i x)
      (_hpsum : ∀ i, (∑ x, p i x) = 1)
      (f : (∀ i, κ i) → ℝ) (b : Fin n → ℝ),
      (∀ i x, variance (p i) (fun y => f (Function.update x i y)) ≤ b i) →
        variance (piWeight p) f ≤ ∑ i, b i := by
  intro n
  induction n with
  | zero =>
    intro κ _ p _hp hpsum f b _hsection
    have hconst : f = fun _ => f (fun i => Fin.elim0 i) := by
      funext x
      exact congrArg f (Subsingleton.elim _ _)
    rw [hconst, variance_const _ (sum_piWeight p hpsum)]
    simp
  | succ n ih =>
    intro κ _ p hp hpsum f b hsection
    let ptail : ∀ i : Fin n, κ i.succ → ℝ := fun i => p i.succ
    have htailnorm : (∑ x, piWeight ptail x) = 1 :=
      sum_piWeight ptail (fun i => hpsum i.succ)
    have htailnonneg : ∀ x, 0 ≤ piWeight ptail x :=
      piWeight_nonneg ptail (fun i => hp i.succ)
    have htail (x : κ 0) :
        variance (piWeight ptail) (fun y => f (Fin.cons x y)) ≤
          ∑ i : Fin n, b i.succ := by
      apply ih (fun i : Fin n => κ i.succ) ptail
        (fun i => hp i.succ) (fun i => hpsum i.succ)
        (fun y => f (Fin.cons x y)) (fun i => b i.succ)
      intro i y
      simpa only [Fin.cons_update] using hsection i.succ (Fin.cons x y)
    have hfirst (y : ∀ i : Fin n, κ i.succ) :
        variance (p 0) (fun x => f (Fin.cons x y)) ≤ b 0 := by
      obtain ⟨x₀⟩ := nonempty_of_sum_eq_one (p 0) (hpsum 0)
      simpa only [Fin.update_cons_zero] using hsection 0 (Fin.cons x₀ y)
    have hvar := variance_equiv (Fin.consEquiv κ) (piWeight p) f
    change variance (fun z : κ 0 × (∀ i : Fin n, κ i.succ) => piWeight p (Fin.cons z.1 z.2))
      (fun z => f (Fin.cons z.1 z.2)) = variance (piWeight p) f at hvar
    simp only [piWeight_cons] at hvar
    have hbound := variance_prod_le (p 0) (piWeight ptail) (hp 0) htailnonneg
      (hpsum 0) htailnorm (fun x y => f (Fin.cons x y))
    have hleft : mean (p 0) (fun x => variance (piWeight ptail)
        (fun y => f (Fin.cons x y))) ≤ ∑ i : Fin n, b i.succ :=
      (mean_mono (p 0) (hp 0) htail).trans_eq (mean_const (p 0) (hpsum 0) _)
    have hright : mean (piWeight ptail) (fun y => variance (p 0)
        (fun x => f (Fin.cons x y))) ≤ b 0 :=
      (mean_mono (piWeight ptail) htailnonneg hfirst).trans_eq
        (mean_const (piWeight ptail) htailnorm _)
    calc
      _ = variance (fun z : κ 0 × (∀ i : Fin n, κ i.succ) => p 0 z.1 * piWeight ptail z.2)
          (fun z => f (Fin.cons z.1 z.2)) := hvar.symm
      _ ≤ (∑ i : Fin n, b i.succ) + b 0 := hbound.trans (add_le_add hleft hright)
      _ = ∑ i, b i := by rw [Fin.sum_univ_succ]; ring

/-- Finite dependent-product variance tensorization from bounds on actual
coordinate sections. It applies to statistics coupling all coordinates. -/
theorem variance_pi_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)]
    (p : ∀ i, κ i → ℝ) (hp : ∀ i x, 0 ≤ p i x)
    (hpsum : ∀ i, (∑ x, p i x) = 1)
    (f : (∀ i, κ i) → ℝ) (b : ι → ℝ)
    (hsection : ∀ i x, variance (p i) (fun y => f (Function.update x i y)) ≤ b i) :
    variance (piWeight p) f ≤ ∑ i, b i := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let ePi := Equiv.piCongrLeft κ e
  let p' : ∀ i : Fin (Fintype.card ι), κ (e i) → ℝ := fun i => p (e i)
  let f' : (∀ i : Fin (Fintype.card ι), κ (e i)) → ℝ := fun x => f (ePi x)
  have hsections (i : Fin (Fintype.card ι)) (x : ∀ j, κ (e j)) :
      variance (p' i) (fun y => f' (Function.update x i y)) ≤ b (e i) := by
    have hupdate (y : κ (e i)) :
        ePi (Function.update x i y) = Function.update (ePi x) (e i) y := by
      exact Function.piCongrLeft'_symm_update κ e.symm x i y
    simpa only [p', f', hupdate] using hsection (e i) (ePi x)
  have hweight (x : ∀ i, κ (e i)) : piWeight p (ePi x) = piWeight p' x := by
    unfold piWeight
    calc
      _ = ∏ i : Fin (Fintype.card ι), p (e i) (ePi x (e i)) :=
        (e.prod_comp (fun j => p j (ePi x j))).symm
      _ = _ := by simp only [ePi, Equiv.piCongrLeft_apply_apply, p']
  have hvar := variance_equiv ePi (piWeight p) f
  simp only [hweight] at hvar
  calc
    _ = variance (piWeight p') f' := hvar.symm
    _ ≤ ∑ i : Fin (Fintype.card ι), b (e i) :=
      variance_pi_fin_le (Fintype.card ι) (fun i => κ (e i)) p'
        (fun i => hp (e i)) (fun i => hpsum (e i)) f' (fun i => b (e i)) hsections
    _ = ∑ i, b i := e.sum_comp b

end Overfull.FiniteProbability
