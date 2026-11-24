import Overfull.Probability.WeightedSampling
import Overfull.Probability.Concentration

/-!
# Prefix-dependent indicators under independent uniform choices

At round `s`, the indicator may depend on all `s` previous choices and the
current choice.  Only its conditional mean, for each fixed previous history,
is bounded.  The indicators themselves need not be independent.

The source distribution is the actual finite product of uniform laws on
`Fin t`, and every expectation and probability below is a finite sum.
-/

noncomputable section

namespace Overfull.PredictableBernoulli

open Finset Classical FiniteProbability

/-- One uniform choice from `Fin t`.  Normalization requires `0 < t`. -/
def choiceWeight (t : ℕ) (_ : Fin t) : ℝ := (t : ℝ)⁻¹

/-- The actual product weight on a history of `q` uniform choices. -/
def weight (t q : ℕ) (ω : Fin q → Fin t) : ℝ :=
  piWeight (fun _ : Fin q => choiceWeight t) ω

/-- A Boolean stage observes its previous history and its current choice. -/
abbrev Process (t : ℕ) := (s : ℕ) → (Fin s → Fin t) → Fin t → Bool

/-- The number of successful stages in a complete history. -/
def count {t : ℕ} (X : Process t) : (q : ℕ) → (Fin q → Fin t) → ℕ
  | 0, _ => 0
  | q + 1, ω => count X q (Fin.init ω) +
      if X q (Fin.init ω) (ω (Fin.last q)) then 1 else 0

/-- The conditional success probability at a fixed previous history. -/
def localMean {t : ℕ} (X : Process t) (s : ℕ) (h : Fin s → Fin t) : ℝ :=
  mean (choiceWeight t) (fun z => if X s h z then 1 else 0)

@[simp] theorem count_zero {t : ℕ} (X : Process t) (ω : Fin 0 → Fin t) :
    count X 0 ω = 0 := rfl

@[simp] theorem count_snoc {t q : ℕ} (X : Process t)
    (h : Fin q → Fin t) (z : Fin t) :
    count X (q + 1) (Fin.snoc h z) = count X q h + if X q h z then 1 else 0 := by
  simp [count]

theorem choiceWeight_nonneg (t : ℕ) (z : Fin t) : 0 ≤ choiceWeight t z := by
  exact inv_nonneg.mpr (Nat.cast_nonneg t)

theorem sum_choiceWeight (t : ℕ) (ht : 0 < t) :
    (∑ z : Fin t, choiceWeight t z) = 1 := by
  simp only [choiceWeight, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  exact mul_inv_cancel₀ (by exact_mod_cast (ne_of_gt ht))

theorem weight_nonneg (t q : ℕ) (ω : Fin q → Fin t) : 0 ≤ weight t q ω :=
  piWeight_nonneg _ (fun _ => choiceWeight_nonneg t) ω

theorem sum_weight (t q : ℕ) (ht : 0 < t) :
    (∑ ω : Fin q → Fin t, weight t q ω) = 1 :=
  sum_piWeight _ (fun _ => sum_choiceWeight t ht)

theorem weight_snoc {t q : ℕ} (h : Fin q → Fin t) (z : Fin t) :
    weight t (q + 1) (Fin.snoc h z) = choiceWeight t z * weight t q h := by
  simp only [weight, piWeight, Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
  exact mul_comm _ _

/-- Integrate the next independent choice after the preceding history.
The statistic itself can depend arbitrarily on the complete history. -/
theorem mean_snoc {t q : ℕ} (f : (Fin (q + 1) → Fin t) → ℝ) :
    mean (weight t (q + 1)) f =
      mean (weight t q) (fun h => mean (choiceWeight t) (fun z => f (Fin.snoc h z))) := by
  let e := Fin.snocEquiv (fun _ : Fin (q + 1) => Fin t)
  calc
    _ = mean (fun zh : Fin t × (Fin q → Fin t) => choiceWeight t zh.1 * weight t q zh.2)
        (fun zh => f (Fin.snoc zh.2 zh.1)) := by
      have he := mean_equiv e (weight t (q + 1)) f
      change mean (fun zh : Fin t × (Fin q → Fin t) =>
          weight t (q + 1) (Fin.snoc zh.2 zh.1))
          (fun zh => f (Fin.snoc zh.2 zh.1)) = _ at he
      simpa only [weight_snoc] using he.symm
    _ = mean (choiceWeight t) (fun z => mean (weight t q) (fun h => f (Fin.snoc h z))) :=
      mean_prod (choiceWeight t) (weight t q) (fun z h => f (Fin.snoc h z))
    _ = _ := mean_comm (choiceWeight t) (weight t q) (fun z h => f (Fin.snoc h z))

/-- A single conditional Bernoulli moment, proved directly from its local mean. -/
theorem local_exponential_moment_le {t : ℕ} (ht : 0 < t) (X : Process t)
    (s : ℕ) (h : Fin s → Fin t) (p θ : ℝ) (hθ : 0 ≤ θ)
    (hp : localMean X s h ≤ p) :
    mean (choiceWeight t) (fun z => Real.exp (θ * (if X s h z then 1 else 0))) ≤
      Real.exp ((Real.exp θ - 1) * p) := by
  have hc : 0 ≤ Real.exp θ - 1 := by
    have := Real.exp_le_exp.mpr hθ
    simpa only [Real.exp_zero, sub_nonneg] using this
  have heq : (fun z : Fin t => Real.exp (θ * (if X s h z then 1 else 0))) =
      (fun z => 1 + (Real.exp θ - 1) * (if X s h z then 1 else 0)) := by
    funext z
    split_ifs <;> simp
  rw [heq, mean_add, mean_const _ (sum_choiceWeight t ht), mean_mul_left]
  calc
    _ ≤ 1 + (Real.exp θ - 1) * p := by
      exact add_le_add_left (mul_le_mul_of_nonneg_left hp hc) 1
    _ ≤ _ := by linarith [Real.add_one_le_exp ((Real.exp θ - 1) * p)]

/-- The actual exponential moment for prefix-dependent indicators.  The only
probabilistic premise is a bound on the mean over the next uniform choice,
for every fixed previous history. -/
theorem exponential_moment_le {t : ℕ} (ht : 0 < t) (X : Process t)
    (p : ℕ → ℝ) (q : ℕ) (θ : ℝ) (hθ : 0 ≤ θ)
    (hlocal : ∀ s < q, ∀ h : Fin s → Fin t, localMean X s h ≤ p s) :
    mean (weight t q) (fun ω => Real.exp (θ * (count X q ω : ℝ))) ≤
      Real.exp ((Real.exp θ - 1) * ∑ s ∈ Finset.range q, p s) := by
  induction q with
  | zero =>
      simp only [count_zero, Nat.cast_zero, mul_zero, Real.exp_zero, Finset.range_zero,
        Finset.sum_empty]
      exact le_of_eq (mean_const _ (sum_weight t 0 ht) 1)
  | succ q ih =>
      have hprev := ih (fun s hs h => hlocal s (Nat.lt_succ_of_lt hs) h)
      rw [mean_snoc]
      calc
        _ ≤ mean (weight t q) (fun h =>
            Real.exp ((Real.exp θ - 1) * p q) * Real.exp (θ * (count X q h : ℝ))) := by
          apply mean_mono _ (weight_nonneg t q)
          intro h
          have hstep := local_exponential_moment_le ht X q h (p q) θ hθ
            (hlocal q (Nat.lt_succ_self q) h)
          have heq : (fun z : Fin t => Real.exp (θ * (count X (q + 1) (Fin.snoc h z) : ℝ))) =
              (fun z => Real.exp (θ * (count X q h : ℝ)) *
                Real.exp (θ * (if X q h z then 1 else 0))) := by
            funext z
            rw [count_snoc, Nat.cast_add, mul_add, Real.exp_add]
            split_ifs <;> simp
          rw [heq, mean_mul_left]
          simpa only [mul_comm] using
            mul_le_mul_of_nonneg_left hstep (Real.exp_pos (θ * (count X q h : ℝ))).le
        _ = Real.exp ((Real.exp θ - 1) * p q) *
            mean (weight t q) (fun h => Real.exp (θ * (count X q h : ℝ))) :=
          mean_mul_left _ _ _
        _ ≤ Real.exp ((Real.exp θ - 1) * p q) *
            Real.exp ((Real.exp θ - 1) * ∑ s ∈ Finset.range q, p s) :=
          mul_le_mul_of_nonneg_left hprev (Real.exp_pos _).le
        _ = _ := by
          rw [← Real.exp_add, Finset.sum_range_succ]
          congr 1
          ring

/-- Exponential Markov bound for the actual complete-history law. -/
theorem exponential_upper_tail {t : ℕ} (ht : 0 < t) (X : Process t)
    (p : ℕ → ℝ) (q : ℕ) (θ L : ℝ) (hθ : 0 ≤ θ)
    (hlocal : ∀ s < q, ∀ h : Fin s → Fin t, localMean X s h ≤ p s) :
    MatchingProbability.probability (weight t q) (fun ω => L < (count X q ω : ℝ)) ≤
      Real.exp ((Real.exp θ - 1) * (∑ s ∈ Finset.range q, p s) - θ * L) := by
  have hm := MatchingProbability.probability_markov (weight t q) (weight_nonneg t q)
    (fun ω => Real.exp (θ * (count X q ω : ℝ))) (fun _ => (Real.exp_pos _).le)
    (Real.exp (θ * L)) (fun ω => L < (count X q ω : ℝ))
    (fun _ h => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h.le hθ))
  have hb := exponential_moment_le ht X p q θ hθ hlocal
  have hmul := mul_le_mul_of_nonneg_left (hm.trans hb) (Real.exp_pos (-θ * L)).le
  have hc : Real.exp (-θ * L) * Real.exp (θ * L) = 1 := by
    rw [← Real.exp_add, show -θ * L + θ * L = 0 by ring, Real.exp_zero]
  rw [← mul_assoc, hc, one_mul, ← Real.exp_add] at hmul
  convert hmul using 1
  congr 1
  ring

/-- A clean upper-tail budget for the link-packing application.  No
independence of the stage indicators is assumed. -/
theorem upper_tail_of_budget_half {t : ℕ} (ht : 0 < t) (X : Process t)
    (p : ℕ → ℝ) (q : ℕ) (L : ℝ) (hL : 0 < L)
    (hlocal : ∀ s < q, ∀ h : Fin s → Fin t, localMean X s h ≤ p s)
    (hbudget : (∑ s ∈ Finset.range q, p s) ≤ L / 2) :
    MatchingProbability.probability (weight t q) (fun ω => L < (count X q ω : ℝ)) ≤
      Real.exp (-L / 24) := by
  refine (exponential_upper_tail ht X p q (1 / 2) L (by norm_num) hlocal).trans ?_
  apply Real.exp_le_exp.mpr
  have hc : 0 ≤ Real.exp (1 / 2 : ℝ) - 1 := by
    have := Real.exp_le_exp.mpr (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    simpa only [Real.exp_zero, sub_nonneg] using this
  have hμ := mul_le_mul_of_nonneg_left hbudget hc
  have he := Bernoulli.exp_quadratic_bound (1 / 2 : ℝ) (by norm_num)
  have hscaled := mul_le_mul_of_nonneg_right he hL.le
  nlinarith

/-- The same clean tail allows one additional deterministic success.  This
permits a link-packing load to include its own link's round. -/
theorem upper_tail_of_budget_half_add_one {t : ℕ} (ht : 0 < t) (X : Process t)
    (p : ℕ → ℝ) (q : ℕ) (L : ℝ) (hL : 8 ≤ L)
    (hlocal : ∀ s < q, ∀ h : Fin s → Fin t, localMean X s h ≤ p s)
    (hbudget : (∑ s ∈ Finset.range q, p s) ≤ L / 2 + 1) :
    MatchingProbability.probability (weight t q) (fun ω => L < (count X q ω : ℝ)) ≤
      Real.exp (-L / 24) := by
  refine (exponential_upper_tail ht X p q (1 / 4) L (by norm_num) hlocal).trans ?_
  apply Real.exp_le_exp.mpr
  have hc : 0 ≤ Real.exp (1 / 4 : ℝ) - 1 := by
    have := Real.exp_le_exp.mpr (show (0 : ℝ) ≤ 1 / 4 by norm_num)
    simpa only [Real.exp_zero, sub_nonneg] using this
  have hμ := mul_le_mul_of_nonneg_left hbudget hc
  have he := Bernoulli.exp_quadratic_bound (1 / 4 : ℝ) (by norm_num)
  have hscaled := mul_le_mul_of_nonneg_right he (show 0 ≤ L / 2 + 1 by linarith)
  nlinarith

end Overfull.PredictableBernoulli
