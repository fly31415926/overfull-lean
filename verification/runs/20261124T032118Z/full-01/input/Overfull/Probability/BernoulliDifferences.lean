import Overfull.Probability.IndependentBernoulli
import Overfull.Probability.WeightedSampling

/-!
# Variance-sensitive bounded differences for finite Bernoulli products

The distribution is the actual product of the prescribed Bernoulli masses.
Integrating out the last coordinate gives the finite conditional mean on
the preceding prefix. Its coordinate oscillations are proved from those
of the original statistic. Iterating this identity proves the exponential
moment bound without a conditional-moment or martingale hypothesis.
-/

noncomputable section

namespace Overfull.BernoulliDifferences

open Finset Classical FiniteProbability
open scoped BigOperators

variable {E : Type*} [Fintype E]

/-- Changing only coordinate `e` changes the actual statistic by at most `c e`. -/
def CoordinateBound (f : (E → Bool) → ℝ) (c : E → ℝ) : Prop :=
  ∀ e ω ω', (∀ j, j ≠ e → ω j = ω' j) → |f ω - f ω'| ≤ c e

omit [Fintype E] in
/-- It suffices to check the true/false toggle in each coordinate. -/
theorem coordinateBound_of_boolean_update [DecidableEq E]
    (f : (E → Bool) → ℝ) (c : E → ℝ) (hc : ∀ e, 0 ≤ c e)
    (hf : ∀ e ω,
      |f (Function.update ω e true) - f (Function.update ω e false)| ≤ c e) :
    CoordinateBound f c := by
  intro e ω ω' hω
  have hu : Function.update ω e (ω' e) = ω' := by
    funext j
    by_cases hj : j = e
    · subst j; simp
    · simpa only [Function.update_of_ne hj] using hω j hj
  have hb : |f (Function.update ω e (ω e)) -
      f (Function.update ω e (ω' e))| ≤ c e := by
    cases ω e <;> cases ω' e
    · simpa only [sub_self, abs_zero] using hc e
    · simpa only [abs_sub_comm] using hf e ω
    · exact hf e ω
    · simpa only [sub_self, abs_zero] using hc e
  simpa only [Function.update_eq_self, hu] using hb

/-- The Bernoulli variance budget of the prescribed coordinate changes. -/
def varianceBudget (p c : E → ℝ) : ℝ := ∑ e, p e * (1 - p e) * (c e) ^ 2

theorem exp_quadratic_unit (x : ℝ) (hx : |x| ≤ 1) :
    Real.exp x ≤ 1 + x + x ^ 2 := by
  have h := Real.exp_bound hx (n := 3) (by decide)
  norm_num [Finset.sum_range_succ] at h
  have hu := (abs_le.mp h).2
  have hc : |x| ^ 3 ≤ x ^ 2 := by
    have hm := mul_le_mul_of_nonneg_right hx (sq_nonneg x)
    rw [pow_succ, sq_abs]
    nlinarith
  nlinarith [sq_nonneg x]

theorem mass_nonneg (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (b : Bool) :
    0 ≤ Bernoulli.mass p b := by
  cases b <;> simp only [Bernoulli.mass, Bool.false_eq_true, if_false, if_true]
  · linarith
  · exact hp

theorem sum_mass (p : ℝ) : (∑ b : Bool, Bernoulli.mass p b) = 1 := by
  simp [Bernoulli.mass]

theorem mean_bool (p : ℝ) (f : Bool → ℝ) :
    mean (Bernoulli.mass p) f = (1 - p) * f false + p * f true := by
  simp [mean, Bernoulli.mass, add_comm]

/-- Exact two-point centering, followed by the unit-interval Taylor estimate. -/
theorem bernoulli_centered_moment (p a b c θ : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hc : 0 ≤ c)
    (hab : |b - a| ≤ c) (hθ : 0 ≤ θ) (hθc : θ * c ≤ 1) :
    (1 - p) * Real.exp (θ * (a - ((1 - p) * a + p * b))) +
      p * Real.exp (θ * (b - ((1 - p) * a + p * b))) ≤
        Real.exp (θ ^ 2 * (p * (1 - p) * c ^ 2)) := by
  have hpc : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  have hd : |θ * (b - a)| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hθ]
    exact (mul_le_mul_of_nonneg_left hab hθ).trans hθc
  have h0 : |-(p * (θ * (b - a)))| ≤ 1 := by
    rw [abs_neg, abs_mul, abs_of_nonneg hp]
    exact (mul_le_of_le_one_left (abs_nonneg _) hp1).trans hd
  have h1 : |(1 - p) * (θ * (b - a))| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hpc]
    exact (mul_le_of_le_one_left (abs_nonneg _) (by linarith : 1 - p ≤ 1)).trans hd
  have he0 := mul_le_mul_of_nonneg_left
    (exp_quadratic_unit (-(p * (θ * (b - a)))) h0) hpc
  have he1 := mul_le_mul_of_nonneg_left
    (exp_quadratic_unit ((1 - p) * (θ * (b - a))) h1) hp
  have hs : (b - a) ^ 2 ≤ c ^ 2 := by
    have hh := (sq_le_sq₀ (abs_nonneg (b - a)) hc).mpr hab
    simpa only [sq_abs] using hh
  have hs' := mul_le_mul_of_nonneg_left hs
    (mul_nonneg (sq_nonneg θ) (mul_nonneg hp hpc))
  have he := Real.add_one_le_exp (θ ^ 2 * (p * (1 - p) * c ^ 2))
  rw [show θ * (a - ((1 - p) * a + p * b)) = -(p * (θ * (b - a))) by ring,
    show θ * (b - ((1 - p) * a + p * b)) = (1 - p) * (θ * (b - a)) by ring]
  nlinarith

/-- The conditional centered exponential moment for one actual Bernoulli choice. -/
theorem mean_bernoulli_centered_moment (p : ℝ) (f : Bool → ℝ) (c θ : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hc : 0 ≤ c)
    (hf : |f true - f false| ≤ c) (hθ : 0 ≤ θ) (hθc : θ * c ≤ 1) :
    mean (Bernoulli.mass p) (fun b => Real.exp (θ * (f b - mean (Bernoulli.mass p) f))) ≤
      Real.exp (θ ^ 2 * (p * (1 - p) * c ^ 2)) := by
  simp only [mean_bool]
  exact bernoulli_centered_moment p (f false) (f true) c θ hp hp1 hc hf hθ hθc

section Prefix

variable {n : ℕ}

theorem weight_snoc (p : Fin (n + 1) → ℝ) (h : Fin n → Bool) (b : Bool) :
    IndependentBernoulli.weight p (Fin.snoc h b) =
      Bernoulli.mass (p (Fin.last n)) b *
        IndependentBernoulli.weight (fun i => p i.castSucc) h := by
  simp only [IndependentBernoulli.weight, Fin.prod_univ_castSucc,
    Fin.snoc_castSucc, Fin.snoc_last]
  exact mul_comm _ _

/-- Actual conditional averaging on a prefix, including probabilities zero and one. -/
theorem mean_snoc (p : Fin (n + 1) → ℝ) (f : (Fin (n + 1) → Bool) → ℝ) :
    mean (IndependentBernoulli.weight p) f =
      mean (IndependentBernoulli.weight (fun i => p i.castSucc))
        (fun h => mean (Bernoulli.mass (p (Fin.last n))) (fun b => f (Fin.snoc h b))) := by
  let e := Fin.snocEquiv (fun _ : Fin (n + 1) => Bool)
  have he := mean_equiv e (IndependentBernoulli.weight p) f
  change mean (fun bh : Bool × (Fin n → Bool) =>
      IndependentBernoulli.weight p (Fin.snoc bh.2 bh.1))
      (fun bh => f (Fin.snoc bh.2 bh.1)) = _ at he
  rw [← he]
  simp only [mean, weight_snoc, Fintype.sum_prod_type, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- Averaging the last independent coordinate preserves every earlier
coordinate oscillation; this proves the needed bound on the conditional mean. -/
theorem coordinateBound_mean_last (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (f : (Fin (n + 1) → Bool) → ℝ) (c : Fin (n + 1) → ℝ)
    (hf : CoordinateBound f c) :
    CoordinateBound
      (fun h => mean (Bernoulli.mass p) (fun b => f (Fin.snoc h b)))
      (fun i => c i.castSucc) := by
  intro i h h' hh
  have hb (b : Bool) : |f (Fin.snoc h b) - f (Fin.snoc h' b)| ≤ c i.castSucc := by
    apply hf i.castSucc
    intro j hj
    revert hj
    refine Fin.lastCases ?_ (fun k => ?_) j
    · intro _; simp
    · intro hj
      simp only [Fin.snoc_castSucc]
      apply hh k
      intro hki
      exact hj (by simp only [hki])
  rw [← mean_sub]
  apply abs_le.mpr
  constructor
  · have hm := mean_mono (Bernoulli.mass p) (mass_nonneg p hp hp1)
      (fun b => (abs_le.mp (hb b)).1)
    simpa only [mean_const _ (sum_mass p)] using hm
  · have hm := mean_mono (Bernoulli.mass p) (mass_nonneg p hp hp1)
      (fun b => (abs_le.mp (hb b)).2)
    simpa only [mean_const _ (sum_mass p)] using hm

/-- The full centered moment on an actual finite prefix product. -/
theorem exponential_moment_fin (n : ℕ) (p c : Fin n → ℝ)
    (f : (Fin n → Bool) → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (hc : ∀ i, 0 ≤ c i) (hf : CoordinateBound f c)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθc : ∀ i, θ * c i ≤ 1) :
    mean (IndependentBernoulli.weight p)
        (fun ω => Real.exp (θ * (f ω - mean (IndependentBernoulli.weight p) f))) ≤
      Real.exp (θ ^ 2 * varianceBudget p c) := by
  induction n with
  | zero =>
      have hfconst : f = fun _ => f (fun i => Fin.elim0 i) := by
        funext ω
        congr 1
        funext i
        exact Fin.elim0 i
      rw [hfconst]
      simp [mean_const _ (IndependentBernoulli.sum_weight p), varianceBudget]
  | succ n ih =>
      let q : Fin n → ℝ := fun i => p i.castSucc
      let d : Fin n → ℝ := fun i => c i.castSucc
      let g : (Fin n → Bool) → ℝ := fun h =>
        mean (Bernoulli.mass (p (Fin.last n))) (fun b => f (Fin.snoc h b))
      have hg : CoordinateBound g d :=
        coordinateBound_mean_last _ (hp _) (hp1 _) f c hf
      have hmean : mean (IndependentBernoulli.weight p) f =
          mean (IndependentBernoulli.weight q) g := mean_snoc p f
      have hprev := ih q d g (fun i => hp i.castSucc) (fun i => hp1 i.castSucc)
        (fun i => hc i.castSucc) hg (fun i => hθc i.castSucc)
      rw [hmean, mean_snoc]
      calc
        _ ≤ mean (IndependentBernoulli.weight q) (fun h =>
            Real.exp (θ ^ 2 * (p (Fin.last n) * (1 - p (Fin.last n)) *
              c (Fin.last n) ^ 2)) *
              Real.exp (θ * (g h - mean (IndependentBernoulli.weight q) g))) := by
          apply mean_mono _ (IndependentBernoulli.weight_nonneg q
            (fun i => hp i.castSucc) (fun i => hp1 i.castSucc))
          intro h
          have hosc : |f (Fin.snoc h true) - f (Fin.snoc h false)| ≤ c (Fin.last n) := by
            apply hf (Fin.last n)
            intro j hj
            revert hj
            refine Fin.lastCases ?_ (fun k => ?_) j
            · intro hj; exact (hj rfl).elim
            · intro _; simp
          have hlocal := mean_bernoulli_centered_moment (p (Fin.last n))
            (fun b => f (Fin.snoc h b)) (c (Fin.last n)) θ
            (hp _) (hp1 _) (hc _) hosc hθ (hθc _)
          have heq : (fun b => Real.exp (θ *
              (f (Fin.snoc h b) - mean (IndependentBernoulli.weight q) g))) =
              (fun b => Real.exp (θ * (g h - mean (IndependentBernoulli.weight q) g)) *
                Real.exp (θ * (f (Fin.snoc h b) - g h))) := by
            funext b
            rw [← Real.exp_add]
            congr 1
            ring
          rw [heq, mean_mul_left]
          exact (mul_le_mul_of_nonneg_left hlocal (Real.exp_pos _).le).trans_eq (mul_comm _ _)
        _ = Real.exp (θ ^ 2 * (p (Fin.last n) * (1 - p (Fin.last n)) *
              c (Fin.last n) ^ 2)) *
            mean (IndependentBernoulli.weight q)
              (fun h => Real.exp (θ * (g h - mean (IndependentBernoulli.weight q) g))) :=
          mean_mul_left _ _ _
        _ ≤ Real.exp (θ ^ 2 * (p (Fin.last n) * (1 - p (Fin.last n)) *
              c (Fin.last n) ^ 2)) * Real.exp (θ ^ 2 * varianceBudget q d) :=
          mul_le_mul_of_nonneg_left hprev (Real.exp_pos _).le
        _ = _ := by
          rw [← Real.exp_add]
          congr 1
          simp only [varianceBudget, Fin.sum_univ_castSucc]
          dsimp [q, d]
          ring

end Prefix

section Reindex

variable {F : Type*} [Fintype F]

theorem weight_reindex (e : E ≃ F) (p : F → ℝ) (ω : E → Bool) :
    IndependentBernoulli.weight (fun i => p (e i)) ω =
      IndependentBernoulli.weight p (fun j => ω (e.symm j)) := by
  unfold IndependentBernoulli.weight
  simpa only [Equiv.symm_apply_apply] using
    e.prod_comp (fun j => Bernoulli.mass (p j) (ω (e.symm j)))

/-- Relabeling the coordinates preserves the actual product expectation. -/
theorem mean_reindex [DecidableEq E] [DecidableEq F]
    (e : E ≃ F) (p : F → ℝ) (f : (F → Bool) → ℝ) :
    mean (IndependentBernoulli.weight (fun i => p (e i)))
        (fun ω => f (fun j => ω (e.symm j))) =
      mean (IndependentBernoulli.weight p) f := by
  have h := mean_equiv (Equiv.arrowCongr e (Equiv.refl Bool))
    (IndependentBernoulli.weight p) f
  change mean (fun ω : E → Bool =>
      IndependentBernoulli.weight p (fun j => ω (e.symm j)))
      (fun ω => f (fun j => ω (e.symm j))) = _ at h
  simpa only [← weight_reindex] using h

omit [Fintype E] [Fintype F] in
theorem coordinateBound_reindex (e : E ≃ F) (f : (F → Bool) → ℝ)
    (c : F → ℝ) (hf : CoordinateBound f c) :
    CoordinateBound (fun ω : E → Bool => f (fun j => ω (e.symm j)))
      (fun i => c (e i)) := by
  intro i ω ω' hω
  apply hf (e i)
  intro j hj
  apply hω (e.symm j)
  intro h
  apply hj
  simpa only [Equiv.apply_symm_apply] using congrArg e h

end Reindex

/-- Variance-sensitive bounded differences for an arbitrary finite coordinate
type. All probabilistic quantities are computed from the Bernoulli product
mass, and the only hypothesis on the statistic is its coordinate oscillation. -/
theorem exponential_moment_le (p c : E → ℝ) (f : (E → Bool) → ℝ)
    (hp : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1) (hc : ∀ e, 0 ≤ c e)
    (hf : CoordinateBound f c) (θ : ℝ) (hθ : 0 ≤ θ)
    (hθc : ∀ e, θ * c e ≤ 1) :
    mean (IndependentBernoulli.weight p)
        (fun ω => Real.exp (θ * (f ω - mean (IndependentBernoulli.weight p) f))) ≤
      Real.exp (θ ^ 2 * varianceBudget p c) := by
  let e : Fin (Fintype.card E) ≃ E := (Fintype.equivFin E).symm
  let q : Fin (Fintype.card E) → ℝ := fun i => p (e i)
  let d : Fin (Fintype.card E) → ℝ := fun i => c (e i)
  let g : (Fin (Fintype.card E) → Bool) → ℝ := fun ω => f (fun j => ω (e.symm j))
  have h := exponential_moment_fin (Fintype.card E)
    q d g
    (fun i => hp (e i)) (fun i => hp1 (e i)) (fun i => hc (e i))
    (coordinateBound_reindex e f c hf) θ hθ (fun i => hθc (e i))
  have hm : mean (IndependentBernoulli.weight q) g =
      mean (IndependentBernoulli.weight p) f := mean_reindex e p f
  have hmexp : mean (IndependentBernoulli.weight q)
      (fun ω => Real.exp (θ * (g ω - mean (IndependentBernoulli.weight p) f))) =
      mean (IndependentBernoulli.weight p)
      (fun ω => Real.exp (θ * (f ω - mean (IndependentBernoulli.weight p) f))) :=
    mean_reindex e p (fun ω => Real.exp (θ * (f ω - mean (IndependentBernoulli.weight p) f)))
  rw [hm, hmexp] at h
  have hv : varianceBudget q d =
      varianceBudget p c := e.sum_comp (fun j => p j * (1 - p j) * c j ^ 2)
  simpa only [hv] using h

theorem varianceBudget_nonneg (p c : E → ℝ)
    (hp : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1) : 0 ≤ varianceBudget p c := by
  exact Finset.sum_nonneg (fun e _ =>
    mul_nonneg (mul_nonneg (hp e) (sub_nonneg.mpr (hp1 e))) (sq_nonneg _))

/-- The looser budget discards the factors `1-p e`; useful for rare edge coins. -/
theorem varianceBudget_le (p c : E → ℝ)
    (hp : ∀ e, 0 ≤ p e) :
    varianceBudget p c ≤ ∑ e, p e * c e ^ 2 := by
  apply Finset.sum_le_sum
  intro e _
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact (mul_le_mul_of_nonneg_left (by linarith [hp e] : 1 - p e ≤ 1) (hp e)).trans_eq
    (mul_one _)

/-- A convenient uniform-coordinate version with any proved variance budget. -/
theorem exponential_moment_le_of_budget (p c : E → ℝ) (f : (E → Bool) → ℝ)
    (hp : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1) (hc : ∀ e, 0 ≤ c e)
    (hf : CoordinateBound f c) (C V θ : ℝ) (hcC : ∀ e, c e ≤ C)
    (hV : varianceBudget p c ≤ V) (hθ : 0 ≤ θ) (hθC : θ * C ≤ 1) :
    mean (IndependentBernoulli.weight p)
        (fun ω => Real.exp (θ * (f ω - mean (IndependentBernoulli.weight p) f))) ≤
      Real.exp (θ ^ 2 * V) := by
  exact (exponential_moment_le p c f hp hp1 hc hf θ hθ
    (fun e => (mul_le_mul_of_nonneg_left (hcC e) hθ).trans hθC)).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hV (sq_nonneg θ)))

omit [Fintype E] in
theorem CoordinateBound.neg {f : (E → Bool) → ℝ} {c : E → ℝ}
    (hf : CoordinateBound f c) : CoordinateBound (fun ω => -f ω) c := by
  intro e ω ω' hω
  simpa only [neg_sub_neg, abs_sub_comm] using hf e ω ω' hω

/-- Exponential Markov applied to the proved centered product moment. -/
theorem upper_tail (p c : E → ℝ) (f : (E → Bool) → ℝ)
    (hp : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1) (hc : ∀ e, 0 ≤ c e)
    (hf : CoordinateBound f c) (θ t : ℝ) (hθ : 0 ≤ θ)
    (hθc : ∀ e, θ * c e ≤ 1) :
    IndependentBernoulli.probability p
        (fun ω => t ≤ f ω - mean (IndependentBernoulli.weight p) f) ≤
      Real.exp (θ ^ 2 * varianceBudget p c - θ * t) := by
  have hm := MatchingProbability.probability_markov (IndependentBernoulli.weight p)
    (IndependentBernoulli.weight_nonneg p hp hp1)
    (fun ω => Real.exp (θ * (f ω - mean (IndependentBernoulli.weight p) f)))
    (fun _ => (Real.exp_pos _).le) (Real.exp (θ * t))
    (fun ω => t ≤ f ω - mean (IndependentBernoulli.weight p) f)
    (fun _ h => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h hθ))
  have hb := exponential_moment_le p c f hp hp1 hc hf θ hθ hθc
  have hmul := mul_le_mul_of_nonneg_left (hm.trans hb) (Real.exp_pos (-θ * t)).le
  have hcancel : Real.exp (-θ * t) * Real.exp (θ * t) = 1 := by
    rw [← Real.exp_add, show -θ * t + θ * t = 0 by ring, Real.exp_zero]
  rw [← mul_assoc, hcancel, one_mul, ← Real.exp_add] at hmul
  convert hmul using 1
  congr 1
  ring

theorem lower_tail (p c : E → ℝ) (f : (E → Bool) → ℝ)
    (hp : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1) (hc : ∀ e, 0 ≤ c e)
    (hf : CoordinateBound f c) (θ t : ℝ) (hθ : 0 ≤ θ)
    (hθc : ∀ e, θ * c e ≤ 1) :
    IndependentBernoulli.probability p
        (fun ω => t ≤ mean (IndependentBernoulli.weight p) f - f ω) ≤
      Real.exp (θ ^ 2 * varianceBudget p c - θ * t) := by
  have h := upper_tail p c (fun ω => -f ω) hp hp1 hc hf.neg θ t hθ hθc
  have hm : mean (IndependentBernoulli.weight p) (fun ω => -f ω) =
      -mean (IndependentBernoulli.weight p) f := by
    simpa only [neg_one_mul] using mean_mul_left (IndependentBernoulli.weight p) (-1) f
  simpa only [hm, sub_neg_eq_add, neg_add_eq_sub] using h

/-- Two-sided concentration with the true Bernoulli variance proxy. -/
theorem two_sided_tail (p c : E → ℝ) (f : (E → Bool) → ℝ)
    (hp : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1) (hc : ∀ e, 0 ≤ c e)
    (hf : CoordinateBound f c) (θ t : ℝ) (hθ : 0 ≤ θ)
    (hθc : ∀ e, θ * c e ≤ 1) :
    IndependentBernoulli.probability p
        (fun ω => t ≤ |f ω - mean (IndependentBernoulli.weight p) f|) ≤
      2 * Real.exp (θ ^ 2 * varianceBudget p c - θ * t) := by
  have hu := upper_tail p c f hp hp1 hc hf θ t hθ hθc
  have hl := lower_tail p c f hp hp1 hc hf θ t hθ hθc
  calc
    _ ≤ IndependentBernoulli.probability p (fun ω =>
        t ≤ f ω - mean (IndependentBernoulli.weight p) f ∨
        t ≤ mean (IndependentBernoulli.weight p) f - f ω) := by
      apply IndependentBernoulli.probability_mono p hp hp1
      intro ω hω
      rcases le_abs.mp hω with h | h
      · exact Or.inl h
      · exact Or.inr (by linarith)
    _ ≤ IndependentBernoulli.probability p (fun ω =>
        t ≤ f ω - mean (IndependentBernoulli.weight p) f) +
        IndependentBernoulli.probability p (fun ω =>
        t ≤ mean (IndependentBernoulli.weight p) f - f ω) :=
      MatchingProbability.probability_union_le _ (IndependentBernoulli.weight_nonneg p hp hp1) _ _
    _ ≤ _ := by linarith

/-- A user-supplied upper bound on the explicitly computed variance budget
and a uniform coordinate bound give the common application interface. -/
theorem two_sided_tail_of_budget (p c : E → ℝ) (f : (E → Bool) → ℝ)
    (hp : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1) (hc : ∀ e, 0 ≤ c e)
    (hf : CoordinateBound f c) (C V θ t : ℝ) (hcC : ∀ e, c e ≤ C)
    (hV : varianceBudget p c ≤ V) (hθ : 0 ≤ θ) (hθC : θ * C ≤ 1) :
    IndependentBernoulli.probability p
        (fun ω => t ≤ |f ω - mean (IndependentBernoulli.weight p) f|) ≤
      2 * Real.exp (θ ^ 2 * V - θ * t) := by
  refine (two_sided_tail p c f hp hp1 hc hf θ t hθ
    (fun e => (mul_le_mul_of_nonneg_left (hcC e) hθ).trans hθC)).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply Real.exp_le_exp.mpr
  exact sub_le_sub_right (mul_le_mul_of_nonneg_left hV (sq_nonneg θ)) _

end Overfull.BernoulliDifferences
