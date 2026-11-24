import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic

/-!
# Uniform finite scales for robust partition refinement

The number of refinement stages depends only on the density lower bound.
The complete scale sequence is chosen from that bound, the tested range,
and the prescribed error function before the graph is introduced.
-/

noncomputable section

namespace Overfull.RobustPartition

/-- A finite ladder with precisely the margins used by the graph split.
The final scale is available for the terminal rank contradiction. -/
structure ScaleLadder (a τ : ℝ) (f : ℝ → ℝ) (K : ℕ) where
  rho : ℕ → ℝ
  nu : ℕ → ℝ
  gamma : ℝ
  gamma_pos : 0 < gamma
  rho_pos : ∀ i ≤ K, 0 < rho i
  nu_pos : ∀ i ≤ K, 0 < nu i
  rho_le_nu : ∀ i ≤ K, rho i ≤ nu i
  nu_le_range : ∀ i ≤ K, nu i ≤ τ
  rho_le_function : ∀ i ≤ K, rho i ≤ f (nu i)
  rho_small : ∀ i ≤ K, rho i ≤ a ^ 2 / 4
  rho_le_one : ∀ i ≤ K, rho i ≤ 1
  gamma_le_rho : ∀ i ≤ K, gamma ≤ rho i
  gamma_le_nu : ∀ i ≤ K, gamma ≤ nu i
  error_le_nu : ∀ i ≤ K, rho i ^ 2 ≤ nu i
  error_mono : ∀ i < K, rho i ^ 2 ≤ rho (i + 1) ^ 2
  split_range : ∀ i < K, 100 * rho (i + 1) ^ 2 ≤ τ * a ^ 2
  split_expansion : ∀ i < K, 200 * nu i ≤ a * rho (i + 1) ^ 2

/-- One backward step chooses the next expansion parameter before the
current error, so an arbitrary positive error function can be respected. -/
theorem exists_scale_ladder (a τ : ℝ) (f : ℝ → ℝ)
    (ha : 0 < a) (ha1 : a ≤ 1) (hτ : 0 < τ) (hτ1 : τ ≤ 1 / 2)
    (hf : ∀ x, 0 < x → x < 1 → 0 < f x) (K : ℕ) :
    Nonempty (ScaleLadder a τ f K) := by
  let c : ℝ := τ * a ^ 2 / 1000
  have hc : 0 < c := by dsimp [c]; positivity
  have hcτ : c ≤ τ := by
    have ha2 : a ^ 2 ≤ 1 := by nlinarith
    dsimp [c]
    nlinarith [mul_le_mul_of_nonneg_left ha2 hτ.le]
  have hc1 : c < 1 := by linarith
  have hca : c ≤ a ^ 2 / 4 := by
    dsimp [c]
    have h := mul_le_mul_of_nonneg_right hτ1 (sq_nonneg a)
    nlinarith
  have hc_split : 100 * c ^ 2 ≤ τ * a ^ 2 := by
    have hcc : c ^ 2 ≤ c := by nlinarith
    dsimp [c] at hcc ⊢
    nlinarith
  have hfinite : ∀ k : ℕ, ∃ r v : ℕ → ℝ,
      (∀ i ≤ k, 0 < r i ∧ r i ≤ v i ∧ 0 < v i ∧ v i ≤ c ∧
        r i ≤ f (v i)) ∧
      (∀ i < k, r i ≤ r (i + 1) ∧
        200 * v i ≤ a * r (i + 1) ^ 2) := by
    intro k
    induction k with
    | zero =>
        let v : ℝ := c / 2
        let r : ℝ := min (v / 2) (f v / 2)
        have hv : 0 < v := by dsimp [v]; positivity
        have hv1 : v < 1 := by dsimp [v]; linarith
        have hfv : 0 < f v := hf v hv hv1
        refine ⟨fun _ => r, fun _ => v, ?_, ?_⟩
        · intro i _
          dsimp only
          refine ⟨lt_min (by positivity) (by positivity), ?_, hv, ?_, ?_⟩
          · exact (min_le_left _ _).trans (by linarith)
          · dsimp [v]; linarith
          · exact (min_le_right _ _).trans (by linarith)
        · intro i hi
          exact False.elim (Nat.not_lt_zero i hi)
    | succ k ih =>
        obtain ⟨r, v, hrv, hstep⟩ := ih
        let v₀ : ℝ := a * r 0 ^ 2 / 1000
        let r₀ : ℝ := min (v₀ / 2) (f v₀ / 2)
        have hr0 := hrv 0 (Nat.zero_le k)
        have hv₀ : 0 < v₀ := by
          exact div_pos (mul_pos ha (sq_pos_of_pos hr0.1)) (by norm_num)
        have hr0c : r 0 ≤ c := hr0.2.1.trans hr0.2.2.2.1
        have hr01 : r 0 < 1 := hr0c.trans_lt hc1
        have hv₀r : v₀ ≤ r 0 := by
          have hsq : r 0 ^ 2 ≤ r 0 := by nlinarith [hr0.1]
          have hmul := mul_le_mul_of_nonneg_right ha1 (sq_nonneg (r 0))
          dsimp [v₀]
          nlinarith
        have hv₀1 : v₀ < 1 := hv₀r.trans_lt hr01
        have hfv₀ := hf v₀ hv₀ hv₀1
        let r' : ℕ → ℝ := fun i => match i with | 0 => r₀ | j + 1 => r j
        let v' : ℕ → ℝ := fun i => match i with | 0 => v₀ | j + 1 => v j
        refine ⟨r', v', ?_, ?_⟩
        · intro i hi
          cases i with
          | zero =>
              change 0 < r₀ ∧ r₀ ≤ v₀ ∧ 0 < v₀ ∧ v₀ ≤ c ∧ r₀ ≤ f v₀
              refine ⟨lt_min (by positivity) (by positivity), ?_, hv₀,
                hv₀r.trans hr0c, ?_⟩
              · exact (min_le_left _ _).trans (by linarith)
              · exact (min_le_right _ _).trans (by linarith)
          | succ i => exact hrv i (Nat.le_of_succ_le_succ hi)
        · intro i hi
          cases i with
          | zero =>
              change r₀ ≤ r 0 ∧ 200 * v₀ ≤ a * r 0 ^ 2
              constructor
              · exact (min_le_left _ _).trans ((by linarith : v₀ / 2 ≤ v₀).trans hv₀r)
              · dsimp [v₀]; nlinarith [mul_pos ha (sq_pos_of_pos hr0.1)]
          | succ i => exact hstep i (Nat.lt_of_succ_lt_succ hi)
  obtain ⟨r, v, hrv, hstep⟩ := hfinite K
  have hrmono : ∀ i ≤ K, r 0 ≤ r i := by
    intro i
    induction i with
    | zero => intro _; exact le_rfl
    | succ i ih =>
        intro hi
        exact (ih (Nat.le_trans (Nat.le_succ i) hi)).trans
          (hstep i (Nat.lt_of_lt_of_le (Nat.lt_succ_self i) hi)).1
  have hrsmall (i : ℕ) (hi : i ≤ K) : r i ≤ c :=
    (hrv i hi).2.1.trans (hrv i hi).2.2.2.1
  have hr1 (i : ℕ) (hi : i ≤ K) : r i ≤ 1 := (hrsmall i hi).trans hc1.le
  have hrzero : 0 < r 0 := (hrv 0 (Nat.zero_le K)).1
  have hgamr0 : r 0 ^ 2 ≤ r 0 := by nlinarith [hr1 0 (Nat.zero_le K)]
  refine ⟨{
    rho := r
    nu := v
    gamma := r 0 ^ 2
    gamma_pos := sq_pos_of_pos hrzero
    rho_pos := fun i hi => (hrv i hi).1
    nu_pos := fun i hi => (hrv i hi).2.2.1
    rho_le_nu := fun i hi => (hrv i hi).2.1
    nu_le_range := fun i hi => (hrv i hi).2.2.2.1.trans hcτ
    rho_le_function := fun i hi => (hrv i hi).2.2.2.2
    rho_small := fun i hi => (hrsmall i hi).trans hca
    rho_le_one := hr1
    gamma_le_rho := fun i hi => hgamr0.trans (hrmono i hi)
    gamma_le_nu := fun i hi => (hgamr0.trans (hrmono i hi)).trans (hrv i hi).2.1
    error_le_nu := ?_
    error_mono := ?_
    split_range := ?_
    split_expansion := fun i hi => (hstep i hi).2 }⟩
  · intro i hi
    have hri := (hrv i hi).1
    have hr := hr1 i hi
    exact (by nlinarith : r i ^ 2 ≤ r i).trans (hrv i hi).2.1
  · intro i hi
    have h := (hstep i hi).1
    exact pow_le_pow_left₀ (hrv i hi.le).1.le h 2
  · intro i hi
    have hri := hrsmall (i + 1) (Nat.succ_le_of_lt hi)
    have hs := pow_le_pow_left₀ (hrv (i + 1) (Nat.succ_le_of_lt hi)).1.le hri 2
    exact (mul_le_mul_of_nonneg_left hs (by norm_num)).trans hc_split

end Overfull.RobustPartition
