import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic

/-!
# Uniform scalar bounds for four foreign-edge epochs

Packing tolerances and thresholds are fixed first.  One original error
and one order threshold then absorb all three possible vertex moves, both
in the core order and in the exceptional order.  No choice depends on the
eventual graph or its exceptional order.
-/

namespace Overfull.ForeignEpochParameters

open Finset Classical

/-- Three quarters of the initial integer degree fit in the actual
floor-valued packing horizon whenever the reserved degree is at most a
quarter. -/
theorem color_horizon_le_packing_horizon (h m : ℕ) (γ : ℝ)
    (hreserve : γ*m ≤ (h : ℝ)/4) :
    3*h/4 ≤ Nat.floor ((h : ℝ)-γ*m) := by
  apply Nat.le_floor
  have hdiv : 4*(3*h/4) ≤ 3*h := Nat.mul_div_le _ _
  have hdivR : 4*((3*h/4 : ℕ) : ℝ) ≤ 3*h := by exact_mod_cast hdiv
  linarith

/-- A single reserve density works for every core and every phase-start
degree retained by the four-phase degree bound. -/
theorem common_reserve (α γ : ℝ) (n m k₀ h : ℕ)
    (hγ : 0 ≤ γ) (hγsmall : γ ≤ α/1024)
    (hm : m ≤ n) (hdensity : α*n ≤ k₀) (hdegree : k₀ ≤ 256*h) :
    γ*m ≤ (h : ℝ)/4 := by
  have hmR : (m : ℝ) ≤ n := by exact_mod_cast hm
  have hdegreeR : (k₀ : ℝ) ≤ 256*h := by exact_mod_cast hdegree
  have hmultiply := mul_le_mul_of_nonneg_left hmR hγ
  have hsmall := mul_le_mul_of_nonneg_right hγsmall (Nat.cast_nonneg n)
  nlinarith

/-- The stronger retained-degree bound gives the strict reserve required
by safe prescription, including the small positive-degree cases. -/
theorem strict_safe_reserve (k₀ h : ℕ) (hk : 0 < k₀) (hreserve : k₀ ≤ 256*h) :
    (k₀ : ℝ)/1024 < h := by
  have hkR : (0 : ℝ) < k₀ := by exact_mod_cast hk
  have hreserveR : (k₀ : ℝ) ≤ 256*h := by exact_mod_cast hreserve
  linarith

/-- Four prescribed tolerances and thresholds admit one initial error
and order threshold.  Every core obtained by at most three vertex moves
meets every phase threshold, the combined error budget, and the actual
exceptional-matching footprint bound.  The exceptional size may vary with
the graph order. -/
theorem exists_uniform_epoch_parameters (α : ℝ) (hα : 0 < α)
    (δ : Fin 4 → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin 4 → ℕ) (q : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ,
      ∀ (n m t t' r : ℕ) (a a' : ℝ),
        n₀ ≤ n → m ≤ n → α*n ≤ m → r ≤ 3 →
        0 ≤ a → a' ≤ a+3 → t' ≤ t+3 → a+(t : ℝ)+1 ≤ ε*n →
        0 < n ∧ (α/2)*n ≤ ((m-r : ℕ) : ℝ) ∧ m-r ≤ n ∧
        ∀ j : Fin 4,
          N j ≤ m-r ∧
          a'+(t' : ℝ)+1 ≤ δ j*(m-r : ℕ) ∧
          ((2*(q+t'+3) : ℕ) : ℝ) ≤ δ j*(m-r : ℕ) := by
  let d : ℝ := univ.inf' univ_nonempty δ
  have hd : 0 < d := (lt_inf'_iff _).mpr (fun j _ => hδ j)
  have hdj (j : Fin 4) : d ≤ δ j := inf'_le δ (mem_univ j)
  let ε : ℝ := d*α/32
  have hε : 0 < ε := by dsimp [ε]; positivity
  let B : ℝ := max 1 (max (6/α)
    (max (2*((univ.sup N : ℕ)+1)/α) (16*((q : ℝ)+10)/(d*α))))
  obtain ⟨n₀,hn₀⟩ := exists_nat_gt B
  refine ⟨ε,hε,n₀,?_⟩
  intro n m t t' r a a' hn hmn hm hr ha haa htt hbudget
  have hbig : B < (n : ℝ) := hn₀.trans_le (by exact_mod_cast hn)
  have hB1 : (1 : ℝ) ≤ B := le_max_left _ _
  have hBsize : 6/α ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hBthreshold : 2*((univ.sup N : ℕ)+1)/α ≤ B :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hBconstant : 16*((q : ℝ)+10)/(d*α) ≤ B :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hnR : (0 : ℝ) < n := (by norm_num : (0 : ℝ) < 1).trans (hB1.trans_lt hbig)
  have hnpos : 0 < n := by exact_mod_cast hnR
  have hsize : (6 : ℝ) < α*n := by
    have hh := (div_lt_iff₀ hα).mp (hBsize.trans_lt hbig)
    nlinarith only [hh]
  have hthreshold : 2*((univ.sup N : ℕ)+1) < α*n := by
    have hh := (div_lt_iff₀ hα).mp (hBthreshold.trans_lt hbig)
    nlinarith only [hh]
  have hconstant : 16*((q : ℝ)+10) < d*α*n := by
    have hh := (div_lt_iff₀ (mul_pos hd hα)).mp (hBconstant.trans_lt hbig)
    nlinarith only [hh]
  have hmthree : 3 ≤ m := by
    have hmR : (3 : ℝ) ≤ m := by linarith
    exact_mod_cast hmR
  have hrm : r ≤ m := hr.trans hmthree
  have hsub : ((m-r : ℕ) : ℝ) = (m : ℝ)-r := Nat.cast_sub hrm
  have hrR : (r : ℝ) ≤ 3 := by exact_mod_cast hr
  have hretained : (α/2)*n ≤ ((m-r : ℕ) : ℝ) := by rw [hsub]; nlinarith
  have hretainedN : m-r ≤ n := (Nat.sub_le _ _).trans hmn
  have httR : (t' : ℝ) ≤ (t : ℝ)+3 := by exact_mod_cast htt
  have hbudget' : a+(t : ℝ)+1 ≤ d*α*n/32 := by
    calc
      _ ≤ ε*n := hbudget
      _ = _ := by dsimp [ε]; ring
  refine ⟨hnpos,hretained,hretainedN,?_⟩
  intro j
  have hNj : N j ≤ univ.sup N := le_sup (mem_univ j)
  have hNjR : (N j : ℝ) ≤ (univ.sup N : ℕ) := by exact_mod_cast hNj
  have hNjretained : (N j : ℝ) ≤ ((m-r : ℕ) : ℝ) := by nlinarith only [hNjR,hthreshold,hretained]
  have hproduct : d*α*n/2 ≤ δ j*((m-r : ℕ) : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hretained hd.le
    have hjmul := mul_le_mul_of_nonneg_right (hdj j) (Nat.cast_nonneg (m-r))
    nlinarith only [hmul,hjmul]
  refine ⟨by exact_mod_cast hNjretained,?_,?_⟩
  · have ht0 : (0 : ℝ) ≤ t := by positivity
    have hq0 : (0 : ℝ) ≤ q := by positivity
    nlinarith only [haa,httR,hbudget',hconstant,hproduct,ht0,hq0]
  · have hcast : ((2*(q+t'+3) : ℕ) : ℝ) = 2*((q : ℝ)+t'+3) := by norm_cast
    rw [hcast]
    nlinarith only [httR,hbudget',ha,hconstant,hproduct]

end Overfull.ForeignEpochParameters
