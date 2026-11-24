import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic

/-!
# Uniform scalar bounds for the forcing phase

The threshold control is fixed before the finite exceptional bound. Once
that bound and the packing parameters are fixed, one original error and
one order threshold supply the inequalities at every actual prefix.
-/

namespace Overfull.AbsorptionParameters

/-- This control is independent of the eventual exceptional bound. -/
noncomputable def firstThresholdBound (α εp : ℝ) : ℝ :=
  min (εp*α/4) (α/160)

theorem firstThresholdBound_pos (α εp : ℝ) (hα : 0 < α) (hεp : 0 < εp) :
    0 < firstThresholdBound α εp := by
  unfold firstThresholdBound
  exact lt_min (by positivity) (by positivity)

theorem firstThresholdBound_packing (α εp : ℝ) :
    firstThresholdBound α εp ≤ εp*α/4 := min_le_left _ _

theorem firstThresholdBound_density (α εp : ℝ) :
    firstThresholdBound α εp ≤ α/160 := min_le_right _ _

/-- All scalar hypotheses needed by one fixed family of forcing rules. -/
structure PhaseScalarBounds (α εp θ ν : ℝ) (T m₀ n h m z p : ℕ)
    (A : ℝ) : Prop where
  order_pos : 0 < n
  degree_pos : 0 < h
  phase_short : 4*p < h
  residual_density : (α/4)*n ≤ ((h-p-1 : ℕ) : ℝ)
  error_nonneg : 0 ≤ A
  packing_error : A ≤ εp*m
  safe_error : A ≤ (α/4)*n/10
  packing_order : m₀ ≤ m
  footprint : ((2*T+6 : ℕ) : ℝ) ≤ εp*m
  robust_cut : 3 < θ^2*(α/4)^2*n
  input_addition : (z : ℝ) ≤ ν*m/4
  output_addition : (z : ℝ) ≤ θ*m/4
  horizon : p ≤ Nat.floor ((h : ℝ)-(α/4)*m)

/-- The original error and graph-order threshold are uniform in all graph
data and every prefix controlled by the initial forcing potential.
`firstThresholdBound α εp` has already been fixed before `T`. -/
theorem exists_uniform_phase_parameters (α εp θ ν : ℝ)
    (hα : 0 < α) (hεp : 0 < εp) (hθ : 0 < θ) (hν : 0 < ν)
    (T m₀ : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ,
      ∀ (n h m z p : ℕ) (a ρ : ℝ), N ≤ n →
        α*n ≤ h → h ≤ n → α*n ≤ m → m ≤ n →
        0 ≤ a → a+(z : ℝ)+1 ≤ ε*n →
        0 ≤ ρ → ρ ≤ firstThresholdBound α εp →
        (p : ℝ) ≤ (h : ℝ)/8+(T : ℝ)*z →
        PhaseScalarBounds α εp θ ν T m₀ n h m z p (a+ρ*h+z) := by
  let κ := firstThresholdBound α εp
  have hκ : 0 < κ := firstThresholdBound_pos α εp hα hεp
  let ε := min κ (min (α/(32*((T : ℝ)+1))) (min (ν*α/4) (θ*α/4)))
  have hε : 0 < ε := by
    dsimp [ε]
    exact lt_min hκ (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have hεκ : ε ≤ κ := min_le_left _ _
  have hεT : ε ≤ α/(32*((T : ℝ)+1)) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hεν : ε ≤ ν*α/4 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεθ : ε ≤ θ*α/4 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hκpack : κ ≤ εp*α/4 := firstThresholdBound_packing α εp
  have hκdensity : κ ≤ α/160 := firstThresholdBound_density α εp
  have hTε : (T : ℝ)*ε ≤ α/32 := by
    have hscaled := (le_div_iff₀ (by positivity : 0 < 32*((T : ℝ)+1))).mp hεT
    nlinarith only [hscaled, hε]
  let b := θ^2*(α/4)^2
  have hb : 0 < b := by dsimp [b]; positivity
  let B := max 1 (max (8/α) (max ((m₀ : ℝ)/α)
    (max (((2*T+6 : ℕ) : ℝ)/(εp*α)) (4/b))))
  obtain ⟨N, hN⟩ := exists_nat_gt B
  refine ⟨ε, hε, N, ?_⟩
  intro n h m z p a ρ hn hdegree hhn hcore hmn ha herror hρ hρκ hp
  have hbig : B < (n : ℝ) := hN.trans_le (by exact_mod_cast hn)
  have hB1 : (1 : ℝ) ≤ B := le_max_left _ _
  have hBdegree : 8/α ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hBorder : (m₀ : ℝ)/α ≤ B :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hBfoot : ((2*T+6 : ℕ) : ℝ)/(εp*α) ≤ B :=
    (le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))
  have hBrobust : 4/b ≤ B :=
    (le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))
  have hnR : (0 : ℝ) < n := (by norm_num : (0 : ℝ) < 1).trans
    (hB1.trans_lt hbig)
  have hnpos : 0 < n := by exact_mod_cast hnR
  have hlarge : (8 : ℝ) < α*n := by
    have hh := (div_lt_iff₀ hα).mp (hBdegree.trans_lt hbig)
    nlinarith only [hh]
  have hhR : (0 : ℝ) < h := (mul_pos hα hnR).trans_le hdegree
  have hhpos : 0 < h := by exact_mod_cast hhR
  have hhnR : (h : ℝ) ≤ n := by exact_mod_cast hhn
  have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hz : (z : ℝ) ≤ ε*n := by linarith only [herror, ha]
  have haz : a+(z : ℝ) ≤ ε*n := by linarith only [herror]
  have hTz : (T : ℝ)*z ≤ α*n/32 := by
    have h₁ := mul_le_mul_of_nonneg_left hz (Nat.cast_nonneg T)
    have h₂ := mul_le_mul_of_nonneg_right hTε hnR.le
    nlinarith only [h₁, h₂]
  have hshortR : 4*(p : ℝ) < h := by
    nlinarith only [hp, hTz, hdegree, hhR]
  have hshort : 4*p < h := by exact_mod_cast hshortR
  have hple : p ≤ h := by omega
  have hsubone : 1 ≤ h-p := by omega
  have hsub : ((h-p-1 : ℕ) : ℝ) = (h : ℝ)-p-1 := by
    rw [Nat.cast_sub hsubone, Nat.cast_sub hple, Nat.cast_one]
  have hresidual : (α/4)*n ≤ ((h-p-1 : ℕ) : ℝ) := by
    rw [hsub]
    nlinarith only [hshortR, hlarge, hdegree]
  have hρn : ρ*(h : ℝ) ≤ κ*n :=
    (mul_le_mul_of_nonneg_right hρκ (Nat.cast_nonneg h)).trans
      (mul_le_mul_of_nonneg_left hhnR hκ.le)
  have hεn : ε*(n : ℝ) ≤ κ*n := mul_le_mul_of_nonneg_right hεκ hnR.le
  have hκnpack := mul_le_mul_of_nonneg_right hκpack hnR.le
  have hκndensity := mul_le_mul_of_nonneg_right hκdensity hnR.le
  have hpackcore := mul_le_mul_of_nonneg_left hcore hεp.le
  have hA : 0 ≤ a+ρ*(h : ℝ)+z := by positivity
  have hApack : a+ρ*(h : ℝ)+z ≤ εp*m := by
    nlinarith only [haz, hρn, hεn, hκnpack, hpackcore, hA]
  have hAsafe : a+ρ*(h : ℝ)+z ≤ (α/4)*n/10 := by
    nlinarith only [haz, hρn, hεn, hκndensity, hA]
  have horderR : (m₀ : ℝ) ≤ m := by
    have hh := (div_lt_iff₀ hα).mp (hBorder.trans_lt hbig)
    nlinarith only [hh, hcore]
  have horder : m₀ ≤ m := by exact_mod_cast horderR
  have hfoot : ((2*T+6 : ℕ) : ℝ) ≤ εp*m := by
    have hh := (div_lt_iff₀ (mul_pos hεp hα)).mp (hBfoot.trans_lt hbig)
    nlinarith only [hh, hpackcore]
  have hrobust : 3 < θ^2*(α/4)^2*n := by
    have hh := (div_lt_iff₀ hb).mp (hBrobust.trans_lt hbig)
    change 4 < (n : ℝ)*b at hh
    dsimp [b] at hh
    nlinarith only [hh]
  have hinput : (z : ℝ) ≤ ν*m/4 := by
    have h₁ := mul_le_mul_of_nonneg_right hεν hnR.le
    have h₂ := mul_le_mul_of_nonneg_left hcore hν.le
    nlinarith only [hz, h₁, h₂]
  have houtput : (z : ℝ) ≤ θ*m/4 := by
    have h₁ := mul_le_mul_of_nonneg_right hεθ hnR.le
    have h₂ := mul_le_mul_of_nonneg_left hcore hθ.le
    nlinarith only [hz, h₁, h₂]
  have hhorizon : p ≤ Nat.floor ((h : ℝ)-(α/4)*m) := by
    apply Nat.le_floor
    have hreserve := mul_le_mul_of_nonneg_left hmnR (show 0 ≤ α/4 by positivity)
    nlinarith only [hreserve, hdegree, hshortR]
  exact ⟨hnpos, hhpos, hshort, hresidual, hA, hApack, hAsafe,
    horder, hfoot, hrobust, hinput, houtput, hhorizon⟩

end Overfull.AbsorptionParameters
