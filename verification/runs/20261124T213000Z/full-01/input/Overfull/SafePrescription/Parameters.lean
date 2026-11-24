import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic

namespace Overfull.SafePrescription

/-- Uniform scalar bounds for safe prescription. The exceptional order
`t` is allowed to grow with `n`; both constants precede `t`. -/
theorem exists_prescription_parameters (α ν η : ℝ)
    (hα : 0 < α) (hν : 0 < ν) (hη : 0 < η)
    (nCore t0 q : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ,
      ∀ (n h k0 t : ℕ) (a : ℝ),
        n₀ ≤ n → h ≤ n → α*n ≤ h → (k0 : ℝ) ≤ 1024*h →
        0 ≤ a → a+(t : ℝ)+1 ≤ ε*n →
        0 < n ∧ 0 < h ∧ 44*2^(t0+4) < h ∧
        (α/2)*n ≤ ((h-1 : ℕ) : ℝ) ∧
        (h : ℝ) ≤ 2*n ∧ ((h-1 : ℕ) : ℝ) ≤ 2*n ∧
        a ≤ (α/2)*n/10 ∧
        ((2*(t+t0+q+30) : ℕ) : ℝ) ≤ (α/2)*n/10 ∧
        ((2*(t+t0+q+30) : ℕ) : ℝ) < (h : ℝ)/10 ∧
        3 < (ν/2)^2*α^2*(n : ℝ) ∧
        a ≤ (h : ℝ)/20 ∧ (k0 : ℝ)/1024000+t0 ≤ (h : ℝ)/20 ∧
        2*(t : ℝ)+4+2*q < (h : ℝ)-(k0 : ℝ)/1024000-t ∧
        ∀ m : ℕ, m ≤ n → α*n ≤ m →
          nCore ≤ m ∧ 2*t+4+2*q < m ∧
          ((2*(q+t+3) : ℕ) : ℝ) ≤ η*m ∧
          (α/2)*m ≤ (h : ℝ)-a := by
  let ε : ℝ := min (α/1000) (η*α/16)
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  have hεα : ε ≤ α/1000 := min_le_left _ _
  have hεη : ε ≤ η*α/16 := min_le_right _ _
  let B : ℝ := max 1 (max (2/α) (max ((nCore : ℝ)/α)
    (max (100*((t0 : ℝ)+q+30)/α)
      (max (8*((q : ℝ)+3)/(η*α))
        (max (((44*2^(t0+4) : ℕ) : ℝ)/α) (3/((ν/2)^2*α^2)))))))
  obtain ⟨n₀,hn₀⟩ := exists_nat_gt B
  refine ⟨ε,hε,n₀,?_⟩
  intro n h k0 t a hn hhn hdensity hk0 ha haε
  have hbig : B < (n : ℝ) := hn₀.trans_le (by exact_mod_cast hn)
  have hB1 : (1 : ℝ) ≤ B := le_max_left _ _
  have hB2 : 2/α ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hBcore : (nCore : ℝ)/α ≤ B :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hBfixed : 100*((t0 : ℝ)+q+30)/α ≤ B :=
    (le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))
  have hBload : 8*((q : ℝ)+3)/(η*α) ≤ B :=
    (le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
  have hBprob : ((44*2^(t0+4) : ℕ) : ℝ)/α ≤ B :=
    (le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans
        ((le_max_right _ _).trans (le_max_right _ _)))))
  have hBsmall : 3/((ν/2)^2*α^2) ≤ B :=
    (le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans
        ((le_max_right _ _).trans (le_max_right _ _)))))
  have hnR : (0 : ℝ) < n := (by norm_num : (0 : ℝ) < 1).trans_le
    (hB1.trans hbig.le)
  have hnpos : 0 < n := by exact_mod_cast hnR
  have hhR : (0 : ℝ) < h := (mul_pos hα hnR).trans_le hdensity
  have hhpos : 0 < h := by exact_mod_cast hhR
  have htwo : (2 : ℝ) < α*n := by
    have hh := (div_lt_iff₀ hα).mp (hB2.trans_lt hbig)
    nlinarith only [hh]
  have hcore : (nCore : ℝ) < α*n := by
    have hh := (div_lt_iff₀ hα).mp (hBcore.trans_lt hbig)
    nlinarith only [hh]
  have hfixed : 100*((t0 : ℝ)+q+30) < α*n := by
    have hh := (div_lt_iff₀ hα).mp (hBfixed.trans_lt hbig)
    nlinarith only [hh]
  have hload : 8*((q : ℝ)+3) < η*α*n := by
    have hh := (div_lt_iff₀ (mul_pos hη hα)).mp (hBload.trans_lt hbig)
    nlinarith only [hh]
  have hprob : ((44*2^(t0+4) : ℕ) : ℝ) < α*n := by
    have hh := (div_lt_iff₀ hα).mp (hBprob.trans_lt hbig)
    nlinarith only [hh]
  have hsmall : 3 < (ν/2)^2*α^2*(n : ℝ) := by
    have hden : 0 < (ν/2)^2*α^2 := by positivity
    have hh := (div_lt_iff₀ hden).mp (hBsmall.trans_lt hbig)
    simpa only [mul_comm] using hh
  have haα : a+(t : ℝ)+1 ≤ (α/1000)*n :=
    haε.trans (mul_le_mul_of_nonneg_right hεα hnR.le)
  have haη : a+(t : ℝ)+1 ≤ (η*α/16)*n :=
    haε.trans (mul_le_mul_of_nonneg_right hεη hnR.le)
  have ht : (0 : ℝ) ≤ t := by positivity
  have ht0 : (0 : ℝ) ≤ t0 := by positivity
  have hq : (0 : ℝ) ≤ q := by positivity
  have hhnR : (h : ℝ) ≤ n := by exact_mod_cast hhn
  have hsub : ((h-1 : ℕ) : ℝ)+1 = h := by
    exact_mod_cast Nat.sub_add_cancel (show 1 ≤ h by omega)
  have hb : ((2*(t+t0+q+30) : ℕ) : ℝ) = 2*((t : ℝ)+t0+q+30) := by norm_cast
  have hbSmall : ((2*(t+t0+q+30) : ℕ) : ℝ) ≤ (α/2)*n/10 := by
    rw [hb]
    nlinarith only [haα,ha,hfixed]
  refine ⟨hnpos,hhpos,?_,?_,?_,?_,?_,hbSmall,?_,hsmall,?_,?_,?_,?_⟩
  · exact_mod_cast hprob.trans_le hdensity
  · linarith
  · linarith
  · linarith
  · nlinarith only [haα,ht,htwo]
  · nlinarith only [hbSmall,hdensity,hhR]
  · nlinarith only [haα,ht,hdensity]
  · nlinarith only [hk0,hfixed,hq,hdensity]
  · nlinarith only [hk0,haα,ha,hfixed,ht0,hdensity]
  · intro m hmn hm
    have hmR : (m : ℝ) ≤ n := by exact_mod_cast hmn
    have hηm := mul_le_mul_of_nonneg_left hm hη.le
    have hαm := mul_le_mul_of_nonneg_left hmR hα.le
    refine ⟨?_,?_,?_,?_⟩
    · exact_mod_cast hcore.le.trans hm
    · have hh : 2*(t : ℝ)+4+2*q < m := by
        nlinarith only [haα,ha,hfixed,ht0,hm]
      exact_mod_cast hh
    · have hh : ((2*(q+t+3) : ℕ) : ℝ) = 2*((q : ℝ)+t+3) := by norm_cast
      rw [hh]
      nlinarith only [haη,ha,hload,hηm]
    · nlinarith only [haα,ht,hdensity,hαm]

end Overfull.SafePrescription
