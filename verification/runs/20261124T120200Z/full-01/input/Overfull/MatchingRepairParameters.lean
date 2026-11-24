import Overfull.OrdinaryPackingBounds

namespace Overfull.MatchingRepairParameters

/-- Choose the error after the path length and the internal-load cap. -/
theorem exists_error (b ζ ν μ ξ : ℝ) (ℓ : ℕ)
    (hb : 0 < b) (hζ : 0 < ζ) (hν : 0 < ν) (hμ : 0 < μ) (hξ : 0 < ξ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ν/2 ∧ δ ≤ ζ/4 ∧ δ ≤ μ/3 ∧ δ ≤ 1/2 ∧
      (8*b*ℓ/μ + ℓ)*δ ≤ min ξ (ζ/3)/16 := by
  let C := 8*b*ℓ/μ + ℓ
  let η := min ξ (ζ/3)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hη : 0 < η := lt_min hξ (by positivity)
  let δ := min (ν/4) (min (ζ/8) (min (μ/6) (min (1/4) (η/(32*(C+1))))))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδν : δ ≤ ν/4 := min_le_left _ _
  have hδζ : δ ≤ ζ/8 := (min_le_right _ _).trans (min_le_left _ _)
  have hδμ : δ ≤ μ/6 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδone : δ ≤ 1/4 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hδC : δ ≤ η/(32*(C+1)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨δ, hδ, by linarith, by linarith, by linarith, by linarith, ?_⟩
  have hh := (le_div_iff₀ (show 0 < 32*(C+1) by positivity)).mp hδC
  change C*δ ≤ η/16
  nlinarith only [hh, hδ, hη]

/-- The fixed order threshold absorbs both the floor error and the path
budget's additive constant. -/
theorem exists_order_threshold (μ ξ ζ : ℝ) (nCut : ℕ)
    (hμ : 0 < μ) (hξ : 0 < ξ) (hζ : 0 < ζ) :
    ∃ n₀ : ℕ, ∀ m : ℕ, n₀ ≤ m →
      nCut ≤ m ∧ 0 < m ∧ 4 ≤ μ*m ∧ 16 ≤ min ξ (ζ/3)*m := by
  let η := min ξ (ζ/3)
  have hη : 0 < η := lt_min hξ (by positivity)
  obtain ⟨q, hq⟩ := exists_nat_gt (max (4/μ) (16/η))
  refine ⟨max nCut q, ?_⟩
  intro m hm
  have hqm : q ≤ m := (le_max_right _ _).trans hm
  have hqmR : (q : ℝ) ≤ m := by exact_mod_cast hqm
  have hl : max (4/μ) (16/η) < (m : ℝ) := hq.trans_le hqmR
  have hμm := (div_lt_iff₀ hμ).mp ((le_max_left _ _).trans_lt hl)
  have hηm := (div_lt_iff₀ hη).mp ((le_max_right _ _).trans_lt hl)
  have hmpos : (0 : ℝ) < m := lt_of_lt_of_le (by positivity : (0 : ℝ) < 4/μ)
    ((le_max_left _ _).trans hl.le)
  exact ⟨(le_max_left _ _).trans hm, by exact_mod_cast hmpos,
    by nlinarith only [hμm], by nlinarith only [hηm]⟩

end Overfull.MatchingRepairParameters
