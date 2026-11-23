import Overfull.NativeReserve.CompletionParameters

/-!
# Uniform budgets with protected primary palette classes

Protecting s primary classes excludes s additional palette labels from all
surplus pieces. The resulting gap is h-6D-s. The estimates below derive its
positivity and whole-class footprint budget from uniform host parameters.
-/

noncomputable section
namespace Overfull.NativeReserve

/-- When at most half the palette labels are protected, a small enough
joining incidence leaves a positive linear unprotected palette margin. -/
theorem protected_palette_margin_lower (α δ : ℝ) (n h D s : ℕ)
    (hα : 0 < α) (hn : 0 < n) (hdensity : α*n/30 ≤ h)
    (hdegree : (D : ℝ) ≤ δ*n) (hδ : δ ≤ α/720) (hs : s ≤ h/2) :
    6*D+s < h ∧ (α/120)*n ≤ ((h-6*D-s : ℕ) : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsR : (2 : ℝ)*s ≤ h := by exact_mod_cast (show 2*s ≤ h from by omega)
  have hδn := mul_le_mul_of_nonneg_right hδ hnR.le
  have hsmall : (6 : ℝ)*D ≤ α*n/120 := by nlinarith only [hdegree, hδn]
  have hmarginR : (6 : ℝ)*D+s < h := by
    have hp := mul_pos hα hnR
    nlinarith only [hsmall, hdensity, hsR, hp]
  have hmargin : 6*D+s < h := by exact_mod_cast hmarginR
  refine ⟨hmargin, ?_⟩
  rw [Nat.cast_sub (show s ≤ h-6*D from by omega),
    Nat.cast_sub (show 6*D ≤ h from by omega), Nat.cast_mul, Nat.cast_ofNat]
  nlinarith only [hdensity, hsmall, hsR]

/-- The explicit capacity based on half the total incidence satisfies the
stronger budget required when protected palette labels are unavailable. -/
theorem protected_palette_capacity (n h D s : ℕ) (hmargin : 6*D+s < h) :
    0 < (n*D/2)/(h-6*D-s)+1 ∧
      n*D ≤ 2*((n*D/2)/(h-6*D-s)+1)*(h-6*D-s) := by
  have hgap : 0 < h-6*D-s := by omega
  refine ⟨Nat.succ_pos _, ?_⟩
  have hquot := Nat.lt_mul_div_succ (n*D/2) hgap
  have hhalf := Nat.lt_mul_div_succ (n*D) (by decide : 0 < 2)
  have hround : n*D/2+1 ≤ ((n*D/2)/(h-6*D-s)+1)*(h-6*D-s) := by nlinarith
  nlinarith

/-- The support capacity over the protected margin has an explicit linear
bound, retaining the six-vertex natural-division rounding term. -/
theorem protected_capacity_support_bound (α δ : ℝ) (n h D s N : ℕ)
    (hα : 0 < α) (hn : 0 < n) (hdensity : α*n/30 ≤ h)
    (hdegree : (D : ℝ) ≤ δ*n) (hδ : δ ≤ α/720) (hs : s ≤ h/2)
    (hcount : 2*N ≤ n*D) :
    ((6*(N/(h-6*D-s)+1) : ℕ) : ℝ) ≤ (360*δ/α)*n+6 := by
  obtain ⟨_hmargin, hgap⟩ := protected_palette_margin_lower α δ n h D s
    hα hn hdensity hdegree hδ hs
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let t := N/(h-6*D-s)
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg _
  have hdiv : (t : ℝ)*((h-6*D-s : ℕ) : ℝ) ≤ N := by
    exact_mod_cast Nat.div_mul_le_self N (h-6*D-s)
  have hprod := mul_le_mul_of_nonneg_left hgap ht
  have hcountR : (2 : ℝ)*N ≤ n*D := by exact_mod_cast hcount
  have hDn := mul_le_mul_of_nonneg_left hdegree hnR.le
  have htα : (t : ℝ)*α ≤ 60*δ*n := by
    apply (mul_le_mul_iff_left₀ hnR).mp
    nlinarith only [hprod, hdiv, hcountR, hDn]
  have hquot : (t : ℝ) ≤ 60*δ*n/α := (le_div_iff₀ hα).mpr htα
  have halgebra : 6*(60*δ*(n : ℝ)/α) = (360*δ/α)*n := by ring
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  change 6*((t : ℝ)+1) ≤ (360*δ/α)*n+6
  nlinarith only [hquot, halgebra]

/-- Both the protected-label exclusion and whole-class footprint are paid
for by parameters fixed before the host. -/
theorem protected_capacity_support_small (α δ ε : ℝ) (n h D s N : ℕ)
    (hα : 0 < α) (hε : 0 < ε) (hn : 0 < n) (hdensity : α*n/30 ≤ h)
    (hdegree : (D : ℝ) ≤ δ*n) (hδ : δ ≤ α/720) (hs : s ≤ h/2)
    (hδε : δ ≤ ε*α/720) (hlarge : 12/ε ≤ n)
    (hcount : 2*N ≤ n*D) :
    ((6*(N/(h-6*D-s)+1) : ℕ) : ℝ) ≤ ε*n := by
  have hbound := protected_capacity_support_bound α δ n h D s N
    hα hn hdensity hdegree hδ hs hcount
  have hcoef : 360*δ/α ≤ ε/2 := (div_le_iff₀ hα).mpr (by linarith only [hδε])
  have hcoefn := mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hl := (div_le_iff₀ hε).mp hlarge
  nlinarith only [hbound, hcoefn, hl]

/-- A single common capacity satisfies the public protected-grouping API
and makes every whole group support small. -/
theorem uniform_protected_palette_budget (α δ ε : ℝ) (n h D s : ℕ)
    (hα : 0 < α) (hε : 0 < ε) (hn : 0 < n) (hdensity : α*n/30 ≤ h)
    (hdegree : (D : ℝ) ≤ δ*n) (hδ : δ ≤ α/720) (hs : s ≤ h/2)
    (hδε : δ ≤ ε*α/720) (hlarge : 12/ε ≤ n) :
    let L := (n*D/2)/(h-6*D-s)+1
    0 < L ∧ 6*D+s < h ∧ n*D ≤ 2*L*(h-6*D-s) ∧ (6*L : ℝ) ≤ ε*n := by
  dsimp only
  have hmargin := (protected_palette_margin_lower α δ n h D s
    hα hn hdensity hdegree hδ hs).1
  obtain ⟨hL, hcapacity⟩ := protected_palette_capacity n h D s hmargin
  refine ⟨hL, hmargin, hcapacity, ?_⟩
  have hcount : 2*(n*D/2) ≤ n*D := by
    have hh := Nat.div_mul_le_self (n*D) 2
    nlinarith
  have hh := protected_capacity_support_small α δ ε n h D s (n*D/2)
    hα hε hn hdensity hdegree hδ hs hδε hlarge hcount
  exact_mod_cast hh

end Overfull.NativeReserve
