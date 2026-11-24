import Overfull.ResidualPalette.ProtectedBudget
import Overfull.WeightedPalette.Loads
import Overfull.WeightedPalette.AsymmetricHall

/-!
# Uniform quantitative budgets for weighted native palettes

The weighted grouping uses the original palette of size `h`, reserves at
most half its labels, and excludes a further `32D` labels. The native
density and joining-incidence estimates give a positive linear margin.
An explicit natural capacity controls the whole support after two actual
stars have added at most four vertices. The load estimates below are
numerical implications of the stated bounds; they do not assert a global
joining-load bound after protected reserve classes have been inserted.
-/

noncomputable section

namespace Overfull.NativeCore

/-- The native density and incidence bounds imply the large original
palette required by the weighted grouping and sequential Hall arguments. -/
theorem weighted_degree_ratio (α δ : ℝ) (n h D : ℕ)
    (hdensity : α*n/30 ≤ h) (hdegree : (D : ℝ) ≤ δ*n)
    (hδ : δ ≤ α/3840) :
    128*D ≤ h := by
  have hδn := mul_le_mul_of_nonneg_right hδ
    (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hratio : (128 : ℝ)*D ≤ h := by
    nlinarith only [hdegree, hδn, hdensity]
  exact_mod_cast hratio

/-- Excluding the protected half and the weighted conflict budget leaves
at least a quarter of the original palette, hence at least `αn/120`. -/
theorem weighted_palette_margin_lower (α δ : ℝ) (n h D s : ℕ)
    (hα : 0 < α) (hn : 0 < n) (hdensity : α*n/30 ≤ h)
    (hdegree : (D : ℝ) ≤ δ*n) (hδ : δ ≤ α/3840) (hs : 2*s ≤ h) :
    128*D ≤ h ∧ s+32*D < h ∧
      (h : ℝ)/4 ≤ ((h-s-32*D : ℕ) : ℝ) ∧
      (α/120)*n ≤ ((h-s-32*D : ℕ) : ℝ) := by
  have hratio := weighted_degree_ratio α δ n h D hdensity hdegree hδ
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hp := mul_pos hα hnR
  have hhR : (0 : ℝ) < h := by nlinarith only [hdensity, hp]
  have hh : 0 < h := by exact_mod_cast hhR
  have hmargin : s+32*D < h :=
    NativeReserve.weighted_palette_protected_margin hh hs hratio
  have hsR : (2 : ℝ)*s ≤ h := by exact_mod_cast hs
  have hratioR : (128 : ℝ)*D ≤ h := by exact_mod_cast hratio
  have hquarter : (h : ℝ)/4 ≤ ((h-s-32*D : ℕ) : ℝ) := by
    rw [Nat.cast_sub (show 32*D ≤ h-s from by omega),
      Nat.cast_sub (show s ≤ h from by omega), Nat.cast_mul, Nat.cast_ofNat]
    nlinarith only [hsR, hratioR]
  refine ⟨hratio, hmargin, hquarter, ?_⟩
  nlinarith only [hquarter, hdensity]

/-- The half-incidence quotient is positive and accommodates all actual
pieces without replacing the original palette by the unprotected palette. -/
theorem weighted_palette_capacity (n h D s : ℕ) (hmargin : s+32*D < h) :
    0 < (n*D/2)/(h-s-32*D)+1 ∧
      n*D ≤ 2*((n*D/2)/(h-s-32*D)+1)*(h-s-32*D) := by
  have hgap : 0 < h-s-32*D := by omega
  refine ⟨Nat.succ_pos _, ?_⟩
  have hquot := Nat.lt_mul_div_succ (n*D/2) hgap
  have hhalf := Nat.lt_mul_div_succ (n*D) (by decide : 0 < 2)
  have hround : n*D/2+1 ≤ ((n*D/2)/(h-s-32*D)+1)*(h-s-32*D) := by
    nlinarith
  nlinarith

/-- The actual twice-piece-count estimate gives precisely the natural
capacity hypothesis consumed by weighted matching grouping. -/
theorem weighted_piece_capacity (n h D s N : ℕ)
    (hmargin : s+32*D < h) (hcount : 2*N ≤ n*D) :
    N ≤ ((n*D/2)/(h-s-32*D)+1)*(h-s-32*D) := by
  have hcapacity := (weighted_palette_capacity n h D s hmargin).2
  nlinarith

/-- The support of the whole grouped class, with four additional vertices
for two stars, retains an explicit linear bound and a rounding term of ten. -/
theorem weighted_capacity_support_bound (α δ : ℝ) (n h D s N : ℕ)
    (hα : 0 < α) (hn : 0 < n) (hdensity : α*n/30 ≤ h)
    (hdegree : (D : ℝ) ≤ δ*n) (hδ : δ ≤ α/3840) (hs : 2*s ≤ h)
    (hcount : 2*N ≤ n*D) :
    ((6*(N/(h-s-32*D)+1)+4 : ℕ) : ℝ) ≤ (360*δ/α)*n+10 := by
  have hgap := (weighted_palette_margin_lower α δ n h D s
    hα hn hdensity hdegree hδ hs).2.2.2
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let t := N/(h-s-32*D)
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg _
  have hdiv : (t : ℝ)*((h-s-32*D : ℕ) : ℝ) ≤ N := by
    exact_mod_cast Nat.div_mul_le_self N (h-s-32*D)
  have hprod := mul_le_mul_of_nonneg_left hgap ht
  have hcountR : (2 : ℝ)*N ≤ n*D := by exact_mod_cast hcount
  have hDn := mul_le_mul_of_nonneg_left hdegree hnR.le
  have htα : (t : ℝ)*α ≤ 60*δ*n := by
    apply (mul_le_mul_iff_left₀ hnR).mp
    nlinarith only [hprod, hdiv, hcountR, hDn]
  have hquot : (t : ℝ) ≤ 60*δ*n/α := (le_div_iff₀ hα).mpr htα
  have halgebra : 6*(60*δ*(n : ℝ)/α) = (360*δ/α)*n := by ring
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  change 6*((t : ℝ)+1)+4 ≤ (360*δ/α)*n+10
  nlinarith only [hquot, halgebra]

/-- A host order of at least `20/ε` absorbs both quotient rounding and the
four support vertices added by the sequential exceptional stars. -/
theorem weighted_capacity_support_small (α δ ε : ℝ) (n h D s N : ℕ)
    (hα : 0 < α) (hε : 0 < ε) (hn : 0 < n) (hdensity : α*n/30 ≤ h)
    (hdegree : (D : ℝ) ≤ δ*n) (hδ : δ ≤ α/3840) (hs : 2*s ≤ h)
    (hδε : δ ≤ ε*α/720) (hlarge : 20/ε ≤ n)
    (hcount : 2*N ≤ n*D) :
    ((6*(N/(h-s-32*D)+1)+4 : ℕ) : ℝ) ≤ ε*n := by
  have hbound := weighted_capacity_support_bound α δ n h D s N
    hα hn hdensity hdegree hδ hs hcount
  have hcoef : 360*δ/α ≤ ε/2 :=
    (div_le_iff₀ hα).mpr (by linarith only [hδε])
  have hcoefn := mul_le_mul_of_nonneg_right hcoef
    (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hl := (div_le_iff₀ hε).mp hlarge
  nlinarith only [hbound, hcoefn, hl]

/-- One native capacity simultaneously supplies the original-palette
regime, the weighted margin, the incidence capacity, and the full support
budget after two star insertions. -/
theorem uniform_weighted_palette_budget (α δ ε : ℝ) (n h D s : ℕ)
    (hα : 0 < α) (hε : 0 < ε) (hn : 0 < n) (hdensity : α*n/30 ≤ h)
    (hdegree : (D : ℝ) ≤ δ*n) (hδ : δ ≤ α/3840) (hs : 2*s ≤ h)
    (hδε : δ ≤ ε*α/720) (hlarge : 20/ε ≤ n) :
    let L := (n*D/2)/(h-s-32*D)+1
    0 < L ∧ 128*D ≤ h ∧ s+32*D < h ∧
      n*D ≤ 2*L*(h-s-32*D) ∧ ((6*L+4 : ℕ) : ℝ) ≤ ε*n := by
  dsimp only
  obtain ⟨hratio, hmargin, _, _⟩ := weighted_palette_margin_lower α δ n h D s
    hα hn hdensity hdegree hδ hs
  obtain ⟨hL, hcapacity⟩ := weighted_palette_capacity n h D s hmargin
  refine ⟨hL, hratio, hmargin, hcapacity, ?_⟩
  have hcount : 2*(n*D/2) ≤ n*D := by
    have hh := Nat.div_mul_le_self (n*D) 2
    nlinarith
  exact weighted_capacity_support_small α δ ε n h D s (n*D/2)
    hα hε hn hdensity hdegree hδ hs hδε hlarge hcount

/-- The same native error bound supplies the second-star Hall margin on
its actual remaining palette, including both multiplicity increases. -/
theorem native_star_hall_margin (α δ : ℝ) (n h D b s : ℕ)
    (hdensity : α*n/30 ≤ h) (hdegree : (D : ℝ) ≤ δ*n)
    (hδ : δ ≤ α/3840) (hb : b ≤ D) (hs : 2*s ≤ h) :
    (D+b)+(h/8+b) ≤ h-s-D := by
  exact CircuitPatterns.star_hall_margin h D b s hb
    (weighted_degree_ratio α δ n h D hdensity hdegree hδ) hs

/-- A vertex load bounded by joining incidence plus the two old-core
multiplicity contributions is at most three times the native incidence. -/
theorem two_star_load_bound (δ : ℝ) (n D b : ℕ)
    (hdegree : (D : ℝ) ≤ δ*n) (hb : b ≤ D) :
    ((D+2*b : ℕ) : ℝ) ≤ 3*δ*n := by
  have hbR : (b : ℝ) ≤ D := by exact_mod_cast hb
  push_cast
  nlinarith only [hdegree, hbR]

/-- The quantitative two-star load can be made arbitrarily small whenever
the actual load estimate is available on the palette under consideration. -/
theorem two_star_load_small (δ ε : ℝ) (n D b q : ℕ)
    (hdegree : (D : ℝ) ≤ δ*n) (hb : b ≤ D) (hδ : δ ≤ ε/3)
    (hq : q ≤ D+2*b) :
    (q : ℝ) ≤ ε*n := by
  have hbound := two_star_load_bound δ n D b hdegree hb
  have hqn : (q : ℝ) ≤ ((D+2*b : ℕ) : ℝ) := by exact_mod_cast hq
  have hδn := mul_le_mul_of_nonneg_right hδ
    (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  nlinarith only [hbound, hqn, hδn]

/-- The weighted palette and two-star budgets can be fixed before the
host, below any previously imposed positive error cap. The load conclusion
concerns the numerical quantity `D+2b`; applying it to actual classes still
requires the corresponding incidence estimate. -/
theorem exists_uniform_weighted_palette_parameters (α ε γ : ℝ)
    (hα : 0 < α) (hε : 0 < ε) (hγ : 0 < γ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ γ ∧ δ ≤ α/3840 ∧
      δ ≤ ε*α/720 ∧ δ ≤ ε/3 ∧
      ∃ N : ℕ, 0 < N ∧ ∀ n h D b s : ℕ,
        N ≤ n → α*n/30 ≤ h → (D : ℝ) ≤ δ*n → b ≤ D → 2*s ≤ h →
        let L := (n*D/2)/(h-s-32*D)+1
        0 < L ∧ 128*D ≤ h ∧ s+32*D < h ∧
          n*D ≤ 2*L*(h-s-32*D) ∧
          ((6*L+4 : ℕ) : ℝ) ≤ ε*n ∧ ((D+2*b : ℕ) : ℝ) ≤ ε*n := by
  let δ := min γ (min (α/3840) (min (ε*α/720) (ε/3)))
  have hδpos : 0 < δ :=
    lt_min hγ (lt_min (div_pos hα (by norm_num))
      (lt_min (div_pos (mul_pos hε hα) (by norm_num))
        (div_pos hε (by norm_num))))
  have hδγ : δ ≤ γ := min_le_left _ _
  have hδdensity : δ ≤ α/3840 := (min_le_right _ _).trans (min_le_left _ _)
  have hδsupport : δ ≤ ε*α/720 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδload : δ ≤ ε/3 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  let N := Nat.ceil (20/ε)+1
  refine ⟨δ, hδpos, hδγ, hδdensity, hδsupport, hδload, N, Nat.succ_pos _, ?_⟩
  intro n h D b s hn hdensity hdegree hb hs
  have hnpos : 0 < n := lt_of_lt_of_le (Nat.succ_pos _) hn
  have hceil : Nat.ceil (20/ε) ≤ n := by dsimp only [N] at hn; omega
  have hlarge : 20/ε ≤ (n : ℝ) :=
    (Nat.le_ceil (20/ε)).trans (by exact_mod_cast hceil)
  obtain ⟨hL, hratio, hmargin, hcapacity, hsupport⟩ :=
    uniform_weighted_palette_budget α δ ε n h D s
      hα hε hnpos hdensity hdegree hδdensity hs hδsupport hlarge
  exact ⟨hL, hratio, hmargin, hcapacity, hsupport,
    two_star_load_small δ ε n D b (D+2*b) hdegree hb hδload le_rfl⟩

end Overfull.NativeCore
