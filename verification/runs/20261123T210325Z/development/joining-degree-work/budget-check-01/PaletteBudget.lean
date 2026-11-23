import Overfull.ResidualPalette.PaletteGrouping
import Overfull.NativeReserve.CompletionParameters

/-!
# Uniform budgets for whole palette classes

The actual incidence bound controls the number of nonempty pieces. Choosing
one more than the natural quotient by the conflict-free palette margin
bounds the support of a whole class by the required small linear budget.
-/

noncomputable section
namespace Overfull.NativeReserve
open Finset Classical

/-- Small joining incidence leaves a linear number of available palette
labels after all six endpoint conflicts have been excluded. -/
theorem palette_margin_lower (α δ : ℝ) (n h D : ℕ)
    (hα : 0 < α) (hn : 0 < n) (hdensity : α*n/30 ≤ h)
    (hdegree : (D : ℝ) ≤ δ*n) (hδ : δ ≤ α/360) :
    6*D < h ∧ (α/60)*n ≤ ((h-6*D : ℕ) : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hδn := mul_le_mul_of_nonneg_right hδ hnR.le
  have hsmall : (6 : ℝ)*D ≤ α*n/60 := by nlinarith only [hdegree, hδn]
  have hDhR : (6 : ℝ)*D < h := by
    have hp := mul_pos hα hnR
    nlinarith only [hsmall, hdensity, hp]
  have hDh : 6*D < h := by exact_mod_cast hDhR
  refine ⟨hDh, ?_⟩
  rw [Nat.cast_sub hDh.le, Nat.cast_mul, Nat.cast_ofNat]
  nlinarith only [hdensity, hsmall]

/-- The natural capacity used by the greedy palette construction is
positive and accommodates the entire finite piece family. -/
theorem natural_palette_capacity (N b : ℕ) (hb : 0 < b) :
    0 < N/b+1 ∧ N ≤ (N/b+1)*b := by
  refine ⟨Nat.succ_pos _, ?_⟩
  have hh := Nat.lt_mul_div_succ N hb
  nlinarith

/-- The incidence estimate converts the natural greedy capacity into a
linear support bound, including its additive six-vertex rounding term. -/
theorem palette_capacity_support_bound (α δ : ℝ) (n h D N : ℕ)
    (hα : 0 < α) (hn : 0 < n) (hdensity : α*n/30 ≤ h)
    (hdegree : (D : ℝ) ≤ δ*n) (hδ : δ ≤ α/360)
    (hcount : 2*N ≤ n*D) :
    ((6*(N/(h-6*D)+1) : ℕ) : ℝ) ≤ (180*δ/α)*n+6 := by
  obtain ⟨hDh, hgap⟩ := palette_margin_lower α δ n h D hα hn hdensity hdegree hδ
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let t := N/(h-6*D)
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg _
  have hdiv : (t : ℝ)*((h-6*D : ℕ) : ℝ) ≤ N := by
    exact_mod_cast Nat.div_mul_le_self N (h-6*D)
  have hprod := mul_le_mul_of_nonneg_left hgap ht
  have hcountR : (2 : ℝ)*N ≤ n*D := by exact_mod_cast hcount
  have hDn := mul_le_mul_of_nonneg_left hdegree hnR.le
  have htα : (t : ℝ)*α ≤ 30*δ*n := by
    apply (mul_le_mul_right hnR).mp
    nlinarith only [hprod, hdiv, hcountR, hDn]
  have hquot : (t : ℝ) ≤ 30*δ*n/α := (le_div_iff₀ hα).mpr htα
  have halgebra : 6*(30*δ*(n : ℝ)/α) = (180*δ/α)*n := by ring
  change 6*((t : ℝ)+1) ≤ (180*δ/α)*n+6
  nlinarith only [hquot, halgebra]

/-- Choosing the error before the host and a sufficiently large order makes
the entire class support small, including the integer rounding term. -/
theorem palette_capacity_support_small (α δ ε : ℝ) (n h D N : ℕ)
    (hα : 0 < α) (hε : 0 < ε) (hn : 0 < n) (hdensity : α*n/30 ≤ h)
    (hdegree : (D : ℝ) ≤ δ*n) (hδ : δ ≤ α/360)
    (hδε : δ ≤ ε*α/360) (hlarge : 12/ε ≤ n)
    (hcount : 2*N ≤ n*D) :
    ((6*(N/(h-6*D)+1) : ℕ) : ℝ) ≤ ε*n := by
  have hbound := palette_capacity_support_bound α δ n h D N hα hn hdensity hdegree hδ hcount
  have hcoef : 180*δ/α ≤ ε/2 := (div_le_iff₀ hα).mpr (by linarith only [hδε])
  have hcoefn := mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hl := (div_le_iff₀ hε).mp hlarge
  nlinarith only [hbound, hcoefn, hl]

variable {V E I : Type*} [Fintype V] [Fintype I]

/-- The actual grouped copies satisfy the small whole-support estimate.
Its input capacity comes from the palette construction, while the total
piece bound is derived from actual disjoint copies and vertex incidence. -/
theorem groupedCopies_support_small (G : Multigraph V E) (M : I → Finset E)
    (S : Finset E) (h D : ℕ) (α δ ε : ℝ) (c : I → Fin h)
    (hne : ∀ i, (M i).Nonempty) (hsize : ∀ i, (M i).card ≤ 3)
    (hdisjoint : Pairwise (fun i j => Disjoint (M i) (M j)))
    (hsubset : ∀ i, M i ⊆ S) (hdegree : ∀ v, G.degreeOn S v ≤ D)
    (hload : ∀ i, (univ.filter (fun j => c j = i)).card ≤
      Fintype.card I/(h-6*D)+1)
    (hα : 0 < α) (hε : 0 < ε) (hn : 0 < Fintype.card V)
    (hdensity : α*Fintype.card V/30 ≤ h)
    (hD : (D : ℝ) ≤ δ*Fintype.card V) (hδ : δ ≤ α/360)
    (hδε : δ ≤ ε*α/360) (hlarge : 12/ε ≤ Fintype.card V) (i : Fin h) :
    ((G.edgeSupport (groupedCopies M c i)).card : ℝ) ≤ ε*Fintype.card V := by
  have hcount := twice_piece_count_le_order_mul_degree G M S D hne hdisjoint hsubset hdegree
  have hbudget := palette_capacity_support_small α δ ε (Fintype.card V) h D
    (Fintype.card I) hα hε hn hdensity hD hδ hδε hlarge hcount
  have hs := groupedCopies_support_card_le G M c hsize hload i
  have hsR : ((G.edgeSupport (groupedCopies M c i)).card : ℝ) ≤
      (6 : ℝ)*((Fintype.card I/(h-6*D) : ℕ)+1) := by exact_mod_cast hs
  exact hsR.trans hbudget

end Overfull.NativeReserve
