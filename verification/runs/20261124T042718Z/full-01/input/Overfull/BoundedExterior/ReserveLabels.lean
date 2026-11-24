import Mathlib.Tactic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.EquivFin

/-!
# Quantitative reserve labels

A fraction `2 ^ (-(s + 1))` of the labels have a balanced footprint.  There
are at most `2 ^ s` exterior shores.  A further factor eight leaves a reserve
small enough to be avoided by the entire first group of labels.
-/

noncomputable section

namespace Overfull.BoundedExterior

open Finset Classical

/-- The fixed loss from footprint balance, exterior shores, and palette slack. -/
def reserveDenominator (s : ℕ) : ℕ := 2 ^ (2 * s + 4)

theorem reserveDenominator_pos (s : ℕ) : 0 < reserveDenominator s := by
  unfold reserveDenominator
  positivity

theorem reserveDenominator_ge_eight (s : ℕ) : 8 ≤ reserveDenominator s := by
  have h : (2 : ℕ) ^ 3 ≤ 2 ^ (2 * s + 4) :=
    pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (by omega)
  simpa only [reserveDenominator] using h

theorem reserveDenominator_factor (s : ℕ) :
    reserveDenominator s = 8 * (2 ^ (s + 1) * 2 ^ s) := by
  unfold reserveDenominator
  rw [show 2 * s + 4 = (s + 1) + s + 3 by omega, pow_add, pow_add]
  norm_num
  ring

/-- The number of original labels retained for the exterior completion. -/
def reserveCount (k s : ℕ) : ℕ := k / reserveDenominator s

theorem reserveCount_mul_le (k s : ℕ) :
    reserveCount k s * reserveDenominator s ≤ k :=
  Nat.div_mul_le_self k (reserveDenominator s)

theorem reserveCount_le_eighth (k s : ℕ) : reserveCount k s ≤ k / 8 := by
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 8)).mpr
  exact (Nat.mul_le_mul_left (reserveCount k s) (reserveDenominator_ge_eight s)).trans
    (reserveCount_mul_le k s)

theorem reserveCount_pos_of_large (k s : ℕ) (hlarge : 2 * reserveDenominator s ≤ k) :
    0 < reserveCount k s := by
  have htwo : 2 ≤ reserveCount k s :=
    (Nat.le_div_iff_mul_le (reserveDenominator_pos s)).mpr hlarge
  omega

/-- Rounding loses at most half the reserve once the host degree is large. -/
theorem reserveCount_lower_of_large (k s : ℕ)
    (hlarge : 2 * reserveDenominator s ≤ k) :
    (k : ℝ) / (2 * (reserveDenominator s : ℝ)) ≤ (reserveCount k s : ℝ) := by
  have hpos := reserveDenominator_pos s
  have hn : 2 ≤ reserveCount k s :=
    (Nat.le_div_iff_mul_le hpos).mpr hlarge
  have hround : k < (reserveCount k s + 1) * reserveDenominator s :=
    (Nat.div_lt_iff_lt_mul hpos).mp (Nat.lt_succ_self (k / reserveDenominator s))
  have hnat : k ≤ reserveCount k s * (2 * reserveDenominator s) := by
    have hnext : reserveCount k s + 1 ≤ 2 * reserveCount k s := by omega
    have hmul := Nat.mul_le_mul_right (reserveDenominator s) hnext
    nlinarith
  apply (div_le_iff₀ (by exact_mod_cast Nat.mul_pos (by decide : 0 < 2) hpos)).mpr
  exact_mod_cast hnat

/-- A small reserve leaves enough distinct labels for the first group. -/
theorem exists_labels_avoiding {k h : ℕ} (J : Finset (Fin k))
    (hroom : h + J.card ≤ k) :
    ∃ labels : Fin h ↪ Fin k, ∀ i ∈ J, i ∉ Set.range labels := by
  have havailable : h ≤ Jᶜ.card := by
    rw [card_compl, Fintype.card_fin]
    omega
  obtain ⟨I, hIJ, hI⟩ := exists_subset_card_eq havailable
  let e : I ≃ Fin h := I.equivFinOfCardEq hI
  let labels : Fin h ↪ Fin k := e.symm.toEmbedding.trans
    (Function.Embedding.subtype (fun i => i ∈ I))
  refine ⟨labels, ?_⟩
  intro i hi ⟨j, hji⟩
  have hmem : labels j ∈ I := (e.symm j).property
  have hnot : labels j ∉ J := mem_compl.mp (hIJ hmem)
  exact hnot (hji.symm ▸ hi)

/-- The first-group upper bound and the reserve bound supply disjoint palettes. -/
theorem exists_labels_avoiding_reserve {k h s : ℕ} (J : Finset (Fin k))
    (hJ : J.card = reserveCount k s) (hupper : (h : ℝ) ≤ 3 * k / 5) :
    ∃ labels : Fin h ↪ Fin k, ∀ i ∈ J, i ∉ Set.range labels := by
  apply exists_labels_avoiding J
  have hJ8 : J.card * 8 ≤ k := by
    rw [hJ]
    exact (Nat.le_div_iff_mul_le (by decide : 0 < 8)).mp (reserveCount_le_eighth k s)
  have hJ8R : (J.card : ℝ) * 8 ≤ k := by exact_mod_cast hJ8
  have hroom : (h : ℝ) + J.card ≤ k := by
    linarith [show (0 : ℝ) ≤ k from Nat.cast_nonneg k]
  exact_mod_cast hroom

end Overfull.BoundedExterior
