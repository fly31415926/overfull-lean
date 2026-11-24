import Overfull.ResidualPalette.PaletteGrouping

/-!
# Resource loads in finite palettes

Weights are natural-valued statistics of the original items. Partitioning
items by their color preserves total weight. An overloaded color consumes
at least the displayed positive threshold, so the total resource budget
bounds the number of overloaded colors. The final arithmetic lemmas give
the explicit constants needed for weighted joining palettes.
-/

noncomputable section

namespace Overfull.NativeReserve

open Finset Classical
open scoped BigOperators

variable {J : Type*} {h : ℕ}

/-- Total resource weight in one color of a finite partial assignment. -/
def paletteWeight (A : Finset J) (c : J → Fin h) (w : J → ℕ) (i : Fin h) : ℕ :=
  ∑ x ∈ A.filter (fun x => c x = i), w x

/-- Colors without room for another item of weight at most `q`, when the
target whole-color resource bound is `W`. -/
def overloadedPalettes (A : Finset J) (c : J → Fin h) (w : J → ℕ)
    (q W : ℕ) : Finset (Fin h) :=
  univ.filter (fun i => W-q < paletteWeight A c w i)

@[simp] theorem mem_overloadedPalettes (A : Finset J) (c : J → Fin h)
    (w : J → ℕ) (q W : ℕ) (i : Fin h) :
    i ∈ overloadedPalettes A c w q W ↔ W-q < paletteWeight A c w i := by
  simp [overloadedPalettes]

@[simp] theorem notMem_overloadedPalettes (A : Finset J) (c : J → Fin h)
    (w : J → ℕ) (q W : ℕ) (i : Fin h) :
    i ∉ overloadedPalettes A c w q W ↔ paletteWeight A c w i ≤ W-q := by
  simp [overloadedPalettes]

@[simp] theorem paletteWeight_empty (c : J → Fin h) (w : J → ℕ) (i : Fin h) :
    paletteWeight ∅ c w i = 0 := by
  simp [paletteWeight]

/-- The color fibers partition the original total resource weight. -/
theorem paletteWeight_sum (A : Finset J) (c : J → Fin h) (w : J → ℕ) :
    ∑ i, paletteWeight A c w i = ∑ x ∈ A, w x := by
  exact sum_fiberwise A c w

/-- Restricting the assigned item set can only decrease a color's load. -/
theorem paletteWeight_mono {A B : Finset J} (hAB : A ⊆ B)
    (c : J → Fin h) (w : J → ℕ) (i : Fin h) :
    paletteWeight A c w i ≤ paletteWeight B c w i := by
  exact sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ hAB)
    (fun _ _ _ => Nat.zero_le _)

/-- Color assignments agreeing on the item set give the same resource load. -/
theorem paletteWeight_congr (A : Finset J) (c d : J → Fin h) (w : J → ℕ)
    (hcd : ∀ x ∈ A, c x = d x) (i : Fin h) :
    paletteWeight A c w i = paletteWeight A d w i := by
  have hfilter : A.filter (fun x => c x = i) = A.filter (fun x => d x = i) := by
    apply filter_congr
    intro x hx
    rw [hcd x hx]
  simp only [paletteWeight, hfilter]

/-- Inserting a fresh item changes precisely its own color's load. -/
theorem paletteWeight_insert (A : Finset J) (c : J → Fin h) (w : J → ℕ)
    {x : J} (hx : x ∉ A) (i : Fin h) :
    paletteWeight (insert x A) c w i =
      (if c x = i then w x else 0) + paletteWeight A c w i := by
  unfold paletteWeight
  rw [filter_insert]
  split_ifs with hxi
  · rw [sum_insert (fun hh => hx (mem_filter.mp hh).1)]
  · simp

/-- Updating an item outside the current domain leaves every current load unchanged. -/
theorem paletteWeight_update_of_notMem (A : Finset J) (c : J → Fin h)
    (w : J → ℕ) {x : J} (hx : x ∉ A) (i j : Fin h) :
    paletteWeight A (Function.update c x i) w j = paletteWeight A c w j := by
  apply paletteWeight_congr
  intro y hy
  apply Function.update_of_ne
  intro heq
  exact hx (heq ▸ hy)

/-- Exact resource accounting for the fresh-item update used in greedy extension. -/
theorem paletteWeight_insert_update (A : Finset J) (c : J → Fin h)
    (w : J → ℕ) {x : J} (hx : x ∉ A) (i j : Fin h) :
    paletteWeight (insert x A) (Function.update c x i) w j =
      (if i = j then w x else 0) + paletteWeight A c w j := by
  rw [paletteWeight_insert A _ w hx, Function.update_self,
    paletteWeight_update_of_notMem A c w hx]

/-- Every overloaded color consumes at least `W-q+1` units of the original
total weight. Natural subtraction is retained explicitly. -/
theorem overloadedPalettes_mul_le (A : Finset J) (c : J → Fin h)
    (w : J → ℕ) (q W : ℕ) :
    (overloadedPalettes A c w q W).card * (W-q+1) ≤ ∑ x ∈ A, w x := by
  calc
    _ = ∑ _i ∈ overloadedPalettes A c w q W, (W-q+1) := by simp
    _ ≤ ∑ i ∈ overloadedPalettes A c w q W, paletteWeight A c w i := by
      apply sum_le_sum
      intro i hi
      have hi' := (mem_overloadedPalettes A c w q W i).mp hi
      omega
    _ ≤ ∑ i, paletteWeight A c w i :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)
    _ = ∑ x ∈ A, w x := paletteWeight_sum A c w

/-- A resource budget permits at most `K` overloaded colors. -/
theorem overloadedPalettes_card_le (A : Finset J) (c : J → Fin h)
    (w : J → ℕ) (q W K : ℕ)
    (hweight : (∑ x ∈ A, w x) ≤ K*(W-q+1)) :
    (overloadedPalettes A c w q W).card ≤ K := by
  exact Nat.le_of_mul_le_mul_right
    ((overloadedPalettes_mul_le A c w q W).trans hweight) (by omega)

/-- The total budget on the complete item set also controls every partial assignment. -/
theorem overloadedPalettes_card_le_of_subset {A T : Finset J} (hAT : A ⊆ T)
    (c : J → Fin h) (w : J → ℕ) (q W K : ℕ)
    (hweight : (∑ x ∈ T, w x) ≤ K*(W-q+1)) :
    (overloadedPalettes A c w q W).card ≤ K := by
  apply overloadedPalettes_card_le A c w q W K
  exact (sum_le_sum_of_subset_of_nonneg hAT (fun _ _ _ => Nat.zero_le _)).trans hweight

/-- The requested density margin leaves room for one six-endpoint item. -/
theorem weighted_palette_item_bound {b D h : ℕ} (hbD : b ≤ D) (hDh : 128*D ≤ h) :
    6*b ≤ h/8 := by
  omega

/-- The integer overload threshold is strictly larger than one thirteenth
of the palette order, including every remainder modulo eight. -/
theorem weighted_palette_threshold {b D h : ℕ} (hbD : b ≤ D) (hDh : 128*D ≤ h) :
    h < 13*(h/8-6*b+1) := by
  omega

/-- A total resource load at most `D*h` produces at most `13*D` overloaded
colors for six-endpoint items and target load `h/8`. -/
theorem overloadedPalettes_card_le_thirteen (A : Finset J) (c : J → Fin h)
    (w : J → ℕ) {b D : ℕ} (hbD : b ≤ D) (hDh : 128*D ≤ h)
    (hweight : (∑ x ∈ A, w x) ≤ D*h) :
    (overloadedPalettes A c w (6*b) (h/8)).card ≤ 13*D := by
  apply overloadedPalettes_card_le A c w (6*b) (h/8) (13*D)
  calc
    _ ≤ D*h := hweight
    _ ≤ D*(13*(h/8-6*b+1)) :=
      Nat.mul_le_mul_left D (weighted_palette_threshold hbD hDh).le
    _ = (13*D)*(h/8-6*b+1) := by ring

/-- With at most half the labels protected, endpoint conflicts and two
resource constraints leave a positive palette gap. -/
theorem weighted_palette_protected_margin {s D h : ℕ}
    (hh : 0 < h) (hs : 2*s ≤ h) (hDh : 128*D ≤ h) :
    s+32*D < h := by
  omega

/-- The same gap retains at least one quarter of the full palette order. -/
theorem weighted_palette_protected_gap {s D h : ℕ}
    (hs : 2*s ≤ h) (hDh : 128*D ≤ h) :
    h ≤ 4*(h-s-32*D) := by
  omega

/-- Both degree conditions for sequential dense Hall extension follow
from the common quantitative regime. No actual star balance is assumed here. -/
theorem weighted_palette_hall_bounds {s b D h : ℕ}
    (hbD : b ≤ D) (hs : 2*s ≤ h) (hDh : 128*D ≤ h) :
    2*(D+b) ≤ h-s-D ∧ 2*(h/8+b) ≤ h-s-D := by
  omega

end Overfull.NativeReserve
