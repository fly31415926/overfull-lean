import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Positive even palette sizes from fixed fractions

Rounding down to an even integer loses less than two colors. A single
order threshold, fixed before the actual palette population, makes every
prescribed positive fraction retain at least half its value. Summing the
upper rounding estimates gives the actual available-color capacity.
-/

noncomputable section

namespace Overfull.BipartiteFactorization.IntegerSizes

open Finset Classical

/-- The largest nonnegative even integer not exceeding the target fraction. -/
def evenPaletteSize (lam : ℝ) (k : ℕ) : ℕ := 2 * ⌊lam * k / 2⌋₊

/-- Every selected palette size is even. -/
theorem evenPaletteSize_even (lam : ℝ) (k : ℕ) : Even (evenPaletteSize lam k) := by
  exact ⟨⌊lam * k / 2⌋₊, by simp [evenPaletteSize, two_mul]⟩

/-- Rounding down never exceeds a nonnegative prescribed fraction. -/
theorem evenPaletteSize_le (lam : ℝ) (k : ℕ) (hlam : 0 ≤ lam) :
    (evenPaletteSize lam k : ℝ) ≤ lam * k := by
  have h := Nat.floor_le (show 0 ≤ lam * k / 2 by positivity)
  simp only [evenPaletteSize, Nat.cast_mul, Nat.cast_ofNat]
  linarith

/-- The rounding loss is strictly less than two colors. -/
theorem evenPaletteSize_gt (lam : ℝ) (k : ℕ) :
    lam * k - 2 < (evenPaletteSize lam k : ℝ) := by
  have h := Nat.lt_floor_add_one (lam * k / 2)
  simp only [evenPaletteSize, Nat.cast_mul, Nat.cast_ofNat]
  linarith

/-- A target of at least four colors yields a positive even size and retains
at least half the target fraction. -/
theorem evenPaletteSize_fraction (lam : ℝ) (k : ℕ) (hk : 0 < k)
    (hlarge : 4 ≤ lam * k) :
    0 < evenPaletteSize lam k ∧
      lam / 2 ≤ (evenPaletteSize lam k : ℝ) / k ∧
      (evenPaletteSize lam k : ℝ) / k ≤ lam := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hlam : 0 ≤ lam := by
    by_contra h
    have := mul_neg_of_neg_of_pos (lt_of_not_ge h) hkR
    linarith
  have hlow := evenPaletteSize_gt lam k
  have hupp := evenPaletteSize_le lam k hlam
  refine ⟨?_, ?_, ?_⟩
  · have hpos : (0 : ℝ) < evenPaletteSize lam k := by linarith
    exact_mod_cast hpos
  · apply (le_div_iff₀ hkR).mpr
    nlinarith
  · exact (div_le_iff₀ hkR).mpr hupp

/-- One finite threshold works for every prescribed positive palette
fraction. It depends only on the fractions and precedes the integer degree. -/
theorem exists_even_palette_threshold {γ : Type*} [Fintype γ]
    (lam : γ → ℝ) (hlam : ∀ j, 0 < lam j) :
    ∃ k₀ : ℕ, 0 < k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      ∀ j, 0 < evenPaletteSize (lam j) k ∧
        Even (evenPaletteSize (lam j) k) ∧
        lam j / 2 ≤ (evenPaletteSize (lam j) k : ℝ) / k ∧
        (evenPaletteSize (lam j) k : ℝ) / k ≤ lam j := by
  let k₀ : ℕ := (univ.sup fun j => ⌈4 / lam j⌉₊) + 1
  refine ⟨k₀, by omega, ?_⟩
  intro k hk j
  have hkpos : 0 < k := by omega
  have hj : ⌈4 / lam j⌉₊ ≤ k := by
    have h := Finset.le_sup (s := univ) (f := fun j => ⌈4 / lam j⌉₊) (mem_univ j)
    exact h.trans (by omega)
  have hdiv : 4 / lam j ≤ (k : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hj)
  have hlarge : 4 ≤ lam j * k := by
    have := (div_le_iff₀ (hlam j)).mp hdiv
    nlinarith
  obtain ⟨hp, hl, hu⟩ := evenPaletteSize_fraction (lam j) k hkpos hlarge
  exact ⟨hp, evenPaletteSize_even (lam j) k, hl, hu⟩

/-- The actual rounded integer sizes fit any population that contains the
sum of the prescribed real fractions. -/
theorem sum_evenPaletteSize_le {γ : Type*} [Fintype γ]
    (lam : γ → ℝ) (hlam : ∀ j, 0 ≤ lam j) (k C : ℕ)
    (hcapacity : (∑ j, lam j) * k ≤ C) :
    (∑ j, evenPaletteSize (lam j) k) ≤ C := by
  have hsum : (∑ j, (evenPaletteSize (lam j) k : ℝ)) ≤ (∑ j, lam j) * k := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun j _ => evenPaletteSize_le (lam j) k (hlam j))
  exact_mod_cast hsum.trans hcapacity

/-- Fully specified positive even sizes, with a uniform threshold, common
lower fraction, and actual population capacity. -/
theorem exists_even_palette_sizes {γ : Type*} [Fintype γ]
    (lam : γ → ℝ) (lam0 σ : ℝ) (hlam0 : 0 < lam0)
    (hlam : ∀ j, 2 * lam0 ≤ lam j) (hsum : (∑ j, lam j) ≤ σ) :
    ∃ k₀ : ℕ, 0 < k₀ ∧ ∀ k C : ℕ, k₀ ≤ k → σ * k ≤ C →
      ∃ n : γ → ℕ,
        (∑ j, n j) ≤ C ∧ (∀ j, 0 < n j ∧ Even (n j)) ∧
        ∀ j, lam0 ≤ (n j : ℝ) / k ∧ (n j : ℝ) / k ≤ lam j := by
  have hlampos : ∀ j, 0 < lam j := fun j => (by linarith [hlam j])
  obtain ⟨k₀, hk₀, hthreshold⟩ := exists_even_palette_threshold lam hlampos
  refine ⟨k₀, hk₀, ?_⟩
  intro k C hk hC
  refine ⟨fun j => evenPaletteSize (lam j) k, ?_, ?_, ?_⟩
  · apply sum_evenPaletteSize_le lam (fun j => (hlampos j).le) k C
    exact (mul_le_mul_of_nonneg_right hsum (Nat.cast_nonneg k)).trans hC
  · intro j
    exact ⟨(hthreshold k hk j).1, (hthreshold k hk j).2.1⟩
  · intro j
    obtain ⟨_, _, hl, hu⟩ := hthreshold k hk j
    exact ⟨(by linarith [hlam j]), hu⟩

/-- Round the common old-cluster size to a multiple of `3*q`. If that
would leave a single `q`-block of exceptional vertices, remove one further
`3*q` vertices from every cluster. The total change is less than `6*q`;
every nonempty sampling population has at least `2*q` vertices. -/
theorem exists_adjusted_cluster_size (m h n q : ℕ)
    (hq : 0 < q) (hh : 0 < h) (hdiv : q ∣ m)
    (hcover : h * n ≤ m) (hlarge : 6 * q ≤ n) :
    ∃ n' e : ℕ,
      3 * q ∣ n' ∧ q ∣ e ∧ 3 * q ≤ n' ∧ n' ≤ n ∧
      n < n' + 6 * q ∧ m = h * n' + e ∧ (e = 0 ∨ 2 * q ≤ e) := by
  let d : ℕ := 3 * q
  let r : ℕ := d * (n / d)
  have hd : 0 < d := by dsimp [d]; omega
  have hrle : r ≤ n := Nat.mul_div_le n d
  have hrd : d ∣ r := by exact ⟨n / d, rfl⟩
  have hqr : q ∣ r := dvd_trans (Nat.dvd_mul_left q 3) hrd
  have hrem : n < r + d := by
    have hm := Nat.mod_add_div n d
    have hb := Nat.mod_lt n hd
    dsimp [r]
    omega
  have hquot : 2 ≤ n / d := (Nat.le_div_iff_mul_le hd).mpr (by dsimp [d]; omega)
  have hrlower : 2 * d ≤ r := by dsimp [r]; nlinarith
  have hhr : h * r ≤ m := (Nat.mul_le_mul_left h hrle).trans hcover
  let e₀ : ℕ := m - h * r
  have heq : m = h * r + e₀ := (Nat.add_sub_of_le hhr).symm
  have hediv : q ∣ e₀ := Nat.dvd_sub hdiv (dvd_mul_of_dvd_right hqr h)
  by_cases heqsmall : e₀ = q
  · refine ⟨r - d, e₀ + h * d, Nat.dvd_sub hrd (dvd_refl d), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact dvd_add hediv (dvd_mul_of_dvd_right (Nat.dvd_mul_left q 3) h)
    · dsimp [d] at *
      omega
    · omega
    · dsimp [d] at *
      omega
    · have hrsub : r - d + d = r := Nat.sub_add_cancel (by omega)
      nlinarith
    · right
      dsimp [d]
      nlinarith
  · refine ⟨r, e₀, hrd, hediv, ?_, hrle, ?_, heq, ?_⟩
    · dsimp [d] at *
      omega
    · dsimp [d] at *
      omega
    · by_cases hezero : e₀ = 0
      · exact Or.inl hezero
      · right
        obtain ⟨a, ha⟩ := hediv
        have hatwo : 2 ≤ a := by
          by_contra hnot
          have ha01 : a = 0 ∨ a = 1 := by omega
          rcases ha01 with rfl | rfl
          · simp only [mul_zero] at ha
            exact hezero ha
          · simp only [mul_one] at ha
            exact heqsmall ha
        nlinarith

end Overfull.BipartiteFactorization.IntegerSizes
