import Overfull.NativeCore.PrefixSelection
import Overfull.OrdinaryRobustStability

/-!
# Uniform budgets for the terminal reserve factorization

The density of the protected half reserve survives integral rounding.  A
single smaller error tolerance and larger host-order threshold give the
old-core error and order requirements returned by the terminal theorem.
-/

noncomputable section

namespace Overfull.NativeTerminal

/-- The terminal robust range can be fixed before running prefix completion. -/
theorem terminal_robust_range (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    0 < α/3840 ∧ α/3840 < 1/2 ∧ α/3840 ≤ min (α/120) 1 / 16 := by
  have hsmall : α/120 ≤ 1 := by linarith only [hα1]
  rw [min_eq_left hsmall]
  constructor
  · positivity
  constructor <;> linarith

/-- Converting a host-order error bound to either old-core order. -/
theorem terminal_core_error (β ε δ a : ℝ) (n u : ℕ)
    (hε : 0 ≤ ε) (hδ : δ ≤ ε*β)
    (hsize : β*n ≤ u) (ha : a ≤ δ*n) : a ≤ ε*u := by
  have h₁ := mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have h₂ := mul_le_mul_of_nonneg_left hsize hε
  nlinarith only [ha,h₁,h₂]

/-- Terminal factorization budgets with all constants preceding the host.
The retained degree is exactly the natural half `r/2`, including odd `r`. -/
theorem exists_uniform_terminal_parameters (α β ε δ : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hε : 0 < ε) (hδ : 0 < δ)
    (m₀ nBase : ℕ) :
    ∃ δ' : ℝ, 0 < δ' ∧ δ' ≤ δ ∧
      ∃ n₀ : ℕ, 0 < n₀ ∧ nBase ≤ n₀ ∧
        ∀ n u r : ℕ, ∀ a : ℝ,
          n₀ ≤ n → β*n ≤ u → u ≤ n → α*n/30 ≤ r → a ≤ δ'*n →
          m₀ ≤ u ∧ (α/120)*u ≤ (r/2 : ℕ) ∧ a ≤ ε*u := by
  let δ' := min δ (ε*β)
  have hδ' : 0 < δ' := lt_min hδ (mul_pos hε hβ)
  let n₀ := max nBase (max 1 (max (Nat.ceil (120/α)) (Nat.ceil ((m₀ : ℝ)/β))))
  have hpos : 0 < n₀ := lt_of_lt_of_le (by omega : 0 < 1)
    ((le_max_left 1 _).trans (le_max_right nBase _))
  refine ⟨δ',hδ',min_le_left _ _,n₀,hpos,le_max_left _ _,?_⟩
  intro n u r a hn hsize hu hr ha
  have hlarge : 120/α ≤ (n : ℝ) := by
    have hh : Nat.ceil (120/α) ≤ n := by dsimp only [n₀] at hn; omega
    exact (Nat.le_ceil _).trans (Nat.cast_le.mpr hh)
  have hmβ : (m₀ : ℝ)/β ≤ n := by
    have hh : Nat.ceil ((m₀ : ℝ)/β) ≤ n := by dsimp only [n₀] at hn; omega
    exact (Nat.le_ceil _).trans (Nat.cast_le.mpr hh)
  have hm : m₀ ≤ u := by
    have hh := (div_le_iff₀ hβ).mp hmβ
    have hh' : (m₀ : ℝ) ≤ u := by nlinarith only [hh,hsize]
    exact_mod_cast hh'
  exact ⟨hm,(NativeCore.half_reserve_prefix_room α n r r u
    hα hr le_rfl hu hlarge).1,
    terminal_core_error β ε δ' a n u hε.le (min_le_right _ _) hsize ha⟩

end Overfull.NativeTerminal
