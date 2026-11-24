import Overfull.CircuitPatterns.Rounding

/-!
# Enumerating every accepted pattern copy exactly once

This is the bridge from integer multiplicities to the finite matching
family and the prefix counts used in exact residual accounting.
-/

noncomputable section
namespace Overfull.CircuitPatterns

open Finset Classical
open scoped BigOperators

variable {P : Type*} [Fintype P]

abbrev PatternCopies (m : P → ℕ) := (p : P) × Fin (m p)

@[simp] theorem card_patternCopies (m : P → ℕ) :
    Fintype.card (PatternCopies m) = ∑ p, m p := by
  simp [PatternCopies,Fintype.card_sigma]

def copyEnumeration (m : P → ℕ) : Fin (∑ p, m p) ≃ PatternCopies m :=
  Fintype.equivOfCardEq (by simp)

def copyPattern (m : P → ℕ) (j : Fin (∑ p, m p)) : P :=
  (copyEnumeration m j).1

def enumeratedPattern (m : P → ℕ) (p₀ : P) (j : ℕ) : P :=
  if h : j < ∑ p, m p then copyPattern m ⟨j,h⟩ else p₀

@[simp] theorem enumeratedPattern_lt (m : P → ℕ) (p₀ : P) (j : ℕ)
    (hj : j < ∑ p, m p) :
    enumeratedPattern m p₀ j = copyPattern m ⟨j,hj⟩ := by
  simp [enumeratedPattern,hj]

theorem copyPattern_positive (m : P → ℕ) (j : Fin (∑ p, m p)) :
    0 < m (copyPattern m j) :=
  Nat.zero_lt_of_lt (copyEnumeration m j).2.isLt

theorem copyPattern_statistic (m : P → ℕ) (f : P → ℕ) :
    (∑ j, f (copyPattern m j)) = ∑ p, m p*f p := by
  calc
    _ = ∑ x : PatternCopies m, f x.1 := (copyEnumeration m).sum_comp (fun x => f x.1)
    _ = _ := by simp [PatternCopies,Fintype.sum_sigma]

theorem enumeratedPattern_statistic (m : P → ℕ) (p₀ : P) (f : P → ℕ) :
    (∑ j ∈ range (∑ p, m p), f (enumeratedPattern m p₀ j)) =
      ∑ p, m p*f p := by
  rw [← Fin.sum_univ_eq_sum_range]
  calc
    _ = ∑ j : Fin (∑ p, m p), f (copyPattern m j) := by
      apply sum_congr rfl
      intro j _
      rw [enumeratedPattern_lt m p₀ j.val j.isLt]
    _ = _ := copyPattern_statistic m f

/-- The full enumeration has exactly the prescribed multiplicity of each
pattern, so no prefix can exceed an accepted demand. -/
theorem enumeratedPattern_count (m : P → ℕ) (p₀ p : P) :
    ((range (∑ q, m q)).filter (fun j => enumeratedPattern m p₀ j = p)).card = m p := by
  have h := enumeratedPattern_statistic m p₀ (fun q => if q = p then 1 else 0)
  simpa [Finset.sum_boole,mul_ite] using h

theorem enumeratedPattern_prefix_le (m : P → ℕ) (p₀ p : P) (s : ℕ)
    (hs : s ≤ ∑ q, m q) :
    ((range s).filter (fun j => enumeratedPattern m p₀ j = p)).card ≤ m p := by
  rw [← enumeratedPattern_count m p₀ p]
  exact card_le_card (filter_subset_filter _ (range_mono hs))

end Overfull.CircuitPatterns
