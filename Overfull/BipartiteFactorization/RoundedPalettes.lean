import Overfull.BipartiteFactorization.UniformSelection
import Overfull.BipartiteFactorization.IntegerSizes

/-!
# Actual disjoint palettes with positive even rounded sizes

Fixed positive target fractions determine the palette sizes. The common
threshold absorbs the rounding loss and the graph-specific union bounds.
The selected palettes satisfy the actual row and pool conclusions and
use no more colors than the allowed population supplies.
-/

noncomputable section

namespace Overfull.BipartiteFactorization.UniformSelection

open Finset Classical IntegerSizes

universe u v w t

/-- Uniformly choose the positive even palette sizes and the actual
disjoint allowed palettes together. Fixed target fractions have total at
most one half, and each achieved fraction lies between `lammin` and its
target. The graph hypotheses contain neither sizes nor success budgets. -/
theorem exists_uniform_rounded_palettes {γ : Type t} [Fintype γ]
    (α θ lammin : ℝ) (target : γ → ℝ) (poolBound : ℕ)
    (hα : 0 < α) (hθ : 0 < θ) (hlammin : 0 < lammin)
    (htarget : ∀ j, 2 * lammin ≤ target j) (htotal : (∑ j, target j) ≤ 1 / 2) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ m₀ : ℕ, 1 ≤ m₀ ∧
      ∀ m : ℕ, m₀ ≤ m → ∀ a : ℝ, 0 ≤ a → a ≤ ε * m →
        ∀ (V : Type u) (E : Type v) [Fintype E] (κ : Type w) [Fintype κ]
          (G : Multigraph V E) (k : ℕ) (c : G.EdgeColoring k)
          (C : Finset (Fin k)) (U Z : Finset V) (P : κ → Finset E),
          α * m ≤ (k : ℝ) → (Z.card : ℝ) ≤ ε * m →
          Fintype.card κ ≤ poolBound →
          (32 / 33 : ℝ) * k ≤ C.card →
          (∀ x ∈ Z, (31 / 32 : ℝ) * (G.edgesTo x U).card ≤
            (colorsOn c (G.edgesTo x U) ∩ C).card) →
          (∀ x ∈ Z, θ * k ≤ (G.edgesTo x U).card) →
          (∀ j, θ * k / 65536 ≤ (P j).card) →
          (∀ j i, i ∈ C → PaletteSampling.poolColorWeight c (P j) i ≤
            2 * m * a / k + 4) →
          ∃ I : γ → Finset (Fin k),
            (∀ j, I j ⊆ C) ∧
            (∀ j l, j ≠ l → Disjoint (I j) (I l)) ∧
            ∀ j, (I j).card = evenPaletteSize (target j) k ∧
              0 < (I j).card ∧ Even (I j).card ∧
              lammin ≤ ((I j).card : ℝ) / k ∧
              ((I j).card : ℝ) / k ≤ target j ∧
              SimultaneousPalettes.Good c U Z P (I j).card (I j) := by
  have htargetpos : ∀ j, 0 < target j := fun j => by linarith [htarget j]
  obtain ⟨k₀, _hk₀, hsizes⟩ := exists_even_palette_threshold target htargetpos
  obtain ⟨ε, hε, m₀, hm₀, hpalettes⟩ := exists_uniform_palettes
    α θ lammin poolBound (Fintype.card γ) hα hθ hlammin
  obtain ⟨m₁, hm₁⟩ := exists_nat_ge ((k₀ : ℝ) / α)
  refine ⟨ε, hε, max m₀ m₁, hm₀.trans (le_max_left _ _), ?_⟩
  intro m hm a ha haε V E _ κ _ G k c C U Z P
    hk hZ hκ hC hretained hactive hlarge hcolor
  have hm₀' : m₀ ≤ m := (le_max_left _ _).trans hm
  have hm₁' : (m₁ : ℝ) ≤ m := by exact_mod_cast (le_max_right m₀ m₁).trans hm
  have hk₀real : (k₀ : ℝ) ≤ k := by
    have h := (div_le_iff₀ hα).mp (hm₁.trans hm₁')
    nlinarith
  have hk₀' : k₀ ≤ k := by exact_mod_cast hk₀real
  let s : γ → ℕ := fun j => evenPaletteSize (target j) k
  have hsum : (∑ j, s j) ≤ C.card := by
    apply sum_evenPaletteSize_le target (fun j => (htargetpos j).le) k C.card
    have h := mul_le_mul_of_nonneg_right htotal (Nat.cast_nonneg k)
    nlinarith [show (0 : ℝ) ≤ k from Nat.cast_nonneg k]
  have hlam : ∀ j, lammin ≤ (s j : ℝ) / k := by
    intro j
    have h := (hsizes k hk₀' j).2.2.1
    dsimp [s]
    linarith [htarget j]
  obtain ⟨I, hsub, hcard, hdisj, hgood⟩ := hpalettes m hm₀' a ha haε
    V E κ γ G k c C U Z P s hk hZ hκ (le_refl _) hC hretained
    hsum hlam hactive hlarge hcolor
  refine ⟨I, hsub, hdisj, ?_⟩
  intro j
  refine ⟨hcard j, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcard j]
    exact (hsizes k hk₀' j).1
  · rw [hcard j]
    exact (hsizes k hk₀' j).2.1
  · rw [hcard j]
    exact hlam j
  · rw [hcard j]
    exact (hsizes k hk₀' j).2.2.2
  · simpa only [hcard] using hgood j

end Overfull.BipartiteFactorization.UniformSelection
