import Overfull.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Real.Basic

/-!
# Statements of the two principal assertions

The propositions in this file are specifications, not axioms. Defining a
proposition does not verify it. `SharpnessFamily` is proved by
`Overfull.sharpness_family` in `Sharpness/Theorems.lean`.
The main assertion `MainTheorem` remains unproved in this project.
-/

namespace Overfull

/-- The main asymptotic edge-coloring assertion of the manuscript.

This proposition is deliberately not asserted as a theorem.
-/
noncomputable def MainTheorem : Prop := by
  classical
  exact ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∀ G : SimpleGraph (Fin n),
      (1 / 4 + ε) * (n : ℝ) ≤ (G.maxDegree : ℝ) →
      (Nonempty (EdgeColoring G G.maxDegree) ↔
        ∀ X : Finset (Fin n), ¬ IsOverfull G G.maxDegree X)

/-- The full assertion in Proposition 7.1, including the edge count.

The two coloring conditions express the class-2 conclusion without assuming
Vizing's theorem. Connectivity is mathlib's graph-theoretic connectivity.
The theorem `Overfull.sharpness_family` proves this proposition.
-/
noncomputable def SharpnessFamily : Prop := by
  classical
  exact ∀ Δ : ℕ, 3 ≤ Δ → Δ % 2 = 1 →
    ∃ G : SimpleGraph (Fin (4 * Δ + 5)),
      G.Connected ∧ G.maxDegree = Δ ∧
      ¬ Nonempty (EdgeColoring G Δ) ∧
      Nonempty (EdgeColoring G (Δ + 1)) ∧
      (∀ X : Finset (Fin (4 * Δ + 5)), ¬ IsOverfull G Δ X) ∧
      G.edgeFinset.card = 2 * Δ * (Δ + 1)

end Overfull
