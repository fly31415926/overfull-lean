import Overfull.RobustPartition.Refinement
import Overfull.RobustPartition.Conclusion

/-!
# The uniform robust-partition theorem

All scales and the positive almost-regularity tolerance are chosen before
the finite graph.  The proof constructs an actual partition by finite
refinement and derives every quantitative clause from degree and incidence
counts.  Only positivity of the prescribed error function is needed.
-/

noncomputable section

universe u

namespace Overfull

attribute [local instance] Classical.propDecidable

namespace RobustPartition

/-- Uniform robust partition for an arbitrary real degree lower bound.
The tolerance is chosen before the vertex type, graph, and degree. -/
theorem exists_uniform_partition (α τ : ℝ) (f : ℝ → ℝ)
    (hα : 0 < α) (hτ : 0 < τ) (hτ1 : τ < 1 / 2)
    (hf : ∀ x, 0 < x → x < 1 → 0 < f x) :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧
      ∀ (V : Type u) [Fintype V] (G : SimpleGraph V) (d : ℝ),
      0 < (Fintype.card V : ℝ) →
      α * Fintype.card V ≤ d →
      (∀ v, d ≤ (G.degree v : ℝ)) →
      (∀ v, (G.degree v : ℝ) ≤ d + γ₀ * Fintype.card V) →
      ∃ (ρ ν : ℝ) (L : List (Piece V)),
        γ₀ ≤ ρ ∧ ρ ≤ ν ∧ ν ≤ τ ∧ ρ ≤ f ν ∧
          PartitionConclusion G d ρ ν τ L := by
  let a : ℝ := min α 1
  have ha : 0 < a := lt_min hα (by norm_num)
  have ha1 : a ≤ 1 := min_le_right _ _
  have haα : a ≤ α := min_le_left _ _
  let K : ℕ := ⌈2 / a⌉₊
  have hK : (2 / a : ℝ) ≤ K := Nat.le_ceil _
  obtain ⟨ladder⟩ := exists_scale_ladder a τ f ha ha1 hτ hτ1.le hf K
  refine ⟨ladder.gamma, ladder.gamma_pos, ?_⟩
  intro V _ G d hn hαd hdegree hdegree'
  have had : a * Fintype.card V ≤ d :=
    (mul_le_mul_of_nonneg_right haα hn.le).trans hαd
  obtain ⟨i, hi, L, hpart, hvalid, hterminal⟩ :=
    exists_terminal_partition G a τ f K ha ha1 hτ hτ1.le hK ladder d
      hn had hdegree hdegree'
  refine ⟨ladder.rho i, ladder.nu i, L, ladder.gamma_le_rho i hi.le,
    ladder.rho_le_nu i hi.le, ladder.nu_le_range i hi.le,
    ladder.rho_le_function i hi.le, ?_⟩
  exact partition_conclusion_of_terminal G d a (ladder.rho i) (ladder.nu i) τ
    ha hn (ladder.rho_pos i hi.le) (ladder.rho_small i hi.le)
    (ladder.rho_le_one i hi.le) had hdegree L hpart hvalid hterminal

end RobustPartition

open RobustPartition

/-- The full assertion of manuscript Theorem 2.23 (`bip:part:imported`).
The order threshold and positive tolerance precede every graph.  The degree
is the actual minimum degree, and near regularity uses the actual maximum
degree.  Positivity of `f` on `(0,1)` suffices, so in particular every
nondecreasing function from `(0,1)` to `(0,1)` is allowed. -/
theorem robust_partition (α τ : ℝ) (f : ℝ → ℝ)
    (hα : 0 < α) (hτ : 0 < τ) (hτ1 : τ < 1 / 2)
    (hf : ∀ x, 0 < x → x < 1 → 0 < f x) :
    ∃ n₀ : ℕ, ∃ γ₀ : ℝ, 0 < γ₀ ∧
      ∀ (V : Type u) [Fintype V] (G : SimpleGraph V),
      n₀ ≤ Fintype.card V →
      α * Fintype.card V ≤ (G.minDegree : ℝ) →
      (G.maxDegree : ℝ) ≤ (G.minDegree : ℝ) + γ₀ * Fintype.card V →
      ∃ (ρ ν : ℝ) (L : List (Piece V)),
        γ₀ ≤ ρ ∧ ρ ≤ ν ∧ ν ≤ τ ∧ ρ ≤ f ν ∧
          PartitionConclusion G G.minDegree ρ ν τ L := by
  obtain ⟨γ₀, hγ₀, hpartition⟩ :=
    exists_uniform_partition α τ f hα hτ hτ1 hf
  refine ⟨1, γ₀, hγ₀, ?_⟩
  intro V _ G hn had hmax
  have hn' : 0 < (Fintype.card V : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hn)
  apply hpartition V G G.minDegree hn' had
  · intro v
    exact_mod_cast G.minDegree_le_degree v
  · intro v
    exact (show (G.degree v : ℝ) ≤ G.maxDegree by
      exact_mod_cast G.degree_le_maxDegree v).trans hmax

end Overfull
