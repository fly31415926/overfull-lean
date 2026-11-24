import Overfull.ThreeCoreReduction.Frequent

/-!
# Three robust cores with a fixed exceptional bound

Range reduction makes the frequent-pattern range available for each exceptional
bound, without imposing a bound-dependent range on the original graph.  This
gives a family of positive error tolerances that can be chosen before the
bounded-absorption theorem selects its eventual exceptional cardinality.
-/

noncomputable section

namespace Overfull

open Finset Classical SimpleGraph CircuitPatterns

universe u

/-- For every fixed exceptional cardinal bound, three robust cores admit a
uniform coloring theorem at a common original range.  The original robust
parameter need not be at most that range. -/
theorem three_core_bounded_exception_factorization (t : ℕ) (α ν τ : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hν : 0 < ν) (hτpos : 0 < τ)
    (hτ : τ ≤ α / 8) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, 0 < n₀ ∧
      ∀ (V : Type u) [Fintype V] (G : SimpleGraph V)
        (U : Fin 3 → Finset V) (H : ∀ i, SimpleGraph (U i))
        (Z : Finset V) (k : ℕ) (a : ℝ),
        n₀ ≤ Fintype.card V → Even (Fintype.card V) →
        (∀ v, G.degree v = k) → α * Fintype.card V ≤ (k : ℝ) →
        (∀ X : Finset V, ¬ IsOverfull G k X) →
        Pairwise (fun i j => Disjoint (U i) (U j)) →
        (∀ i, Disjoint (U i) Z) → (∀ v, v ∈ Z ∨ ∃ i, v ∈ U i) →
        Z.card ≤ t → (∀ i, α * Fintype.card V ≤ ((U i).card : ℝ)) →
        (∀ i, H i ≤ G.induce (U i : Set V)) →
        (∀ i, IsRobustExpander (H i) ν τ) →
        (∀ i v, (k : ℝ) - a ≤ ((H i).degree v : ℝ)) →
        0 ≤ a → a ≤ ε * Fintype.card V →
        Nonempty ((Multigraph.ofSimpleGraph G).EdgeColoring k) := by
  let B : ℝ := patternBound t
  have hB : 0 < B := by exact_mod_cast patternBound_pos t
  let σ := min τ (α / (1000 * B))
  have hσ : 0 < σ := lt_min hτpos (by positivity)
  have hστ : σ ≤ τ := min_le_left _ _
  have hσbound : σ ≤ α / (1000 * patternBound t) := min_le_right _ _
  let μ := min ν ((α / 2) * σ / 2)
  have hμ : 0 < μ := lt_min hν (by positivity)
  have hμσ : μ ≤ σ := by
    have h := min_le_right ν ((α / 2) * σ / 2)
    have hh := mul_le_mul_of_nonneg_right hα1 hσ.le
    dsimp [μ]
    nlinarith only [h, hh, hσ]
  obtain ⟨εF, hεF, n₀, hn₀, hfactor⟩ :=
    three_core_frequent_pattern_factorization t α μ σ hα hα1 hμ hμσ hσbound
  let ε := min εF (α / 2)
  have hε : 0 < ε := lt_min hεF (by positivity)
  refine ⟨ε, hε, n₀, hn₀, ?_⟩
  intro V _ G U H Z k a hn heven hregular hdensity hno hdisjoint hUZ hcover
    ht hsize hembed hrobust hdegree ha herror
  have hsmall : a ≤ (α / 2) * Fintype.card V :=
    herror.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg _))
  have herrorF : a ≤ εF * Fintype.card V :=
    herror.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _))
  have hrobust' (i : Fin 3) : IsRobustExpander (H i) μ σ := by
    apply robust_range_reduction (H i) (α / 2) ν τ σ
      (by positivity) (by linarith) hν (by linarith) hσ hστ
    · intro v
      have hm : ((U i).card : ℝ) ≤ Fintype.card V := by exact_mod_cast card_le_univ (U i)
      have hm' := mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ α / 2)
      simp only [Fintype.card_coe]
      linarith only [hm', hdensity, hsmall, hdegree i v]
    · exact hrobust i
  exact hfactor V G U H Z k a hn heven hregular hdensity hno hdisjoint hUZ hcover
    ht hsize hembed hrobust' hdegree ha herrorF

end Overfull
