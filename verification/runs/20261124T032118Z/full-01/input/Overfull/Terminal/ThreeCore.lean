import Overfull.Terminal.Prefix
import Overfull.Terminal.CompletedFactorization

/-!
# Uniform terminal factorization for three robust core parts

This is the three-core subcase of terminal Proposition 4.16. The theorem
constructs every joining decomposition, completed matching prefix, residual
coloring and restored original coloring from the original simple host data.
The four-core cases of Proposition 4.16 are not asserted here.
-/

noncomputable section

namespace Overfull

open Finset Classical SimpleGraph Terminal

universe u

/-- An even-order regular simple graph with no overfull set and three
disjoint covering robust cores has a coloring with exactly the degree palette.
The positive error tolerance and order threshold precede the host, its cores,
its degree and its core error. No residual decomposition or coloring is assumed.
-/
theorem three_core_terminal_factorization (α ν τ : ℝ)
    (hα : 0 < α) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτ : τ ≤ min α 1 / 64) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, 0 < n₀ ∧
      ∀ (V : Type u) [Fintype V] (G : SimpleGraph V)
        (U : Fin 3 → Finset V) (H : ∀ i, SimpleGraph (U i)) (h : ℕ) (a : ℝ),
        n₀ ≤ Fintype.card V → Even (Fintype.card V) →
        (∀ v, G.degree v = h) → α * Fintype.card V ≤ (h : ℝ) →
        (∀ X : Finset V, ¬ IsOverfull G h X) →
        Pairwise (fun i j => Disjoint (U i) (U j)) →
        (∀ v, ∃ i, v ∈ U i) →
        (∀ i, α * Fintype.card V ≤ ((U i).card : ℝ)) →
        (∀ i, H i ≤ G.induce (U i : Set V)) →
        (∀ i, IsRobustExpander (H i) ν τ) →
        (∀ i v, (h : ℝ) - a ≤ ((H i).degree v : ℝ)) →
        0 ≤ a → a + 1 ≤ ε * Fintype.card V →
        Nonempty ((Multigraph.ofSimpleGraph G).EdgeColoring h) := by
  let β := min α 1
  have hβ : 0 < β := lt_min hα (by norm_num)
  have hβ1 : β ≤ 1 := min_le_right _ _
  have hτβ : τ ≤ β / 64 := hτ
  have hτprefix : τ ≤ β / 8 := by linarith
  obtain ⟨θ, hθ, hθτ, hprefix⟩ :=
    exists_uniform_three_core_prefix β ν τ hβ hβ1 hν hντ hτprefix
  have hτresidual : τ / 2 ≤ (β / 2) / 64 := by linarith
  obtain ⟨η, hη, m₀, hcomplete⟩ :=
    exists_uniform_completed_prefix_factorization (β / 2) θ (τ / 2)
      (by positivity) (by linarith) hθ hθτ hτresidual
  obtain ⟨ε, hε, n₀, hn₀, hconstruct⟩ := hprefix η hη m₀
  refine ⟨ε, hε, n₀, hn₀, ?_⟩
  intro V _ G U H h a hn hEven hregular hdensity hno hdisjoint hcover
    hsize hembed hrobust hdegree ha herror
  have hdensity' : β * Fintype.card V ≤ (h : ℝ) :=
    (mul_le_mul_of_nonneg_right (min_le_left α 1) (Nat.cast_nonneg (Fintype.card V))).trans hdensity
  have hsize' (i : Fin 3) : β * Fintype.card V ≤ ((U i).card : ℝ) :=
    (mul_le_mul_of_nonneg_right (min_le_left α 1) (Nat.cast_nonneg (Fintype.card V))).trans (hsize i)
  obtain ⟨P, hm, hk, hsmall⟩ := hconstruct V G U H h a hn hEven hregular
    hdensity' hno hdisjoint hcover hsize' hembed hrobust hdegree ha herror
  exact hcomplete V G U H h a P (fun i j hij => hdisjoint hij) hcover hm hk hsmall

/-- The original graph's edge copies are partitioned into exactly `h`
pairwise disjoint perfect matchings. This is an original-host existence
theorem, with all constants chosen before any graph-specific input. -/
theorem three_core_terminal_one_factorization (α ν τ : ℝ)
    (hα : 0 < α) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτ : τ ≤ min α 1 / 64) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, 0 < n₀ ∧
      ∀ (V : Type u) [Fintype V] (G : SimpleGraph V)
        (U : Fin 3 → Finset V) (H : ∀ i, SimpleGraph (U i)) (h : ℕ) (a : ℝ),
        n₀ ≤ Fintype.card V → Even (Fintype.card V) →
        (∀ v, G.degree v = h) → α * Fintype.card V ≤ (h : ℝ) →
        (∀ X : Finset V, ¬ IsOverfull G h X) →
        Pairwise (fun i j => Disjoint (U i) (U j)) →
        (∀ v, ∃ i, v ∈ U i) →
        (∀ i, α * Fintype.card V ≤ ((U i).card : ℝ)) →
        (∀ i, H i ≤ G.induce (U i : Set V)) →
        (∀ i, IsRobustExpander (H i) ν τ) →
        (∀ i v, (h : ℝ) - a ≤ ((H i).degree v : ℝ)) →
        0 ≤ a → a + 1 ≤ ε * Fintype.card V →
        ∃ M : Fin h → Finset G.edgeSet,
          (∀ i, (Multigraph.ofSimpleGraph G).IsPerfectMatching (M i)) ∧
          Pairwise (fun i j => Disjoint (M i) (M j)) ∧
          univ.biUnion M = univ := by
  obtain ⟨ε, hε, n₀, hn₀, hfactor⟩ :=
    three_core_terminal_factorization α ν τ hα hν hντ hτ
  refine ⟨ε, hε, n₀, hn₀, ?_⟩
  intro V _ G U H h a hn hEven hregular hdensity hno hdisjoint hcover
    hsize hembed hrobust hdegree ha herror
  obtain ⟨c⟩ := hfactor V G U H h a hn hEven hregular hdensity hno hdisjoint
    hcover hsize hembed hrobust hdegree ha herror
  have hregularM : ∀ v, (Multigraph.ofSimpleGraph G).degree v = h := by
    intro v
    rw [Multigraph.ofSimpleGraph_degree]
    exact hregular v
  have hinst : (fun e f : G.edgeSet => propDecidable (e = f)) =
      (inferInstance : DecidableEq G.edgeSet) := Subsingleton.elim _ _
  simpa only [hinst] using
    BoundedExterior.exists_oneFactorization_of_coloring (Multigraph.ofSimpleGraph G) h hregularM c

end Overfull
