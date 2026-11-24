import Overfull.NativeTerminal.TwoCore
import Overfull.FewExceptions.Factorization

/-!
# The bounded-input corollary with one or two robust cores

One common error tolerance and order threshold handle both alternatives
in Corollary 4.6. The output is a coloring of the original regular host,
and hence an exact one-factorization of its original multigraph copies.
-/

noncomputable section

namespace Overfull

open Finset Classical SmallCuts

/-- The complete bounded-input coloring conclusion, with either one core
and at most three exceptions, or two cores and at most two exceptions. -/
theorem bounded_input_factorization (α β ν τ : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτ : τ ≤ min α (min β 1) / 16) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, 0 < n₀ ∧
      ∀ (V E : Type*) [Fintype V] [Fintype E] (G : Multigraph V E)
        (k : ℕ) (a : ℝ),
        n₀ ≤ Fintype.card V → Even (Fintype.card V) →
        (∀ v, G.degree v = k) → α * Fintype.card V ≤ (k : ℝ) →
        (∀ X : Finset V, ¬ G.IsOverfull k X) →
        a + 1 ≤ ε * Fintype.card V →
        ((∃ (U : Finset V) (C : Core G U),
            Uᶜ.card ≤ 3 ∧ β * Fintype.card V ≤ U.card ∧
            IsRobustExpander C.graph ν τ ∧
            ∀ v, (k : ℝ)-a ≤ (C.graph.degree v : ℝ)) ∨
          (∃ (U₀ U₁ Z : Finset V) (C₀ : Core G U₀) (C₁ : Core G U₁),
            Disjoint U₀ U₁ ∧ Disjoint U₀ Z ∧ Disjoint U₁ Z ∧
            (∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) ∧ Z.card ≤ 2 ∧
            β * Fintype.card V ≤ U₀.card ∧ β * Fintype.card V ≤ U₁.card ∧
            IsRobustExpander C₀.graph ν τ ∧ IsRobustExpander C₁.graph ν τ ∧
            (∀ v, (k : ℝ)-a ≤ (C₀.graph.degree v : ℝ)) ∧
            (∀ v, (k : ℝ)-a ≤ (C₁.graph.degree v : ℝ)))) →
        Nonempty (G.EdgeColoring k) := by
  let γ := min α (min β 1)
  have hγ : 0 < γ := lt_min hα (lt_min hβ (by norm_num))
  have hγα : γ ≤ α := min_le_left _ _
  have hγβ : γ ≤ β := (min_le_right _ _).trans (min_le_left _ _)
  have hγ1 : γ ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  have hτone : τ ≤ min γ 1 / 16 := by simpa only [min_eq_left hγ1] using hτ
  have hτtwo : τ ≤ γ/8 := by linarith only [hτ,hγ]
  obtain ⟨ε₁,hε₁,n₁,hOne⟩ :=
    one_core_three_exception_factorization γ ν τ hγ hν hντ hτone
  obtain ⟨ε₂,hε₂,n₂,hn₂,hTwo⟩ :=
    two_core_two_exception_factorization γ β ν τ hγ hγ1 hβ hν hντ hτtwo
  refine ⟨min ε₁ ε₂,lt_min hε₁ hε₂,max n₁ n₂,
    hn₂.trans_le (le_max_right _ _),?_⟩
  intro V E _ _ G k a hn hEven hregular hk hno ha hshape
  have hγdegree : γ * Fintype.card V ≤ (k : ℝ) :=
    (mul_le_mul_of_nonneg_right hγα (Nat.cast_nonneg _)).trans hk
  have ha₁ : a+1 ≤ ε₁ * Fintype.card V := ha.trans
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _))
  have ha₂ : a+1 ≤ ε₂ * Fintype.card V := ha.trans
    (mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg _))
  rcases hshape with ⟨U,C,hZ,hU,hrob,hdegree⟩ |
    ⟨U₀,U₁,Z,C₀,C₁,h01,h0Z,h1Z,hcover,hZ,hU₀,hU₁,hrob₀,hrob₁,hdegree₀,hdegree₁⟩
  · have hγU : γ * Fintype.card V ≤ U.card :=
      (mul_le_mul_of_nonneg_right hγβ (Nat.cast_nonneg _)).trans hU
    exact hOne V E G U C k a ((le_max_left _ _).trans hn) hEven hZ
      hregular hγdegree hγU hno hrob ha₁ hdegree
  · exact hTwo V E G k U₀ U₁ Z C₀ C₁ a ((le_max_right _ _).trans hn)
      hEven hγdegree hU₀ hU₁ h01 h0Z h1Z hcover hZ hregular hno
      hrob₀ hrob₁ ha₂ hdegree₀ hdegree₁

/-- Corollary 4.6 as exactly `k` disjoint perfect matchings covering every
original edge copy. Both core-count alternatives use the same constants. -/
theorem bounded_input_one_factorization (α β ν τ : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτ : τ ≤ min α (min β 1) / 16) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, 0 < n₀ ∧
      ∀ (V E : Type*) [Fintype V] [Fintype E] (G : Multigraph V E)
        (k : ℕ) (a : ℝ),
        n₀ ≤ Fintype.card V → Even (Fintype.card V) →
        (∀ v, G.degree v = k) → α * Fintype.card V ≤ (k : ℝ) →
        (∀ X : Finset V, ¬ G.IsOverfull k X) →
        a + 1 ≤ ε * Fintype.card V →
        ((∃ (U : Finset V) (C : Core G U),
            Uᶜ.card ≤ 3 ∧ β * Fintype.card V ≤ U.card ∧
            IsRobustExpander C.graph ν τ ∧
            ∀ v, (k : ℝ)-a ≤ (C.graph.degree v : ℝ)) ∨
          (∃ (U₀ U₁ Z : Finset V) (C₀ : Core G U₀) (C₁ : Core G U₁),
            Disjoint U₀ U₁ ∧ Disjoint U₀ Z ∧ Disjoint U₁ Z ∧
            (∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) ∧ Z.card ≤ 2 ∧
            β * Fintype.card V ≤ U₀.card ∧ β * Fintype.card V ≤ U₁.card ∧
            IsRobustExpander C₀.graph ν τ ∧ IsRobustExpander C₁.graph ν τ ∧
            (∀ v, (k : ℝ)-a ≤ (C₀.graph.degree v : ℝ)) ∧
            (∀ v, (k : ℝ)-a ≤ (C₁.graph.degree v : ℝ)))) →
        ∃ F : Fin k → Finset E,
          (∀ i, G.IsPerfectMatching (F i)) ∧
          Pairwise (fun i j => Disjoint (F i) (F j)) ∧
          univ.biUnion F = univ := by
  obtain ⟨ε,hε,n₀,hn₀,hfactor⟩ := bounded_input_factorization α β ν τ hα hβ hν hντ hτ
  refine ⟨ε,hε,n₀,hn₀,?_⟩
  intro V E _ _ G k a hn hEven hregular hk hno ha hshape
  obtain ⟨c⟩ := hfactor V E G k a hn hEven hregular hk hno ha hshape
  exact BoundedExterior.exists_oneFactorization_of_coloring G k hregular c

end Overfull
