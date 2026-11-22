import Overfull.TerminalComplement.Coloring
import Overfull.OrdinaryFactorization.Parity

/-!
# Complete factorization of the terminal one-core pieces

Every ordinary exterior vertex has few incidences outside the core; one
additional apex is unrestricted.  The complementary coloring is proved
from these conditions, core parity is adjusted on actual copies, and
ordinary-core factorization colors the entire original host.
-/

noncomputable section

namespace Overfull.TerminalComplement

open Finset Classical SmallCuts OneCore OrdinaryFactorization

/-- Uniform factorization of the terminal one-core pieces, including a
possible contraction apex.  No complementary coloring, core parity, or
bound on apex bundles is assumed. -/
theorem exists_uniform_terminal_factorization (α ν τ : ℝ) (s : ℕ)
    (hα : 0 < α) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτ : τ ≤ min α 1 / 16) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ m₀ : ℕ,
      ∀ (V E : Type*) [Fintype V] [Fintype E]
        (G : Multigraph V E) (U : Finset V) (C : Core G U)
        (z : V) (k : ℕ) (a b : ℝ),
        m₀ ≤ U.card → Even (Fintype.card V) → Uᶜ.card ≤ s →
        (∀ v, G.degree v = k) → α * U.card ≤ (k : ℝ) →
        IsRobustExpander C.graph ν τ → 0 ≤ a → 0 ≤ b →
        a + b ≤ ε * U.card →
        (∀ v, (k : ℝ) - a ≤ (C.graph.degree v : ℝ)) →
        (∀ v ∉ U, v ≠ z → ((G.edgesTo v Uᶜ).card : ℝ) ≤ b) →
        Nonempty (G.EdgeColoring k) := by
  classical
  obtain ⟨η, hη, m₁, hfactor⟩ :=
    exists_uniform_factorization_any_core_parity α ν τ s hα hν hντ hτ
  let ε : ℝ := min η (α / 10)
  have hε : 0 < ε := lt_min hη (by positivity)
  refine ⟨ε, hε, max m₁ 1, ?_⟩
  intro V E _ _ G U C z k a b hn hEven hZ hregular hk hrob ha hb hab hdegree hout
  have hn1 : 1 ≤ U.card := (le_max_right _ _).trans hn
  have hnpos : (0 : ℝ) < U.card := by exact_mod_cast (show 0 < U.card by omega)
  have hαn : 0 < α * U.card := mul_pos hα hnpos
  have habα : a + b ≤ α * U.card / 10 := by
    have h := hab.trans (mul_le_mul_of_nonneg_right (min_le_right η (α / 10))
      (Nat.cast_nonneg U.card))
    linarith
  have hmax : max a b ≤ a + b := max_le (by linarith) (by linarith)
  have hfan : 2 * a + b < (k : ℝ) := by linarith
  have hgreedy : 2 * max a b < (k : ℝ) := by linarith
  have hc := core_colorable_one_apex G U C z k a b ha hb hregular
    hdegree hout hfan hgreedy
  have haη : a ≤ η * U.card := by
    have h := hab.trans (mul_le_mul_of_nonneg_right (min_le_left η (α / 10))
      (Nat.cast_nonneg U.card))
    linarith
  exact hfactor V E G U C k a ((le_max_left _ _).trans hn) hEven hZ
    hregular hk hrob haη hdegree hc

/-- The terminal conclusion is an exact partition of the original edge
copies into perfect matchings, not a coloring of a surrogate graph. -/
theorem exists_uniform_terminal_one_factorization (α ν τ : ℝ) (s : ℕ)
    (hα : 0 < α) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτ : τ ≤ min α 1 / 16) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ m₀ : ℕ,
      ∀ (V E : Type*) [Fintype V] [Fintype E]
        (G : Multigraph V E) (U : Finset V) (C : Core G U)
        (z : V) (k : ℕ) (a b : ℝ),
        m₀ ≤ U.card → Even (Fintype.card V) → Uᶜ.card ≤ s →
        (∀ v, G.degree v = k) → α * U.card ≤ (k : ℝ) →
        IsRobustExpander C.graph ν τ → 0 ≤ a → 0 ≤ b →
        a + b ≤ ε * U.card →
        (∀ v, (k : ℝ) - a ≤ (C.graph.degree v : ℝ)) →
        (∀ v ∉ U, v ≠ z → ((G.edgesTo v Uᶜ).card : ℝ) ≤ b) →
        ∃ M : Fin k → Finset E,
          (∀ i, G.IsPerfectMatching (M i)) ∧
          Pairwise (fun i j => Disjoint (M i) (M j)) ∧
          univ.biUnion M = univ := by
  obtain ⟨ε, hε, m₀, hfactor⟩ :=
    exists_uniform_terminal_factorization α ν τ s hα hν hντ hτ
  refine ⟨ε, hε, m₀, ?_⟩
  intro V E _ _ G U C z k a b hm heven hZ hregular hk hrob ha hb hab hdegree hout
  obtain ⟨c⟩ := hfactor V E G U C z k a b hm heven hZ hregular hk
    hrob ha hb hab hdegree hout
  exact BoundedExterior.exists_oneFactorization_of_coloring G k hregular c

end Overfull.TerminalComplement
