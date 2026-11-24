import Overfull.CircuitPatterns.Frequent
import Overfull.Terminal.ThreeCore
import Overfull.OrdinaryRobustStability

/-!
# Factorization before the three-core frequent-pattern reduction

The frequent-pattern theorem fixes its surviving robustness before its requested
error.  We then choose the terminal tolerance, request a sufficiently small
error, factor the actual enlarged residual, and restore every deleted original
matching.  Neither a frequent-pattern record nor a residual coloring is an
input to the public existence theorem.
-/

noncomputable section

namespace Overfull

open Finset Classical SimpleGraph CircuitPatterns Terminal ForeignPhase

universe u

/-- The three-core input to the frequent-pattern reduction has a degree-palette
coloring.  All constants precede the host; the exceptional bound is fixed. -/
theorem three_core_frequent_pattern_factorization (t : ℕ) (α ν τ : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτ : τ ≤ α / (1000 * patternBound t)) :
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
  have hB1 : 1 ≤ B := by exact_mod_cast patternBound_pos t
  let β := α / (3 * B)
  have hβ : 0 < β := by dsimp [β]; positivity
  have hβα : β ≤ α := div_le_self hα.le (by nlinarith)
  have hβ1 : β ≤ 1 := hβα.trans hα1
  have hτβ : τ ≤ β / 64 := by
    have hnum : τ * (1000 * B) ≤ α :=
      (le_div_iff₀ (by positivity : 0 < 1000 * B)).mp hτ
    have hβeq : β * (3 * B) = α := div_mul_cancel₀ _ (by positivity)
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 64)).mpr
    apply (mul_le_mul_right hB).mp
    nlinarith only [hnum, hβeq]
  obtain ⟨νout, hνout, hpattern⟩ :=
    circuit_frequent_boundary_pattern.{u,0} t α ν τ hα hα1 hν hντ hτ
  let θ := min νout τ
  have hθ : 0 < θ := lt_min hνout (hν.trans_le hντ)
  have hθτ : θ ≤ τ := min_le_right _ _
  obtain ⟨εT, hεT, nT, _hnT, hterminal⟩ :=
    three_core_terminal_factorization β θ τ hβ hθ hθτ
      (by simpa only [min_eq_left hβ1] using hτβ)
  obtain ⟨ε, hε, nF, hconstruct⟩ := hpattern (εT / 2) (by positivity)
  let n₀ := max (max nF nT) (max 1 ⌈2 / εT⌉₊)
  have hn₀ : 0 < n₀ := lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ))
    ((le_max_left _ _).trans (le_max_right _ _))
  refine ⟨ε, hε, n₀, hn₀, ?_⟩
  intro V _ G U H Z k a hn heven hregular hdensity hno hdisjoint hUZ hcover
    ht hsize hembed hrobust hdegree ha herror
  have hnF : nF ≤ Fintype.card V :=
    (le_max_left _ _).trans ((le_max_left _ _).trans hn)
  have hnT' : nT ≤ Fintype.card V :=
    (le_max_right _ _).trans ((le_max_left _ _).trans hn)
  have hnceil : ⌈2 / εT⌉₊ ≤ Fintype.card V :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hnpos : 0 < Fintype.card V := hn₀.trans_le hn
  obtain ⟨R⟩ := hconstruct V (Fin 3) G U H Z k a hnF (Or.inl (by simp))
    hregular hdensity hno hdisjoint hUZ hcover ht hsize hembed hdegree hrobust ha herror
  have hRDensity : β * Fintype.card V ≤ (R.h : ℝ) := by
    have h := div_le_div_of_nonneg_right hdensity (by positivity : 0 ≤ 3 * B)
    have h' : β * Fintype.card V ≤ (k : ℝ) / (3 * B) := by
      simpa only [β, div_mul_eq_mul_div] using h
    exact h'.trans R.retained_degree
  have hRSize (i : Fin 3) : β * Fintype.card V ≤ ((R.U i).card : ℝ) := by
    have hc : ((U i).card : ℝ) ≤ (R.U i).card := by
      exact_mod_cast card_le_card (R.core_enlargement i)
    exact ((mul_le_mul_of_nonneg_right hβα (Nat.cast_nonneg _)).trans (hsize i)).trans hc
  have hRRobust (i : Fin 3) : IsRobustExpander (R.H i) θ τ :=
    IsRobustExpander.mono_parameter (R.H i) (R.core_robust i) (min_le_left _ _)
  obtain ⟨v₀⟩ := Fintype.card_pos_iff.mp hnpos
  have hRh : R.h ≤ Fintype.card V := by
    have h := R.G.degree_lt_card_verts v₀
    rw [R.regular v₀] at h
    exact h.le
  have hRhR : (R.h : ℝ) ≤ Fintype.card V := by exact_mod_cast hRh
  have hceilR : (⌈2 / εT⌉₊ : ℝ) ≤ Fintype.card V := by exact_mod_cast hnceil
  have htwo : 2 ≤ εT * Fintype.card V := by
    have h := (div_le_iff₀ hεT).mp ((Nat.le_ceil (2 / εT)).trans hceilR)
    linarith
  have hRError : R.error + 1 ≤ εT * Fintype.card V := by
    have h := mul_le_mul_of_nonneg_left hRhR (by positivity : 0 ≤ εT / 2)
    linarith only [R.error_bound, h, htwo]
  obtain ⟨c⟩ := hterminal V R.G R.U R.H R.h R.error hnT' heven R.regular
    hRDensity R.no_overfull R.core_disjoint R.cover hRSize R.core_embed
    hRRobust R.core_degree R.error_nonneg hRError
  have c' : (Multigraph.ofSimpleGraph (afterDeletions G R.N R.rounds)).EdgeColoring R.h := by
    simpa only [← R.graph_eq] using c
  have hr : R.rounds ≤ k := by
    have hpos := R.degree_positive
    have heq := R.degree_eq
    omega
  have hsum : R.rounds + R.h = k := by rw [R.degree_eq]; omega
  have hc : Nonempty ((Multigraph.ofSimpleGraph G).EdgeColoring (R.rounds + R.h)) :=
    ⟨restoredColoring G R.N R.rounds (fun j hj => (R.perfect j hj).1) c'⟩
  simpa only [hsum] using hc

/-- Exact one-factorization on the original copies before the actual
frequent-pattern matching prefix is removed. -/
theorem three_core_frequent_pattern_one_factorization (t : ℕ) (α ν τ : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτ : τ ≤ α / (1000 * patternBound t)) :
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
        ∃ M : Fin k → Finset G.edgeSet,
          (∀ i, (Multigraph.ofSimpleGraph G).IsPerfectMatching (M i)) ∧
          Pairwise (fun i j => Disjoint (M i) (M j)) ∧ univ.biUnion M = univ := by
  obtain ⟨ε, hε, n₀, hn₀, hfactor⟩ :=
    three_core_frequent_pattern_factorization t α ν τ hα hα1 hν hντ hτ
  refine ⟨ε, hε, n₀, hn₀, ?_⟩
  intro V _ G U H Z k a hn heven hregular hdensity hno hdisjoint hUZ hcover
    ht hsize hembed hrobust hdegree ha herror
  obtain ⟨c⟩ := hfactor V G U H Z k a hn heven hregular hdensity hno hdisjoint
    hUZ hcover ht hsize hembed hrobust hdegree ha herror
  have hregularM : ∀ v, (Multigraph.ofSimpleGraph G).degree v = k := by
    simpa only [Multigraph.ofSimpleGraph_degree] using hregular
  have hinst : (fun e f : G.edgeSet => propDecidable (e = f)) =
      (inferInstance : DecidableEq G.edgeSet) := Subsingleton.elim _ _
  simpa only [hinst] using
    BoundedExterior.exists_oneFactorization_of_coloring (Multigraph.ofSimpleGraph G) k hregularM c

end Overfull
