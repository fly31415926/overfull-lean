import Overfull.CircuitPatterns.Frequent
import Overfull.TerminalFour.Result
import Overfull.OrdinaryRobustStability

/-!
# Factorization before the frequent-pattern reduction

The frequent-pattern theorem fixes its surviving robustness before its requested
error.  We then choose the terminal tolerance, request a sufficiently small
error, factor the actual enlarged residual, and restore every deleted original
matching.  Neither a frequent-pattern record nor a residual coloring is an
input to the public existence theorem.
-/

noncomputable section

namespace Overfull

open Finset Classical SimpleGraph CircuitPatterns Terminal ForeignPhase

universe u v

/-- A family of actual matchings covering every edge gives an edge coloring. -/
theorem coloring_from_covering_matchings {V E : Type*} [Fintype E]
    (G : Multigraph V E) (k : ℕ) (M : Fin k → Finset E)
    (hM : ∀ i, G.IsMatching (M i)) (hcover : univ.biUnion M = univ) :
    Nonempty (G.EdgeColoring k) := by
  have hex (e : E) : ∃ i, e ∈ M i := by
    have hm : e ∈ univ.biUnion M := by rw [hcover]; exact mem_univ _
    simpa only [mem_biUnion, mem_univ, true_and] using hm
  choose color hcolor using hex
  refine ⟨{ color := color, proper := ?_ }⟩
  intro e f v heq he hf
  apply hM (color e) e (hcolor e) f _ v he hf
  rw [heq]
  exact hcolor f

/-- The three-or-four-core input to the frequent-pattern reduction has a degree-palette
coloring.  All constants precede the host; the exceptional bound is fixed. -/
theorem core_frequent_pattern_factorization (t : ℕ) (α ν τ : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτ : τ ≤ α / (1000 * patternBound t)) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, 0 < n₀ ∧
      ∀ (V : Type u) [Fintype V] (I : Type v) [Fintype I] (G : SimpleGraph V)
        (U : I → Finset V) (H : ∀ i, SimpleGraph (U i))
        (Z : Finset V) (k : ℕ) (a : ℝ),
        n₀ ≤ Fintype.card V → (Fintype.card I = 3 ∨ Fintype.card I = 4) →
        Even (Fintype.card V) →
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
  have hB : 0 < B := by dsimp [B]; exact_mod_cast patternBound_pos t
  have hB1 : 1 ≤ B := by dsimp [B]; exact_mod_cast Nat.succ_le_iff.mpr (patternBound_pos t)
  let β := α / (3 * B)
  have hβ : 0 < β := by dsimp [β]; positivity
  have hβα : β ≤ α := div_le_self hα.le (by nlinarith)
  have hβ1 : β ≤ 1 := hβα.trans hα1
  have hτβ : τ ≤ β / 64 := by
    have hnum : τ * (1000 * B) ≤ α :=
      (le_div_iff₀ (by positivity : 0 < 1000 * B)).mp hτ
    have hβeq : β * (3 * B) = α := div_mul_cancel₀ _ (by positivity)
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 64)).mpr
    have hτB : 0 ≤ τ * B := mul_nonneg (hν.trans_le hντ).le hB.le
    apply (mul_le_mul_iff_left₀ hB).mp
    nlinarith only [hnum, hβeq, hτB]
  obtain ⟨νout, hνout, hpattern⟩ :=
    circuit_frequent_boundary_pattern.{u,v} t α ν τ hα hα1 hν hντ hτ
  let θ := min νout τ
  have hθ : 0 < θ := lt_min hνout (hν.trans_le hντ)
  have hθτ : θ ≤ τ := min_le_right _ _
  obtain ⟨εT, hεT, nT, _hnT, hterminal⟩ :=
    frequent_pattern_result_one_factorization.{u,v} β θ τ hβ hθ hθτ
      (by simpa only [min_eq_left hβ1] using hτβ)
  obtain ⟨ε, hε, nF, hconstruct⟩ := hpattern εT hεT
  let n₀ := max (max nF nT) 1
  have hn₀ : 0 < n₀ := lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ))
    (le_max_right _ _)
  refine ⟨ε, hε, n₀, hn₀, ?_⟩
  intro V _ I _ G U H Z k a hn hI _heven hregular hdensity hno hdisjoint hUZ hcover
    ht hsize hembed hrobust hdegree ha herror
  have hnF : nF ≤ Fintype.card V :=
    (le_max_left _ _).trans ((le_max_left _ _).trans hn)
  have hnT' : nT ≤ Fintype.card V :=
    (le_max_right _ _).trans ((le_max_left _ _).trans hn)
  obtain ⟨R⟩ := hconstruct V I G U H Z k a hnF hI
    hregular hdensity hno hdisjoint hUZ hcover ht hsize hembed hdegree hrobust ha herror
  have hRDensity : β * Fintype.card V ≤ (R.h : ℝ) := by
    have h := div_le_div_of_nonneg_right hdensity (by positivity : 0 ≤ 3 * B)
    have h' : β * Fintype.card V ≤ (k : ℝ) / (3 * B) := by
      simpa only [β, div_mul_eq_mul_div] using h
    exact h'.trans R.retained_degree
  have hRSize (i : I) : β * Fintype.card V ≤ ((R.U i).card : ℝ) := by
    have hc : ((U i).card : ℝ) ≤ (R.U i).card := by
      exact_mod_cast card_le_card (R.core_enlargement i)
    exact ((mul_le_mul_of_nonneg_right hβα (Nat.cast_nonneg _)).trans (hsize i)).trans hc
  have hRRobust (i : I) : IsRobustExpander (R.H i) θ τ :=
    IsRobustExpander.mono_parameter (R.H i) (R.core_robust i) (min_le_left _ _)
  let RT : FrequentPatternResult G U k t εT θ τ :=
    { R with core_robust := hRRobust }
  obtain ⟨M,hM,_hdisM,hcoverM⟩ := hterminal V I G U k t RT hI hnT' hRDensity hRSize
  have hdec : (fun a b : R.G.edgeSet => Classical.propDecidable (a = b)) =
      (fun a b : R.G.edgeSet => Subtype.instDecidableEq a b) := Subsingleton.elim _ _
  obtain ⟨c⟩ := coloring_from_covering_matchings (Multigraph.ofSimpleGraph R.G) R.h
    M (fun i => (hM i).isMatching) (by simpa only [hdec] using hcoverM)
  have c' : (Multigraph.ofSimpleGraph (afterDeletions G R.N R.rounds)).EdgeColoring R.h := by
    rw [← R.graph_eq]
    exact c
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
theorem core_frequent_pattern_one_factorization (t : ℕ) (α ν τ : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτ : τ ≤ α / (1000 * patternBound t)) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, 0 < n₀ ∧
      ∀ (V : Type u) [Fintype V] (I : Type v) [Fintype I] (G : SimpleGraph V)
        (U : I → Finset V) (H : ∀ i, SimpleGraph (U i))
        (Z : Finset V) (k : ℕ) (a : ℝ),
        n₀ ≤ Fintype.card V → (Fintype.card I = 3 ∨ Fintype.card I = 4) →
        Even (Fintype.card V) →
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
    core_frequent_pattern_factorization t α ν τ hα hα1 hν hντ hτ
  refine ⟨ε, hε, n₀, hn₀, ?_⟩
  intro V _ I _ G U H Z k a hn hI heven hregular hdensity hno hdisjoint hUZ hcover
    ht hsize hembed hrobust hdegree ha herror
  obtain ⟨c⟩ := hfactor V I G U H Z k a hn hI heven hregular hdensity hno hdisjoint
    hUZ hcover ht hsize hembed hrobust hdegree ha herror
  have hregularM : ∀ v, (Multigraph.ofSimpleGraph G).degree v = k := by
    simpa only [Multigraph.ofSimpleGraph_degree] using hregular
  have hinst : (fun e f : G.edgeSet => propDecidable (e = f)) =
      (inferInstance : DecidableEq G.edgeSet) := Subsingleton.elim _ _
  simpa only [hinst] using
    BoundedExterior.exists_oneFactorization_of_coloring (Multigraph.ofSimpleGraph G) k hregularM c

end Overfull
