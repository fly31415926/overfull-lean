import Overfull.OrdinaryFactorization.FirstHalf
import Overfull.OrdinaryFactorization.ResidualComplement
import Overfull.OrdinaryFactorization.ResidualInterface

/-!
# Uniform reduction to factorization through a bipartite robust core

The residual host and its embedded crossing core are actual restrictions
of the original edge copies. Its complementary coloring is constructed.
Factorization of the whole residual host is the remaining input: the
presence of a bipartite core does not make that host bipartite.
-/

noncomputable section

namespace Overfull.OrdinaryFactorization

open Finset Classical SmallCuts PairedCut

variable {V E : Type*} [Fintype V] [Fintype E]
variable {G : Multigraph V E} {U : Finset V} {C : Core G U} {k : ℕ}
variable {α ν τ ξ p σ κ δ μ : ℝ}

/-- The actual residual input for factorization through a balanced
bipartite robust core, including its constructed complementary coloring.
The error is normalized by the side order, rather than the full core order. -/
structure BipartiteResidualData
    (D : FirstHalfData G U C k α ν τ ξ p σ κ δ μ) (η : ℝ) where
  error : ℝ
  error_nonneg : 0 ≤ error
  error_small : error ≤ η * D.geometry.left.card
  completed_perfect : ∀ i, G.IsPerfectMatching (D.completed i)
  regular : ∀ v, D.remaining.degree v = k - D.count
  even : Even (Fintype.card V)
  density : (α / 2) * D.geometry.left.card ≤ ((k - D.count : ℕ) : ℝ)
  core_degree : ∀ v : U,
    ((k - D.count : ℕ) : ℝ) - error ≤ ((residualCrossingCore C D).graph.degree v : ℝ)
  robust : IsBipartiteRobustExpander
    (cutSidesGraph (residualCrossingCore C D).graph D.geometry.left D.geometry.right)
    (ξ / 2) (4 * τ)
  complementColor : (residualCrossingComplement C D).EdgeColoring (k - D.count)
  preserves : ∀ e : ↥(inheritedComplementEdges C D),
    complementColor.color e.val = (inheritedComplementColoring C D).color e
  reassemble : D.remaining.EdgeColoring (k - D.count) → G.EdgeColoring k

/-- Complete the residual construction once its numerical budget is fixed.
Neither a residual complementary coloring nor a full residual coloring is
an input. The returned reconstruction function has an explicit full-coloring
argument; existence of that argument is not asserted. -/
theorem complete_bipartite_reduction
    (D : FirstHalfData G U C k α ν τ ξ p σ κ δ μ) (η a : ℝ)
    (hα : 0 ≤ α) (hp : 0 ≤ p) (hδ : 0 ≤ δ) (hμ : 0 ≤ μ) (ha : 0 ≤ a)
    (hμξ : 4 * μ ≤ ξ) (hregular : ∀ v, G.degree v = k)
    (hEven : Even (Fintype.card V)) (hk : α * U.card ≤ (k : ℝ))
    (hcore : ∀ v : U, (k : ℝ) - a ≤ C.graph.degree v)
    (hsmall : a + (p + 4 * δ + μ) * U.card ≤ η * U.card / 2)
    (hslack : 2 * (a + (p + 4 * δ + μ) * U.card) < ((k - D.count : ℕ) : ℝ)) :
    Nonempty (BipartiteResidualData D η) := by
  let b : ℝ := a + (p + 4 * δ + μ) * U.card
  have hhalf : (U.card : ℝ) = 2 * D.geometry.left.card := by
    have h := core_card_eq_twice_left_card C D
    simp only [Fintype.card_coe] at h
    exact_mod_cast h
  have hsmallSide : b ≤ η * D.geometry.left.card := by
    calc
      b ≤ η * U.card / 2 := hsmall
      _ = η * D.geometry.left.card := by rw [hhalf]; ring
  have hdensity : (α / 2) * D.geometry.left.card ≤ ((k - D.count : ℕ) : ℝ) := by
    have hremaining := D.remaining_degree_lower
    rw [hhalf] at hk
    have hnonneg : 0 ≤ α * (D.geometry.left.card : ℝ) := by positivity
    nlinarith only [hk, hremaining, hnonneg]
  have hdegree (v : U) :
      ((k - D.count : ℕ) : ℝ) - b ≤ ((residualCrossingCore C D).graph.degree v : ℝ) := by
    have hsum := OneCore.complement_degree_add_core (residualCrossingCore C D) v
    rw [D.remaining_regular hregular] at hsum
    have hsumR : ((residualCrossingComplement C D).degree v.val : ℝ) +
        (residualCrossingCore C D).graph.degree v = ((k - D.count : ℕ) : ℝ) := by
      dsimp only [residualCrossingComplement]
      simp only [Multigraph.restrictEdges_degree] at hsum ⊢
      have hcast := congrArg (fun n : ℕ => (n : ℝ)) hsum
      simp only [Nat.cast_add] at hcast
      convert hcast using 2
      congr 2
      ext e
      simp only [mem_inter, mem_compl]
    have hbound := residualCrossingComplement_degree_le_error C D a hp hregular hcore v
    change _ ≤ b at hbound
    linarith only [hsumR, hbound]
  obtain ⟨c, hc⟩ := exists_residualCrossingComplement_coloring C D a hp hregular hcore hslack
  exact ⟨{
    error := b
    error_nonneg := by dsimp only [b]; positivity
    error_small := hsmallSide
    completed_perfect := D.completed_perfect hregular
    regular := D.remaining_regular hregular
    even := hEven
    density := hdensity
    core_degree := hdegree
    robust := residualCrossing_robust C D hμ hμξ
    complementColor := c
    preserves := hc
    reassemble := reconstructColoring C D.exteriorColor D.labels D.matchings D.matching D.verts
  }⟩

/-- Uniformly reduce the ordinary-core problem to an actual residual with
a balanced bipartite robust core and a colored complement. An arbitrary
requested side-order threshold and complementary error tolerance are met.
The crossing constant precedes that tolerance, and every other constant
and the final order threshold precede the input graph and exterior coloring. -/
theorem exists_uniform_bipartite_reduction (α ν τ : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτα : τ ≤ α / 8) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∀ η : ℝ, 0 < η →
      ∃ p σ κ δ μ ε : ℝ,
        0 < p ∧ 0 < σ ∧ 0 < κ ∧ 0 < δ ∧ 0 < μ ∧ 0 < ε ∧
          ∀ mExt : ℕ, ∃ m₀ : ℕ,
            ∀ (V E : Type*) [Fintype V] [Fintype E]
              (G : Multigraph V E) (U : Finset V) (C : Core G U) (k : ℕ) (a : ℝ),
              m₀ ≤ U.card → Even U.card → Even (Fintype.card V) →
              (∀ v, G.degree v = k) → α * U.card ≤ (k : ℝ) →
              IsRobustExpander C.graph ν τ → 0 ≤ a → a ≤ ε * U.card →
              (∀ v, (k : ℝ) - a ≤ (C.graph.degree v : ℝ)) →
              (_c₀ : (G.restrictEdges (OneCore.coreEdges C)ᶜ).EdgeColoring k) →
              ∃ D : FirstHalfData G U C k α ν τ ξ p σ κ δ μ,
                mExt ≤ D.geometry.left.card ∧ Nonempty (BipartiteResidualData D η) := by
  obtain ⟨ξ, hξ, hfirst⟩ := exists_uniform_first_half α ν τ hα hα1 hν hντ hτα
  refine ⟨ξ, hξ, ?_⟩
  intro η hη
  let p : ℝ := min (α / 100) (min (η / 100) (1 / 4))
  have hp : 0 < p := lt_min (by positivity) (lt_min (by positivity) (by norm_num))
  have hpα : p ≤ α / 100 := min_le_left _ _
  have hpη : p ≤ η / 100 := (min_le_right _ _).trans (min_le_left _ _)
  have hpQuarter : p ≤ 1 / 4 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨σ, μ₀, hσ, _hστ, hμ₀, hconstruct⟩ := hfirst p hp (by linarith only [hpQuarter])
  let μ : ℝ := min (μ₀ / 2) (min p (ξ / 8))
  have hμ : 0 < μ := lt_min (by positivity) (lt_min hp (by positivity))
  have hμμ₀ : μ ≤ μ₀ := by
    have h : μ ≤ μ₀ / 2 := min_le_left _ _
    linarith only [h, hμ₀]
  have hμp : μ ≤ p := (min_le_right _ _).trans (min_le_left _ _)
  have hμξ : 4 * μ ≤ ξ := by
    have h : μ ≤ ξ / 8 := (min_le_right _ _).trans (min_le_right _ _)
    linarith only [h, hξ]
  obtain ⟨κ, δ, ε, hκ, _hκα, hδ, hδp, hε, hεp, nFirst, hFirst⟩ :=
    hconstruct μ hμ hμμ₀
  have hδp' : δ ≤ p / 32 := by
    have h := mul_le_mul_of_nonneg_left hα1 hp.le
    nlinarith only [h, hδp]
  refine ⟨p, σ, κ, δ, μ, ε, hp, hσ, hκ, hδ, hμ, hε, ?_⟩
  intro mExt
  refine ⟨max nFirst (2 * max 1 mExt), ?_⟩
  intro V E _ _ G U C k a hn hEven hHostEven hregular hk hrob ha haε hcore c₀
  have hnFirst : nFirst ≤ U.card := (le_max_left _ _).trans hn
  have hnExtra : 2 * max 1 mExt ≤ U.card := (le_max_right _ _).trans hn
  obtain ⟨D⟩ := hFirst V E G U C k a hnFirst hEven hHostEven hregular hk hrob ha haε hcore c₀
  have hside : D.geometry.left.card = U.card / 2 := by
    simpa only [Fintype.card_fin] using D.geometry.left_card
  have hnSide : mExt ≤ D.geometry.left.card := by rw [hside]; omega
  refine ⟨D, hnSide, ?_⟩
  have hn0 : (0 : ℝ) < U.card := by exact_mod_cast (show 0 < U.card by omega)
  have hap : a ≤ p * U.card :=
    haε.trans (mul_le_mul_of_nonneg_right hεp hn0.le)
  have herror : a + (p + 4 * δ + μ) * U.card ≤ 4 * p * U.card := by
    have hδn := mul_le_mul_of_nonneg_right hδp' hn0.le
    have hμn := mul_le_mul_of_nonneg_right hμp hn0.le
    have hpn : 0 ≤ p * (U.card : ℝ) := by positivity
    nlinarith only [hap, hδn, hμn, hpn]
  have hsmall : a + (p + 4 * δ + μ) * U.card ≤ η * U.card / 2 := by
    have hηn := mul_le_mul_of_nonneg_right hpη hn0.le
    have hηpos : 0 ≤ η * (U.card : ℝ) := by positivity
    nlinarith only [herror, hηn, hηpos]
  have hslack : 2 * (a + (p + 4 * δ + μ) * U.card) < ((k - D.count : ℕ) : ℝ) := by
    have hαn := mul_le_mul_of_nonneg_right hpα hn0.le
    have hαpos : 0 < α * (U.card : ℝ) := by positivity
    have hremaining := D.remaining_degree_lower
    nlinarith only [herror, hαn, hαpos, hk, hremaining]
  exact complete_bipartite_reduction D η a hα.le hp.le hδ.le hμ.le ha hμξ hregular
    hHostEven hk hcore hsmall hslack

end Overfull.OrdinaryFactorization
