import Overfull.OrdinaryFactorization.Reduction
import Overfull.OrdinaryFactorization.FirstHalfBounded

/-!
# Bipartite residual with an original bounded-footprint palette

The first completed colors are chosen after balancing a positive fraction
of a bounded even footprint family. A caller can reserve original colors
using that count, and its exact property survives into the genuine
bipartite residual. The residual degree, error, robustness, coloring, and
reconstruction guarantees are those of the verified ordinary reduction.
-/

noncomputable section

namespace Overfull.OrdinaryFactorization

open Finset Classical SmallCuts PairedCut

/-- Uniformly reduce the ordinary-core problem to an actual residual with
a balanced bipartite robust core and a colored complement. An arbitrary
requested side-order threshold and complementary error tolerance are met.
The crossing constant precedes that tolerance, and every other constant
and the final order threshold precede the input graph and exterior coloring. -/
theorem exists_uniform_bipartite_reduction_with_bounded_footprints (α ν τ : ℝ) (s : ℕ)
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
              ∀ (_c₀ : (G.restrictEdges (OneCore.coreEdges C)ᶜ).EdgeColoring k)
              (pairing : Fin (U.card / 2) × Bool ≃ U)
              (X : (G.restrictEdges (OneCore.coreEdges C)ᶜ).EdgeColoring k →
                Fin k → Finset U),
              (∀ c i, Even (X c i).card) → (∀ c i, (X c i).card ≤ s) →
              ∀ (P : (A B : Finset U) → (h : ℕ) →
                (G.restrictEdges (OneCore.coreEdges C)ᶜ).EdgeColoring k →
                (Fin h ↪ Fin k) → Prop),
              (∀ (D : CutReserveData C.graph pairing (α / 2) τ ξ p
                    (min ν (α * σ / 4)) σ δ) (h : ℕ),
                0 < h → h ≤ k → (h : ℝ) ≤ 3 * k / 5 →
                ∀ c : (G.restrictEdges (OneCore.coreEdges C)ᶜ).EdgeColoring k,
                  k ≤ 2 ^ (s + 1) * (univ.filter (fun i =>
                    (X c i ∩ D.left).card = (X c i ∩ D.right).card)).card →
                  ∃ labels : Fin h ↪ Fin k, P D.left D.right h c labels) →
              ∃ D : FirstHalfData G U C k α ν τ ξ p σ κ δ μ,
                mExt ≤ D.geometry.left.card ∧ Nonempty (BipartiteResidualData D η) ∧
                D.pairing = pairing ∧
                P D.geometry.left D.geometry.right D.count D.exteriorColor D.labels := by
  obtain ⟨ξ, hξ, hfirst⟩ :=
    exists_uniform_first_half_with_bounded_footprints α ν τ s hα hα1 hν hντ hτα
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
  intro V E _ _ G U C k a hn hEven hHostEven hregular hk hrob ha haε hcore c₀ pairing X hXeven hXsize P hchoose
  have hnFirst : nFirst ≤ U.card := (le_max_left _ _).trans hn
  have hnExtra : 2 * max 1 mExt ≤ U.card := (le_max_right _ _).trans hn
  obtain ⟨D, hpair, hproperty⟩ := hFirst V E G U C k a hnFirst hEven hHostEven
    hregular hk hrob ha haε hcore c₀ pairing X hXeven hXsize P hchoose
  have hside : D.geometry.left.card = U.card / 2 := by
    simpa only [Fintype.card_fin] using D.geometry.left_card
  have hnSide : mExt ≤ D.geometry.left.card := by rw [hside]; omega
  refine ⟨D, hnSide, ?_, hpair, hproperty⟩
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
