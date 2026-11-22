import Overfull.ColoringExtension.NearPerfect
import Overfull.OrdinaryFactorization.MatchingBridge
import Overfull.MatchingRepair

/-!
# Uniform construction and repair of internal color classes

The graph and its forbidden footprints are supplied after every tolerance
and order threshold has been chosen. The near-perfect coloring theorem
constructs the actual feasible coloring, and the verified reserve-repair
theorem constructs the actual matching family from its color classes.
-/

namespace Overfull.OrdinaryFactorization

open Finset Classical SimpleGraph
open scoped BigOperators
open OrdinaryPackingWorking BipartitePackingAccounting ColoringExtension

/-- Uniformly construct and repair compatible internal color classes.
The caller supplies graph bounds and small even forbidden footprints;
both the initial feasible coloring and the repaired family are outputs.
The uniform order is `μ₀`, then `κ, ε, m₀` for each admissible `μ`, before
any graph or prescribed footprint family is supplied. -/
theorem exists_uniform_repaired_color_family (ζ ν τ β : ℝ)
    (hζ : 0 < ζ) (hν : 0 < ν) (hντ : ν ≤ 4 * τ)
    (hτ : τ ≤ 1 / 16) (hτζ : 16 * τ ≤ ζ / 3)
    (hβ : 0 < β) (hβ1 : β ≤ 1) :
    ∃ μ₀ : ℝ, 0 < μ₀ ∧ ∀ μ : ℝ, 0 < μ → μ ≤ μ₀ →
      ∃ κ ε : ℝ, 0 < κ ∧ κ ≤ 1 / 4 ∧ κ ≤ β / 64 ∧ 0 < ε ∧ ∃ m₀ : ℕ,
        ∀ (V : Type*) [Fintype V] [DecidableEq V]
          (G R J : SimpleGraph V), R ≤ G → ∀ hJG : J ≤ G, Disjoint J R →
          ∀ m : ℕ, Fintype.card V = m → m₀ ≤ m → Even m →
          (∀ v, ζ * m ≤ (R.degree v : ℝ)) → IsRobustExpander R ν τ →
          (∀ v, β * m ≤ (J.degree v : ℝ)) →
          (∀ v, (J.maxDegree : ℝ) - J.degree v ≤ κ * m) →
          let h := J.maxDegree + 1 + Nat.ceil (κ * m)
          ∀ F : Fin h → Finset V,
            (∀ i, Even (F i).card) →
            (∀ i, ((F i).card : ℝ) ≤ ε * m) →
            (∀ v, ((forbiddenColors F v).card : ℝ) ≤ ε * m) →
            h ≤ 2 * m ∧
            ∃ c : (Multigraph.ofSimpleGraph J).EdgeColoring h,
              c.AvoidsVertices F ∧ ∃ N : Fin h → G.Subgraph,
                (∀ i, (N i).IsMatching) ∧
                (∀ i, (N i).verts = (F i : Set V)ᶜ) ∧
                (∀ i, (N i).spanningCoe ≤ (colorMatching G J hJG c i).spanningCoe ⊔ R) ∧
                Pairwise (fun i j => Disjoint (N i).spanningCoe (N j).spanningCoe) ∧
                (∀ v, ((edgeUnion (fun i => (N i).spanningCoe ⊓ R) univ).degree v : ℝ)
                  ≤ μ * m) ∧
                (∀ v, ((edgeUnion (fun i =>
                  (colorMatching G J hJG c i).spanningCoe \ (N i).spanningCoe)
                  univ).degree v : ℝ) ≤ μ * m) := by
  obtain ⟨μ₀, hμ₀, hrepair⟩ :=
    MatchingRepair.reserve_repair 2 ζ ν τ (by norm_num) hζ hν hντ hτ hτζ
  refine ⟨μ₀, hμ₀, ?_⟩
  intro μ hμ hμsmall
  obtain ⟨δ, hδ, nRepair, hRepair⟩ := hrepair μ hμ hμsmall
  obtain ⟨κ, ε, hκ, hκsmall, hκβ, hε, _hεδ, nColor, hColor⟩ :=
    exists_uniform_near_perfect_coloring β δ hβ hβ1 hδ
  refine ⟨κ, ε, hκ, hκsmall, hκβ, hε, max nRepair nColor, ?_⟩
  intro V _ _ G R J hRG hJG hJR m hV hmLarge hmEven hRmin hRexpand hJmin hJspread
  subst m
  dsimp only
  intro F hFeven hF hload
  have hnRepair : nRepair ≤ Fintype.card V := (le_max_left _ _).trans hmLarge
  have hnColor : nColor ≤ Fintype.card V := (le_max_right _ _).trans hmLarge
  obtain ⟨hh, c, hc, hFsize, _hUncovered, _hMissing, hYsize, hYinc⟩ :=
    hColor V J hnColor hJmin hJspread F hF hload
  have hhR : ((J.maxDegree + 1 + Nat.ceil (κ * Fintype.card V) : ℕ) : ℝ) ≤
      2 * Fintype.card V := by exact_mod_cast hh
  obtain ⟨N, hN⟩ := hRepair V G R hRG (Fintype.card V)
    (J.maxDegree + 1 + Nat.ceil (κ * Fintype.card V)) rfl hnRepair hmEven hhR hRmin hRexpand
    (colorMatching G J hJG c) F
    (colorMatching_isMatching G J hJG c)
    (colorMatching_pairwise_disjoint G J hJG c)
    (colorMatching_disjoint_reserve G J R hJG c hJR)
    ((colorMatching_avoids_iff G J hJG c F).mpr hc)
    hFeven hFsize
    (by intro i; simpa only [colorMatching_uncoveredOutside] using hYsize i)
    (by
      intro v
      simp only [colorMatching_uncoveredOutside]
      convert hYinc v using 2
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and])
  exact ⟨hh, c, hc, N, hN⟩

end Overfull.OrdinaryFactorization
