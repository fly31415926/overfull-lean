import Overfull.OrdinaryFactorization.MatchingBridge
import Overfull.MatchingRepair

/-!
# Reserve repair of actual balanced color classes

The original classes are the actual matching subgraphs of the supplied
proper coloring. Their repair requirements are derived from class spread,
degree deficits and the scalar budget. The reserve construction then
produces actual disjoint matchings, with quantitative bounds on the used
reserve and on the released original edges.
-/

namespace Overfull.OrdinaryFactorization

open Finset Classical SimpleGraph
open scoped BigOperators
open OrdinaryPackingWorking BipartitePackingAccounting

variable {V : Type*} [Fintype V] {r : ℕ}

/-- The finite color-counting estimates imply every quantitative input to
the actual reserve-repair theorem. -/
theorem colorMatching_repair_bounds (G J : SimpleGraph V) (hJG : J ≤ G)
    (c : (Multigraph.ofSimpleGraph J).EdgeColoring r) (F : Fin r → Finset V)
    (f : ℕ) (D δ : ℝ) (m : ℕ) (hV : Fintype.card V = m) (hr : 0 < r)
    (hF : ∀ i, (F i).card ≤ f)
    (hspread : ∀ i j,
      |((c.colorClass i).card : ℤ) - ((c.colorClass j).card : ℤ)| ≤ (f : ℤ) + 1)
    (hdegree : ∀ v, (r : ℝ) - D ≤ J.degree v)
    (hf : (f : ℝ) ≤ δ * m) (hD : D ≤ δ * m)
    (hbudget : (m : ℝ) * D + 2 * r * ((f : ℝ) + 1) ≤ r * (δ * m)) :
    (∀ i, ((F i).card : ℝ) ≤ δ * m) ∧
    (∀ i, ((uncoveredOutside G (colorMatching G J hJG c i) (F i)).card : ℝ) ≤ δ * m) ∧
    (∀ v, ((univ.filter (fun i : Fin r =>
      v ∈ uncoveredOutside G (colorMatching G J hJG c i) (F i))).card : ℝ) ≤ δ * m) := by
  have hdegree' : ∀ v, (r : ℝ) - D ≤ (Multigraph.ofSimpleGraph J).degree v := by
    intro v
    simpa only [Multigraph.ofSimpleGraph_degree] using hdegree v
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact (show ((F i).card : ℝ) ≤ f by exact_mod_cast hF i).trans hf
  · intro i
    rw [colorMatching_uncoveredOutside]
    apply (mul_le_mul_iff_right₀ hrR).mp
    have hh := c.repairVertices_scaled_bound F f hspread D hdegree' i
    rw [hV] at hh
    exact hh.trans hbudget
  · intro v
    simp only [colorMatching_uncoveredOutside]
    exact (c.repairVertices_incidence_le_error F D hdegree' v).trans hD

/-- Uniform repair of supplied actual balanced color classes. The order
of the uniform choices is exactly that of `MatchingRepair.reserve_repair`:
first `μ₀`, then `δ` and `m₀` for each admissible `μ`, before the graph,
coloring and forbidden footprints are supplied. -/
theorem balanced_color_reserve_repair (b ζ ν τ : ℝ)
    (hb : 0 < b) (hζ : 0 < ζ) (hν : 0 < ν) (hντ : ν ≤ 4 * τ)
    (hτ : τ ≤ 1 / 16) (hτζ : 16 * τ ≤ ζ / 3) :
    ∃ μ₀ : ℝ, 0 < μ₀ ∧ ∀ μ : ℝ, 0 < μ → μ ≤ μ₀ →
      ∃ δ : ℝ, 0 < δ ∧ ∃ m₀ : ℕ,
        ∀ (V : Type*) [Fintype V] [DecidableEq V]
          (G R J : SimpleGraph V), R ≤ G → ∀ hJG : J ≤ G, Disjoint J R →
          ∀ (m r : ℕ), Fintype.card V = m → m₀ ≤ m → Even m →
          0 < r → (r : ℝ) ≤ b * m →
          (∀ v, ζ * m ≤ (R.degree v : ℝ)) → IsRobustExpander R ν τ →
          ∀ (c : (Multigraph.ofSimpleGraph J).EdgeColoring r)
            (F : Fin r → Finset V) (f : ℕ) (D : ℝ),
            c.AvoidsVertices F → (∀ i, (F i).card ≤ f) →
            (∀ i, Even (F i).card) →
            (∀ i j,
              |((c.colorClass i).card : ℤ) - ((c.colorClass j).card : ℤ)| ≤ (f : ℤ) + 1) →
            (∀ v, (r : ℝ) - D ≤ J.degree v) →
            (f : ℝ) ≤ δ * m → D ≤ δ * m →
            (m : ℝ) * D + 2 * r * ((f : ℝ) + 1) ≤ r * (δ * m) →
            ∃ N : Fin r → G.Subgraph,
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
    MatchingRepair.reserve_repair b ζ ν τ hb hζ hν hντ hτ hτζ
  refine ⟨μ₀, hμ₀, ?_⟩
  intro μ hμ hμsmall
  obtain ⟨δ, hδ, m₀, hrepairδ⟩ := hrepair μ hμ hμsmall
  refine ⟨δ, hδ, m₀, ?_⟩
  intro V _ _ G R J hRG hJG hJR m r hV hmLarge hmEven hrpos hr hRmin hRexpand
    c F f D hc hF hFeven hspread hdegree hf hD hbudget
  obtain ⟨hFsize, hYsize, hYinc⟩ :=
    colorMatching_repair_bounds G J hJG c F f D δ m hV hrpos
      hF hspread hdegree hf hD hbudget
  exact hrepairδ V G R hRG m r hV hmLarge hmEven hr hRmin hRexpand
    (colorMatching G J hJG c) F
    (colorMatching_isMatching G J hJG c)
    (colorMatching_pairwise_disjoint G J hJG c)
    (colorMatching_disjoint_reserve G J R hJG c hJR)
    ((colorMatching_avoids_iff G J hJG c F).mpr hc)
    hFeven hFsize hYsize (by
      intro v
      convert hYinc v using 2
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and])

end Overfull.OrdinaryFactorization
