import Overfull.ColoringExtension.AsymptoticBounds
import Overfull.ColoringExtension.Simple

/-!
# Uniform forbidden-color extension with a linear number of spare colors

For every positive slack proportion, fix a positive forbidden-label
tolerance and an order threshold before the graph and its constraints.
The proof uses finite permutation counts and deterministic repair. For
simple graphs the verified Vizing theorem supplies the initial coloring.
-/

namespace Overfull.ColoringExtension

open Finset Classical
open Multigraph

/-- Uniformly add at most the prescribed linear ceiling of spare colors
to any actual proper coloring and avoid a small number of labels per edge. -/
theorem exists_uniform_avoiding_coloring (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ,
      ∀ (V E : Type*) [Fintype V] [Fintype E]
        (G : Multigraph V E) (r : ℕ) (_c₀ : G.EdgeColoring r),
        n₀ ≤ Fintype.card V →
        ∀ B : E → Finset (Fin (r + Nat.ceil (δ * Fintype.card V))),
          (∀ e, ((B e).card : ℝ) ≤ ε * Fintype.card V) →
          ∃ c : G.EdgeColoring (r + Nat.ceil (δ * Fintype.card V)),
            ∀ e, c.color e ∉ B e := by
  classical
  obtain ⟨ε, hε, n₀, hn₀⟩ := exists_uniform_coloring_bounds δ hδ
  refine ⟨ε, hε, n₀, ?_⟩
  intro V E _ _ G r c₀ hn B hB
  let b := Nat.floor (ε * Fintype.card V)
  have hb : (b : ℝ) ≤ ε * Fintype.card V := Nat.floor_le (by positivity)
  have hBn : ∀ e, (B e).card ≤ b := fun e => Nat.le_floor (hB e)
  obtain ⟨t, ht, htail, hslack⟩ := hn₀ (Fintype.card V) hn b hb
  exact exists_avoiding_with_spare_colors c₀ (Nat.ceil (δ * Fintype.card V))
    B b t ht hBn htail hslack

/-- Uniformly construct and balance an extension respecting fixed
per-color forbidden vertices. The load and class-size bounds are separate:
the load supplies feasibility, and each footprint size controls balancing. -/
theorem exists_uniform_balanced_avoiding (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ,
      ∀ (V E : Type*) [Fintype V] [Fintype E]
        (G : Multigraph V E) (r : ℕ) (_c₀ : G.EdgeColoring r),
        n₀ ≤ Fintype.card V →
        ∀ (F : Fin (r + Nat.ceil (δ * Fintype.card V)) → Finset V) (f : ℕ),
          (∀ i, (F i).card ≤ f) →
          (∀ v, ((forbiddenColors F v).card : ℝ) ≤ ε * Fintype.card V) →
          ∃ c : G.EdgeColoring (r + Nat.ceil (δ * Fintype.card V)),
            c.AvoidsVertices F ∧
            ∀ i j, |((c.colorClass i).card : ℤ) - ((c.colorClass j).card : ℤ)| ≤
              (f : ℤ) + 1 := by
  classical
  obtain ⟨ε, hε, n₀, hn₀⟩ := exists_uniform_avoiding_coloring δ hδ
  refine ⟨ε / 2, by positivity, n₀, ?_⟩
  intro V E _ _ G r c₀ hn F f hF hload
  have hB (e : E) : ((edgeForbiddens G F e).card : ℝ) ≤ ε * Fintype.card V := by
    have hcard : ((edgeForbiddens G F e).card : ℝ) ≤
        (forbiddenColors F (G.firstEnd e)).card + (forbiddenColors F (G.secondEnd e)).card := by
      exact_mod_cast Finset.card_union_le
        (forbiddenColors F (G.firstEnd e)) (forbiddenColors F (G.secondEnd e))
    have hu := hload (G.firstEnd e)
    have hv := hload (G.secondEnd e)
    linarith
  obtain ⟨c, hc⟩ := hn₀ V E G r c₀ hn (edgeForbiddens G F) hB
  exact c.exists_balanced_avoiding F f hF
    ((avoidsVertices_iff_edgeForbiddens c F).mpr hc)

/-- A uniform simple-graph substitute for the bounded-forbidden-label
application of asymptotic list coloring. It makes no assertion about
arbitrary lists or the general list edge-coloring theorem. -/
theorem exists_uniform_simple_avoiding (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ,
      ∀ (V : Type*) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V →
        ∀ B : G.edgeSet → Finset (Fin (G.maxDegree + 1 + Nat.ceil (δ * Fintype.card V))),
          (∀ e, ((B e).card : ℝ) ≤ ε * Fintype.card V) →
          ∃ c : Overfull.EdgeColoring G (G.maxDegree + 1 + Nat.ceil (δ * Fintype.card V)),
            ∀ e, c.color e ∉ B e := by
  classical
  obtain ⟨ε, hε, n₀, hn₀⟩ := exists_uniform_avoiding_coloring δ hδ
  refine ⟨ε, hε, n₀, ?_⟩
  intro V _ G _ hn B hB
  obtain ⟨c₀⟩ := exists_initial_simple_coloring G
  obtain ⟨c, hc⟩ := hn₀ V G.edgeSet (Multigraph.ofSimpleGraph G) (G.maxDegree + 1)
    c₀ hn B hB
  exact ⟨toSimpleColoring c, hc⟩

/-- The simple internal graph has an actual feasible balanced coloring
with `maxDegree+1+ceil(δ*|V|)` colors, uniformly over all fixed footprints. -/
theorem exists_uniform_simple_balanced_avoiding (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ,
      ∀ (V : Type*) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V →
        ∀ (F : Fin (G.maxDegree + 1 + Nat.ceil (δ * Fintype.card V)) → Finset V)
          (f : ℕ),
          (∀ i, (F i).card ≤ f) →
          (∀ v, ((forbiddenColors F v).card : ℝ) ≤ ε * Fintype.card V) →
          ∃ c : (Multigraph.ofSimpleGraph G).EdgeColoring
              (G.maxDegree + 1 + Nat.ceil (δ * Fintype.card V)),
            c.AvoidsVertices F ∧
            ∀ i j, |((c.colorClass i).card : ℤ) - ((c.colorClass j).card : ℤ)| ≤
              (f : ℤ) + 1 := by
  classical
  obtain ⟨ε, hε, n₀, hn₀⟩ := exists_uniform_balanced_avoiding δ hδ
  refine ⟨ε, hε, n₀, ?_⟩
  intro V _ G _ hn F f hF hload
  obtain ⟨c₀⟩ := exists_initial_simple_coloring G
  exact hn₀ V G.edgeSet (Multigraph.ofSimpleGraph G) (G.maxDegree + 1)
    c₀ hn F f hF hload

end Overfull.ColoringExtension
