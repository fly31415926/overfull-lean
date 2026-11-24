import Overfull.NativeTerminal.ShoreFactorization
import Overfull.NativeTerminal.ColoringGlue

/-!
# Factorization when the robust core parts are components

Once every joining copy has been removed, the actual component colorings
can be constructed independently and glued on the original edge type.
The constants do not depend on the number of component parts.
-/

noncomputable section

namespace Overfull.Terminal

open Finset Classical Multigraph SmallCuts NativeTerminal BoundaryExtension

/-- Colorings of a disjoint covering family of closed shores glue on the
original edge copies, with no compatibility conditions between components. -/
theorem exists_glued_component_coloring {V E I : Type*} [Fintype E]
    (G : Multigraph V E) (U : I → Finset V) (k : ℕ)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hcover : ∀ v, ∃ i, v ∈ U i)
    (hcut : ∀ i, G.cutEdges (U i) = ∅)
    (hcolor : ∀ i, Nonempty ((retainedGraph G (U i)).EdgeColoring k)) :
    Nonempty (G.EdgeColoring k) := by
  classical
  let c : ∀ i, PaletteColoring (retainedGraph G (U i)) (Fin k) :=
    fun i => PaletteColoring.ofEdgeColoring (Classical.choice (hcolor i))
  obtain ⟨d, _⟩ := exists_glued_retained_coloring G U hcover c (by
    intro i j e hi hj
    by_cases hij : i = j
    · subst j
      rfl
    · exact (no_overlap_of_closed_shore G (U i) (U j)
        (hdisjoint i j hij) (hcut j) e hi hj).elim)
  exact ⟨d.toEdgeColoring⟩

/-- Uniformly construct the whole host coloring when its even robust-core
parts are closed components. No local coloring is supplied as a hypothesis. -/
theorem exists_uniform_closed_core_factorization (α ν τ : ℝ)
    (hα : 0 < α) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτ : τ ≤ min α 1 / 16) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ m₀ : ℕ,
      ∀ (V E I : Type*) [Fintype E] (G : Multigraph V E)
        (U : I → Finset V) (C : ∀ i, Core G (U i)) (k : ℕ) (a : ℝ),
        (∀ i j, i ≠ j → Disjoint (U i) (U j)) →
        (∀ v, ∃ i, v ∈ U i) →
        (∀ i, m₀ ≤ (U i).card) →
        (∀ i, Even (U i).card) →
        (∀ i, G.cutEdges (U i) = ∅) →
        (∀ v, G.degree v = k) →
        (∀ i, α * (U i).card ≤ (k : ℝ)) →
        (∀ i, IsRobustExpander (C i).graph ν τ) →
        (∀ i, a ≤ ε * (U i).card) →
        (∀ i v, (k : ℝ) - a ≤ ((C i).graph.degree v : ℝ)) →
        Nonempty (G.EdgeColoring k) := by
  obtain ⟨ε, hε, m₀, hfactor⟩ :=
    exists_uniform_shore_coloring_of_star_incidence α ν τ 0 hα hν hντ hτ
  refine ⟨ε, hε, m₀, ?_⟩
  intro V E I _ G U C k a hdisjoint hcover hm heven hcut hregular hk hrob ha hdegree
  apply exists_glued_component_coloring G U k hdisjoint hcover hcut
  intro i
  have hshore := hfactor V E G (U i) (U i) (C i) k a
    (Subset.refl _) (hm i) (by simp) (fun v _ => hregular v)
    (hk i) (hrob i) (ha i) (hdegree i) (by
      intro z hz
      simp at hz)
  exact hshore.1 (hcut i) (heven i)

/-- The closed-core coloring gives exactly the degree number of disjoint
perfect matchings, covering every original edge copy. -/
theorem exists_uniform_closed_core_one_factorization (α ν τ : ℝ)
    (hα : 0 < α) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτ : τ ≤ min α 1 / 16) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ m₀ : ℕ,
      ∀ (V E I : Type*) [Fintype V] [Fintype E] (G : Multigraph V E)
        (U : I → Finset V) (C : ∀ i, Core G (U i)) (k : ℕ) (a : ℝ),
        (∀ i j, i ≠ j → Disjoint (U i) (U j)) →
        (∀ v, ∃ i, v ∈ U i) →
        (∀ i, m₀ ≤ (U i).card) →
        (∀ i, Even (U i).card) →
        (∀ i, G.cutEdges (U i) = ∅) →
        (∀ v, G.degree v = k) →
        (∀ i, α * (U i).card ≤ (k : ℝ)) →
        (∀ i, IsRobustExpander (C i).graph ν τ) →
        (∀ i, a ≤ ε * (U i).card) →
        (∀ i v, (k : ℝ) - a ≤ ((C i).graph.degree v : ℝ)) →
        ∃ M : Fin k → Finset E,
          (∀ j, G.IsPerfectMatching (M j)) ∧
          Pairwise (fun i j => Disjoint (M i) (M j)) ∧
          univ.biUnion M = univ := by
  obtain ⟨ε, hε, m₀, hfactor⟩ :=
    exists_uniform_closed_core_factorization α ν τ hα hν hντ hτ
  refine ⟨ε, hε, m₀, ?_⟩
  intro V E I _ _ G U C k a hd hc hm heven hcut hregular hk hrob ha hdegree
  obtain ⟨c⟩ := hfactor V E I G U C k a hd hc hm heven hcut hregular hk hrob ha hdegree
  exact BoundedExterior.exists_oneFactorization_of_coloring G k hregular c

end Overfull.Terminal
