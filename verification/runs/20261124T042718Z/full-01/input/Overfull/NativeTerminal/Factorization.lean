import Overfull.NativeTerminal.ShoreFactorization
import Overfull.NativeTerminal.ColoringGlue
import Overfull.NativeTerminal.PairColoring

/-!
# Factorization of the terminal two-shore geometry

The actual terminal graph consists of two assigned shores and an optional
closed pair. The two robust old cores may each have either parity. Even
assigned shores are colored as components; odd assigned shores are contracted
at their common cut, whose copies are aligned before gluing. All colorings
are constructed from the displayed geometric and robust-core hypotheses.
-/

noncomputable section

namespace Overfull.NativeTerminal

open Finset Classical SmallCuts BoundaryExtension Multigraph

/-- Uniform terminal coloring from two robust cores, bounded independent
assigned exteriors, and a common cut of size zero or the regular degree. -/
theorem exists_uniform_two_shore_factorization (α ν τ : ℝ) (s : ℕ)
    (hα : 0 < α) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτ : τ ≤ min α 1 / 16) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ m₀ : ℕ,
      ∀ (V E : Type*) [Fintype E] (G : Multigraph V E)
        (U₀ U₁ A₀ A₁ B : Finset V) (C₀ : Core G U₀) (C₁ : Core G U₁)
        (k : ℕ) (a : ℝ),
        Disjoint A₀ A₁ → Disjoint A₀ B → Disjoint A₁ B →
        (∀ v, v ∈ A₀ ∨ v ∈ A₁ ∨ v ∈ B) → U₀ ⊆ A₀ → U₁ ⊆ A₁ →
        m₀ ≤ U₀.card → m₀ ≤ U₁.card →
        (A₀ \ U₀).card ≤ s → (A₁ \ U₁).card ≤ s → B.card ≤ 2 →
        G.cutEdges B = ∅ → (∀ v, G.degree v = k) →
        α * U₀.card ≤ (k : ℝ) → α * U₁.card ≤ (k : ℝ) →
        IsRobustExpander C₀.graph ν τ → IsRobustExpander C₁.graph ν τ →
        a ≤ ε * U₀.card → a ≤ ε * U₁.card →
        (∀ v, (k : ℝ) - a ≤ (C₀.graph.degree v : ℝ)) →
        (∀ v, (k : ℝ) - a ≤ (C₁.graph.degree v : ℝ)) →
        (∀ z ∈ A₀ \ U₀, ∀ e, z ∈ G.edge e → G.otherEnd z e ∈ U₀) →
        (∀ z ∈ A₁ \ U₁, ∀ e, z ∈ G.edge e → G.otherEnd z e ∈ U₁) →
        G.cutEdges A₀ = G.cutEdges A₁ →
        ((Even A₀.card ∧ Even A₁.card ∧ G.cutEdges A₀ = ∅) ∨
          (Odd A₀.card ∧ Odd A₁.card ∧ G.cutSize A₀ = k)) →
        Nonempty (G.EdgeColoring k) := by
  obtain ⟨ε,hε,m₀,hshore⟩ :=
    exists_uniform_shore_coloring_of_star_incidence α ν τ s hα hν hντ hτ
  refine ⟨ε,hε,m₀,?_⟩
  intro V E _ G U₀ U₁ A₀ A₁ B C₀ C₁ k a h01 h0B h1B hcover hUA₀ hUA₁
    hm₀ hm₁ hs₀ hs₁ hBcard hBcut hregular hk₀ hk₁ hrob₀ hrob₁ ha₀ ha₁
    hdegree₀ hdegree₁ hstar₀ hstar₁ hcut hparity
  obtain ⟨hEven₀,hOdd₀⟩ := hshore V E G A₀ U₀ C₀ k a hUA₀ hm₀ hs₀
    (fun v _ => hregular v) hk₀ hrob₀ ha₀ hdegree₀ hstar₀
  obtain ⟨hEven₁,hOdd₁⟩ := hshore V E G A₁ U₁ C₁ k a hUA₁ hm₁ hs₁
    (fun v _ => hregular v) hk₁ hrob₁ ha₁ hdegree₁ hstar₁
  obtain ⟨cB⟩ := retained_pair_colorable G B k hBcut hBcard
    (fun v _ => (hregular v).le)
  rcases hparity with ⟨he₀,he₁,hzero⟩ | ⟨ho₀,ho₁,hsize⟩
  · obtain ⟨c₀⟩ := hEven₀ hzero he₀
    obtain ⟨c₁⟩ := hEven₁ (hcut.symm.trans hzero) he₁
    exact exists_glued_closed_shores_coloring G A₀ A₁ B k h01 h0B h1B hcover
      hzero hBcut c₀ c₁ cB
  · have hsize₁ : G.cutSize A₁ = k := by
      simpa only [Multigraph.cutSize, ← hcut] using hsize
    obtain ⟨c₀⟩ := hOdd₀ hsize ho₀
    obtain ⟨c₁⟩ := hOdd₁ hsize₁ ho₁
    exact exists_glued_contracted_shores_coloring G A₀ A₁ B k h01 h0B h1B hcover
      hBcut hcut hsize c₀ c₁ cB

end Overfull.NativeTerminal
