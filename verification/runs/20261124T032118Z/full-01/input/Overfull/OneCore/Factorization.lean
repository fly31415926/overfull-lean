import Overfull.OneCore.Reduction
import Overfull.OneCore.ResidualShores
import Overfull.TwoApexFactorization.Theorem

/-!
# Complete factorization of a regular one-apex graph

An odd robust core is reduced to an even core by moving one original
vertex outside. The constructed first-half palette leaves that vertex
with a linear supply on both shores of the actual bipartite residual
core. The two-apex completion then colors the entire remainder, and the
original completed colors reconstruct the original host coloring.
-/

noncomputable section

namespace Overfull.OneCore

open Finset Classical SmallCuts OrdinaryFactorization

private theorem bipartite_robust_change_instances
    {A B : Type*} [Fintype A] [Fintype B] (H : SimpleGraph (A ⊕ B))
    {d₁ d₂ : DecidableEq A} {r₁ r₂ : DecidableRel H.Adj} {ν τ : ℝ}
    (h : @IsBipartiteRobustExpander A B _ _ d₁ H r₁ ν τ) :
    @IsBipartiteRobustExpander A B _ _ d₂ H r₂ ν τ := by
  have hd : d₁ = d₂ := Subsingleton.elim _ _
  have hr : r₁ = r₂ := Subsingleton.elim _ _
  cases hd
  cases hr
  exact h

/-- A regular finite loopless multigraph with one exterior vertex and an
odd dense robust simple core has a full coloring with its regular degree.
All tolerances and the order threshold precede the input graph. -/
theorem exists_uniform_one_apex_factorization (α ν τ : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτα : τ ≤ α / 8) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ m₀ : ℕ,
      ∀ (V E : Type*) [Fintype V] [Fintype E]
        (G : Multigraph V E) (U : Finset V) (C : Core G U)
        (z : V) (k : ℕ) (a : ℝ),
        m₀ ≤ U.card → U.card % 2 = 1 → Uᶜ = {z} →
        (∀ v, G.degree v = k) → α * U.card ≤ (k : ℝ) →
        IsRobustExpander C.graph ν τ → 0 ≤ a → a ≤ ε * U.card →
        (∀ v, (k : ℝ) - a ≤ (C.graph.degree v : ℝ)) →
        Nonempty (G.EdgeColoring k) := by
  obtain ⟨ν₁, τ₁, ξ, _hν₁, _hν₁τ₁, hτ₁, hτ₁α, hξ, hreduce⟩ :=
    exists_uniform_two_apex_reduction α ν τ hα hα1 hν hντ hτα
  let νB := min (ξ / 2) (4 * τ₁)
  have hνB : 0 < νB := lt_min (by positivity) (by positivity)
  have hνBτ : νB ≤ 4 * τ₁ := min_le_right _ _
  have hτB : 4 * τ₁ < (α / 4) / 16 := by linarith
  obtain ⟨η, hη, mB, hfactor⟩ :=
    TwoApexFactorization.exists_uniform_two_apex_factorization
      (α / 4) (α / 100) νB (4 * τ₁) (by positivity) (by linarith)
      (by positivity) (by linarith) hνB hνBτ hτB
  obtain ⟨p, σ, κ, δ, μ, ε, _hp, _hσ, _hκ, _hδ, _hμ, hε, hthreshold⟩ := hreduce η hη
  obtain ⟨m₀, hconstruct⟩ := hthreshold mB
  refine ⟨ε, hε, m₀, ?_⟩
  intro V E _ _ G U C z k a hm hodd hout hregular hk hrob ha hae hdegree
  obtain ⟨y, D, hmB, ⟨R⟩, houtside, hzy, hleft, hright⟩ :=
    hconstruct V E G U C z k a hm hodd hout hregular hk hrob ha hae hdegree
  let Cnew := restrictCore C {y.val}
  let e := residualShoreEquiv Cnew D
  have hrobB : IsBipartiteRobustExpander
      ((residualCrossingCore Cnew D).graph.comap e) νB (4 * τ₁) := by
    apply residualShore_robust Cnew D
    exact IsBipartiteRobustExpander.mono_parameter _ R.robust (min_le_left _ _)
  have hdensity : (α / 4) * Fintype.card D.geometry.left ≤
      ((k - D.count : ℕ) : ℝ) := by
    simpa only [Fintype.card_coe, show α / 2 / 2 = α / 4 by ring] using R.density
  obtain ⟨rest⟩ := hfactor V _ D.geometry.left D.geometry.right D.remaining
    (U \ {y.val}) (residualCrossingCore Cnew D) e z y.val (k - D.count) R.error
    (residualShore_balance Cnew D)
    (by simpa only [Fintype.card_coe] using hmB)
    hzy houtside R.regular hdensity (residualShore_bipartite Cnew D)
    (bipartite_robust_change_instances _ hrobB)
    R.error_nonneg (by simpa only [Fintype.card_coe] using R.error_small) R.core_degree
    (by simpa only [e, residualShore_left, Fintype.card_coe] using hleft)
    (by simpa only [e, residualShore_right, Fintype.card_coe] using hright)
  exact ⟨R.reassemble rest⟩

end Overfull.OneCore
