import Overfull.BoundaryExtension.Reduction
import Overfull.OneCore.Factorization

/-!
# The full prescribed boundary extension

The reduction constructs the actual regular one-apex residual. The proved
one-apex factorization colors that graph, and the exact reconstruction
restores every original prescribed boundary label. Every error tolerance
and order threshold is chosen before the host graph or boundary coloring.
-/

namespace Overfull

open Finset Classical BoundaryExtension

set_option maxHeartbeats 800000 in
/-- Full Lemma 4.14: extend the prescribed singleton/triple boundary
coloring to every original edge copy incident with the robust odd core. -/
theorem boundary_extension (α γ ν τ : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hγ : 0 < γ)
    (hν : 0 < ν) (hντ : ν ≤ τ) (hτ : τ ≤ α / 8) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ m₀ : ℕ,
      ∀ (V E : Type*) [Fintype E] (G : Multigraph V E)
        (U : Finset V) (C : SmallCuts.Core G U) (d : ℕ) (a : ℝ)
        (c : BoundaryColoring G U d),
        m₀ ≤ U.card → U.card % 2 = 1 →
        (∀ v : U, G.degree v.val = d) → α * U.card ≤ d →
        IsRobustExpander C.graph ν τ → 0 ≤ a → a ≤ ε * U.card →
        (∀ v, (d : ℝ) - a ≤ C.graph.degree v) →
        (∀ i, (c.classEdges i).card = 1 ∨ (c.classEdges i).card = 3) →
        γ * U.card ≤ c.singletonColors.card →
        ∃ full : (retainedGraph G U).EdgeColoring d,
          ∀ e : G.cutEdges U, full.color (boundaryLift G U e) = c.color e := by
  obtain ⟨εR, θ, σ, hεR, hθ, hθσ, _hσ, _hστ, hσγ, mR, hreduce⟩ :=
    boundary_extension_reduction α γ ν τ hα hα1 hγ hν hντ hτ
  let β := min γ 1
  have hβ : 0 < β := lt_min hγ zero_lt_one
  have hβ1 : β ≤ 1 := min_le_right _ _
  have hσβ : σ ≤ β / 8 := by
    change σ ≤ β / 20 at hσγ
    linarith
  obtain ⟨εF, hεF, mF, hfactor⟩ :=
    OneCore.exists_uniform_one_apex_factorization β θ σ hβ hβ1 hθ hθσ hσβ
  refine ⟨min εR εF, lt_min hεR hεF, max mR mF, ?_⟩
  intro V E _ G U C d a c hm hodd hregular hdensity hrob ha haSmall hdegree hclasses hsingle
  have haR : a ≤ εR * U.card := haSmall.trans
    (mul_le_mul_of_nonneg_right (min_le_left εR εF) (Nat.cast_nonneg _))
  have haF : a ≤ εF * U.card := haSmall.trans
    (mul_le_mul_of_nonneg_right (min_le_right εR εF) (Nat.cast_nonneg _))
  obtain ⟨D⟩ := hreduce V E G U C d a c ((le_max_left _ _).trans hm) hodd
    hregular hdensity hrob ha haR hdegree hclasses hsingle
  let R := G.restrictEdges D.deletedᶜ
  have hcore : ∀ v : coreVertices U,
      ((d - c.tripleColors.card : ℕ) : ℝ) - a ≤ (contractCore D.core).graph.degree v := by
    intro v
    rw [contractCore_degree]
    exact D.core_degree ((coreEquiv U).symm v)
  have hrobust : IsRobustExpander (contractCore D.core).graph θ σ :=
    contractCore_robust D.core θ σ D.core_robust
  have hd : β * (coreVertices U).card ≤ ((d - c.tripleColors.card : ℕ) : ℝ) := by
    rw [coreVertices_card]
    exact (mul_le_mul_of_nonneg_right (min_le_left γ 1)
      (Nat.cast_nonneg _)).trans D.retained_density
  obtain ⟨color⟩ := hfactor (Vertex U) (RetainedEdge R U) (contract R U)
    (coreVertices U) (contractCore D.core) (Sum.inr ()) (d - c.tripleColors.card) a
    (by simpa only [coreVertices_card] using (le_max_right mR mF).trans hm)
    (by simpa only [coreVertices_card] using hodd)
    (by
      ext v
      rcases v with u | u
      · simp
      · cases u
        simp)
    D.contracted_regular hd (by convert hrobust using 1) ha
    (by simpa only [coreVertices_card] using haF)
    (by intro v; convert hcore v using 1)
  exact D.extend color

end Overfull
