import Overfull.NativeReserve.CompletionFootprints
import Overfull.BoundaryExtension.Packing

/-!
# Uniform completion packing in each original embedded core

The forbidden sets are the actual endpoints of the boundary copy family.
Their parity and load come from that family's disjoint original copies.
-/

noncomputable section

namespace Overfull.NativeReserve

open Finset Classical

theorem pack_original_core (α γ ν τ σ : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hγ : 0 < γ)
    (hν : 0 < ν) (hντ : ν ≤ τ) (hτ : τ ≤ α / 8)
    (hσ : 0 < σ) (hσhalf : σ < 1 / 2) :
    ∃ ε θ : ℝ, 0 < ε ∧ 0 < θ ∧ ∃ m₀ : ℕ,
      ∀ (V E : Type*) [Fintype E] (G : Multigraph V E)
        (U : Finset V) (C : SmallCuts.Core G U) (k : ℕ) (a : ℝ),
        m₀ ≤ U.card → IsRobustExpander C.graph ν τ → α * U.card ≤ k →
        (∀ v, G.degree v = k) →
        (∀ v, (k : ℝ) - a ≤ (C.graph.degree v : ℝ)) →
        a ≤ ε * U.card → 6 ≤ ε * U.card →
        ∀ (q : ℕ) (F : Fin q → Finset E),
          q ≤ Nat.floor ((k : ℝ) - γ * U.card) →
          Pairwise (fun i j => Disjoint (F i) (F j)) →
          (∀ j, Disjoint (F j) (OneCore.coreEdges C)) →
          (∀ j, (F j).card ≤ 3) →
          (∀ j, Even (U \ G.edgeSupport (F j)).card) →
          Nonempty (BoundaryExtension.CorePacking C.graph q
            (fun j => coreFootprint G U (F j)) θ σ) := by
  obtain ⟨ε, θ, hε, hθ, m₀, hpack⟩ := BoundaryExtension.pack_fixed_forbidden_sets
    α γ ν τ σ hα hα1 hγ hν hντ hτ hσ hσhalf
  refine ⟨ε, θ, hε, hθ, m₀, ?_⟩
  intro V E _ G U C k a hm hrobust hdensity hregular hdegree herror hsize
    q F hq hdisj hout hcard heven
  have hnear : ∀ v, |(C.graph.degree v : ℝ) - k| ≤ ε * U.card := by
    intro v
    have hupper : (C.graph.degree v : ℝ) ≤ k := by
      exact_mod_cast (OneCore.core_degree_le C v).trans_eq (hregular v.val)
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hupper)]
    linarith only [hdegree v, herror]
  obtain ⟨hparity, hfoot, hload⟩ := coreFootprint_admissible G C F
    hdisj hout hcard heven k a ε hregular hdegree hsize herror
  apply hpack U C.graph k
  · simpa only [Fintype.card_coe] using hm
  · convert hrobust using 1
  · simpa only [Fintype.card_coe] using hdensity
  · simpa only [Fintype.card_coe] using hnear
  · simpa only [Fintype.card_coe] using hq
  · simpa only [Fintype.card_coe] using hparity
  · simpa only [Fintype.card_coe] using hfoot
  · intro v
    convert hload v using 1

end Overfull.NativeReserve
