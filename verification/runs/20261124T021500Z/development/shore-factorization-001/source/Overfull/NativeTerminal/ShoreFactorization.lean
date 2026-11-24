import Overfull.NativeTerminal.ShoreCore

/-!
# Uniform coloring of actual terminal shores

One parameter choice handles the even component shore and the odd shore
with one contracted apex.  The old core can have either parity.  The
colorings are obtained from the independent-exterior factorization theorem;
no coloring of either terminal host is assumed.
-/

noncomputable section

namespace Overfull.NativeTerminal

open Finset Classical SmallCuts BoundaryExtension Multigraph NativeCore

/-- Uniformly color the actual shore host in either parity case.  The
geometric assumptions exclude edges between assigned exceptional vertices
and, in the contracted case, force every crossing endpoint into the old core. -/
theorem exists_uniform_shore_coloring (α ν τ : ℝ) (s : ℕ)
    (hα : 0 < α) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτ : τ ≤ min α 1 / 16) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ m₀ : ℕ,
      ∀ (V E : Type*) [Fintype E] (G : Multigraph V E)
        (A U : Finset V) (C : Core G U) (k : ℕ) (a : ℝ),
        U ⊆ A → m₀ ≤ U.card → (A \ U).card ≤ s →
        (∀ v ∈ A, G.degree v = k) → α * U.card ≤ (k : ℝ) →
        IsRobustExpander C.graph ν τ → a ≤ ε * U.card →
        (∀ v, (k : ℝ) - a ≤ (C.graph.degree v : ℝ)) →
        G.internalEdges (A \ U) = ∅ →
        (G.cutEdges A = ∅ → Even A.card →
          Nonempty ((retainedGraph G A).EdgeColoring k)) ∧
        (G.cutSize A = k → Odd A.card →
          (∀ e ∈ G.cutEdges A, ∀ v, v ∈ G.edge e → v ∈ A → v ∈ U) →
          Nonempty ((contract G A).EdgeColoring k)) := by
  obtain ⟨ε,hε,m₀,hfactor⟩ :=
    exists_uniform_independent_exterior_factorization α ν τ (s+1) hα hν hντ hτ
  refine ⟨ε,hε,m₀,?_⟩
  intro V E _ G A U C k a hUA hm hs hregular hk hrob ha hdegree hindependent
  constructor
  · intro hcut heven
    have hc := inducedCoreVertices_card A U hUA
    have hz : (inducedCoreVertices A U)ᶜ.card ≤ s+1 := by
      rw [inducedCoreVertices_compl_card]
      omega
    obtain ⟨c⟩ := hfactor A (G.internalEdges A) (inducedHost G A)
      (inducedCoreVertices A U) (inducedCore C hUA) k a
      (by simpa only [hc] using hm) (by simpa using heven) hz
      (inducedHost_regular G A k hcut hregular) (by simpa only [hc] using hk)
      (inducedHost_independent_exterior G A U hindependent)
      (inducedCore_robust C hUA ν τ hrob) (by simpa only [hc] using ha)
      (by intro v; rw [inducedCore_degree]; exact hdegree _)
    exact ⟨inducedColoringToRetained G A k hcut c⟩
  · intro hcut hodd hcross
    have hc := contractedCoreVertices_card hUA
    have hz : (contractedCoreVertices A U)ᶜ.card ≤ s+1 := by
      rw [contractedCoreVertices_compl_card hUA]
      omega
    exact hfactor (Vertex A) (RetainedEdge G A) (contract G A)
      (contractedCoreVertices A U) (contractedCore C hUA) k a
      (by simpa only [hc] using hm) (even_contracted_order A hodd) hz
      (contract_regular G A k (fun v => hregular v.val v.property) hcut)
      (by simpa only [hc] using hk)
      (contractedHost_independent_exterior G A U hindependent hcross)
      (contractedCore_robust C hUA ν τ hrob) (by simpa only [hc] using ha)
      (by intro v; rw [contractedCore_degree]; exact hdegree _)

end Overfull.NativeTerminal
