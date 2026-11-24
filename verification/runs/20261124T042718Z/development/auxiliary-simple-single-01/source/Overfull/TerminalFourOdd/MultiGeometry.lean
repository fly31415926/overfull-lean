import Overfull.TerminalFourOdd.MultiContraction
import Overfull.NativeCore.IndependentExterior

/-! Regularity and independent apices in simultaneous shore contractions. -/

noncomputable section

namespace Overfull.TerminalFourOdd.Multi

open Finset Classical SmallCuts Multigraph NativeCore

variable {V E I : Type*} [Fintype I]

@[simp] theorem centralVertex_card (U : Finset V) :
    Fintype.card (CentralVertex U I) = U.card + Fintype.card I := by simp [CentralVertex]

@[simp] theorem centralCoreVertices_compl_card (U : Finset V) :
    (centralCoreVertices U I)ᶜ.card = Fintype.card I := by
  rw [Finset.card_compl,centralCoreVertices_card,centralVertex_card]
  omega

variable [Fintype E]

omit [Fintype I] in
theorem central_regular (G : Multigraph V E) (U : Finset V) (label : V → I)
    (X : I → Finset V) (k : ℕ)
    (hfiber : ∀ i v, centralMap U label v = Sum.inr i ↔ v ∈ X i)
    (hregular : ∀ u ∈ U, G.degree u = k) (hcut : ∀ i, G.cutSize (X i) = k) :
    ∀ v, (centralGraph G U label).degree v = k := by
  rintro (u | i)
  · exact (central_degree_inl G U label u).trans (hregular u.val u.property)
  · exact (central_degree_fiber G U (X i) label (Sum.inr i) (hfiber i)).trans (hcut i)

/-- A host edge outside the core can only remain when it joins different
outside labels. Excluding those edges makes all contracted apices independent. -/
theorem central_independent_exterior (G : Multigraph V E) (U : Finset V) (label : V → I)
    (hout : ∀ e, G.firstEnd e ∉ U → G.secondEnd e ∉ U →
      label (G.firstEnd e) = label (G.secondEnd e)) :
    (centralGraph G U label).internalEdges (centralCoreVertices U I)ᶜ = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  have hcore : G.firstEnd e.val ∈ U ∨ G.secondEnd e.val ∈ U := by
    by_contra hn
    push_neg at hn
    exact e.property (by simp only [centralMap, dif_neg hn.1, dif_neg hn.2, hout e.val hn.1 hn.2])
  obtain ⟨u, hu⟩ : ∃ u : U, Sum.inl u ∈ (centralGraph G U label).edge e := by
    rcases hcore with hf | hs
    · refine ⟨⟨G.firstEnd e.val,hf⟩, ?_⟩
      rw [central_incident_inl_iff]
      exact (G.incident_iff _ _).mpr (Or.inl rfl)
    · refine ⟨⟨G.secondEnd e.val,hs⟩, ?_⟩
      rw [central_incident_inl_iff]
      exact (G.incident_iff _ _).mpr (Or.inr rfl)
  have he' := ((centralGraph G U label).mem_internalEdges _ e).mp he
  rcases ((centralGraph G U label).incident_iff e (Sum.inl u)).mp hu with hf | hs
  · rw [hf] at he'
    exact (mem_compl.mp he'.1) (central_inl_mem_core U u)
  · rw [hs] at he'
    exact (mem_compl.mp he'.2) (central_inl_mem_core U u)

omit [Fintype I] [Fintype E] in
private theorem robust_instances_transport {W : Type*} [Fintype W]
    (H : SimpleGraph W) (d₀ d₁ : DecidableEq W) (r₀ r₁ : DecidableRel H.Adj)
    (ν τ : ℝ) (h : @IsRobustExpander W _ d₀ H r₀ ν τ) :
    @IsRobustExpander W _ d₁ H r₁ ν τ := by
  cases Subsingleton.elim d₀ d₁
  cases Subsingleton.elim r₀ r₁
  exact h

omit [Fintype I] [Fintype E] in
theorem exists_uniform_central_star_coloring (α ν τ : ℝ) (s : ℕ)
    (hα : 0 < α) (hν : 0 < ν) (hντ : ν ≤ τ) (hτ : τ ≤ min α 1/16) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ m₀ : ℕ,
      ∀ (V E I : Type*) [Fintype E] [Fintype I]
        (G : Multigraph V E) (U : Finset V) (C : Core G U)
        (label : V → I) (X : I → Finset V) (k : ℕ) (a : ℝ),
        m₀ ≤ U.card → Even (U.card+Fintype.card I) → Fintype.card I ≤ s →
        (∀ i v, centralMap U label v = Sum.inr i ↔ v ∈ X i) →
        (∀ u ∈ U, G.degree u = k) → (∀ i, G.cutSize (X i) = k) →
        α*U.card ≤ (k : ℝ) →
        (∀ e, G.firstEnd e ∉ U → G.secondEnd e ∉ U →
          label (G.firstEnd e) = label (G.secondEnd e)) →
        IsRobustExpander C.graph ν τ → a ≤ ε*U.card →
        (∀ v, (k : ℝ)-a ≤ (C.graph.degree v : ℝ)) →
        Nonempty ((centralGraph G U label).EdgeColoring k) := by
  obtain ⟨ε,hε,m₀,hfactor⟩ := exists_uniform_independent_exterior_factorization α ν τ s
    hα hν hντ hτ
  refine ⟨ε,hε,m₀,?_⟩
  intro V E I _ _ G U C label X k a hm heven hI hfiber hregular hcut hk hout hrob ha hdegree
  exact hfactor (CentralVertex U I) (CentralEdge G U label) (centralGraph G U label)
    (centralCoreVertices U I) (centralCore C label) k a
    (by simpa only [centralCoreVertices_card] using hm)
    (by simpa only [centralVertex_card] using heven)
    (by simpa only [centralCoreVertices_compl_card] using hI)
    (central_regular G U label X k hfiber hregular hcut)
    (by simpa only [centralCoreVertices_card] using hk)
    (central_independent_exterior G U label hout)
    (by
      apply robust_instances_transport _ _ _ _ _ ν τ
      exact centralCore_robust C label ν τ hrob)
    (by simpa only [centralCoreVertices_card] using ha)
    (by intro v; rw [centralCore_degree]; exact hdegree _)

end Overfull.TerminalFourOdd.Multi
