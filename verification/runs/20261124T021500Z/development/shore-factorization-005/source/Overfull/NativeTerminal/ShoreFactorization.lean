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

private theorem robust_decidableEq_transport {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (d₀ d₁ : DecidableEq W)
    (ν τ : ℝ) (h : @IsRobustExpander W _ d₀ H _ ν τ) :
    @IsRobustExpander W _ d₁ H _ ν τ := by
  cases Subsingleton.elim d₀ d₁
  exact h

/-- Assigned exceptions whose incidences all go into their old core are
independent, and none can be an endpoint of a shore crossing. -/
theorem shore_geometry_of_star_incidence {V E : Type*} [Fintype E]
    (G : Multigraph V E) (A U : Finset V) (hUA : U ⊆ A)
    (hstar : ∀ z ∈ A \ U, ∀ e, z ∈ G.edge e → G.otherEnd z e ∈ U) :
    G.internalEdges (A \ U) = ∅ ∧
      (∀ e ∈ G.cutEdges A, ∀ v, v ∈ G.edge e → v ∈ A → v ∈ U) := by
  constructor
  · apply eq_empty_iff_forall_notMem.mpr
    intro e he
    have he' := (G.mem_internalEdges (A \ U) e).mp he
    have hi := (G.incident_iff e (G.firstEnd e)).mpr (Or.inl rfl)
    have hh := hstar _ he'.1 e hi
    have ho : G.otherEnd (G.firstEnd e) e = G.secondEnd e := by simp [Multigraph.otherEnd]
    rw [ho] at hh
    exact (mem_sdiff.mp he'.2).2 hh
  · intro e he v hv hvA
    by_contra hvU
    have ho := hstar v (mem_sdiff.mpr ⟨hvA,hvU⟩) e hv
    have hi := (G.internalEdges_iff_of_edge e v _ (G.edge_eq_otherEnd v e hv) A).mpr
      ⟨hvA,hUA ho⟩
    have hends := (G.mem_internalEdges A e).mp hi
    exact (G.mem_cutEdges A e).mp he (propext (iff_of_true hends.1 hends.2))

set_option maxHeartbeats 800000 in
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
  classical
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
    obtain ⟨c⟩ := @hfactor A (G.internalEdges A)
      (Finset.Subtype.fintype A) (Finset.Subtype.fintype (G.internalEdges A)) (inducedHost G A)
      (inducedCoreVertices A U) (inducedCore C hUA) k a
      (by simpa only [hc] using hm) (by simpa using heven)
      (by simpa only [card_compl] using hz)
      (inducedHost_regular G A k hcut hregular) (by simpa only [hc] using hk)
      (by
        convert inducedHost_independent_exterior G A U hindependent using 2 <;>
          ext v <;> simp only [mem_compl])
      (by
        apply robust_decidableEq_transport _ _ _ ν τ
        exact inducedCore_robust C hUA ν τ hrob)
      (by simpa only [hc] using ha)
      (by intro v; rw [inducedCore_degree]; exact hdegree _)
    exact ⟨inducedColoringToRetained G A k hcut c⟩
  · intro hcut hodd hcross
    have hc := contractedCoreVertices_card hUA
    have hz : (contractedCoreVertices A U)ᶜ.card ≤ s+1 := by
      rw [contractedCoreVertices_compl_card hUA]
      omega
    exact @hfactor (Vertex A) (RetainedEdge G A) inferInstance inferInstance (contract G A)
      (contractedCoreVertices A U) (contractedCore C hUA) k a
      (by simpa only [hc] using hm) (even_contracted_order A hodd)
      (by simpa only [card_compl] using hz)
      (contract_regular G A k (fun v => hregular v.val v.property) hcut)
      (by simpa only [hc] using hk)
      (by
        convert contractedHost_independent_exterior G A U hindependent hcross using 2 <;>
          ext v <;> simp only [mem_compl])
      (by
        apply robust_decidableEq_transport _ _ _ ν τ
        exact contractedCore_robust C hUA ν τ hrob)
      (by simpa only [hc] using ha)
      (by intro v; rw [contractedCore_degree]; exact hdegree _)

/-- The same uniform shore colorings from the direct native incidence
condition on assigned exceptional vertices. -/
theorem exists_uniform_shore_coloring_of_star_incidence (α ν τ : ℝ) (s : ℕ)
    (hα : 0 < α) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτ : τ ≤ min α 1 / 16) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ m₀ : ℕ,
      ∀ (V E : Type*) [Fintype E] (G : Multigraph V E)
        (A U : Finset V) (C : Core G U) (k : ℕ) (a : ℝ),
        U ⊆ A → m₀ ≤ U.card → (A \ U).card ≤ s →
        (∀ v ∈ A, G.degree v = k) → α * U.card ≤ (k : ℝ) →
        IsRobustExpander C.graph ν τ → a ≤ ε * U.card →
        (∀ v, (k : ℝ) - a ≤ (C.graph.degree v : ℝ)) →
        (∀ z ∈ A \ U, ∀ e, z ∈ G.edge e → G.otherEnd z e ∈ U) →
        (G.cutEdges A = ∅ → Even A.card →
          Nonempty ((retainedGraph G A).EdgeColoring k)) ∧
        (G.cutSize A = k → Odd A.card →
          Nonempty ((contract G A).EdgeColoring k)) := by
  obtain ⟨ε,hε,m₀,hfactor⟩ := exists_uniform_shore_coloring α ν τ s hα hν hντ hτ
  refine ⟨ε,hε,m₀,?_⟩
  intro V E _ G A U C k a hUA hm hs hregular hk hrob ha hdegree hstar
  obtain ⟨hindependent,hcross⟩ := shore_geometry_of_star_incidence G A U hUA hstar
  obtain ⟨heven,hodd⟩ :=
    hfactor V E G A U C k a hUA hm hs hregular hk hrob ha hdegree hindependent
  exact ⟨heven,fun hcut hA => hodd hcut hA hcross⟩

end Overfull.NativeTerminal
