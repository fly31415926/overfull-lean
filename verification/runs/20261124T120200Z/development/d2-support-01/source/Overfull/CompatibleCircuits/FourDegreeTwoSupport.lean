import Overfull.CompatibleCircuits.FourAdmissibleTransfer

/-!
# Removing unused labels from compatible-circuit problems

The graph on its selected support retains the actual selected edge copies.
Consequently the three-label existence theorem applies whenever at most
three labels occur, regardless of the ambient vertex type.
-/

noncomputable section

namespace Overfull.Multigraph

open Finset Classical

variable {V W E F K : Type*} (G : Multigraph V E)

theorem IsCircuit.embedVertices [Fintype V] (φ : V ↪ W) {C : Finset E}
    (hC : G.IsCircuit C) : (G.embedVertices φ).IsCircuit C := by
  refine ⟨hC.1, ?_, ?_⟩
  · intro w hw
    rw [G.embedVertices_edgeSupport] at hw
    obtain ⟨v, hv, rfl⟩ := mem_map.mp hw
    rw [G.embedVertices_degreeOn]
    exact hC.2.1 v hv
  · intro X hX hnonempty hproper
    let Y := univ.filter (fun v => φ v ∈ X)
    have hY : Y ⊆ G.edgeSupport C := by
      intro v hv
      have hmem := hX (mem_filter.mp hv).2
      rw [G.embedVertices_edgeSupport] at hmem
      obtain ⟨u, hu, huv⟩ := mem_map.mp hmem
      simpa only [φ.injective huv] using hu
    have hXY : Y.map φ = X := by
      ext w
      constructor
      · rintro hw
        obtain ⟨v, hv, rfl⟩ := mem_map.mp hw
        exact (mem_filter.mp hv).2
      · intro hw
        have hmem := hX hw
        rw [G.embedVertices_edgeSupport] at hmem
        obtain ⟨v, _, rfl⟩ := mem_map.mp hmem
        exact mem_map.mpr ⟨v, mem_filter.mpr ⟨mem_univ _, hw⟩, rfl⟩
    have hYnonempty : Y.Nonempty := by
      have := hnonempty
      rw [← hXY] at this
      exact Finset.map_nonempty.mp this
    have hYproper : Y ≠ G.edgeSupport C := by
      intro heq
      apply hproper
      rw [← hXY, heq, G.embedVertices_edgeSupport]
    simpa only [G.embedVertices_cutOn, Y] using hC.2.2 Y hY hYnonempty hYproper

/-- Padding a circuit partition by isolated labels keeps every original part. -/
def CompatibleCircuitPartition.embedVertices [Fintype V] (φ : V ↪ W)
    {classOf : V → E → K} {C : Finset E}
    (P : G.CompatibleCircuitPartition classOf C) :
    (G.embedVertices φ).CompatibleCircuitPartition (embedIncidenceClasses φ classOf) C where
  parts := P.parts
  circuit D hD := (P.circuit D hD).embedVertices G φ
  compatible D hD := (G.embedVertices_compatible φ classOf D).mpr (P.compatible D hD)
  disjoint := P.disjoint
  cover := P.cover

/-- Restrict both endpoints and copies to the support of the selected copies. -/
def selectedSupportGraph (C : Finset E) : Multigraph (G.edgeSupport C) C where
  edge e := s(⟨G.firstEnd e, (G.mem_edgeSupport C _).mpr
    ⟨e, e.property, (G.incident_iff _ _).mpr (Or.inl rfl)⟩⟩,
    ⟨G.secondEnd e, (G.mem_edgeSupport C _).mpr
      ⟨e, e.property, (G.incident_iff _ _).mpr (Or.inr rfl)⟩⟩)
  loopless e := by
    simp only [Sym2.isDiag_iff_proj_eq]
    intro h
    exact G.endpoints_distinct e (congrArg Subtype.val h)

theorem selectedSupportGraph_embedded_edge (C : Finset E) (e : C) :
    ((G.selectedSupportGraph C).embedVertices
      (Function.Embedding.subtype (fun v => v ∈ G.edgeSupport C))).edge e = G.edge e := by
  change s(G.firstEnd e, G.secondEnd e) = G.edge e
  exact G.edge_eq e

theorem selectedSupportGraph_incident (C : Finset E) (e : C) (v : G.edgeSupport C) :
    v ∈ (G.selectedSupportGraph C).edge e ↔ v.val ∈ G.edge e.val := by
  rw [← G.selectedSupportGraph_embedded_edge C e]
  exact ((G.selectedSupportGraph C).embedVertices_incident_image
    (Function.Embedding.subtype (fun v => v ∈ G.edgeSupport C)) e v).symm

theorem selectedSupportGraph_degree (C : Finset E) (v : G.edgeSupport C) :
    (G.selectedSupportGraph C).degreeOn univ v = G.degreeOn C v := by
  let ψ := Function.Embedding.subtype (fun e => e ∈ C)
  have hmap : univ.map ψ = C := by ext e; simp [ψ]
  let φ := Function.Embedding.subtype (fun v => v ∈ G.edgeSupport C)
  let J := (G.selectedSupportGraph C).embedVertices φ
  have h := copyEmbedding_degree J G ψ (fun e =>
    (G.selectedSupportGraph_embedded_edge C e).symm) univ v.val
  rw [hmap, (G.selectedSupportGraph C).embedVertices_degreeOn φ] at h
  exact h.symm

theorem selectedSupportGraph_cut (C : Finset E) (X : Finset (G.edgeSupport C)) :
    ((G.selectedSupportGraph C).cutOn univ X).map
      (Function.Embedding.subtype (fun e => e ∈ C)) =
      G.cutOn C (X.map (Function.Embedding.subtype (fun v => v ∈ G.edgeSupport C))) := by
  let ψ := Function.Embedding.subtype (fun e => e ∈ C)
  have hmap : univ.map ψ = C := by ext e; simp [ψ]
  let φ := Function.Embedding.subtype (fun v => v ∈ G.edgeSupport C)
  let J := (G.selectedSupportGraph C).embedVertices φ
  have h := copyEmbedding_cut J G ψ (fun e =>
    (G.selectedSupportGraph_embedded_edge C e).symm) univ (X.map φ)
  rw [hmap, (G.selectedSupportGraph C).embedVertices_cutOn_map φ] at h
  exact h.symm

theorem selectedSupportGraph_admissible (classOf : V → E → K) (C : Finset E)
    (hadmissible : G.AdmissibleOn classOf C) :
    (G.selectedSupportGraph C).AdmissibleOn (fun v e => classOf v e) univ := by
  intro v k X
  let ψ := Function.Embedding.subtype (fun e => e ∈ C)
  let φ := Function.Embedding.subtype (fun v => v ∈ G.edgeSupport C)
  have hclass :
      ((G.selectedSupportGraph C).classCutOn (fun v e => classOf v e) univ v k X).map ψ =
        G.classCutOn classOf C v k (X.map φ) := by
    simp only [classCutOn]
    rw [← G.selectedSupportGraph_cut C X, filter_map]
    congr 1
    ext e
    simp only [mem_filter, G.selectedSupportGraph_incident]
    rfl
  have hcut := G.selectedSupportGraph_cut C X
  have hh := hadmissible v k (X.map φ)
  rw [← hclass, ← hcut, card_map, card_map] at hh
  exact hh

/-- Actual-copy decomposition when the selected support has at most three vertices. -/
theorem exists_compatibleCircuitPartition_of_support_card_le_three
    (classOf : V → E → K) (C : Finset E)
    (hsize : (G.edgeSupport C).card ≤ 3)
    (hadmissible : G.AdmissibleOn classOf C)
    (heven : ∀ v, Even (G.degreeOn C v)) :
    Nonempty (G.CompatibleCircuitPartition classOf C) := by
  let H := G.selectedSupportGraph C
  let f : G.edgeSupport C → C → K := fun v e => classOf v e
  obtain ⟨P⟩ := H.exists_compatibleCircuitPartition_of_card_le_three
    (by simpa using hsize) f univ (G.selectedSupportGraph_admissible classOf C hadmissible)
    (fun v => by simpa only [G.selectedSupportGraph_degree] using heven v)
  let φ := Function.Embedding.subtype (fun v => v ∈ G.edgeSupport C)
  let ψ := Function.Embedding.subtype (fun e => e ∈ C)
  let J := H.embedVertices φ
  let P' := P.embedVertices H φ
  have hcomp (D : Finset C) (hD : D ∈ P'.parts) :
      J.Compatible (fun v e => classOf v e) D := by
    intro v e he hve e' he' hve' hclasses
    obtain ⟨u, hu, rfl⟩ := (H.embedVertices_incident φ e v).mp hve
    apply P'.compatible D hD (φ u) e he
      ((H.embedVertices_incident_image φ e u).mpr hu) e' he' hve'
    simpa only [embedIncidenceClasses_image, f] using congrArg some hclasses
  let P'' : J.CompatibleCircuitPartition (fun v e => classOf v e) univ := {
    parts := P'.parts
    circuit := P'.circuit
    compatible := hcomp
    disjoint := P'.disjoint
    cover := P'.cover }
  have hmap : univ.map ψ = C := by ext e; simp [ψ]
  exact ⟨hmap ▸ P''.map_copies J G ψ
    (fun e => (G.selectedSupportGraph_embedded_edge C e).symm) classOf⟩

/-- An unused label reduces the four-label problem to the complete three-label theorem. -/
theorem exists_compatibleCircuitPartition_of_four_label_degree_zero
    (Q : Multigraph (Fin 4) E) (classOf : Fin 4 → E → K) (C : Finset E)
    (hadmissible : Q.AdmissibleOn classOf C)
    (heven : ∀ v, Even (Q.degreeOn C v))
    (v : Fin 4) (hzero : Q.degreeOn C v = 0) :
    Nonempty (Q.CompatibleCircuitPartition classOf C) := by
  apply Q.exists_compatibleCircuitPartition_of_support_card_le_three classOf C
    ?_ hadmissible heven
  have hv : v ∉ Q.edgeSupport C := by
    intro hv
    have := (Q.degreeOn_pos_iff C v).mpr hv
    omega
  have hsub : Q.edgeSupport C ⊆ univ.erase v := by
    intro u hu
    exact mem_erase.mpr ⟨fun heq => hv (heq ▸ hu), mem_univ _⟩
  exact (card_le_card hsub).trans (by simp)

end Overfull.Multigraph
