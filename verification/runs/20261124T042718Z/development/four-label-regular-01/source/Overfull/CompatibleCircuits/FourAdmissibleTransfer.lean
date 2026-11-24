import Overfull.CompatibleCircuits.AtMostThree

/-! Copy embeddings transport compatible partitions without identifying parallel copies. -/

namespace Overfull.Multigraph

open Finset Classical

variable {V E F K : Type*} (G : Multigraph V E) (H : Multigraph V F)
  (ψ : E ↪ F) (hedge : ∀ e, H.edge (ψ e) = G.edge e)

include hedge

theorem copyEmbedding_support (C : Finset E) :
    H.edgeSupport (C.map ψ) = G.edgeSupport C := by
  ext v
  simp only [mem_edgeSupport, mem_map]
  constructor
  · rintro ⟨_, ⟨e, he, rfl⟩, hv⟩
    exact ⟨e, he, by simpa only [hedge] using hv⟩
  · rintro ⟨e, he, hv⟩
    exact ⟨ψ e, ⟨e, he, rfl⟩, by simpa only [hedge] using hv⟩

theorem copyEmbedding_degree (C : Finset E) (v : V) :
    H.degreeOn (C.map ψ) v = G.degreeOn C v := by
  simp only [degreeOn, filter_map, Function.comp_def, hedge, card_map]

theorem copyEmbedding_crosses (e : E) (X : Finset V) :
    ((H.firstEnd (ψ e) ∈ X) ≠ (H.secondEnd (ψ e) ∈ X)) ↔
      ((G.firstEnd e ∈ X) ≠ (G.secondEnd e ∈ X)) := by
  have h : s(H.firstEnd (ψ e), H.secondEnd (ψ e)) =
      s(G.firstEnd e, G.secondEnd e) := by
    rw [H.edge_eq, G.edge_eq, hedge]
  rcases Sym2.eq_iff.mp h with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · simp only [ha,hb]
  · simp only [ha,hb,ne_eq,eq_iff_iff]
    tauto

theorem copyEmbedding_cut (C : Finset E) (X : Finset V) :
    H.cutOn (C.map ψ) X = (G.cutOn C X).map ψ := by
  ext f
  simp only [mem_cutOn, mem_map]
  constructor
  · rintro ⟨⟨e,he,rfl⟩,hx⟩
    exact ⟨e,⟨he,(copyEmbedding_crosses G H ψ hedge e X).mp hx⟩,rfl⟩
  · rintro ⟨e,⟨he,hx⟩,rfl⟩
    exact ⟨⟨e,he,rfl⟩,(copyEmbedding_crosses G H ψ hedge e X).mpr hx⟩

theorem IsCircuit.map_copies {C : Finset E} (hC : G.IsCircuit C) :
    H.IsCircuit (C.map ψ) := by
  refine ⟨hC.1.map, ?_, ?_⟩
  · intro v hv
    rw [copyEmbedding_degree G H ψ hedge]
    exact hC.2.1 v (by simpa only [copyEmbedding_support G H ψ hedge] using hv)
  · intro X hX hne hproper
    rw [copyEmbedding_cut G H ψ hedge]
    apply Finset.Nonempty.map
    apply hC.2.2 X
    · simpa only [copyEmbedding_support G H ψ hedge] using hX
    · exact hne
    · simpa only [copyEmbedding_support G H ψ hedge] using hproper

theorem Compatible.map_copies (classOf : V → F → K) {C : Finset E}
    (hC : G.Compatible (fun v e => classOf v (ψ e)) C) :
    H.Compatible classOf (C.map ψ) := by
  intro v f hf hvf f' hf' hvf' hclass
  obtain ⟨e,he,rfl⟩ := mem_map.mp hf
  obtain ⟨e',he',rfl⟩ := mem_map.mp hf'
  exact congrArg ψ (hC v e he (by simpa only [hedge] using hvf)
    e' he' (by simpa only [hedge] using hvf') hclass)

/-- A copy embedding sends every part and its exact union to the original copies. -/
noncomputable def CompatibleCircuitPartition.map_copies (classOf : V → F → K)
    {C : Finset E} (P : G.CompatibleCircuitPartition (fun v e => classOf v (ψ e)) C) :
    H.CompatibleCircuitPartition classOf (C.map ψ) where
  parts := P.parts.image (Finset.map ψ)
  circuit := by
    intro D hD
    obtain ⟨A,hA,rfl⟩ := mem_image.mp hD
    exact (P.circuit A hA).map_copies G H ψ hedge
  compatible := by
    intro D hD
    obtain ⟨A,hA,rfl⟩ := mem_image.mp hD
    exact (P.compatible A hA).map_copies G H ψ hedge classOf
  disjoint := by
    intro D hD D' hD' hne
    obtain ⟨A,hA,rfl⟩ := mem_image.mp hD
    obtain ⟨A',hA',rfl⟩ := mem_image.mp hD'
    exact (Finset.disjoint_map ψ).mpr (P.disjoint A hA A' hA' (by
      intro h; exact hne (congrArg (Finset.map ψ) h)))
  cover := by
    calc
      _ = (P.parts.biUnion id).map ψ := by
        ext f
        simp only [mem_biUnion,mem_image,id_eq]
        constructor
        · rintro ⟨D,⟨A,hA,rfl⟩,hf⟩
          obtain ⟨e,he,rfl⟩ := mem_map.mp hf
          exact mem_map.mpr ⟨e,mem_biUnion.mpr ⟨A,hA,he⟩,rfl⟩
        · intro hf
          obtain ⟨e,he,rfl⟩ := mem_map.mp hf
          obtain ⟨A,hA,he⟩ := mem_biUnion.mp he
          exact ⟨A.map ψ,⟨A,hA,rfl⟩,mem_map.mpr ⟨e,he,rfl⟩⟩
      _ = _ := congrArg (Finset.map ψ) P.cover

end Overfull.Multigraph
