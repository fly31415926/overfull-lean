import Overfull.TerminalFourTwoOdd.CentralGeometry
import Overfull.TerminalFourTwoOdd.CutCertificates

/-! The central matchings preserve even-core uncovered parity and both apex incidences. -/

noncomputable section

namespace Overfull.TerminalFourTwoOdd

open Finset Classical Multigraph SmallCuts Terminal

variable {V E : Type*} [Fintype E]

theorem centralMatching_disjoint (G : Multigraph V E) (S A : Finset V)
    (M N : Finset E) (hMN : Disjoint M N) :
    Disjoint (centralMatching G S A M) (centralMatching G S A N) := by
  apply disjoint_left.mpr
  intro e he hf
  exact disjoint_left.mp hMN
    ((mem_centralMatching G S A M e).mp he) ((mem_centralMatching G S A N e).mp hf)

theorem centralMatching_support_core (G : Multigraph V E) (S A : Finset V)
    (M : Finset E) (v : V) (hv : v ∈ S) :
    centralMap S A v ∈ (centralGraph G S A).edgeSupport (centralMatching G S A M) ↔
      v ∈ G.edgeSupport M := by
  rw [show centralMap S A v = Sum.inl (⟨v,hv⟩ : S) from centralMap_core S A ⟨v,hv⟩]
  constructor
  · intro h
    obtain ⟨e, he, hi⟩ := ((centralGraph G S A).mem_edgeSupport _ _).mp h
    exact (G.mem_edgeSupport M v).mpr ⟨e.val,
      (mem_centralMatching G S A M e).mp he,
      (central_incident_inl_iff G S A e ⟨v,hv⟩).mp hi⟩
  · intro h
    obtain ⟨e, he, hi⟩ := (G.mem_edgeSupport M v).mp h
    let f : CentralEdge G S A := ⟨e,central_retained_of_core_incident G S A hv hi⟩
    exact ((centralGraph G S A).mem_edgeSupport _ _).mpr ⟨f,
      (mem_centralMatching G S A M f).mpr he,
      (central_incident_inl_iff G S A f ⟨v,hv⟩).mpr hi⟩

theorem centralMatching_uncovered_card (G : Multigraph V E) (S W A : Finset V)
    (hWS : W ⊆ S) (M : Finset E) :
    (keptSet hWS \ (centralGraph G S A).edgeSupport (centralMatching G S A M)).card =
      (W \ G.edgeSupport M).card := by
  symm
  apply card_bij (fun v _ => centralMap S A v)
  · intro v hv
    obtain ⟨hw,hn⟩ := mem_sdiff.mp hv
    exact mem_sdiff.mpr ⟨(centralMap_mem_keptSet hWS A v).mpr hw,
      fun hc => hn ((centralMatching_support_core G S A M v (hWS hw)).mp hc)⟩
  · intro u hu v _ huv
    exact centralMap_injective_at_core S A (hWS (mem_sdiff.mp hu).1) huv
  · intro v hv
    obtain ⟨hvW,hvn⟩ := mem_sdiff.mp hv
    obtain ⟨w,_,rfl⟩ := mem_image.mp hvW
    refine ⟨w.val,mem_sdiff.mpr ⟨w.property,?_⟩,?_⟩
    · intro hw
      apply hvn
      have hh := (centralMatching_support_core G S A M w.val (hWS w.property)).mpr hw
      have heq : centralMap S A w.val = keptVertex hWS w :=
        centralMap_core S A ⟨w.val,hWS w.property⟩
      exact heq ▸ hh
    · exact centralMap_core S A ⟨w.val,hWS w.property⟩

theorem centralMatching_covers_apex (G : Multigraph V E) (S A X : Finset V)
    (z : CentralVertex S) (hfiber : ∀ v, centralMap S A v = z ↔ v ∈ X)
    (M : Finset E) (hcut : (M ∩ G.cutEdges X).card = 1) :
    z ∈ (centralGraph G S A).edgeSupport (centralMatching G S A M) := by
  obtain ⟨e,he⟩ := card_pos.mp (show 0 < (M ∩ G.cutEdges X).card by omega)
  let f := centralBoundaryLift G S A X z hfiber ⟨e,(mem_inter.mp he).2⟩
  exact ((centralGraph G S A).mem_edgeSupport _ _).mpr ⟨f,
    (mem_centralMatching G S A M f).mpr (mem_inter.mp he).1,
    (central_incident_fiber_iff G S A X z hfiber f).mpr (mem_inter.mp he).2⟩

theorem central_internal_kept_of_original (G : Multigraph V E) (S W A : Finset V)
    (hWS : W ⊆ S) (e : CentralEdge G S A) (he : e.val ∈ G.internalEdges W) :
    e ∈ (centralGraph G S A).internalEdges (keptSet hWS) := by
  have hvertices (v : CentralVertex S) (hv : v ∈ (centralGraph G S A).edge e) :
      v ∈ keptSet hWS := by
    rw [centralGraph_edge,Sym2.mem_map] at hv
    obtain ⟨w,hw,rfl⟩ := hv
    apply (centralMap_mem_keptSet hWS A w).mpr
    have he' := (G.mem_internalEdges W e.val).mp he
    rcases (G.incident_iff e.val w).mp hw with h | h
    · exact h ▸ he'.1
    · exact h ▸ he'.2
  apply ((centralGraph G S A).mem_internalEdges (keptSet hWS) e).mpr
  exact ⟨hvertices _ (((centralGraph G S A).incident_iff e _).mpr (Or.inl rfl)),
    hvertices _ (((centralGraph G S A).incident_iff e _).mpr (Or.inr rfl))⟩

theorem central_not_internal_fiber (G : Multigraph V E) (S A X : Finset V)
    (z : CentralVertex S) (hfiber : ∀ v, centralMap S A v = z ↔ v ∈ X)
    (e : CentralEdge G S A) : e.val ∉ G.internalEdges X := by
  intro he
  have he' := (G.mem_internalEdges X e.val).mp he
  exact e.property (((hfiber _).mpr he'.1).trans ((hfiber _).mpr he'.2).symm)

/-- No even-to-even joining copy is discarded in the central cover. -/
theorem centralMatching_two_core_cover (G : Multigraph V E) (U W A B : Finset V)
    (hSA : Disjoint (U ∪ W) A) (hSB : Disjoint (U ∪ W) B) (hAB : Disjoint A B)
    (hcover : ∀ v, v ∈ U ∪ W ∨ v ∈ A ∨ v ∈ B)
    (k : ℕ) (M : Fin k → Finset E)
    (hM : ∀ e, e ∉ G.internalEdges U → e ∉ G.internalEdges W →
      e ∉ G.internalEdges A → e ∉ G.internalEdges B → ∃ j, e ∈ M j) :
    ∀ e : CentralEdge G (U ∪ W) A,
      e ∉ (centralGraph G (U ∪ W) A).internalEdges (keptSet (subset_union_left : U ⊆ U ∪ W)) →
      e ∉ (centralGraph G (U ∪ W) A).internalEdges (keptSet (subset_union_right : W ⊆ U ∪ W)) →
      ∃ j, e ∈ centralMatching G (U ∪ W) A (M j) := by
  intro e heU heW
  obtain ⟨j,hj⟩ := hM e.val
    (fun h => heU (central_internal_kept_of_original G (U ∪ W) U A subset_union_left e h))
    (fun h => heW (central_internal_kept_of_original G (U ∪ W) W A subset_union_right e h))
    (central_not_internal_fiber G (U ∪ W) A A (Sum.inr 0)
      (centralMap_eq_first_apex_iff (U ∪ W) A hSA) e)
    (central_not_internal_fiber G (U ∪ W) A B (Sum.inr 1)
      (centralMap_eq_second_apex_iff (U ∪ W) A B hSB hAB hcover) e)
  exact ⟨j,(mem_centralMatching G (U ∪ W) A (M j) e).mpr hj⟩

end Overfull.TerminalFourTwoOdd
