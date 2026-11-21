import Overfull.MatchingProbability
import Overfull.BipartitePackingAccounting
import Overfull.MatchingExtension

/-!
# The actual submatching selected by a finite set of edges

The selected graph has exactly the incident vertices and exactly the
chosen host edges. All incidence and cardinality identities therefore
refer to the actual matching used by compression.
-/

namespace Overfull.Compression

open Finset Classical SimpleGraph FractionalMatching MatchingProbability
open scoped BigOperators

variable {V : Type*}

def selectedMatching (G : SimpleGraph V) (A : Finset G.edgeSet) : G.Subgraph where
  verts := {v | ∃ w, ∃ h : G.Adj v w, (⟨s(v,w),h⟩ : G.edgeSet) ∈ A}
  Adj v w := ∃ h : G.Adj v w, (⟨s(v,w),h⟩ : G.edgeSet) ∈ A
  adj_sub := fun h => h.choose
  edge_vert := fun ⟨h,ha⟩ => ⟨_,h,ha⟩
  symm := by
    rintro v w ⟨h,ha⟩
    refine ⟨h.symm,?_⟩
    have heq : (⟨s(w,v),h.symm⟩ : G.edgeSet) = ⟨s(v,w),h⟩ :=
      Subtype.ext Sym2.eq_swap
    rw [heq]
    exact ha

theorem selectedMatching_mem_edge (G : SimpleGraph V) (A : Finset G.edgeSet)
    (e : G.edgeSet) : e.val ∈ (selectedMatching G A).edgeSet ↔ e ∈ A := by
  obtain ⟨⟨v,w⟩,he⟩ := e
  change (∃ h : G.Adj v w, (⟨s(v,w),h⟩ : G.edgeSet) ∈ A) ↔
    (⟨s(v,w),he⟩ : G.edgeSet) ∈ A
  exact ⟨fun ⟨_,ha⟩ => ha,fun ha => ⟨he,ha⟩⟩

theorem selectedMatching_mem_verts (G : SimpleGraph V) (A : Finset G.edgeSet)
    (v : V) : v ∈ (selectedMatching G A).verts ↔ ∃ e ∈ A, v ∈ e.val := by
  constructor
  · rintro ⟨w,h,ha⟩
    exact ⟨⟨s(v,w),h⟩,ha,by simp⟩
  · rintro ⟨⟨⟨x,y⟩,hxy⟩,ha,hv⟩
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · exact ⟨y,hxy,ha⟩
    · refine ⟨x,hxy.symm,?_⟩
      have heq : (⟨s(v,x),hxy.symm⟩ : G.edgeSet) = ⟨s(x,v),hxy⟩ :=
        Subtype.ext Sym2.eq_swap
      rw [heq]
      exact ha

theorem selectedMatching_edgeSet_card (G : SimpleGraph V) (A : Finset G.edgeSet) :
    (selectedMatching G A).edgeSet.ncard = A.card := by
  have heq : Subtype.val '' (A : Set G.edgeSet) = (selectedMatching G A).edgeSet := by
    ext e
    constructor
    · intro he
      obtain ⟨f,hf,rfl⟩ := he
      exact (selectedMatching_mem_edge G A f).mpr hf
    · intro he
      let f : G.edgeSet := ⟨e,(selectedMatching G A).edgeSet_subset he⟩
      exact ⟨f,(selectedMatching_mem_edge G A f).mp he,rfl⟩
  rw [← heq,Set.ncard_image_of_injective _ Subtype.val_injective,Set.ncard_coe_finset]

variable [Fintype V]

theorem selectedMatching_edges (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset G.edgeSet) :
    matchingEdges (selectedMatching G A) = A := by
  ext e
  simp only [matchingEdges,Finset.mem_filter,Finset.mem_univ,true_and,
    selectedMatching_mem_edge]

theorem selectedMatching_le (G : SimpleGraph V) [DecidableRel G.Adj] (M : G.Subgraph)
    (A : Finset G.edgeSet) (hA : A ⊆ matchingEdges M) : selectedMatching G A ≤ M := by
  have hadj {v w : V} (h : (selectedMatching G A).Adj v w) : M.Adj v w := by
    obtain ⟨h,ha⟩ := h
    have he := hA ha
    simpa only [matchingEdges,Finset.mem_filter,Finset.mem_univ,true_and,
      Subgraph.mem_edgeSet] using he
  exact ⟨fun _ ⟨w,h,ha⟩ => M.edge_vert (hadj ⟨h,ha⟩),fun _ _ h => hadj h⟩

theorem selectedMatching_isMatching (G : SimpleGraph V) [DecidableRel G.Adj] (M : G.Subgraph)
    (hM : M.IsMatching) (A : Finset G.edgeSet) (hA : A ⊆ matchingEdges M) :
    (selectedMatching G A).IsMatching := by
  have hle := selectedMatching_le G M A hA
  rintro v ⟨w,h,ha⟩
  have hvw : (selectedMatching G A).Adj v w := ⟨h,ha⟩
  refine ⟨w,hvw,?_⟩
  intro z hz
  exact hM.eq_of_adj_left (hle.2 hz) (hle.2 hvw)

theorem incidentCount_matchingEdges_degree (G : SimpleGraph V) [DecidableRel G.Adj] (M : G.Subgraph)
    (v : V) : incidentCount (matchingEdges M) v = M.spanningCoe.degree v := by
  let A := (matchingEdges M).filter (fun e => firstEnd e = v ∨ secondEnd e = v)
  have heq : A.image Subtype.val = M.spanningCoe.incidenceFinset v := by
    ext e
    constructor
    · intro he
      obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp he
      rcases Finset.mem_filter.mp hf with ⟨hm,hv⟩
      have hm' : f.val ∈ M.edgeSet := by simpa only [matchingEdges,
        Finset.mem_filter,Finset.mem_univ,true_and] using hm
      exact (M.spanningCoe.mem_incidenceFinset v f.val).mpr
        ⟨hm',(incident_iff f v).mpr hv⟩
    · intro he
      obtain ⟨hm,hv⟩ := (M.spanningCoe.mem_incidenceFinset v e).mp he
      let f : G.edgeSet := ⟨e,M.edgeSet_subset hm⟩
      refine Finset.mem_image.mpr ⟨f,?_,rfl⟩
      apply Finset.mem_filter.mpr
      refine ⟨?_,(incident_iff f v).mp hv⟩
      simpa only [matchingEdges,Finset.mem_filter,Finset.mem_univ,true_and] using hm
  calc
    incidentCount (matchingEdges M) v = A.card := rfl
    _ = (A.image Subtype.val).card := (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ = _ := by rw [heq,SimpleGraph.card_incidenceFinset_eq_degree]

theorem selectedMatching_incidentCount (G : SimpleGraph V) [DecidableRel G.Adj] (M : G.Subgraph)
    (hM : M.IsMatching) (A : Finset G.edgeSet) (hA : A ⊆ matchingEdges M) (v : V) :
    incidentCount A v = if v ∈ (selectedMatching G A).verts then 1 else 0 := by
  calc
    incidentCount A v = incidentCount (matchingEdges (selectedMatching G A)) v :=
      congrArg (fun B => incidentCount B v) (selectedMatching_edges G A).symm
    _ = (selectedMatching G A).spanningCoe.degree v :=
      incidentCount_matchingEdges_degree G (selectedMatching G A) v
    _ = _ := BipartitePackingAccounting.matching_degree G (selectedMatching G A)
      (selectedMatching_isMatching G M hM A hA) v

theorem selectedMatching_covered_count [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (M : G.Subgraph) (hM : M.IsMatching)
    (A : Finset G.edgeSet) (hA : A ⊆ matchingEdges M) (X : Finset V) :
    ((selectedMatching G A).verts.toFinset ∩ X).card = ∑ v ∈ X, incidentCount A v := by
  simp_rw [selectedMatching_incidentCount G M hM A hA]
  rw [Finset.sum_boole]
  congr 1
  ext v
  simp only [Finset.mem_inter,Set.mem_toFinset,Finset.mem_filter]
  tauto

theorem selectedMatching_verts_card (G : SimpleGraph V) [DecidableRel G.Adj] (M : G.Subgraph)
    (hM : M.IsMatching) (A : Finset G.edgeSet) (hA : A ⊆ matchingEdges M) :
    (selectedMatching G A).verts.ncard = 2*A.card := by
  have hh := selectedMatching_covered_count G M hM A hA univ
  rw [Finset.inter_univ] at hh
  rw [Set.ncard_eq_toFinset_card']
  exact hh.trans (total_incidence A)

theorem covered_count_of_incident [DecidableEq V] (G : SimpleGraph V)
    (F : G.Subgraph) (A : Finset G.edgeSet)
    (hinc : ∀ v, incidentCount A v = if v ∈ F.verts then 1 else 0) (X : Finset V) :
    (F.verts.toFinset ∩ X).card = ∑ v ∈ X, incidentCount A v := by
  simp_rw [hinc]
  rw [Finset.sum_boole]
  congr 1
  ext v
  simp only [Finset.mem_inter,Set.mem_toFinset,Finset.mem_filter]
  tauto

theorem selected_edges_card_le_of_incident (G : SimpleGraph V) [DecidableRel G.Adj] (M : G.Subgraph)
    (hM : M.IsMatching) (A : Finset G.edgeSet) (hA : A ⊆ matchingEdges M)
    (Z : Finset V) (hZ : ∀ e ∈ A, ∃ v ∈ Z, v ∈ e.val) : A.card ≤ Z.card := by
  have htouch (e : A) : ∃ v : Z, v.val ∈ e.val.val := by
    obtain ⟨v,hv,hve⟩ := hZ e.val e.property
    exact ⟨⟨v,hv⟩,hve⟩
  choose pick hpick using htouch
  have hinj : Function.Injective pick := by
    intro e f hef
    have hv : (pick e).val = (pick f).val := congrArg Subtype.val hef
    have heM : e.val.val ∈ M.edgeSet := by
      simpa only [matchingEdges,Finset.mem_filter,Finset.mem_univ,true_and] using hA e.property
    have hfM : f.val.val ∈ M.edgeSet := by
      simpa only [matchingEdges,Finset.mem_filter,Finset.mem_univ,true_and] using hA f.property
    have hh := MatchingExtension.matching_edge_eq G hM
      ⟨e.val.val,heM⟩ ⟨f.val.val,hfM⟩ (hpick e) (hv.symm ▸ hpick f)
    exact Subtype.ext (Subtype.ext (congrArg (fun q : M.edgeSet => q.val) hh))
  have hh := Nat.card_le_card_of_injective pick hinj
  simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using hh

theorem selected_edges_card_le_of_endpoint (G : SimpleGraph V) [DecidableRel G.Adj] (M : G.Subgraph)
    (hM : M.IsMatching) (A : Finset G.edgeSet) (hA : A ⊆ matchingEdges M)
    (Z : Finset V) (hZ : ∀ e ∈ A, firstEnd e ∈ Z ∨ secondEnd e ∈ Z) :
    A.card ≤ Z.card := by
  apply selected_edges_card_le_of_incident G M hM A hA Z
  intro e he
  rcases hZ e he with h | h
  · exact ⟨firstEnd e,h,(incident_iff e _).mpr (Or.inl rfl)⟩
  · exact ⟨secondEnd e,h,(incident_iff e _).mpr (Or.inr rfl)⟩

/-- The actual submatching with exactly the selected edges and endpoints. -/
theorem exists_selected_matching (G : SimpleGraph V) [DecidableRel G.Adj] (M : G.Subgraph)
    (hM : M.IsMatching) (A : Finset G.edgeSet) (hA : A ⊆ matchingEdges M) :
    ∃ F : G.Subgraph, F.IsMatching ∧ F ≤ M ∧ matchingEdges F = A ∧
      F.edgeSet.ncard = A.card ∧ F.verts.ncard = 2*A.card ∧
      (∀ v, incidentCount A v = if v ∈ F.verts then 1 else 0) := by
  exact ⟨selectedMatching G A,selectedMatching_isMatching G M hM A hA,
    selectedMatching_le G M A hA,selectedMatching_edges G A,
    selectedMatching_edgeSet_card G A,selectedMatching_verts_card G M hM A hA,
    selectedMatching_incidentCount G M hM A hA⟩

end Overfull.Compression
