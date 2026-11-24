import Overfull.Compression.SelectedEdges

namespace Overfull.SafePrescription

open Finset Classical SimpleGraph FractionalMatching MatchingProbability
open scoped BigOperators

variable {V I : Type*} [Fintype V]

/-- The host edges whose endpoints are in different unmarked clusters. -/
noncomputable def clusterCrossingEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → I) (Z₀ : Finset V) : Finset G.edgeSet :=
  univ.filter (fun e => firstEnd e ∉ Z₀ ∧ secondEnd e ∉ Z₀ ∧
    c (firstEnd e) ≠ c (secondEnd e))

/-- The host edges that must be fixed during the clusterwise replacement. -/
noncomputable def boundaryEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → I) (Z₀ : Finset V) : Finset G.edgeSet :=
  univ.filter (fun e => firstEnd e ∈ Z₀ ∨ secondEnd e ∈ Z₀ ∨
    c (firstEnd e) ≠ c (secondEnd e))

theorem mem_boundaryEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → I) (Z₀ : Finset V) (e : G.edgeSet) :
    e ∈ boundaryEdges G c Z₀ ↔ firstEnd e ∈ Z₀ ∨ secondEnd e ∈ Z₀ ∨
      c (firstEnd e) ≠ c (secondEnd e) := by
  simp only [boundaryEdges, mem_filter, mem_univ, true_and]

theorem pair_mem_boundaryEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → I) (Z₀ : Finset V) {u v : V} (huv : G.Adj u v) :
    (⟨s(u,v),huv⟩ : G.edgeSet) ∈ boundaryEdges G c Z₀ ↔
      u ∈ Z₀ ∨ v ∈ Z₀ ∨ c u ≠ c v := by
  rw [mem_boundaryEdges]
  have heq := edge_eq (⟨s(u,v),huv⟩ : G.edgeSet)
  rcases Sym2.eq_iff.mp heq with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · simp only [ha,hb]
  · simp only [ha,hb,ne_comm]
    tauto

/-- Counting all incidences at marked vertices gives the boundary-edge bound. -/
theorem boundaryEdges_card_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → I) (Z₀ : Finset V) (h : ℕ) (hregular : ∀ v, G.degree v = h) :
    (boundaryEdges G c Z₀).card ≤ Z₀.card*h + (clusterCrossingEdges G c Z₀).card := by
  classical
  let A : V → Finset G.edgeSet := fun v =>
    univ.filter (fun e => firstEnd e = v ∨ secondEnd e = v)
  have hsub : boundaryEdges G c Z₀ ⊆ Z₀.biUnion A ∪ clusterCrossingEdges G c Z₀ := by
    intro e he
    have he' := (mem_boundaryEdges G c Z₀ e).mp he
    by_cases ha : firstEnd e ∈ Z₀
    · exact mem_union_left _ (mem_biUnion.mpr
        ⟨firstEnd e,ha,mem_filter.mpr ⟨mem_univ _,Or.inl rfl⟩⟩)
    by_cases hb : secondEnd e ∈ Z₀
    · exact mem_union_left _ (mem_biUnion.mpr
        ⟨secondEnd e,hb,mem_filter.mpr ⟨mem_univ _,Or.inr rfl⟩⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _,ha,hb,by tauto⟩)
  calc
    _ ≤ (Z₀.biUnion A ∪ clusterCrossingEdges G c Z₀).card := card_le_card hsub
    _ ≤ (Z₀.biUnion A).card + (clusterCrossingEdges G c Z₀).card := card_union_le _ _
    _ ≤ (∑ v ∈ Z₀, (A v).card) + (clusterCrossingEdges G c Z₀).card :=
      Nat.add_le_add_right card_biUnion_le _
    _ = _ := by simp [A,incident_card,hregular]

theorem boundaryEdges_card_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → I) (Z₀ : Finset V) (h k₀ t₀ : ℕ)
    (hregular : ∀ v, G.degree v = h) (hh : h ≤ k₀) (hZ : Z₀.card ≤ t₀)
    (hcross : (clusterCrossingEdges G c Z₀).card ≤ 6*k₀) :
    (boundaryEdges G c Z₀).card ≤ (t₀+6)*k₀ := by
  have hbound := boundaryEdges_card_le G c Z₀ h hregular
  have hmul := Nat.mul_le_mul hZ hh
  nlinarith

/-- Select precisely the sampled matching edges that belong to the boundary. -/
theorem exists_boundary_submatching (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → I) (Z₀ : Finset V) (K : G.Subgraph) (hK : K.IsMatching) :
    ∃ B : G.Subgraph, B.IsMatching ∧ B ≤ K ∧
      matchingEdges B = (boundaryEdges G c Z₀).filter (fun e => e.val ∈ K.edgeSet) ∧
      B.edgeSet.ncard = ((boundaryEdges G c Z₀).filter (fun e => e.val ∈ K.edgeSet)).card ∧
      B.verts.ncard = 2*B.edgeSet.ncard ∧
      (∀ u v, B.Adj u v ↔ K.Adj u v ∧ (u ∈ Z₀ ∨ v ∈ Z₀ ∨ c u ≠ c v)) := by
  classical
  let A := (boundaryEdges G c Z₀).filter (fun e => e.val ∈ K.edgeSet)
  have hA : A ⊆ matchingEdges K := by
    intro e he
    exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp he).2⟩
  obtain ⟨B,hB,hBK,hBE,hBcard,hBverts,_⟩ :=
    Compression.exists_selected_matching G K hK A hA
  refine ⟨B,hB,hBK,hBE,hBcard,by omega,?_⟩
  intro u v
  constructor
  · intro huv
    have hKuv := hBK.2 huv
    let e : G.edgeSet := ⟨s(u,v),K.adj_sub hKuv⟩
    have heB : e ∈ matchingEdges B := by
      simpa only [matchingEdges,mem_filter,mem_univ,true_and] using huv
    have heA : e ∈ A := hBE ▸ heB
    exact ⟨hKuv,(pair_mem_boundaryEdges G c Z₀ (K.adj_sub hKuv)).mp
      (mem_filter.mp heA).1⟩
  · rintro ⟨huv,hboundary⟩
    let e : G.edgeSet := ⟨s(u,v),K.adj_sub huv⟩
    have heA : e ∈ A := mem_filter.mpr
      ⟨(pair_mem_boundaryEdges G c Z₀ (K.adj_sub huv)).mpr hboundary,huv⟩
    have heB : e ∈ matchingEdges B := hBE.symm ▸ heA
    simpa only [matchingEdges,mem_filter,mem_univ,true_and] using heB


end Overfull.SafePrescription
