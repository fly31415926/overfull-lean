import Overfull.CompatibleCircuits.FourDegreeTwoParallel

/-! Exact local transport and disjoint reassembly for degree-two suppression. -/

noncomputable section

namespace Overfull.Multigraph

open Finset Classical

variable {V E K : Type*} (G H : Multigraph V E)

theorem edgeSupport_congrOn {C : Finset E} (hedge : ∀ e ∈ C, G.edge e = H.edge e) :
    G.edgeSupport C = H.edgeSupport C := by
  ext v
  simp only [mem_edgeSupport]
  constructor
  · rintro ⟨e,he,hv⟩
    exact ⟨e,he,hedge e he ▸ hv⟩
  · rintro ⟨e,he,hv⟩
    exact ⟨e,he,(hedge e he).symm ▸ hv⟩

theorem degreeOn_congrOn {C : Finset E} (hedge : ∀ e ∈ C, G.edge e = H.edge e)
    (v : V) : G.degreeOn C v = H.degreeOn C v := by
  unfold degreeOn
  congr 1
  apply filter_congr
  intro e he
  rw [hedge e he]

theorem cutOn_congrOn {C : Finset E} (hedge : ∀ e ∈ C, G.edge e = H.edge e)
    (X : Finset V) : G.cutOn C X = H.cutOn C X := by
  ext e
  by_cases he : e ∈ C
  · rw [G.mem_cutOn_of_edge_eq ((hedge e he).trans (H.edge_eq e).symm),mem_cutOn]
  · simp only [mem_cutOn,he,false_and]

theorem IsCircuit.congrOn {C : Finset E} (hC : G.IsCircuit C)
    (hedge : ∀ e ∈ C, G.edge e = H.edge e) : H.IsCircuit C := by
  refine ⟨hC.1,?_,?_⟩
  · intro v hv
    rw [← G.degreeOn_congrOn H hedge]
    exact hC.2.1 v (by simpa only [G.edgeSupport_congrOn H hedge] using hv)
  · intro X hX hne hproper
    rw [← G.cutOn_congrOn H hedge]
    exact hC.2.2 X (by simpa only [G.edgeSupport_congrOn H hedge] using hX)
      hne (by simpa only [G.edgeSupport_congrOn H hedge] using hproper)

def CompatibleCircuitPartition.congrOn
    {C : Finset E} {classOf classOf' : V → E → K}
    (P : G.CompatibleCircuitPartition classOf C)
    (hedge : ∀ e ∈ C, G.edge e = H.edge e)
    (hclass : ∀ v e, e ∈ C → classOf v e = classOf' v e) :
    H.CompatibleCircuitPartition classOf' C where
  parts := P.parts
  circuit D hD := (P.circuit D hD).congrOn G H
    (fun e he => hedge e (P.part_subset G hD he))
  compatible := by
    intro D hD v e he hve f hf hvf hclasses
    apply P.compatible D hD v e he
      ((hedge e (P.part_subset G hD he)).symm ▸ hve) f hf
      ((hedge f (P.part_subset G hD hf)).symm ▸ hvf)
    rw [hclass v e (P.part_subset G hD he),hclass v f (P.part_subset G hD hf)]
    exact hclasses
  disjoint := P.disjoint
  cover := P.cover

/-- Combine two disjoint actual-copy circuit partitions. -/
def CompatibleCircuitPartition.union
    {C D : Finset E} {classOf : V → E → K}
    (P : G.CompatibleCircuitPartition classOf C)
    (R : G.CompatibleCircuitPartition classOf D) (hCD : Disjoint C D) :
    G.CompatibleCircuitPartition classOf (C ∪ D) where
  parts := P.parts ∪ R.parts
  circuit := by
    intro A hA
    exact (mem_union.mp hA).elim (P.circuit A) (R.circuit A)
  compatible := by
    intro A hA
    exact (mem_union.mp hA).elim (P.compatible A) (R.compatible A)
  disjoint := by
    intro A hA B hB hne
    rcases mem_union.mp hA with hA | hA <;> rcases mem_union.mp hB with hB | hB
    · exact P.disjoint A hA B hB hne
    · exact hCD.mono (P.part_subset G hA) (R.part_subset G hB)
    · exact hCD.symm.mono (R.part_subset G hA) (P.part_subset G hB)
    · exact R.disjoint A hA B hB hne
  cover := by
    calc
      _ = P.parts.biUnion id ∪ R.parts.biUnion id := by
        ext e
        simp only [mem_biUnion,mem_union,or_and_right,exists_or]
      _ = C ∪ D := congrArg₂ (fun A B : Finset E => A ∪ B) P.cover R.cover

end Overfull.Multigraph
