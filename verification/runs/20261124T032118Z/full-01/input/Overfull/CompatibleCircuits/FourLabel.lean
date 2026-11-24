import Overfull.CompatibleCircuits.Counting
import Overfull.Compression.Parity

/-!
# Ordinary circuit decomposition on four labels

An even-degree edge-copy graph on four labels can be decomposed by
successively removing parallel pairs.  The remaining simple even graph,
if nonempty, is one triangle or one four-cycle.  The latter finite
classification is checked by kernel reduction over the six label pairs.

This gives ordinary circuit decomposition, and compatible decomposition
when the whole selected edge set is already compatible.  It does not
prove that the half-cut inequalities suffice for arbitrary classes.
-/

namespace Overfull.CompatibleCircuits

open Finset Compression

def labelSupport (P : Finset LabelPair) : Finset (Fin 4) :=
  P.biUnion Subtype.val

def IsLabelCircuit (P : Finset LabelPair) : Prop :=
  P.Nonempty ∧
  (∀ i ∈ labelSupport P, pairDegree P i = 2) ∧
  ∀ X : Finset (Fin 4), X ⊆ labelSupport P → X.Nonempty →
    X ≠ labelSupport P → ∃ p ∈ P, (p.val ∩ X).card = 1

instance (P : Finset LabelPair) : Decidable (IsLabelCircuit P) := by
  unfold IsLabelCircuit
  infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- A nonempty simple even graph on four labels is a single circuit. -/
theorem simple_even_isLabelCircuit :
    ∀ P : Finset LabelPair, P.Nonempty →
      (∀ i : Fin 4, pairDegree P i % 2 = 0) → IsLabelCircuit P := by
  decide

end Overfull.CompatibleCircuits

namespace Overfull.Multigraph

open Finset Classical Compression CompatibleCircuits

variable {V E K : Type*} (G : Multigraph V E)

theorem CompatibleCircuitPartition.part_subset {classOf : V → E → K}
    {C D : Finset E} (P : G.CompatibleCircuitPartition classOf C)
    (hD : D ∈ P.parts) : D ⊆ C := by
  rw [← P.cover]
  exact Finset.subset_biUnion_of_mem id hD

/-- Two distinct parallel copies form a genuine circuit. -/
theorem isCircuit_parallel_pair {e f : E} (hne : e ≠ f)
    (hparallel : G.edge e = G.edge f) : G.IsCircuit {e, f} := by
  have hs : G.edgeSupport {e, f} = (G.edge e).toFinset := by
    ext v
    simp [mem_edgeSupport, ← hparallel]
  refine ⟨by simp, ?_, ?_⟩
  · intro v hv
    have hve : v ∈ G.edge e := by simpa [hs] using hv
    simp [degreeOn, Finset.filter_insert, Finset.filter_singleton, ← hparallel, hve, hne]
  · intro X hX hnonempty hproper
    refine ⟨e, (G.mem_cutOn {e, f} X e).mpr ⟨by simp, ?_⟩⟩
    intro hsame
    by_cases hu : G.firstEnd e ∈ X
    · have hv : G.secondEnd e ∈ X := hsame.mp hu
      apply hproper
      apply Finset.Subset.antisymm hX
      intro w hw
      have hwe : w ∈ G.edge e := by simpa [hs] using hw
      rcases (G.incident_iff e w).mp hwe with rfl | rfl
      · exact hu
      · exact hv
    · have hv : G.secondEnd e ∉ X := fun h => hu (hsame.mpr h)
      obtain ⟨w, hw⟩ := hnonempty
      have hwe : w ∈ G.edge e := by simpa [hs] using hX hw
      rcases (G.incident_iff e w).mp hwe with rfl | rfl
      · exact hu hw
      · exact hv hw

/-- Deleting an even-degree subgraph preserves even degrees. -/
theorem even_degreeOn_sdiff {C D : Finset E} (hDC : D ⊆ C)
    (hC : ∀ v, Even (G.degreeOn C v)) (hD : ∀ v, Even (G.degreeOn D v)) :
    ∀ v, Even (G.degreeOn (C \ D) v) := by
  intro v
  have hsplit : G.degreeOn (C \ D) v + G.degreeOn D v = G.degreeOn C v := by
    have hfilter : (C \ D).filter (fun e => v ∈ G.edge e) =
        (C.filter (fun e => v ∈ G.edge e)) \ (D.filter (fun e => v ∈ G.edge e)) := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_sdiff]
      tauto
    unfold degreeOn
    rw [hfilter]
    exact Finset.card_sdiff_add_card_eq_card (Finset.filter_subset_filter _ hDC)
  have hc := Nat.even_iff.mp (hC v)
  have hd := Nat.even_iff.mp (hD v)
  exact Nat.even_iff.mpr (by omega)

variable (Q : Multigraph (Fin 4) E)

/-- The projected unordered pair of one actual edge copy. -/
noncomputable def edgeLabelPair (e : E) : LabelPair :=
  ⟨(Q.edge e).toFinset, Sym2.card_toFinset_of_not_isDiag _ (Q.loopless e)⟩

@[simp] theorem mem_edgeLabelPair (e : E) (i : Fin 4) :
    i ∈ (Q.edgeLabelPair e).val ↔ i ∈ Q.edge e :=
  Sym2.mem_toFinset

theorem edgeLabelPair_eq_iff (e f : E) :
    Q.edgeLabelPair e = Q.edgeLabelPair f ↔ Q.edge e = Q.edge f := by
  constructor
  · intro h
    apply Sym2.ext
    intro i
    have hi := congrArg (fun p : LabelPair => i ∈ p.val) h
    simpa using hi
  · intro h
    apply Subtype.ext
    exact congrArg Sym2.toFinset h

theorem edgeLabelPair_support (C : Finset E) :
    labelSupport (C.image Q.edgeLabelPair) = Q.edgeSupport C := by
  ext i
  simp [labelSupport, mem_edgeSupport]

theorem edgeLabelPair_degree {C : Finset E} (hinj : Set.InjOn Q.edgeLabelPair C)
    (i : Fin 4) : pairDegree (C.image Q.edgeLabelPair) i = Q.degreeOn C i := by
  have himage : (C.image Q.edgeLabelPair).filter (fun p => i ∈ p.val) =
      (C.filter (fun e => i ∈ Q.edge e)).image Q.edgeLabelPair := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨e, he, rfl⟩, hi⟩
      exact ⟨e, ⟨he, (Q.mem_edgeLabelPair e i).mp hi⟩, rfl⟩
    · rintro ⟨e, ⟨he, hi⟩, rfl⟩
      exact ⟨⟨e, he, rfl⟩, (Q.mem_edgeLabelPair e i).mpr hi⟩
  unfold pairDegree degreeOn
  rw [himage]
  convert Finset.card_image_of_injOn
    (hinj.mono (Finset.filter_subset (fun e => i ∈ Q.edge e) C)) using 1
  congr 1
  ext e
  simp

theorem edgeLabelPair_crosses (e : E) (X : Finset (Fin 4)) :
    ((Q.edgeLabelPair e).val ∩ X).card = 1 ↔
      (Q.firstEnd e ∈ X) ≠ (Q.secondEnd e ∈ X) := by
  change ((Q.edge e).toFinset ∩ X).card = 1 ↔ _
  rw [← Q.edge_eq e]
  have hne := Q.endpoints_distinct e
  by_cases h₁ : Q.firstEnd e ∈ X <;> by_cases h₂ : Q.secondEnd e ∈ X <;>
    simp [Sym2.toFinset_mk_eq, h₁, h₂, hne]

/-- The finite simple-graph classification transfers to the original
edge copies when the pair projection is injective. -/
theorem isCircuit_of_even_injective_labels {C : Finset E} (hC : C.Nonempty)
    (hinj : Set.InjOn Q.edgeLabelPair C) (heven : ∀ i, Even (Q.degreeOn C i)) :
    Q.IsCircuit C := by
  have hlabel := simple_even_isLabelCircuit (C.image Q.edgeLabelPair)
    (hC.image _) (fun i => by rw [Q.edgeLabelPair_degree hinj i]; exact Nat.even_iff.mp (heven i))
  refine ⟨hC, ?_, ?_⟩
  · intro i hi
    rw [← Q.edgeLabelPair_degree hinj i]
    exact hlabel.2.1 i (by rwa [Q.edgeLabelPair_support])
  · intro X hX hnonempty hproper
    obtain ⟨p, hp, hcross⟩ := hlabel.2.2 X
      (by rwa [Q.edgeLabelPair_support]) hnonempty
      (by rwa [Q.edgeLabelPair_support])
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨e, (Q.mem_cutOn C X e).mpr ⟨he, (Q.edgeLabelPair_crosses e X).mp hcross⟩⟩

/-- Ordinary Eulerian decomposition on four labels, with compatibility
retained whenever the original selected set is already compatible. -/
theorem exists_compatibleCircuitPartition_of_compatible
    (classOf : Fin 4 → E → K) (C : Finset E)
    (hcomp : Q.Compatible classOf C) (heven : ∀ i, Even (Q.degreeOn C i)) :
    Nonempty (Q.CompatibleCircuitPartition classOf C) := by
  classical
  induction hn : C.card using Nat.strong_induction_on generalizing C with
  | h n ih =>
    by_cases hC : C.Nonempty
    · by_cases hinj : Set.InjOn Q.edgeLabelPair C
      · refine ⟨{
          parts := {C}
          circuit := ?_
          compatible := ?_
          disjoint := ?_
          cover := by simp }⟩
        · intro D hD
          have hDC : D = C := Finset.mem_singleton.mp hD
          subst D
          exact Q.isCircuit_of_even_injective_labels hC hinj heven
        · intro D hD
          exact Finset.mem_singleton.mp hD ▸ hcomp
        · intro D hD D' hD' hne
          exact (hne ((Finset.mem_singleton.mp hD).trans (Finset.mem_singleton.mp hD').symm)).elim
      · have hcollision : ∃ e ∈ C, ∃ f ∈ C,
            Q.edgeLabelPair e = Q.edgeLabelPair f ∧ e ≠ f := by
          simp only [Set.InjOn] at hinj
          push_neg at hinj
          exact hinj
        obtain ⟨e, he, f, hf, hpair, hne⟩ := hcollision
        let D : Finset E := {e, f}
        have hDsub : D ⊆ C := by
          intro a ha
          rcases Finset.mem_insert.mp ha with rfl | ha
          · exact he
          · exact Finset.mem_singleton.mp ha ▸ hf
        have hDcircuit : Q.IsCircuit D :=
          Q.isCircuit_parallel_pair hne ((Q.edgeLabelPair_eq_iff e f).mp hpair)
        have hcard : (C \ D).card < n := by
          have hsplit := Finset.card_sdiff_add_card_eq_card hDsub
          have hDcard : D.card = 2 := by simp [D, hne]
          omega
        obtain ⟨P⟩ := ih (C \ D).card hcard (C \ D)
          (Compatible.mono Q hcomp (Finset.sdiff_subset))
          (Q.even_degreeOn_sdiff hDsub heven hDcircuit.even_degreeOn) rfl
        have hDdisjoint (A : Finset E) (hA : A ∈ P.parts) : Disjoint D A := by
          apply Finset.disjoint_left.mpr
          intro a haD haA
          exact (Finset.mem_sdiff.mp
            (CompatibleCircuitPartition.part_subset Q P hA haA)).2 haD
        refine ⟨{
          parts := insert D P.parts
          circuit := ?_
          compatible := ?_
          disjoint := ?_
          cover := ?_ }⟩
        · intro A hA
          rcases Finset.mem_insert.mp hA with rfl | hA
          · exact hDcircuit
          · exact P.circuit A hA
        · intro A hA
          rcases Finset.mem_insert.mp hA with rfl | hA
          · exact Compatible.mono Q hcomp hDsub
          · exact P.compatible A hA
        · intro A hA B hB hneAB
          rcases Finset.mem_insert.mp hA with rfl | hA <;>
            rcases Finset.mem_insert.mp hB with rfl | hB
          · exact (hneAB rfl).elim
          · exact hDdisjoint B hB
          · exact (hDdisjoint A hA).symm
          · exact P.disjoint A hA B hB hneAB
        · rw [Finset.biUnion_insert, id_eq, P.cover]
          exact Finset.union_sdiff_of_subset hDsub
    · have hempty : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hC
      subst C
      exact ⟨{
        parts := ∅
        circuit := by simp
        compatible := by simp
        disjoint := by simp
        cover := by simp }⟩

/-- No compatibility condition is needed for ordinary circuit decomposition:
give each actual copy its own incidence class. -/
theorem exists_circuitPartition (C : Finset E)
    (heven : ∀ i, Even (Q.degreeOn C i)) :
    Nonempty (Q.CompatibleCircuitPartition (fun _ e => e) C) := by
  apply Q.exists_compatibleCircuitPartition_of_compatible (fun _ e => e) C
  · intro _ _ _ _ _ _ _ h
    exact h
  · exact heven

end Overfull.Multigraph
