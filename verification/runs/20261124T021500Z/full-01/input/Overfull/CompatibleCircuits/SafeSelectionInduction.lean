import Overfull.CompatibleCircuits.FourLabel
import Overfull.CompatibleCircuits.ThreeVertexDeletion

/-!
# Exact circuit partitions from safe selection

This file supplies the induction and actual-copy accounting for a
compatible-circuit selector. A nonempty admissible even-degree residual
must supply a compatible circuit whose deletion remains admissible.
That selection assertion is an explicit hypothesis here, not a proved
existence theorem for arbitrary incidence classes.

For at most three vertices, the selector may instead supply witnesses
that its circuit meets each tight incidence class on each crossed cut.
The checked exact-deletion criterion then discharges residual
admissibility. `ThreeLabel.lean` supplies the unconditional selector on
three labels; this generic induction theorem retains its explicit interface.
-/

namespace Overfull.Multigraph

open Finset Classical

variable {V E K : Type*} (G : Multigraph V E)

/-- The empty actual-copy set has the empty compatible circuit partition. -/
noncomputable def CompatibleCircuitPartition.empty (classOf : V → E → K) :
    G.CompatibleCircuitPartition classOf ∅ where
  parts := ∅
  circuit := by simp
  compatible := by simp
  disjoint := by simp
  cover := by simp

/-- Reinsert a selected circuit into an exact partition of its residual.
The disjointness and covering equations refer to actual original copies. -/
noncomputable def CompatibleCircuitPartition.insertCircuit
    {classOf : V → E → K} {C D : Finset E}
    (P : G.CompatibleCircuitPartition classOf (C \ D))
    (hDC : D ⊆ C) (hD : G.IsCircuit D) (hcomp : G.Compatible classOf D) :
    G.CompatibleCircuitPartition classOf C := by
  have hDdisjoint (A : Finset E) (hA : A ∈ P.parts) : Disjoint D A := by
    apply Finset.disjoint_left.mpr
    intro e heD heA
    exact (Finset.mem_sdiff.mp (P.part_subset G hA heA)).2 heD
  exact {
    parts := insert D P.parts
    circuit := by
      intro A hA
      rcases Finset.mem_insert.mp hA with rfl | hA
      · exact hD
      · exact P.circuit A hA
    compatible := by
      intro A hA
      rcases Finset.mem_insert.mp hA with rfl | hA
      · exact hcomp
      · exact P.compatible A hA
    disjoint := by
      intro A hA B hB hne
      rcases Finset.mem_insert.mp hA with rfl | hA <;>
        rcases Finset.mem_insert.mp hB with rfl | hB
      · exact (hne rfl).elim
      · exact hDdisjoint B hB
      · exact (hDdisjoint A hA).symm
      · exact P.disjoint A hA B hB hne
    cover := by
      rw [Finset.biUnion_insert, id_eq, P.cover]
      exact Finset.union_sdiff_of_subset hDC }

/-- Removing one part leaves an exact compatible circuit partition of
the original copies outside that part. -/
noncomputable def CompatibleCircuitPartition.eraseCircuit
    {classOf : V → E → K} {C D : Finset E}
    (P : G.CompatibleCircuitPartition classOf C) (hD : D ∈ P.parts) :
    G.CompatibleCircuitPartition classOf (C \ D) where
  parts := P.parts.erase D
  circuit := fun A hA => P.circuit A (Finset.mem_erase.mp hA).2
  compatible := fun A hA => P.compatible A (Finset.mem_erase.mp hA).2
  disjoint := fun A hA B hB hne =>
    P.disjoint A (Finset.mem_erase.mp hA).2 B (Finset.mem_erase.mp hB).2 hne
  cover := by
    ext e
    simp only [Finset.mem_biUnion, id_eq, Finset.mem_sdiff]
    constructor
    · rintro ⟨A, hA, heA⟩
      obtain ⟨hAD, hAP⟩ := Finset.mem_erase.mp hA
      exact ⟨P.part_subset G hAP heA,
        fun heD => Finset.disjoint_left.mp (P.disjoint A hAP D hD hAD) heA heD⟩
    · rintro ⟨heC, heD⟩
      rw [← P.cover] at heC
      obtain ⟨A, hA, heA⟩ := Finset.mem_biUnion.mp heC
      have hAD : A ≠ D := fun h => heD (h ▸ heA)
      exact ⟨A, Finset.mem_erase.mpr ⟨hAD, hA⟩, heA⟩

/-- Every part of an existing compatible partition is safely removable.
This gives a checkable witness when the partition is already known. -/
theorem CompatibleCircuitPartition.exists_safe_circuit
    {classOf : V → E → K} {C : Finset E}
    (P : G.CompatibleCircuitPartition classOf C) (hC : C.Nonempty) :
    ∃ D ⊆ C, G.IsCircuit D ∧ G.Compatible classOf D ∧
      G.AdmissibleOn classOf (C \ D) := by
  obtain ⟨e, he⟩ := hC
  rw [← P.cover] at he
  obtain ⟨D, hD, _⟩ := Finset.mem_biUnion.mp he
  exact ⟨D, P.part_subset G hD, P.circuit D hD, P.compatible D hD,
    (P.eraseCircuit G hD).admissibleOn G⟩

/-- A compatible circuit can be selected safely from every nonempty
admissible even-degree residual of the given original copy set. -/
def HasSafeCircuitSelection (classOf : V → E → K) (C : Finset E) : Prop :=
  ∀ R ⊆ C, R.Nonempty → G.AdmissibleOn classOf R →
    (∀ v, Even (G.degreeOn R v)) →
    ∃ D ⊆ R, G.IsCircuit D ∧ G.Compatible classOf D ∧
      G.AdmissibleOn classOf (R \ D)

/-- A selector on the original copies also applies to any residual. -/
theorem HasSafeCircuitSelection.mono {classOf : V → E → K}
    {C R : Finset E} (h : G.HasSafeCircuitSelection classOf C) (hRC : R ⊆ C) :
    G.HasSafeCircuitSelection classOf R := by
  intro S hSR hS hadmissible heven
  exact h S (hSR.trans hRC) hS hadmissible heven

/-- Safe circuit selection yields an exact compatible circuit partition.
Only actual selected copies are removed, their number strictly decreases,
and every selected circuit has even degree at each vertex. -/
theorem exists_compatibleCircuitPartition_of_safe_selection
    (classOf : V → E → K) (C : Finset E)
    (hselect : G.HasSafeCircuitSelection classOf C)
    (hadmissible : G.AdmissibleOn classOf C)
    (heven : ∀ v, Even (G.degreeOn C v)) :
    Nonempty (G.CompatibleCircuitPartition classOf C) := by
  classical
  induction hn : C.card using Nat.strong_induction_on generalizing C with
  | h n ih =>
    by_cases hC : C.Nonempty
    · obtain ⟨D, hDC, hD, hcomp, hsafe⟩ :=
        hselect C (Finset.Subset.refl _) hC hadmissible heven
      have hcard : (C \ D).card < n := by
        have hsplit := Finset.card_sdiff_add_card_eq_card hDC
        have hpositive := Finset.card_pos.mpr hD.1
        omega
      obtain ⟨P⟩ := ih (C \ D).card hcard (C \ D)
        (hselect.mono G Finset.sdiff_subset) hsafe
        (G.even_degreeOn_sdiff hDC heven hD.even_degreeOn) rfl
      exact ⟨P.insertCircuit G hDC hD hcomp⟩
    · have hempty : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hC
      subst C
      exact ⟨CompatibleCircuitPartition.empty G classOf⟩

/-- On at most three labels, meeting all tight classes on the crossed
cuts is enough to supply the residual admissibility needed by induction.
The compatible-circuit witness is still an explicit selection hypothesis. -/
theorem exists_compatibleCircuitPartition_of_tight_class_selection
    [Fintype V] (hV : Fintype.card V ≤ 3)
    (classOf : V → E → K) (C : Finset E)
    (hselect : ∀ R ⊆ C, R.Nonempty → G.AdmissibleOn classOf R →
      (∀ v, Even (G.degreeOn R v)) →
      ∃ D ⊆ R, G.IsCircuit D ∧ G.Compatible classOf D ∧
        ∀ v k X, (G.cutOn R X).card = 2 * (G.classCutOn classOf R v k X).card →
          (G.cutOn D X).Nonempty → (G.classCutOn classOf D v k X).Nonempty)
    (hadmissible : G.AdmissibleOn classOf C)
    (heven : ∀ v, Even (G.degreeOn C v)) :
    Nonempty (G.CompatibleCircuitPartition classOf C) := by
  apply G.exists_compatibleCircuitPartition_of_safe_selection classOf C
    ?_ hadmissible heven
  intro R hRC hR hRadmissible hReven
  obtain ⟨D, hDR, hD, hcomp, htight⟩ := hselect R hRC hR hRadmissible hReven
  exact ⟨D, hDR, hD, hcomp,
    (G.admissibleOn_sdiff_iff_meets_tight_classes_of_card_le_three hV
      classOf hDR hD hRadmissible hReven).mpr htight⟩

end Overfull.Multigraph
