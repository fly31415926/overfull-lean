import Overfull.CompatibleCircuits.FourDegreeTwoReassembly

/-!
# Restoring disjoint original-copy blocks across a suppressed shore

The block associated with a virtual copy is its original path through the
shore. Blocks outside the shore may be singleton original copies. A common
incidence class at an anchor ensures that each compatible suppressed part
uses at most one block that meets the shore. The expanded part is therefore
compatible, and exact degree identities show that all its degrees are even.
Ordinary decomposition on four labels then gives genuine original circuits.

These are restoration theorems with explicit block identities. They do not
assume that the suppressed graph is admissible or that its partition exists;
constructing those objects from a tight cut remains a separate obligation.
-/

noncomputable section

namespace Overfull.Multigraph

open Finset Classical
open scoped BigOperators

variable {V E F K L : Type*}

/-- Refine a disjoint family of original-copy blocks by genuine partitions
of each block. The resulting cover contains each original copy exactly once. -/
def CompatibleCircuitPartition.refineBlocks
    (G : Multigraph V E) (classOf : V → E → K)
    (B : Finset (Finset E))
    (P : ∀ D ∈ B, G.CompatibleCircuitPartition classOf D)
    (hdisjoint : ∀ D ∈ B, ∀ D' ∈ B, D ≠ D' → Disjoint D D') :
    G.CompatibleCircuitPartition classOf (B.biUnion id) where
  parts := B.attach.biUnion (fun D => (P D.val D.property).parts)
  circuit := by
    intro A hA
    obtain ⟨D, _, hA⟩ := mem_biUnion.mp hA
    exact (P D.val D.property).circuit A hA
  compatible := by
    intro A hA
    obtain ⟨D, _, hA⟩ := mem_biUnion.mp hA
    exact (P D.val D.property).compatible A hA
  disjoint := by
    intro A hA A' hA' hne
    obtain ⟨D, _, hA⟩ := mem_biUnion.mp hA
    obtain ⟨D', _, hA'⟩ := mem_biUnion.mp hA'
    by_cases hDD' : D = D'
    · subst D'
      exact (P D.val D.property).disjoint A hA A' hA' hne
    · apply (hdisjoint D.val D.property D'.val D'.property
        (fun h => hDD' (Subtype.ext h))).mono
      · exact (P D.val D.property).part_subset G hA
      · exact (P D'.val D'.property).part_subset G hA'
  cover := by
    ext e
    simp only [mem_biUnion, id_eq]
    constructor
    · rintro ⟨A, ⟨D, _, hA⟩, heA⟩
      exact ⟨D.val, D.property, (P D.val D.property).part_subset G hA heA⟩
    · rintro ⟨D, hD, heD⟩
      rw [← (P D hD).cover] at heD
      obtain ⟨A, hA, heA⟩ := mem_biUnion.mp heD
      exact ⟨A, ⟨⟨D, hD⟩, mem_attach _ _, hA⟩, heA⟩

/-- Degree sums over pairwise disjoint actual-copy blocks. -/
theorem degreeOn_biUnion_disjoint (G : Multigraph V E)
    (R : Finset F) (block : F → Finset E)
    (hdisjoint : ∀ i ∈ R, ∀ j ∈ R, i ≠ j → Disjoint (block i) (block j))
    (v : V) :
    G.degreeOn (R.biUnion block) v = ∑ i ∈ R, G.degreeOn (block i) v := by
  have heq : (R.biUnion block).filter (fun e => v ∈ G.edge e) =
      R.biUnion (fun i => (block i).filter (fun e => v ∈ G.edge e)) := by
    ext e
    simp only [mem_filter, mem_biUnion]
    aesop
  unfold degreeOn
  rw [heq]
  apply card_biUnion
  intro i hi j hj hij
  exact (hdisjoint i hi j hj hij).mono (filter_subset _ _) (filter_subset _ _)

/-- Exact sufficient data for restoring a suppressed edge to a block of
original copies. All identities are on the selected copies, not supports. -/
structure CompatibleBlockExpansion
    (G : Multigraph V E) (H : Multigraph V F)
    (classOf : V → E → K) (hclass : V → F → L)
    (C : Finset F) (block : F → Finset E) (X : Finset V) (anchor : V) (k : L) where
  disjoint : ∀ i ∈ C, ∀ j ∈ C, i ≠ j → Disjoint (block i) (block j)
  compatible : ∀ i ∈ C, G.Compatible classOf (block i)
  inner_even : ∀ i ∈ C, ∀ v ∈ X, Even (G.degreeOn (block i) v)
  outer_degree : ∀ i ∈ C, ∀ v, v ∉ X →
    G.degreeOn (block i) v = if v ∈ H.edge i then 1 else 0
  outer_class : ∀ i ∈ C, ∀ v, v ∉ X → ∀ e ∈ block i, v ∈ G.edge e →
    v ∈ H.edge i ∧ ∀ j ∈ C, ∀ f ∈ block j, v ∈ G.edge f →
      classOf v e = classOf v f → hclass v i = hclass v j
  common_class : ∀ i ∈ C, ∀ v ∈ X, ∀ e ∈ block i, v ∈ G.edge e →
    anchor ∈ H.edge i ∧ hclass anchor i = k

variable (G : Multigraph V E) (H : Multigraph V F)
  {classOf : V → E → K} {hclass : V → F → L}
  {C : Finset F} {block : F → Finset E} {X : Finset V} {anchor : V} {k : L}

/-- Compatibility of the suppressed part prevents two distinct blocks
from meeting the restored shore, and transfers all outer conflicts. -/
theorem CompatibleBlockExpansion.compatible_biUnion
    (B : CompatibleBlockExpansion G H classOf hclass C block X anchor k)
    {R : Finset F} (hRC : R ⊆ C) (hR : H.Compatible hclass R) :
    G.Compatible classOf (R.biUnion block) := by
  intro v e he hve f hf hvf heq
  obtain ⟨i, hi, hei⟩ := mem_biUnion.mp he
  obtain ⟨j, hj, hfj⟩ := mem_biUnion.mp hf
  have hij : i = j := by
    by_cases hv : v ∈ X
    · have hiA := B.common_class i (hRC hi) v hv e hei hve
      have hjA := B.common_class j (hRC hj) v hv f hfj hvf
      exact hR anchor i hi hiA.1 j hj hjA.1 (hiA.2.trans hjA.2.symm)
    · have hiO := B.outer_class i (hRC hi) v hv e hei hve
      have hjO := B.outer_class j (hRC hj) v hv f hfj hvf
      exact hR v i hi hiO.1 j hj hjO.1 (hiO.2 j (hRC hj) f hfj hvf heq)
  subst j
  exact B.compatible i (hRC hi) v e hei hve f hfj hvf heq

/-- Exact block degree identities preserve evenness at every vertex. -/
theorem CompatibleBlockExpansion.even_degrees_biUnion
    (B : CompatibleBlockExpansion G H classOf hclass C block X anchor k)
    {R : Finset F} (hRC : R ⊆ C) (heven : ∀ v, Even (H.degreeOn R v)) :
    ∀ v, Even (G.degreeOn (R.biUnion block) v) := by
  intro v
  rw [G.degreeOn_biUnion_disjoint R block
    (fun i hi j hj hij => B.disjoint i (hRC hi) j (hRC hj) hij)]
  by_cases hv : v ∈ X
  · have hdvd : 2 ∣ ∑ i ∈ R, G.degreeOn (block i) v :=
      Finset.dvd_sum (fun i hi => (B.inner_even i (hRC hi) v hv).two_dvd)
    exact Nat.even_iff.mpr (Nat.mod_eq_zero_of_dvd hdvd)
  · have heq : (∑ i ∈ R, G.degreeOn (block i) v) = H.degreeOn R v := by
      calc
        _ = ∑ i ∈ R, if v ∈ H.edge i then 1 else 0 :=
          sum_congr rfl (fun i hi => B.outer_degree i (hRC hi) v hv)
        _ = _ := by simp only [sum_boole, degreeOn, Nat.cast_id]
    rw [heq]
    exact heven v

/-- Disjoint suppressed copy sets expand to disjoint original copy sets. -/
theorem CompatibleBlockExpansion.disjoint_biUnion
    (B : CompatibleBlockExpansion G H classOf hclass C block X anchor k)
    {R S : Finset F} (hRC : R ⊆ C) (hSC : S ⊆ C) (hRS : Disjoint R S) :
    Disjoint (R.biUnion block) (S.biUnion block) := by
  apply disjoint_left.mpr
  intro e heR heS
  obtain ⟨i, hi, hei⟩ := mem_biUnion.mp heR
  obtain ⟨j, hj, hej⟩ := mem_biUnion.mp heS
  have hij : i ≠ j := fun h => disjoint_left.mp hRS hi (h.symm ▸ hj)
  exact disjoint_left.mp (B.disjoint i (hRC hi) j (hSC hj) hij) hei hej

end Overfull.Multigraph

namespace Overfull.Multigraph

open Finset Classical

variable {E F K L : Type*} (G : Multigraph (Fin 4) E) (H : Multigraph (Fin 4) F)
  {classOf : Fin 4 → E → K} {hclass : Fin 4 → F → L}
  {C : Finset F} {block : F → Finset E} {X : Finset (Fin 4)} {anchor : Fin 4} {k : L}

/-- A compatible even suppressed part expands to a genuine partition of
its original copies. No connectivity assumption on the expansion is needed. -/
theorem CompatibleBlockExpansion.exists_partition_biUnion
    (B : CompatibleBlockExpansion G H classOf hclass C block X anchor k)
    {R : Finset F} (hRC : R ⊆ C) (hR : H.Compatible hclass R)
    (heven : ∀ v, Even (H.degreeOn R v)) :
    Nonempty (G.CompatibleCircuitPartition classOf (R.biUnion block)) :=
  G.exists_compatibleCircuitPartition_of_compatible classOf (R.biUnion block)
    (B.compatible_biUnion G H hRC hR) (B.even_degrees_biUnion G H hRC heven)

/-- Restore all parts of a suppressed partition simultaneously. The
result covers exactly the union of the original blocks, with no repeated
copy and no virtual copy left in its edge type. -/
theorem CompatibleBlockExpansion.exists_partition_of_partition
    (B : CompatibleBlockExpansion G H classOf hclass C block X anchor k)
    (P : H.CompatibleCircuitPartition hclass C) :
    Nonempty (G.CompatibleCircuitPartition classOf (C.biUnion block)) := by
  let expand : Finset F → Finset E := fun R => R.biUnion block
  let pieces := P.parts.image expand
  have hparts (D : Finset E) (hD : D ∈ pieces) :
      Nonempty (G.CompatibleCircuitPartition classOf D) := by
    obtain ⟨R, hR, rfl⟩ := mem_image.mp hD
    exact B.exists_partition_biUnion G H (P.part_subset H hR)
      (P.compatible R hR) (P.circuit R hR).even_degreeOn
  have hdisjoint : ∀ D ∈ pieces, ∀ D' ∈ pieces, D ≠ D' → Disjoint D D' := by
    intro D hD D' hD' hne
    obtain ⟨R, hR, rfl⟩ := mem_image.mp hD
    obtain ⟨S, hS, rfl⟩ := mem_image.mp hD'
    have hRS : R ≠ S := fun h => hne (congrArg expand h)
    exact B.disjoint_biUnion G H (P.part_subset H hR) (P.part_subset H hS)
      (P.disjoint R hR S hS hRS)
  have hcover : pieces.biUnion id = C.biUnion block := by
    ext e
    constructor
    · intro he
      obtain ⟨D, hD, heD⟩ := mem_biUnion.mp he
      obtain ⟨R, hR, rfl⟩ := mem_image.mp hD
      obtain ⟨i, hi, hei⟩ := mem_biUnion.mp heD
      exact mem_biUnion.mpr ⟨i, P.part_subset H hR hi, hei⟩
    · intro he
      obtain ⟨i, hi, hei⟩ := mem_biUnion.mp he
      rw [← P.cover] at hi
      obtain ⟨R, hR, hiR⟩ := mem_biUnion.mp hi
      exact mem_biUnion.mpr ⟨expand R, mem_image.mpr ⟨R, hR, rfl⟩,
        mem_biUnion.mpr ⟨i, hiR, hei⟩⟩
  exact ⟨hcover ▸ CompatibleCircuitPartition.refineBlocks G classOf pieces
    (fun D hD => Classical.choice (hparts D hD)) hdisjoint⟩

end Overfull.Multigraph
