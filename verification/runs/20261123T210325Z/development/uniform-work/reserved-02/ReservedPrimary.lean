import Overfull.CompatibleCircuits.TwoOddDecomposition

/-!
# Prescribed singleton primary crossings

Selected original copies between the two odd labels are paired with distinct
virtual copies before the remaining compatible circuits are constructed.
The class budget is derived relative to the number of unused virtual copies.
-/

noncomputable section
namespace Overfull.NativeReserve
open Finset Classical

variable {V E K : Type*} [Fintype V]

/-- Any selected copy of the prescribed pair crosses exactly the shores
that separate its ends. -/
omit [Fintype V] in
theorem pair_copy_crosses (Q : Multigraph V E) (a b : V) {e : E}
    (he : Q.edge e = s(a,b)) (X : Finset V) :
    ((Q.firstEnd e ∈ X) ≠ (Q.secondEnd e ∈ X)) ↔ (a ∈ X) ≠ (b ∈ X) := by
  have hh := (Q.edge_eq e).trans he
  rcases Sym2.eq_iff.mp hh with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · simp only [h₁,h₂]
  · simp only [h₁,h₂,ne_comm]

/-- An original copy paired with one virtual copy forms a compatible
parallel two-circuit, regardless of other prescribed original endpoints. -/
omit [Fintype V] in
theorem original_virtual_pair_compatible (Q : Multigraph V E) (a b : V)
    (hab : a ≠ b) (h : ℕ) (classOf : V → E → K) (e : E) (j : Fin h) :
    (Q.pairAugmentation a b hab h).Compatible
      (Multigraph.pairAugmentationClass h classOf) {Sum.inl e,Sum.inr j} := by
  intro v x hx _hvx y hy _hvy hclass
  simp only [mem_insert,mem_singleton] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · rfl
  · cases hclass
  · cases hclass
  · rfl

/-- On at most three labels, all specified copies of one pair may be made
individual original/virtual circuits. The construction proves residual
admissibility rather than assuming a safe circuit selector. -/
theorem exists_circuit_partition_with_reserved_pairs
    (Q : Multigraph V E) (a b : V) (hab : a ≠ b) (h : ℕ)
    (hV : Fintype.card V ≤ 3) (classOf : V → E → K)
    (A C : Finset E) (B : Finset (Fin h))
    (hAC : A ⊆ C) (hpair : ∀ e ∈ A, Q.edge e = s(a,b)) (hAB : A.card ≤ B.card)
    (hclosed : ∀ X : Finset V, (a ∈ X) = (b ∈ X) → ∀ v k,
      2*(Q.classCutOn classOf C v k X).card ≤ (Q.cutOn C X).card)
    (hseparating : ∀ X : Finset V, (a ∈ X) ≠ (b ∈ X) →
      B.card ≤ (Q.cutOn C X).card ∧
        ∀ v k, (Q.classCutOn classOf C v k X).card ≤ B.card-A.card)
    (heven : ∀ v, Even ((Q.pairAugmentation a b hab h).degreeOn (C.disjSum B) v)) :
    ∃ P : (Q.pairAugmentation a b hab h).CompatibleCircuitPartition
        (Multigraph.pairAugmentationClass h classOf) (C.disjSum B),
      ∀ e ∈ A, ∃ j : Fin h, {Sum.inl e,Sum.inr j} ∈ P.parts := by
  induction A using Finset.induction_on generalizing C B with
  | empty =>
    have hadm : (Q.pairAugmentation a b hab h).AdmissibleOn
        (Multigraph.pairAugmentationClass h classOf) (C.disjSum B) := by
      apply Q.pairAugmentation_admissibleOn a b hab h classOf (C.disjSum B)
      · simpa only [toLeft_disjSum] using hclosed
      · simpa only [toLeft_disjSum,toRight_disjSum,card_empty,Nat.sub_zero] using hseparating
    obtain ⟨P⟩ := (Q.pairAugmentation a b hab h).exists_compatibleCircuitPartition_of_card_le_three
      hV (Multigraph.pairAugmentationClass h classOf) (C.disjSum B) hadm heven
    exact ⟨P,by simp⟩
  | @insert e A heA ih =>
    have heC : e ∈ C := hAC (mem_insert_self _ _)
    have hepair : Q.edge e = s(a,b) := hpair e (mem_insert_self _ _)
    have hBpos : 0 < B.card := by
      rw [card_insert_of_notMem heA] at hAB
      omega
    obtain ⟨j,hj⟩ := card_pos.mp hBpos
    let C' := C \ {e}
    let B' := B \ {j}
    let D : Finset (E ⊕ Fin h) := {Sum.inl e,Sum.inr j}
    have hAC' : A ⊆ C' := by
      intro f hf
      exact mem_sdiff.mpr ⟨hAC (mem_insert_of_mem hf),by simpa using ne_of_mem_of_not_mem hf heA⟩
    have hBcount : B'.card+1=B.card := by
      have hh := card_sdiff_add_card_eq_card (show ({j} : Finset (Fin h)) ⊆ B from singleton_subset_iff.mpr hj)
      simpa only [card_singleton] using hh
    have hAB' : A.card ≤ B'.card := by
      rw [card_insert_of_notMem heA] at hAB
      omega
    have hcutClosed (X : Finset V) (hX : (a ∈ X) = (b ∈ X)) : Q.cutOn C' X = Q.cutOn C X := by
      have hzero : Q.cutOn {e} X = ∅ := by
        ext f
        simp only [Q.mem_cutOn,mem_singleton,notMem_empty,iff_false,not_and]
        intro hfe
        subst f
        exact fun hh => ((pair_copy_crosses Q a b hepair X).mp hh) hX
      change Q.cutOn (C \ {e}) X = Q.cutOn C X
      rw [Q.cutOn_sdiff,hzero,sdiff_empty]
    have hclosed' : ∀ X : Finset V, (a ∈ X) = (b ∈ X) → ∀ v k,
        2*(Q.classCutOn classOf C' v k X).card ≤ (Q.cutOn C' X).card := by
      intro X hX v k
      have hc := hclosed X hX v k
      simpa only [Multigraph.classCutOn,hcutClosed X hX] using hc
    have hsep' : ∀ X : Finset V, (a ∈ X) ≠ (b ∈ X) →
        B'.card ≤ (Q.cutOn C' X).card ∧
          ∀ v k, (Q.classCutOn classOf C' v k X).card ≤ B'.card-A.card := by
      intro X hX
      obtain ⟨hcut,hclass⟩ := hseparating X hX
      have hsingle : Q.cutOn {e} X = {e} := by
        ext f
        simp only [Q.mem_cutOn,mem_singleton]
        exact ⟨fun hh => hh.1,fun hh => ⟨hh,hh ▸ (pair_copy_crosses Q a b hepair X).mpr hX⟩⟩
      have hcount := Q.cutOn_card_sdiff_add (singleton_subset_iff.mpr heC) X
      rw [hsingle,card_singleton] at hcount
      refine ⟨by change B'.card ≤ (Q.cutOn (C \ {e}) X).card; omega,?_⟩
      intro v k
      have hmono : (Q.classCutOn classOf C' v k X).card ≤ (Q.classCutOn classOf C v k X).card := by
        apply card_le_card
        exact filter_subset_filter _ (filter_subset_filter _ sdiff_subset)
      have hc := hclass v k
      rw [card_insert_of_notMem heA] at hc
      omega
    have hDsub : D ⊆ C.disjSum B := by
      intro x hx
      rcases mem_insert.mp hx with rfl | hx
      · exact inl_mem_disjSum.mpr heC
      · have hxj := mem_singleton.mp hx
        subst x
        exact inr_mem_disjSum.mpr hj
    have hDcir : (Q.pairAugmentation a b hab h).IsCircuit D :=
      (Q.pairAugmentation a b hab h).isCircuit_parallel_pair
        (e := Sum.inl e) (f := Sum.inr j) (by simp)
        (by simpa only [Multigraph.pairAugmentation_edge_inl,Multigraph.pairAugmentation_edge_inr] using hepair)
    have hDcomp : (Q.pairAugmentation a b hab h).Compatible
        (Multigraph.pairAugmentationClass h classOf) D :=
      original_virtual_pair_compatible Q a b hab h classOf e j
    have hrest : C'.disjSum B' = C.disjSum B \ D := by
      ext x
      cases x <;> simp [C',B',D]
    have heven' : ∀ v, Even ((Q.pairAugmentation a b hab h).degreeOn (C'.disjSum B') v) := by
      rw [hrest]
      exact (Q.pairAugmentation a b hab h).even_degreeOn_sdiff hDsub heven hDcir.even_degreeOn
    obtain ⟨P,hP⟩ := ih C' B' hAC' (fun f hf => hpair f (mem_insert_of_mem hf))
      hAB' hclosed' hsep' heven'
    let P' : (Q.pairAugmentation a b hab h).CompatibleCircuitPartition
        (Multigraph.pairAugmentationClass h classOf) (C.disjSum B \ D) := hrest ▸ P
    let R := P'.insertCircuit (Q.pairAugmentation a b hab h) hDsub hDcir hDcomp
    refine ⟨R,?_⟩
    intro f hf
    rcases mem_insert.mp hf with rfl | hf
    · exact ⟨j,mem_insert_self _ _⟩
    · obtain ⟨k,hk⟩ := hP f hf
      exact ⟨k,mem_insert_of_mem hk⟩

end Overfull.NativeReserve
