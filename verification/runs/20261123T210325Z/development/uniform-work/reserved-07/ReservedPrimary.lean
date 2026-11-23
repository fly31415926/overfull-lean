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

variable {V E K : Type*}

/-- Any selected copy of the prescribed pair crosses exactly the shores
that separate its ends. -/
theorem pair_copy_crosses (Q : Multigraph V E) (a b : V) {e : E}
    (he : Q.edge e = s(a,b)) (X : Finset V) :
    ((Q.firstEnd e ∈ X) ≠ (Q.secondEnd e ∈ X)) ↔ (a ∈ X) ≠ (b ∈ X) := by
  have hh := (Q.edge_eq e).trans he
  rcases Sym2.eq_iff.mp hh with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · simp only [h₁,h₂]
  · simp only [h₁,h₂,ne_comm]

/-- An original copy paired with one virtual copy forms a compatible
parallel two-circuit, regardless of other prescribed original endpoints. -/
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

variable [Fintype V]

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
  letI : DecidableEq (E ⊕ Fin h) := Classical.decEq _
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
    have hDcir : (Q.pairAugmentation a b hab h).IsCircuit D := by
      convert (Q.pairAugmentation a b hab h).isCircuit_parallel_pair
        (e := Sum.inl e) (f := Sum.inr j) (by simp)
        (by simpa only [Multigraph.pairAugmentation_edge_inl,Multigraph.pairAugmentation_edge_inr] using hepair) using 1
    have hDcomp : (Q.pairAugmentation a b hab h).Compatible
        (Multigraph.pairAugmentationClass h classOf) D := by
      convert original_virtual_pair_compatible Q a b hab h classOf e j using 1
      ext x
      simp [D]
    have hrest : C'.disjSum B' = C.disjSum B \ D := by
      ext x
      cases x <;> simp [C',B',D]
    have heven' : ∀ v, Even ((Q.pairAugmentation a b hab h).degreeOn (C'.disjSum B') v) := by
      rw [hrest]
      exact (Q.pairAugmentation a b hab h).even_degreeOn_sdiff hDsub heven hDcir.even_degreeOn
    obtain ⟨P,hP⟩ := ih C' B' hAC' (fun f hf => hpair f (mem_insert_of_mem hf))
      hAB' hclosed' hsep' heven'
    let P' : (Q.pairAugmentation a b hab h).CompatibleCircuitPartition
        (Multigraph.pairAugmentationClass h classOf) (C.disjSum B \ D) :=
      { parts := P.parts, circuit := P.circuit, compatible := P.compatible,
        disjoint := P.disjoint, cover := P.cover.trans hrest }
    let R := P'.insertCircuit (Q.pairAugmentation a b hab h) hDsub hDcir hDcomp
    refine ⟨R,?_⟩
    intro f hf
    rcases mem_insert.mp hf with rfl | hf
    · refine ⟨j,?_⟩
      simp only [R,Multigraph.CompatibleCircuitPartition.insertCircuit,mem_insert]
      left
      ext x
      simp [D]
    · obtain ⟨k,hk⟩ := hP f hf
      exact ⟨k,mem_insert_of_mem hk⟩

section OriginalHost

open FourOdd

variable {W F I : Type*} [Fintype W] [Fintype F] [Fintype I] [DecidableEq I]

/-- An original endpoint class in any joining quotient cut is bounded by
that endpoint's joining degree, not its full host degree. -/
theorem joining_endpoint_class_card_le (G : Multigraph W F) (label : W → I)
    (i : I) (v : W) (X : Finset I) :
    ((joiningQuotient G label).classCutOn
      ((joiningGraph G label).endpointClass label) univ i v X).card ≤
        (joiningGraph G label).degree v := by
  change (((joiningGraph G label).labelQuotient label (joiningGraph_join G label)).classCutOn
    ((joiningGraph G label).endpointClass label) univ i v X).card ≤ _
  rw [Multigraph.labelQuotient_classCutOn_endpointClass]
  split_ifs
  · change (((joiningQuotient G label).cutOn univ X).filter
        (fun e => v ∈ (joiningGraph G label).edge e)).card ≤
      ((univ : Finset (joiningCopies G label)).filter
        (fun e => v ∈ (joiningGraph G label).edge e)).card
    apply card_le_card
    intro e he
    exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp he).2⟩
  · simp

/-- The original regular non-overfull host gives a complete two-odd
joining decomposition in which every prescribed crossing is a singleton
primary piece. Prescribed copies may share original endpoints. -/
theorem exists_twoOddJoining_decomposition_with_reserved_primary
    (G : Multigraph W F) (label : W → I) (a b : I) (hab : a ≠ b)
    (h D : ℕ) (hI : Fintype.card I ≤ 3)
    (hregular : ∀ v, G.degree v = h)
    (hno : ∀ X : Finset W, ¬ G.IsOverfull h X)
    (hfibers : ∀ i, (univ.filter (fun v => label v = i)).card % 2 =
      if i=a ∨ i=b then 1 else 0)
    (A : Finset (joiningCopies G label))
    (hpair : ∀ e ∈ A, (joiningQuotient G label).edge e = s(a,b))
    (hA : A.card ≤ h)
    (hdegree : ∀ v, (joiningGraph G label).degree v ≤ D) (hD : D ≤ h-A.card) :
    ∃ P : TwoOddJoiningDecomposition G label a b h,
      ∀ e ∈ A, {e.val} ∈ P.primary := by
  let Q := joiningQuotient G label
  let classOf := (joiningGraph G label).endpointClass label
  have hclosed : ∀ X : Finset I, (a ∈ X) = (b ∈ X) → ∀ i v,
      2*(Q.classCutOn classOf univ i v X).card ≤ (Q.cutOn univ X).card := by
    intro X hX i v
    have hparity : (labelShore label X).card % 2 = 0 := by
      rw [labelShore_card_parity_of_two_odd_fibers label a b hab hfibers]
      simp [hX]
    rw [joiningQuotient_classCutOn_card]
    by_cases hvi : label v = i
    · rw [if_pos hvi]
      change 2*G.degreeOn (G.cutOn univ (labelShore label X)) v ≤ (joiningCut G label X).card
      rw [joiningCut_card]
      exact regular_even_cut_twice_degree_le G hregular hno _ hparity v
    · simp [hvi]
  have hsep : ∀ X : Finset I, (a ∈ X) ≠ (b ∈ X) →
      (univ : Finset (Fin h)).card ≤ (Q.cutOn univ X).card ∧
        ∀ i v, (Q.classCutOn classOf univ i v X).card ≤
          (univ : Finset (Fin h)).card-A.card := by
    intro X hX
    have hparity : (labelShore label X).card % 2 = 1 := by
      rw [labelShore_card_parity_of_two_odd_fibers label a b hab hfibers]
      simp [hX]
    simp only [card_univ,Fintype.card_fin]
    constructor
    · change h ≤ (joiningCut G label X).card
      rw [joiningCut_card]
      exact regular_odd_cut_lower G hregular hno _ hparity
    · intro i v
      exact (joining_endpoint_class_card_le G label i v X).trans ((hdegree v).trans hD)
  have huniv : (univ : Finset (joiningCopies G label)).disjSum
      (univ : Finset (Fin h)) = univ := by
    ext x
    cases x <;> simp
  have heven : ∀ i, Even ((Q.pairAugmentation a b hab h).degreeOn
      ((univ : Finset (joiningCopies G label)).disjSum (univ : Finset (Fin h))) i) := by
    rw [huniv]
    intro i
    simpa only [Multigraph.degreeOn,Multigraph.degree,Multigraph.incidenceEdges] using
      twoOddJoiningQuotient_even_degrees G label a b hab h hregular hfibers i
  obtain ⟨P,hP⟩ := exists_circuit_partition_with_reserved_pairs Q a b hab h hI classOf
    A univ univ (subset_univ _) hpair (by simpa using hA) hclosed hsep heven
  let R : (twoOddJoiningQuotient G label a b hab h).CompatibleCircuitPartition
      (twoOddJoiningClasses G label h) univ :=
    { parts := P.parts, circuit := P.circuit, compatible := P.compatible,
      disjoint := P.disjoint, cover := P.cover.trans huniv }
  let T : TwoOddJoiningDecomposition G label a b h := {
    primary := twoOddPrimaryParts G label a b hab h R
    surplus := twoOddSurplusParts G label a b hab h R
    primary_card := twoOddPrimaryParts_card G label a b hab h R
    families_disjoint := twoOddParts_families_disjoint G label a b hab h R
    nonempty := fun _ hM => twoOddParts_nonempty G label a b hab h R hM
    matching := fun _ hM => twoOddParts_isMatching G label a b hab h R hM
    disjoint := fun _ hM _ hN hne => twoOddParts_disjoint G label a b hab h R hM hN hne
    cover := twoOddParts_cover G label a b hab h R
    primary_card_le := fun _ hM => twoOddPrimaryParts_card_le G label a b hab h R hI hM
    surplus_card_le := fun _ hM => twoOddSurplusParts_card_le G label a b hab h R hI hM
    primary_cut_eq_one := fun _ hM i hi =>
      twoOddPrimaryParts_cut_eq_one G label a b hab h R hM i hi
    primary_odd_cut_iff := fun _ hM i =>
      twoOddPrimaryParts_odd_cut_iff G label a b hab h R hM i
    surplus_even_cut := fun _ hM i => twoOddSurplusParts_even_cut G label a b hab h R hM i
  }
  refine ⟨T,?_⟩
  intro e he
  obtain ⟨j,hj⟩ := hP e he
  change {e.val} ∈ twoOddPrimaryParts G label a b hab h R
  apply mem_image.mpr
  refine ⟨{Sum.inl e,Sum.inr j},?_,?_⟩
  · apply mem_filter.mpr
    refine ⟨hj,?_⟩
    have hright : ({Sum.inl e,Sum.inr j} : Finset ((joiningCopies G label) ⊕ Fin h)).toRight = {j} := by
      ext x
      simp
    rw [hright,card_singleton]
  · have hleft : ({Sum.inl e,Sum.inr j} : Finset ((joiningCopies G label) ⊕ Fin h)).toLeft = {e} := by
      ext x
      simp
    simp only [twoOddOriginalPart,hleft,image_singleton]

end OriginalHost

end Overfull.NativeReserve
