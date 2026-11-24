import Overfull.CompatibleCircuits.Counting
import Mathlib.Data.Finset.Sum

/-!
# A single family of virtual parallel copies

The arbitrary vertex type is retained. Original copies embed by `Sum.inl`;
the `h` new copies all join two specified distinct vertices and have one
fresh incidence class. The exact cut formulas yield augmented admissibility
from the original cut bounds needed by the two-odd-part construction.
These are supporting interfaces; no original host reserve or factorization
is assumed to have been constructed here.
-/

namespace Overfull.Multigraph

open Finset Classical
open scoped BigOperators

variable {V E K : Type*} (Q : Multigraph V E)
variable (a b : V) (hab : a ≠ b) (h : ℕ)

/-- Retain every original copy and add `h` distinct copies of the pair `ab`. -/
def pairAugmentation : Multigraph V (E ⊕ Fin h) where
  edge
    | .inl e => Q.edge e
    | .inr _ => s(a, b)
  loopless e := by
    cases e with
    | inl e => exact Q.loopless e
    | inr j => simpa using hab

/-- The virtual copies have one class, distinct from every original class. -/
def pairAugmentationClass (classOf : V → E → K) : V → (E ⊕ Fin h) → K ⊕ Unit
  | v, .inl e => .inl (classOf v e)
  | _, .inr _ => .inr ()

@[simp] theorem pairAugmentation_edge_inl (e : E) :
    (Q.pairAugmentation a b hab h).edge (.inl e) = Q.edge e := rfl

@[simp] theorem pairAugmentation_edge_inr (j : Fin h) :
    (Q.pairAugmentation a b hab h).edge (.inr j) = s(a, b) := rfl

@[simp] theorem pairAugmentation_incident_inr (j : Fin h) (v : V) :
    v ∈ (Q.pairAugmentation a b hab h).edge (.inr j) ↔ v = a ∨ v = b := by
  simp [Sym2.mem_iff, eq_comm]

@[simp] theorem pairAugmentation_firstEnd_inl (e : E) :
    (Q.pairAugmentation a b hab h).firstEnd (.inl e) = Q.firstEnd e := rfl

@[simp] theorem pairAugmentation_secondEnd_inl (e : E) :
    (Q.pairAugmentation a b hab h).secondEnd (.inl e) = Q.secondEnd e := rfl

theorem pairAugmentation_virtual_crosses (j : Fin h) (X : Finset V) :
    (((Q.pairAugmentation a b hab h).firstEnd (.inr j) ∈ X) ≠
      ((Q.pairAugmentation a b hab h).secondEnd (.inr j) ∈ X)) ↔
      (a ∈ X) ≠ (b ∈ X) := by
  have he := (Q.pairAugmentation a b hab h).edge_eq (.inr j)
  change s((Q.pairAugmentation a b hab h).firstEnd (.inr j),
    (Q.pairAugmentation a b hab h).secondEnd (.inr j)) = s(a, b) at he
  rcases Sym2.eq_iff.mp he with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · simp only [h₁, h₂]
  · simp only [h₁, h₂, ne_comm]

/-- Restriction of an augmented cut to original copies is the original cut. -/
theorem pairAugmentation_cutOn_toLeft (C : Finset (E ⊕ Fin h)) (X : Finset V) :
    ((Q.pairAugmentation a b hab h).cutOn C X).toLeft = Q.cutOn C.toLeft X := by
  ext e
  simp

/-- All selected virtual copies cross exactly the shores separating `a` and `b`. -/
theorem pairAugmentation_cutOn_toRight (C : Finset (E ⊕ Fin h)) (X : Finset V) :
    ((Q.pairAugmentation a b hab h).cutOn C X).toRight =
      if (a ∈ X) ≠ (b ∈ X) then C.toRight else ∅ := by
  ext j
  by_cases hsep : (a ∈ X) ≠ (b ∈ X) <;>
    simp [Q.pairAugmentation_virtual_crosses a b hab h, hsep]

/-- Exact original and virtual cut-cardinality accounting. -/
theorem pairAugmentation_cutOn_card (C : Finset (E ⊕ Fin h)) (X : Finset V) :
    ((Q.pairAugmentation a b hab h).cutOn C X).card =
      (Q.cutOn C.toLeft X).card +
        if (a ∈ X) ≠ (b ∈ X) then C.toRight.card else 0 := by
  have hc := Finset.card_toLeft_add_card_toRight
    (u := (Q.pairAugmentation a b hab h).cutOn C X)
  rw [Q.pairAugmentation_cutOn_toLeft, Q.pairAugmentation_cutOn_toRight] at hc
  by_cases hsep : (a ∈ X) ≠ (b ∈ X) <;> simpa [hsep] using hc.symm

/-- The two endpoints gain precisely the selected virtual multiplicity. -/
theorem pairAugmentation_degreeOn_split (C : Finset (E ⊕ Fin h)) (v : V) :
    (Q.pairAugmentation a b hab h).degreeOn C v =
      Q.degreeOn C.toLeft v + if v = a ∨ v = b then C.toRight.card else 0 := by
  let S := C.filter (fun e => v ∈ (Q.pairAugmentation a b hab h).edge e)
  have hleft : S.toLeft = C.toLeft.filter (fun e => v ∈ Q.edge e) := by
    ext e
    simp [S]
  have hright : S.toRight = if v = a ∨ v = b then C.toRight else ∅ := by
    ext j
    by_cases hv : v = a ∨ v = b <;> simp [S, hv]
  have hc := Finset.card_toLeft_add_card_toRight (u := S)
  rw [hleft, hright] at hc
  by_cases hv : v = a ∨ v = b <;> simpa [S, degreeOn, hv] using hc.symm

/-- Original class-cut cardinalities are unchanged under the original-copy injection. -/
theorem pairAugmentation_classCutOn_original_card (classOf : V → E → K)
    (C : Finset (E ⊕ Fin h)) (v : V) (k : K) (X : Finset V) :
    ((Q.pairAugmentation a b hab h).classCutOn
      (pairAugmentationClass h classOf) C v (.inl k) X).card =
      (Q.classCutOn classOf C.toLeft v k X).card := by
  let S := (Q.pairAugmentation a b hab h).classCutOn
    (pairAugmentationClass h classOf) C v (.inl k) X
  have hleft : S.toLeft = Q.classCutOn classOf C.toLeft v k X := by
    ext e
    simp [S, classCutOn, pairAugmentationClass]
  have hright : S.toRight = ∅ := by
    ext j
    simp [S, classCutOn, pairAugmentationClass]
  have hc := Finset.card_toLeft_add_card_toRight (u := S)
  rw [hleft, hright, Finset.card_empty, Nat.add_zero] at hc
  exact hc.symm

/-- The single fresh class contains precisely the selected virtual copies
when the shore separates their ends and the specified vertex is an end. -/
theorem pairAugmentation_classCutOn_virtual_card (classOf : V → E → K)
    (C : Finset (E ⊕ Fin h)) (v : V) (X : Finset V) :
    ((Q.pairAugmentation a b hab h).classCutOn
      (pairAugmentationClass h classOf) C v (.inr ()) X).card =
      if ((a ∈ X) ≠ (b ∈ X)) ∧ (v = a ∨ v = b) then C.toRight.card else 0 := by
  let S := (Q.pairAugmentation a b hab h).classCutOn
    (pairAugmentationClass h classOf) C v (.inr ()) X
  have hleft : S.toLeft = ∅ := by
    ext e
    simp [S, classCutOn, pairAugmentationClass]
  have hright : S.toRight =
      if ((a ∈ X) ≠ (b ∈ X)) ∧ (v = a ∨ v = b) then C.toRight else ∅ := by
    ext j
    by_cases hs : (a ∈ X) ≠ (b ∈ X) <;> by_cases hv : v = a ∨ v = b <;>
      simp [S, classCutOn, pairAugmentationClass,
        Q.pairAugmentation_virtual_crosses a b hab h, hs, hv]
  have hc := Finset.card_toLeft_add_card_toRight (u := S)
  rw [hleft, hright, Finset.card_empty, Nat.zero_add] at hc
  by_cases hp : ((a ∈ X) ≠ (b ∈ X)) ∧ (v = a ∨ v = b)
  · rw [if_pos hp] at hc
    rw [if_pos hp]
    exact hc.symm
  · rw [if_neg hp] at hc
    rw [if_neg hp]
    simpa only [Finset.card_empty] using hc.symm

/-- Exact sufficient cut conditions for admissibility after adding a
single family of virtual copies. All original classes are still checked. -/
theorem pairAugmentation_admissibleOn (classOf : V → E → K)
    (C : Finset (E ⊕ Fin h))
    (hclosed : ∀ X : Finset V, (a ∈ X) = (b ∈ X) → ∀ v k,
      2 * (Q.classCutOn classOf C.toLeft v k X).card ≤ (Q.cutOn C.toLeft X).card)
    (hseparating : ∀ X : Finset V, (a ∈ X) ≠ (b ∈ X) →
      C.toRight.card ≤ (Q.cutOn C.toLeft X).card ∧
        ∀ v k, (Q.classCutOn classOf C.toLeft v k X).card ≤ C.toRight.card) :
    (Q.pairAugmentation a b hab h).AdmissibleOn (pairAugmentationClass h classOf) C := by
  intro v k X
  cases k with
  | inl k =>
    rw [Q.pairAugmentation_classCutOn_original_card, Q.pairAugmentation_cutOn_card]
    by_cases hs : (a ∈ X) ≠ (b ∈ X)
    · rw [if_pos hs]
      obtain ⟨hcut, hclass⟩ := hseparating X hs
      have hbound := hclass v k
      omega
    · rw [if_neg hs, Nat.add_zero]
      exact hclosed X (not_ne_iff.mp hs) v k
  | inr k =>
    cases k
    rw [Q.pairAugmentation_classCutOn_virtual_card, Q.pairAugmentation_cutOn_card]
    by_cases hs : (a ∈ X) ≠ (b ∈ X)
    · have hcut := (hseparating X hs).1
      rw [if_pos hs]
      by_cases hv : v = a ∨ v = b
      · rw [if_pos ⟨hs, hv⟩]
        omega
      · rw [if_neg (fun hp => hv hp.2)]
        omega
    · rw [if_neg hs, if_neg (fun hp => hs hp.1)]
      omega

/-- Compatibility of an augmented selected set restricts to the original classes. -/
theorem Compatible.original_of_pairAugmentation {classOf : V → E → K}
    {C : Finset (E ⊕ Fin h)}
    (hC : (Q.pairAugmentation a b hab h).Compatible (pairAugmentationClass h classOf) C) :
    Q.Compatible classOf C.toLeft := by
  intro v e he hve f hf hvf hclass
  apply Sum.inl_injective
  apply hC v (.inl e) (Finset.mem_toLeft.mp he) hve
    (.inl f) (Finset.mem_toLeft.mp hf) hvf
  exact congrArg Sum.inl hclass

/-- Compatibility forces at most one copy from the virtual parallel family. -/
theorem Compatible.pairVirtual_card_le_one {classOf : V → E → K}
    {C : Finset (E ⊕ Fin h)}
    (hC : (Q.pairAugmentation a b hab h).Compatible (pairAugmentationClass h classOf) C) :
    C.toRight.card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro j hj l hl
  apply Sum.inr_injective
  apply hC a (.inr j) (Finset.mem_toRight.mp hj) ?_
    (.inr l) (Finset.mem_toRight.mp hl) ?_ rfl <;> simp

/-- A compatible augmented circuit always retains an original copy. -/
theorem IsCircuit.pairOriginal_nonempty {classOf : V → E → K}
    {C : Finset (E ⊕ Fin h)}
    (hC : (Q.pairAugmentation a b hab h).IsCircuit C)
    (hcompatible : (Q.pairAugmentation a b hab h).Compatible
      (pairAugmentationClass h classOf) C) : C.toLeft.Nonempty := by
  by_contra hn
  have hl : C.toLeft = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
  have hr := Compatible.pairVirtual_card_le_one Q a b hab h hcompatible
  have hsplit := Finset.card_toLeft_add_card_toRight (u := C)
  have hc : C.card ≤ 1 := by
    rw [hl, Finset.card_empty, Nat.zero_add] at hsplit
    omega
  obtain ⟨e, he⟩ := hC.1
  cases e with
  | inl e =>
    have he' : e ∈ C.toLeft := Finset.mem_toLeft.mpr he
    simp [hl] at he'
  | inr j =>
    have ha : a ∈ (Q.pairAugmentation a b hab h).edgeSupport C := by
      exact (Q.pairAugmentation a b hab h).mem_edgeSupport C a |>.mpr
        ⟨.inr j, he, by simp⟩
    have hd := hC.2.1 a ha
    have hdle : (Q.pairAugmentation a b hab h).degreeOn C a ≤ C.card :=
      Finset.card_filter_le _ _
    omega

/-- Adding the virtual family repairs precisely the two specified parity defects. -/
theorem pairAugmentation_even_degreeOn_of_parity (C : Finset (E ⊕ Fin h))
    (hparity : ∀ v, Q.degreeOn C.toLeft v % 2 =
      if v = a ∨ v = b then C.toRight.card % 2 else 0) :
    ∀ v, Even ((Q.pairAugmentation a b hab h).degreeOn C v) := by
  intro v
  rw [Q.pairAugmentation_degreeOn_split]
  apply Nat.even_iff.mpr
  have hp := hparity v
  by_cases hv : v = a ∨ v = b <;> simp only [hv, if_true, if_false] at * <;> omega

/-- One virtual copy leaves degree one at its two ends and even original
degree elsewhere. The cardinality estimate counts actual original copies. -/
theorem IsCircuit.one_pairVirtual_original [Fintype V]
    {C : Finset (E ⊕ Fin h)}
    (hC : (Q.pairAugmentation a b hab h).IsCircuit C)
    (hvirtual : C.toRight.card = 1) :
    C.toLeft.card + 1 ≤ Fintype.card V ∧
      (∀ v, v = a ∨ v = b → Q.degreeOn C.toLeft v = 1) ∧
      ∀ v, Odd (Q.degreeOn C.toLeft v) ↔ v = a ∨ v = b := by
  have hcard := hC.card_le
  have hsplit := Finset.card_toLeft_add_card_toRight (u := C)
  have hend (v : V) (hv : v = a ∨ v = b) : Q.degreeOn C.toLeft v = 1 := by
    have hd := Q.pairAugmentation_degreeOn_split a b hab h C v
    rw [if_pos hv, hvirtual] at hd
    have hs : v ∈ (Q.pairAugmentation a b hab h).edgeSupport C :=
      ((Q.pairAugmentation a b hab h).degreeOn_pos_iff C v).mp (by omega)
    have hc := hC.2.1 v hs
    omega
  refine ⟨by omega, hend, ?_⟩
  intro v
  by_cases hv : v = a ∨ v = b
  · simp [hv, hend v hv]
  · have hd := Q.pairAugmentation_degreeOn_split a b hab h C v
    rw [if_neg hv, Nat.add_zero] at hd
    have he := Nat.even_iff.mp
      (IsCircuit.even_degreeOn (Q.pairAugmentation a b hab h) hC v)
    rw [hd] at he
    rw [Nat.odd_iff]
    constructor
    · intro ho
      omega
    · exact fun hp => (hv hp).elim

theorem pairAugmentation_edgeSupport_of_no_virtual {C : Finset (E ⊕ Fin h)}
    (hvirtual : C.toRight = ∅) :
    (Q.pairAugmentation a b hab h).edgeSupport C = Q.edgeSupport C.toLeft := by
  ext v
  simp only [mem_edgeSupport]
  constructor
  · rintro ⟨e, he, hve⟩
    cases e with
    | inl e => exact ⟨e, Finset.mem_toLeft.mpr he, hve⟩
    | inr j =>
      have hj : j ∈ C.toRight := Finset.mem_toRight.mpr he
      simp [hvirtual] at hj
  · rintro ⟨e, he, hve⟩
    exact ⟨.inl e, Finset.mem_toLeft.mp he, hve⟩

/-- A part with no virtual copy is an actual original circuit, including
its connectedness, rather than only an even-degree selected set. -/
theorem IsCircuit.no_pairVirtual_original {C : Finset (E ⊕ Fin h)}
    (hC : (Q.pairAugmentation a b hab h).IsCircuit C)
    (hvirtual : C.toRight = ∅) : Q.IsCircuit C.toLeft := by
  have hs := Q.pairAugmentation_edgeSupport_of_no_virtual a b hab h hvirtual
  have hd (v : V) : (Q.pairAugmentation a b hab h).degreeOn C v =
      Q.degreeOn C.toLeft v := by
    simpa [hvirtual] using Q.pairAugmentation_degreeOn_split a b hab h C v
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨e, he⟩ := hC.1
    cases e with
    | inl e => exact ⟨e, Finset.mem_toLeft.mpr he⟩
    | inr j =>
      have hj : j ∈ C.toRight := Finset.mem_toRight.mpr he
      simp [hvirtual] at hj
  · intro v hv
    rw [← hd]
    exact hC.2.1 v (hs.symm ▸ hv)
  · intro X hX hne hproper
    obtain ⟨e, he⟩ := hC.2.2 X (hs.symm ▸ hX) hne (hs.symm ▸ hproper)
    obtain ⟨heC, hecut⟩ := (Q.pairAugmentation a b hab h).mem_cutOn C X e |>.mp he
    cases e with
    | inl e =>
      exact ⟨e, Q.mem_cutOn C.toLeft X e |>.mpr ⟨Finset.mem_toLeft.mpr heC, hecut⟩⟩
    | inr j =>
      have hj : j ∈ C.toRight := Finset.mem_toRight.mpr heC
      simp [hvirtual] at hj

variable [Fintype E]

/-- The full augmented cut gains `h` copies exactly when it separates `a,b`. -/
theorem pairAugmentation_cutOn_univ_card (X : Finset V) :
    ((Q.pairAugmentation a b hab h).cutOn univ X).card =
      (Q.cutOn univ X).card + if (a ∈ X) ≠ (b ∈ X) then h else 0 := by
  have hl : (univ : Finset (E ⊕ Fin h)).toLeft = univ := by ext e; simp
  have hr : (univ : Finset (E ⊕ Fin h)).toRight = univ := by ext j; simp
  simpa [hl, hr] using Q.pairAugmentation_cutOn_card a b hab h univ X

/-- Full-degree accounting, with every parallel virtual copy counted separately. -/
theorem pairAugmentation_degree (v : V) :
    (Q.pairAugmentation a b hab h).degree v =
      Q.degree v + if v = a ∨ v = b then h else 0 := by
  have hl : (univ : Finset (E ⊕ Fin h)).toLeft = univ := by ext e; simp
  have hr : (univ : Finset (E ⊕ Fin h)).toRight = univ := by ext j; simp
  have hd := Q.pairAugmentation_degreeOn_split a b hab h univ v
  simpa [hl, hr, degreeOn, degree, incidenceEdges] using hd

/-- The full-copy form of the augmented admissibility bridge. -/
theorem pairAugmentation_admissibleOn_univ (classOf : V → E → K)
    (hclosed : ∀ X : Finset V, (a ∈ X) = (b ∈ X) → ∀ v k,
      2 * (Q.classCutOn classOf univ v k X).card ≤ (Q.cutOn univ X).card)
    (hseparating : ∀ X : Finset V, (a ∈ X) ≠ (b ∈ X) →
      h ≤ (Q.cutOn univ X).card ∧
        ∀ v k, (Q.classCutOn classOf univ v k X).card ≤ h) :
    (Q.pairAugmentation a b hab h).AdmissibleOn (pairAugmentationClass h classOf) univ := by
  have hl : (univ : Finset (E ⊕ Fin h)).toLeft = univ := by ext e; simp
  have hr : (univ : Finset (E ⊕ Fin h)).toRight = univ := by ext j; simp
  apply Q.pairAugmentation_admissibleOn a b hab h classOf univ
  · simpa [hl] using hclosed
  · simpa [hl, hr] using hseparating

namespace CompatibleCircuitPartition

variable {Q a b hab h} {classOf : V → E → K}
variable (P : (Q.pairAugmentation a b hab h).CompatibleCircuitPartition
  (pairAugmentationClass h classOf) univ)

/-- The actual augmented parts containing a virtual copy. -/
noncomputable def pairVirtualParts : Finset (Finset (E ⊕ Fin h)) :=
  P.parts.filter (fun D => D.toRight.card = 1)

@[simp] theorem mem_pairVirtualParts (D : Finset (E ⊕ Fin h)) :
    D ∈ P.pairVirtualParts ↔ D ∈ P.parts ∧ D.toRight.card = 1 := by
  simp [pairVirtualParts]

/-- Restricting different parts to original copies preserves disjointness. -/
theorem pairOriginal_parts_disjoint {D D' : Finset (E ⊕ Fin h)}
    (hD : D ∈ P.parts) (hD' : D' ∈ P.parts) (hne : D ≠ D') :
    Disjoint D.toLeft D'.toLeft := by
  apply Finset.disjoint_left.mpr
  intro e he he'
  exact Finset.disjoint_left.mp (P.disjoint D hD D' hD' hne)
    (Finset.mem_toLeft.mp he) (Finset.mem_toLeft.mp he')

/-- Every original copy is retained by exactly one original restriction. -/
theorem pairOriginal_parts_cover : P.parts.biUnion Finset.toLeft = univ := by
  have hfull : P.parts.biUnion id = (univ : Finset (E ⊕ Fin h)) := by
    convert P.cover using 1
    congr
    exact Subsingleton.elim _ _
  ext e
  constructor
  · intro _
    exact Finset.mem_univ _
  · intro _
    have he : Sum.inl e ∈ P.parts.biUnion id := by rw [hfull]; simp
    obtain ⟨D, hD, heD⟩ := Finset.mem_biUnion.mp he
    exact Finset.mem_biUnion.mpr ⟨D, hD, Finset.mem_toLeft.mpr heD⟩

/-- Original restriction does not identify two different circuit indices. -/
theorem pairOriginal_restriction_injective :
    Set.InjOn (fun D : Finset (E ⊕ Fin h) => D.toLeft) P.parts := by
  intro D hD D' hD' heq
  change D.toLeft = D'.toLeft at heq
  by_contra hne
  obtain ⟨e, he⟩ := IsCircuit.pairOriginal_nonempty Q a b hab h
    (P.circuit D hD) (P.compatible D hD)
  exact Finset.disjoint_left.mp (P.pairOriginal_parts_disjoint hD hD' hne)
    he (heq ▸ he)

/-- All virtual copies are counted once among the actual circuit parts. -/
theorem pairVirtual_card_sum : (∑ D ∈ P.parts, D.toRight.card) = h := by
  have hfull : P.parts.biUnion id = (univ : Finset (E ⊕ Fin h)) := by
    convert P.cover using 1
    congr
    exact Subsingleton.elim _ _
  have hdisjoint : P.parts.toSet.PairwiseDisjoint Finset.toRight := by
    intro D hD D' hD' hne
    apply Finset.disjoint_left.mpr
    intro j hj hj'
    exact Finset.disjoint_left.mp (P.disjoint D hD D' hD' hne)
      (Finset.mem_toRight.mp hj) (Finset.mem_toRight.mp hj')
  have hcover : P.parts.biUnion Finset.toRight = (univ : Finset (Fin h)) := by
    ext j
    constructor
    · intro _
      exact Finset.mem_univ _
    · intro _
      have hj : Sum.inr j ∈ P.parts.biUnion id := by rw [hfull]; simp
      obtain ⟨D, hD, hjD⟩ := Finset.mem_biUnion.mp hj
      exact Finset.mem_biUnion.mpr ⟨D, hD, Finset.mem_toRight.mpr hjD⟩
  rw [← Finset.card_biUnion hdisjoint, hcover]
  simp

/-- Exactly `h` actual circuit parts contain one virtual copy. -/
theorem pairVirtualParts_card : P.pairVirtualParts.card = h := by
  have hpart (D : Finset (E ⊕ Fin h)) (hD : D ∈ P.parts) :
      D.toRight.card = if D.toRight.card = 1 then 1 else 0 := by
    have hle := Compatible.pairVirtual_card_le_one Q a b hab h (P.compatible D hD)
    by_cases hone : D.toRight.card = 1
    · rw [if_pos hone]
      exact hone
    · rw [if_neg hone]
      omega
  have hsum : (∑ D ∈ P.parts, D.toRight.card) = P.pairVirtualParts.card := by
    calc
      _ = ∑ D ∈ P.parts, if D.toRight.card = 1 then 1 else 0 :=
        Finset.sum_congr rfl hpart
      _ = _ := by simp [pairVirtualParts]
  rw [← hsum]
  exact P.pairVirtual_card_sum

end CompatibleCircuitPartition

end Overfull.Multigraph
