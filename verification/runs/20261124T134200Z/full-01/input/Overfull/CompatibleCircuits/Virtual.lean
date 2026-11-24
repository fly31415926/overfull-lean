import Overfull.CompatibleCircuits.Counting
import Mathlib.Data.Finset.Sum

/-!
# Virtual perfect-matching copies on four labels

The augmented edge type retains every original copy and adds two disjoint
families of virtual copies, on `01` and `23`. All virtual incidences have one
new forbidden class. The results below classify an already supplied compatible
circuit; none asserts that a compatible circuit decomposition exists.
-/

namespace Overfull.Multigraph

open Finset Classical

/-- The two pairs of the fixed label perfect matching. -/
def virtualPair : Bool → Sym2 (Fin 4)
  | false => s(0, 1)
  | true => s(2, 3)

/-- The unique virtual family incident with a label. -/
def virtualSide (v : Fin 4) : Bool := decide (2 ≤ v.val)

theorem virtualPair_incident (v : Fin 4) (b : Bool) :
    v ∈ virtualPair b ↔ virtualSide v = b := by
  fin_cases v <;> cases b <;> decide

private def virtualAnchor : Bool → Fin 4
  | false => 0
  | true => 2

private theorem virtualAnchor_incident (b : Bool) :
    virtualAnchor b ∈ virtualPair b := by
  cases b <;> decide

variable {E K : Type*} (Q : Multigraph (Fin 4) E)

/-- Add `h` distinct virtual copies of each of `01` and `23`. -/
def virtualAugmentation (h : ℕ) : Multigraph (Fin 4) (E ⊕ (Bool × Fin h)) where
  edge
    | .inl e => Q.edge e
    | .inr e => virtualPair e.1
  loopless e := by
    cases e with
    | inl e => exact Q.loopless e
    | inr e =>
      rcases e with ⟨b, j⟩
      change ¬ (virtualPair b).IsDiag
      cases b <;> decide

/-- Original classes remain distinct from the one new virtual class. -/
def virtualClass {h : ℕ} (classOf : Fin 4 → E → K) :
    Fin 4 → (E ⊕ (Bool × Fin h)) → K ⊕ Unit
  | v, .inl e => .inl (classOf v e)
  | _, .inr _ => .inr ()

@[simp] theorem virtualAugmentation_edge_inl (h : ℕ) (e : E) :
    (Q.virtualAugmentation h).edge (.inl e) = Q.edge e := rfl

@[simp] theorem virtualAugmentation_edge_inr (h : ℕ) (e : Bool × Fin h) :
    (Q.virtualAugmentation h).edge (.inr e) = virtualPair e.1 := rfl

@[simp] theorem virtualAugmentation_firstEnd_inl (h : ℕ) (e : E) :
    (Q.virtualAugmentation h).firstEnd (.inl e) = Q.firstEnd e := rfl

@[simp] theorem virtualAugmentation_secondEnd_inl (h : ℕ) (e : E) :
    (Q.virtualAugmentation h).secondEnd (.inl e) = Q.secondEnd e := rfl

variable {h : ℕ}

/-- Selected copies of one virtual family, retaining both copy coordinates. -/
noncomputable def virtualFamily (C : Finset (E ⊕ (Bool × Fin h))) (b : Bool) :
    Finset (Bool × Fin h) := C.toRight.filter (fun e => e.1 = b)

@[simp] theorem mem_virtualFamily (C : Finset (E ⊕ (Bool × Fin h)))
    (b : Bool) (e : Bool × Fin h) :
    e ∈ virtualFamily C b ↔ Sum.inr e ∈ C ∧ e.1 = b := by
  simp [virtualFamily]

theorem virtualFamily_card_sum (C : Finset (E ⊕ (Bool × Fin h))) :
    (virtualFamily C false).card + (virtualFamily C true).card = C.toRight.card := by
  have hfilter : C.toRight.filter (fun e => ¬e.1 = false) = virtualFamily C true := by
    ext e
    cases he : e.1 <;> simp [virtualFamily, he]
  simpa only [virtualFamily, hfilter] using
    (Finset.filter_card_add_filter_neg_card_eq_card (s := C.toRight)
      (fun e => e.1 = false))

/-- Compatibility survives restriction to the original, unchanged copies. -/
theorem Compatible.original_of_virtual {classOf : Fin 4 → E → K}
    {C : Finset (E ⊕ (Bool × Fin h))}
    (hC : (Q.virtualAugmentation h).Compatible (virtualClass classOf) C) :
    Q.Compatible classOf C.toLeft := by
  intro v e he hve f hf hvf hclass
  apply Sum.inl_injective
  apply hC v (.inl e) (Finset.mem_toLeft.mp he) hve
    (.inl f) (Finset.mem_toLeft.mp hf) hvf
  exact congrArg Sum.inl hclass

/-- A compatible selected set uses at most one copy of each virtual family. -/
theorem Compatible.virtualFamily_card_le_one {classOf : Fin 4 → E → K}
    {C : Finset (E ⊕ (Bool × Fin h))}
    (hC : (Q.virtualAugmentation h).Compatible (virtualClass classOf) C)
    (b : Bool) : (virtualFamily C b).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro e he f hf
  obtain ⟨he, heb⟩ := mem_virtualFamily C b e |>.mp he
  obtain ⟨hf, hfb⟩ := mem_virtualFamily C b f |>.mp hf
  apply Sum.inr_injective
  apply hC (virtualAnchor b) (.inr e) he ?_ (.inr f) hf ?_ rfl
  · simpa only [virtualAugmentation_edge_inr, heb] using virtualAnchor_incident b
  · simpa only [virtualAugmentation_edge_inr, hfb] using virtualAnchor_incident b

/-- There are at most two virtual copies in any compatible selected set. -/
theorem Compatible.virtual_card_le_two {classOf : Fin 4 → E → K}
    {C : Finset (E ⊕ (Bool × Fin h))}
    (hC : (Q.virtualAugmentation h).Compatible (virtualClass classOf) C) :
    C.toRight.card ≤ 2 := by
  have h₀ := Compatible.virtualFamily_card_le_one Q hC false
  have h₁ := Compatible.virtualFamily_card_le_one Q hC true
  have hsum := virtualFamily_card_sum C
  omega

/-- Degree accounting separates original copies from the unique virtual
family incident with each label. -/
theorem virtual_degreeOn_split (C : Finset (E ⊕ (Bool × Fin h))) (v : Fin 4) :
    (Q.virtualAugmentation h).degreeOn C v =
      Q.degreeOn C.toLeft v + (virtualFamily C (virtualSide v)).card := by
  let S := C.filter (fun e => v ∈ (Q.virtualAugmentation h).edge e)
  have hleft : S.toLeft = C.toLeft.filter (fun e => v ∈ Q.edge e) := by
    ext e
    simp [S]
  have hright : S.toRight = virtualFamily C (virtualSide v) := by
    ext e
    simp [S, virtualFamily, virtualPair_incident, eq_comm]
  have hcard := Finset.card_toLeft_add_card_toRight (u := S)
  rw [hleft, hright] at hcard
  convert hcard.symm using 1 <;> simp only [S, degreeOn] <;> congr

/-- A compatible circuit containing two virtual copies contains one of each
family. Its two original copies have degree one at every quotient label. -/
theorem IsCircuit.two_virtual_original {classOf : Fin 4 → E → K}
    {C : Finset (E ⊕ (Bool × Fin h))}
    (hC : (Q.virtualAugmentation h).IsCircuit C)
    (hcompatible : (Q.virtualAugmentation h).Compatible (virtualClass classOf) C)
    (hvirtual : C.toRight.card = 2) :
    C.toLeft.card = 2 ∧ (∀ v : Fin 4, Q.degreeOn C.toLeft v = 1) ∧
      ∀ b : Bool, (virtualFamily C b).card = 1 := by
  have h₀ := Compatible.virtualFamily_card_le_one Q hcompatible false
  have h₁ := Compatible.virtualFamily_card_le_one Q hcompatible true
  have hsum := virtualFamily_card_sum C
  have hfamily (b : Bool) : (virtualFamily C b).card = 1 := by
    cases b <;> omega
  have hsupport (v : Fin 4) : v ∈ (Q.virtualAugmentation h).edgeSupport C := by
    apply (Q.virtualAugmentation h).degreeOn_pos_iff C v |>.mp
    rw [Q.virtual_degreeOn_split, hfamily]
    omega
  have hdegree (v : Fin 4) : Q.degreeOn C.toLeft v = 1 := by
    have hdegree := hC.2.1 v (hsupport v)
    rw [Q.virtual_degreeOn_split, hfamily] at hdegree
    omega
  have huniv : (Q.virtualAugmentation h).edgeSupport C = univ :=
    Finset.eq_univ_iff_forall.mpr hsupport
  have hcard := hC.card_eq_support_card
  rw [huniv] at hcard
  norm_num at hcard
  have hsplit := Finset.card_toLeft_add_card_toRight (u := C)
  exact ⟨by omega, hdegree, hfamily⟩

/-- With exactly one virtual copy, at most three original copies remain.
Their odd projected degrees occur precisely at the ends of that virtual pair. -/
theorem IsCircuit.one_virtual_original {C : Finset (E ⊕ (Bool × Fin h))}
    (hC : (Q.virtualAugmentation h).IsCircuit C)
    (hvirtual : C.toRight.card = 1) :
    C.toLeft.card ≤ 3 ∧ ∃ e : Bool × Fin h, C.toRight = {e} ∧
      ∀ v : Fin 4, Odd (Q.degreeOn C.toLeft v) ↔ v ∈ virtualPair e.1 := by
  have hcard := hC.card_le
  have hsplit := Finset.card_toLeft_add_card_toRight (u := C)
  norm_num at hcard
  obtain ⟨e, he⟩ := Finset.card_eq_one.mp hvirtual
  refine ⟨by omega, e, he, ?_⟩
  intro v
  have hdegree := Q.virtual_degreeOn_split C v
  have heven := IsCircuit.even_degreeOn (Q.virtualAugmentation h) hC v
  rw [Nat.even_iff] at heven
  by_cases hv : v ∈ virtualPair e.1
  · have hside := (virtualPair_incident v e.1).mp hv
    have hfamily : (virtualFamily C (virtualSide v)).card = 1 := by
      simp [virtualFamily, he, hside, Finset.filter_singleton]
    rw [hfamily] at hdegree
    constructor
    · intro _
      exact hv
    · intro _
      apply Nat.odd_iff.mpr
      omega
  · have hside : virtualSide v ≠ e.1 := (virtualPair_incident v e.1).not.mp hv
    have hfamily : (virtualFamily C (virtualSide v)).card = 0 := by
      simp [virtualFamily, he, Ne.symm hside, Finset.filter_singleton]
    rw [hfamily] at hdegree
    constructor
    · intro hodd
      rw [Nat.odd_iff] at hodd
      omega
    · intro hv'
      exact (hv hv').elim

theorem virtual_edgeSupport_of_no_virtual {C : Finset (E ⊕ (Bool × Fin h))}
    (hvirtual : C.toRight = ∅) :
    (Q.virtualAugmentation h).edgeSupport C = Q.edgeSupport C.toLeft := by
  ext v
  simp only [mem_edgeSupport]
  constructor
  · rintro ⟨e, he, hve⟩
    cases e with
    | inl e => exact ⟨e, Finset.mem_toLeft.mpr he, hve⟩
    | inr e =>
      have he' : e ∈ C.toRight := Finset.mem_toRight.mpr he
      simp [hvirtual] at he'
  · rintro ⟨e, he, hve⟩
    exact ⟨.inl e, Finset.mem_toLeft.mp he, hve⟩

/-- Removing an empty virtual part retains the actual original circuit,
including its connectivity, rather than only its degree sequence. -/
theorem IsCircuit.no_virtual_original {C : Finset (E ⊕ (Bool × Fin h))}
    (hC : (Q.virtualAugmentation h).IsCircuit C)
    (hvirtual : C.toRight = ∅) : Q.IsCircuit C.toLeft := by
  have hsupport := Q.virtual_edgeSupport_of_no_virtual hvirtual
  have hdegree (v : Fin 4) :
      (Q.virtualAugmentation h).degreeOn C v = Q.degreeOn C.toLeft v := by
    simpa [virtualFamily, hvirtual] using Q.virtual_degreeOn_split C v
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨e, he⟩ := hC.1
    cases e with
    | inl e => exact ⟨e, Finset.mem_toLeft.mpr he⟩
    | inr e =>
      have he' : e ∈ C.toRight := Finset.mem_toRight.mpr he
      simp [hvirtual] at he'
  · intro v hv
    rw [← hdegree]
    exact hC.2.1 v (hsupport.symm ▸ hv)
  · intro X hX hne hproper
    have hX' : X ⊆ (Q.virtualAugmentation h).edgeSupport C := hsupport.symm ▸ hX
    have hproper' : X ≠ (Q.virtualAugmentation h).edgeSupport C :=
      hsupport.symm ▸ hproper
    obtain ⟨e, he⟩ := hC.2.2 X hX' hne hproper'
    obtain ⟨heC, hecut⟩ := (Q.virtualAugmentation h).mem_cutOn C X e |>.mp he
    cases e with
    | inl e =>
      refine ⟨e, Q.mem_cutOn C.toLeft X e |>.mpr ⟨Finset.mem_toLeft.mpr heC, ?_⟩⟩
      exact hecut
    | inr e =>
      have he' : e ∈ C.toRight := Finset.mem_toRight.mpr heC
      simp [hvirtual] at he'

theorem virtualFamily_univ_card [Fintype E] (b : Bool) :
    (virtualFamily (univ : Finset (E ⊕ (Bool × Fin h))) b).card = h := by
  have hfamily : virtualFamily (univ : Finset (E ⊕ (Bool × Fin h))) b =
      (univ : Finset (Fin h)).image (fun j => (b, j)) := by
    ext ⟨c, j⟩
    simp [virtualFamily, eq_comm]
  rw [hfamily, Finset.card_image_of_injective _
    (fun _ _ hpair => Prod.mk.inj hpair |>.2)]
  simp

/-- Every label gains exactly `h` incidences from its virtual family. -/
theorem virtualAugmentation_degree [Fintype E] (v : Fin 4) :
    (Q.virtualAugmentation h).degree v = Q.degree v + h := by
  have hleft : (univ : Finset (E ⊕ (Bool × Fin h))).toLeft = univ := by
    ext e
    simp
  have hsplit := Q.virtual_degreeOn_split (h := h) univ v
  rw [hleft, virtualFamily_univ_card] at hsplit
  exact hsplit

end Overfull.Multigraph
