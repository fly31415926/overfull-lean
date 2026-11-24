import Overfull.CompatibleCircuits.Virtual

/-!
# Counting virtual families in an actual circuit partition

The indices remain the original augmented circuit parts. In particular,
counting never takes an image under restriction to original copies, which
could identify distinct indices. A supplied genuine compatible partition
accounts for all virtual copies exactly once; no existence assertion is used.
-/

namespace Overfull.Multigraph

open Finset Classical
open scoped BigOperators

variable {E K : Type*} [Fintype E] {Q : Multigraph (Fin 4) E}
  {h : ℕ} {classOf : Fin 4 → E → K}

namespace CompatibleCircuitPartition

variable (P : (Q.virtualAugmentation h).CompatibleCircuitPartition
  (virtualClass classOf) univ)

/-- The actual augmented parts containing two virtual copies. -/
noncomputable def twoVirtualParts : Finset (Finset (E ⊕ (Bool × Fin h))) :=
  P.parts.filter (fun D => D.toRight.card = 2)

/-- The actual augmented parts containing one virtual copy of family `b`. -/
noncomputable def oneVirtualParts (b : Bool) : Finset (Finset (E ⊕ (Bool × Fin h))) :=
  P.parts.filter (fun D => D.toRight.card = 1 ∧ (virtualFamily D b).card = 1)

@[simp] theorem mem_twoVirtualParts (D : Finset (E ⊕ (Bool × Fin h))) :
    D ∈ P.twoVirtualParts ↔ D ∈ P.parts ∧ D.toRight.card = 2 := by
  simp [twoVirtualParts]

@[simp] theorem mem_oneVirtualParts (b : Bool) (D : Finset (E ⊕ (Bool × Fin h))) :
    D ∈ P.oneVirtualParts b ↔
      D ∈ P.parts ∧ D.toRight.card = 1 ∧ (virtualFamily D b).card = 1 := by
  simp [oneVirtualParts]

/-- Original-copy restrictions of distinct augmented parts are disjoint. -/
theorem original_parts_disjoint {D D' : Finset (E ⊕ (Bool × Fin h))}
    (hD : D ∈ P.parts) (hD' : D' ∈ P.parts) (hne : D ≠ D') :
    Disjoint D.toLeft D'.toLeft := by
  apply Finset.disjoint_left.mpr
  intro e he he'
  exact Finset.disjoint_left.mp (P.disjoint D hD D' hD' hne)
    (Finset.mem_toLeft.mp he) (Finset.mem_toLeft.mp he')

/-- Every virtual copy of one family is counted once among the actual parts. -/
theorem virtual_family_card_sum (b : Bool) :
    (∑ D ∈ P.parts, (virtualFamily D b).card) = h := by
  have hfull : P.parts.biUnion id = (univ : Finset (E ⊕ (Bool × Fin h))) := by
    convert P.cover using 1
    congr
    exact Subsingleton.elim _ _
  have hdisjoint : P.parts.toSet.PairwiseDisjoint (fun D => virtualFamily D b) := by
    intro D hD D' hD' hne
    apply Finset.disjoint_left.mpr
    intro e he he'
    exact Finset.disjoint_left.mp (P.disjoint D hD D' hD' hne)
      ((mem_virtualFamily D b e).mp he).1 ((mem_virtualFamily D' b e).mp he').1
  have hcover : P.parts.biUnion (fun D => virtualFamily D b) =
      virtualFamily (univ : Finset (E ⊕ (Bool × Fin h))) b := by
    ext e
    constructor
    · intro he
      obtain ⟨D, _, heD⟩ := Finset.mem_biUnion.mp he
      exact (mem_virtualFamily _ b e).mpr
        ⟨Finset.mem_univ _, ((mem_virtualFamily D b e).mp heD).2⟩
    · intro he
      have heb := ((mem_virtualFamily _ b e).mp he).2
      have hcopy : Sum.inr e ∈ P.parts.biUnion id := by
        rw [hfull]
        exact Finset.mem_univ _
      obtain ⟨D, hD, heD⟩ := Finset.mem_biUnion.mp hcopy
      exact Finset.mem_biUnion.mpr ⟨D, hD, (mem_virtualFamily D b e).mpr ⟨heD, heb⟩⟩
  rw [← Finset.card_biUnion hdisjoint, hcover, virtualFamily_univ_card]

/-- If `r` parts have two virtual copies and `u_b` have one copy of family
`b`, then `u_b + r = h`, derived from the genuine partition. -/
theorem oneVirtualParts_card_add_twoVirtualParts_card (b : Bool) :
    (P.oneVirtualParts b).card + P.twoVirtualParts.card = h := by
  have hpart (D : Finset (E ⊕ (Bool × Fin h))) (hD : D ∈ P.parts) :
      (virtualFamily D b).card =
        (if D.toRight.card = 1 ∧ (virtualFamily D b).card = 1 then 1 else 0) +
        (if D.toRight.card = 2 then 1 else 0) := by
    have hcompatible := P.compatible D hD
    have hle := Compatible.virtual_card_le_two Q hcompatible
    have hfamily := Compatible.virtualFamily_card_le_one Q hcompatible b
    have hsubset : virtualFamily D b ⊆ D.toRight := Finset.filter_subset _ _
    have hsubcard := Finset.card_le_card hsubset
    by_cases htwo : D.toRight.card = 2
    · have hcount :=
        (IsCircuit.two_virtual_original Q (P.circuit D hD) hcompatible htwo).2.2 b
      simp [htwo, hcount]
    · by_cases hzero : (virtualFamily D b).card = 0
      · simp [htwo, hzero]
      · have hcount : (virtualFamily D b).card = 1 := by omega
        have hone : D.toRight.card = 1 := by omega
        simp [hcount, hone]
  have hsum : (∑ D ∈ P.parts, (virtualFamily D b).card) =
      (P.oneVirtualParts b).card + P.twoVirtualParts.card := by
    calc
      _ = ∑ D ∈ P.parts,
          ((if D.toRight.card = 1 ∧ (virtualFamily D b).card = 1 then 1 else 0) +
          (if D.toRight.card = 2 then 1 else 0)) := Finset.sum_congr rfl hpart
      _ = _ := by simp [Finset.sum_add_distrib, oneVirtualParts, twoVirtualParts]
  rw [← hsum]
  exact P.virtual_family_card_sum b

/-- Both one-virtual-copy families have the same number of actual parts. -/
theorem oneVirtualParts_card_eq :
    (P.oneVirtualParts false).card = (P.oneVirtualParts true).card := by
  have h₀ := P.oneVirtualParts_card_add_twoVirtualParts_card false
  have h₁ := P.oneVirtualParts_card_add_twoVirtualParts_card true
  omega

/-- The common size is exactly `h - r`, where `r` counts two-virtual parts. -/
theorem oneVirtualParts_card_eq_sub (b : Bool) :
    (P.oneVirtualParts b).card = h - P.twoVirtualParts.card := by
  have hcount := P.oneVirtualParts_card_add_twoVirtualParts_card b
  omega

/-- The two-virtual primary pieces and either one-virtual family total `h`. -/
theorem twoVirtualParts_card_add_oneVirtualParts_card (b : Bool) :
    P.twoVirtualParts.card + (P.oneVirtualParts b).card = h := by
  rw [Nat.add_comm]
  exact P.oneVirtualParts_card_add_twoVirtualParts_card b

end CompatibleCircuitPartition

end Overfull.Multigraph
