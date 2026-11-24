import Overfull.Terminal.PartLabels

/-!
# Selecting the even core in the two-odd case

The three-core host has either three even parts or one even part and two
odd parts.  These lemmas provide the actual distinct indices and retain
the covering condition after putting the even part first.
-/

namespace Overfull.Terminal

open Finset Classical

/-- Two distinct indices among three have one remaining index. -/
theorem exists_third_core_index (a b : Fin 3) (hab : a ≠ b) :
    ∃ c : Fin 3, c ≠ a ∧ c ≠ b ∧ ∀ i : Fin 3, i = c ∨ i = a ∨ i = b := by
  have ha := a.isLt
  have hb := b.isLt
  have hab' : a.val ≠ b.val := fun h => hab (Fin.ext h)
  let c : Fin 3 := ⟨3 - a.val - b.val, by omega⟩
  have hc : c.val = 3 - a.val - b.val := rfl
  refine ⟨c, ?_, ?_, ?_⟩
  · intro h
    have he := congrArg Fin.val h
    omega
  · intro h
    have he := congrArg Fin.val h
    omega
  · intro i
    have hi := i.isLt
    simp only [Fin.ext_iff]
    omega

/-- Parity determines actual core indices; it is not an extra structural
hypothesis in the three-core terminal theorem. -/
theorem three_core_even_or_two_odd {V : Type*} [Fintype V]
    (U : Fin 3 → Finset V)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hcover : ∀ v, ∃ i, v ∈ U i) (hV : Even (Fintype.card V)) :
    (∀ i, Even (U i).card) ∨
      ∃ c a b : Fin 3, c ≠ a ∧ c ≠ b ∧ a ≠ b ∧
        (∀ i : Fin 3, i = c ∨ i = a ∨ i = b) ∧
        Even (U c).card ∧ Odd (U a).card ∧ Odd (U b).card := by
  rcases three_core_parity U hdisjoint hcover hV with heven | ⟨a, b, hab, hp⟩
  · exact Or.inl (fun i => Nat.even_iff.mpr (heven i))
  · obtain ⟨c, hca, hcb, hindices⟩ := exists_third_core_index a b hab
    refine Or.inr ⟨c, a, b, hca, hcb, hab, hindices, ?_, ?_, ?_⟩
    · apply Nat.even_iff.mpr
      simpa only [hca, hcb, false_or, if_false] using hp c
    · apply Nat.odd_iff.mpr
      simpa using hp a
    · apply Nat.odd_iff.mpr
      simpa using hp b

/-- Reordering the three actual core indices preserves their vertex cover. -/
theorem reordered_three_core_cover {V : Type*} (U : Fin 3 → Finset V)
    (hcover : ∀ v, ∃ i, v ∈ U i) (c a b : Fin 3)
    (hindices : ∀ i : Fin 3, i = c ∨ i = a ∨ i = b) :
    ∀ v, v ∈ U c ∨ v ∈ U a ∨ v ∈ U b := by
  intro v
  obtain ⟨i, hi⟩ := hcover v
  rcases hindices i with rfl | rfl | rfl
  · exact Or.inl hi
  · exact Or.inr (Or.inl hi)
  · exact Or.inr (Or.inr hi)

end Overfull.Terminal
