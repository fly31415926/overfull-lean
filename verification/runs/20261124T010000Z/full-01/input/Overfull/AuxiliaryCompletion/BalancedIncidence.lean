import Overfull.BipartiteMatching
import Mathlib.Data.Real.Archimedean
import Overfull.AuxiliaryCompletion.Incidence

/-!
# Balanced simple incidences to the auxiliary vertices

Prescribed left degrees are realized by actual finite neighbor sets.
Vertices of left degree one receive distinct neighbors. Minimizing the sum
of squares of the right degrees makes those degrees differ by at most one.
-/

namespace Overfull.AuxiliaryCompletion

open Finset Classical SimpleGraph
open scoped BigOperators

variable {V B : Type*} [Fintype V] [Fintype B]

/-- All prescribed row sizes are retained, and a right vertex meets at
most one left vertex whose prescribed degree is one. -/
def ValidIncidences (d : V → ℕ) (N : V → Finset B) : Prop :=
  (∀ v, (N v).card = d v) ∧
  ∀ b, (univ.filter (fun v => d v = 1 ∧ b ∈ N v)).card ≤ 1

/-- An initial system of simple incidences with the required restriction
on the vertices of degree one. -/
theorem exists_valid_incidences (d : V → ℕ)
    (horder : Fintype.card V ≤ Fintype.card B)
    (hd : ∀ v, d v ≤ Fintype.card B) :
    ∃ N : V → Finset B, ValidIncidences d N := by
  classical
  have hrow : ∀ v, ∃ T : Finset B, T.card = d v := by
    intro v
    obtain ⟨T, _, hT⟩ := Finset.exists_subset_card_eq
      (s := (univ : Finset B)) (by simpa using hd v)
    exact ⟨T, hT⟩
  choose row hrow using hrow
  let U := {v : V // d v = 1}
  have hU : Fintype.card U ≤ Fintype.card B :=
    (Fintype.card_subtype_le _).trans horder
  let f : U ↪ B := Classical.choice (Function.Embedding.nonempty_iff_card_le.mpr hU)
  let N : V → Finset B := fun v => if h : d v = 1 then {f ⟨v, h⟩} else row v
  refine ⟨N, ?_, ?_⟩
  · intro v
    by_cases hv : d v = 1
    · simp [N, hv]
    · simpa [N, hv] using hrow v
  · intro b
    apply Finset.card_le_one.mpr
    intro v hv w hw
    obtain ⟨hv1, hvb⟩ := (Finset.mem_filter.mp hv).2
    obtain ⟨hw1, hwb⟩ := (Finset.mem_filter.mp hw).2
    have hvb' : b = f ⟨v, hv1⟩ := by simpa [N, hv1] using hvb
    have hwb' : b = f ⟨w, hw1⟩ := by simpa [N, hw1] using hwb
    exact congrArg Subtype.val (f.injective (hvb'.symm.trans hwb'))

omit [Fintype B] in
/-- A gap of at least two between right degrees gives a transferable
incidence at a left vertex whose prescribed degree is not one. -/
theorem exists_transfer_vertex (d : V → ℕ) (N : V → Finset B)
    (hN : ValidIncidences d N) (x y : B)
    (hgap : rightLoad N y + 2 ≤ rightLoad N x) :
    ∃ v, x ∈ N v ∧ y ∉ N v ∧ d v ≠ 1 := by
  classical
  by_contra! hnone
  let A := univ.filter (fun v => x ∈ N v)
  let C := univ.filter (fun v => y ∈ N v)
  let U := univ.filter (fun v => d v = 1 ∧ x ∈ N v)
  have hsub : A ⊆ C ∪ U := by
    intro v hv
    have hvx : x ∈ N v := (Finset.mem_filter.mp hv).2
    by_cases hvy : y ∈ N v
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvy⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnone v hvx hvy, hvx⟩)
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le C U)
  have hunit : U.card ≤ 1 := hN.2 x
  change rightLoad N x ≤ rightLoad N y + U.card at hcard
  omega

/-- The row switch replaces one neighbor by a previously absent neighbor. -/
noncomputable def transfer (N : V → Finset B) (v : V) (x y : B) : V → Finset B :=
  Function.update N v (insert y ((N v).erase x))

omit [Fintype B] in
theorem transfer_valid (d : V → ℕ) (N : V → Finset B)
    (hN : ValidIncidences d N) (v : V) (x y : B)
    (hx : x ∈ N v) (hy : y ∉ N v) (hv : d v ≠ 1) :
    ValidIncidences d (transfer N v x y) := by
  classical
  have hyerase : y ∉ (N v).erase x := fun h => hy (Finset.mem_of_mem_erase h)
  constructor
  · intro w
    by_cases hw : w = v
    · subst w
      simp only [transfer, Function.update_self, Finset.card_insert_of_notMem hyerase]
      have hcard := Finset.card_erase_add_one hx
      have hrow := hN.1 v
      omega
    · simpa only [transfer, Function.update_of_ne hw] using hN.1 w
  · intro b
    have heq : univ.filter (fun w => d w = 1 ∧ b ∈ transfer N v x y w) =
        univ.filter (fun w => d w = 1 ∧ b ∈ N w) := by
      apply Finset.filter_congr
      intro w _
      by_cases hw : w = v
      · subst w
        simp [hv]
      · simp [transfer, Function.update_of_ne hw]
    rw [heq]
    exact hN.2 b

omit [Fintype B] in
/-- Exact change in a right degree after changing one left row. -/
theorem rightLoad_update (N : V → Finset B) (v : V) (T : Finset B) (b : B) :
    rightLoad (Function.update N v T) b + (if b ∈ N v then 1 else 0) =
      rightLoad N b + (if b ∈ T then 1 else 0) := by
  classical
  let f : V → ℕ := fun w => if b ∈ N w then 1 else 0
  let g : V → ℕ := fun w => if b ∈ Function.update N v T w then 1 else 0
  have hf := Finset.sum_erase_add (s := (univ : Finset V)) f (Finset.mem_univ v)
  have hg := Finset.sum_erase_add (s := (univ : Finset V)) g (Finset.mem_univ v)
  have hrest : ∑ w ∈ univ.erase v, f w = ∑ w ∈ univ.erase v, g w := by
    apply Finset.sum_congr rfl
    intro w hw
    have hwv : w ≠ v := (Finset.mem_erase.mp hw).1
    simp [f, g, Function.update_of_ne hwv]
  have hsumf : ∑ w, f w = rightLoad N b := by simp [f, rightLoad]
  have hsumg : ∑ w, g w = rightLoad (Function.update N v T) b := by
    simp [g, rightLoad]
  rw [hsumf] at hf
  rw [hsumg] at hg
  have hgv : g v = if b ∈ T then 1 else 0 := by simp [g]
  change (∑ w ∈ univ.erase v, f w) + (if b ∈ N v then 1 else 0) = _ at hf
  rw [hgv, ← hrest] at hg
  omega

omit [Fintype B] in
/-- The transferred degree decreases by one at the source, increases by
one at the destination, and is unchanged elsewhere. -/
theorem transfer_loads (N : V → Finset B) (v : V) (x y : B)
    (hx : x ∈ N v) (hy : y ∉ N v) :
    rightLoad (transfer N v x y) x + 1 = rightLoad N x ∧
    rightLoad (transfer N v x y) y = rightLoad N y + 1 ∧
    ∀ b, b ≠ x → b ≠ y → rightLoad (transfer N v x y) b = rightLoad N b := by
  classical
  have hxy : x ≠ y := by rintro rfl; exact hy hx
  have hxnew : x ∉ insert y ((N v).erase x) := by simp [hxy]
  have hynew : y ∈ insert y ((N v).erase x) := Finset.mem_insert_self _ _
  constructor
  · have h := rightLoad_update N v (insert y ((N v).erase x)) x
    simpa only [if_pos hx, if_neg hxnew, add_zero] using h
  constructor
  · have h := rightLoad_update N v (insert y ((N v).erase x)) y
    simpa only [if_neg hy, if_pos hynew, add_zero] using h
  · intro b hbx hby
    have hb : b ∈ insert y ((N v).erase x) ↔ b ∈ N v := by simp [hbx, hby]
    have h := rightLoad_update N v (insert y ((N v).erase x)) b
    simp only [hb] at h
    exact Nat.add_right_cancel h

private theorem sum_change_at_two (f g : B → ℕ) (x y : B) (hxy : x ≠ y)
    (h : ∀ b, b ≠ x → b ≠ y → f b = g b) :
    (∑ b, f b) + g x + g y = (∑ b, g b) + f x + f y := by
  classical
  have hx := Finset.sum_erase_add (s := (univ : Finset B)) f (Finset.mem_univ x)
  have hy := Finset.sum_erase_add (s := (univ.erase x : Finset B)) f
    (Finset.mem_erase.mpr ⟨hxy.symm, Finset.mem_univ y⟩)
  have hxg := Finset.sum_erase_add (s := (univ : Finset B)) g (Finset.mem_univ x)
  have hyg := Finset.sum_erase_add (s := (univ.erase x : Finset B)) g
    (Finset.mem_erase.mpr ⟨hxy.symm, Finset.mem_univ y⟩)
  have hrest : ∑ b ∈ (univ.erase x).erase y, f b =
      ∑ b ∈ (univ.erase x).erase y, g b := by
    apply Finset.sum_congr rfl
    intro b hb
    exact h b (Finset.mem_erase.mp (Finset.mem_erase.mp hb).2).1
      (Finset.mem_erase.mp hb).1
  omega

/-- Actual simple incidences with balanced right degrees and distinct
neighbors for all left vertices of prescribed degree one. -/
theorem exists_balanced_incidences (d : V → ℕ)
    (horder : Fintype.card V ≤ Fintype.card B)
    (hd : ∀ v, d v ≤ Fintype.card B) :
    ∃ N : V → Finset B, ValidIncidences d N ∧
      ∀ x y, rightLoad N x ≤ rightLoad N y + 1 := by
  classical
  let S := (univ : Finset (V → Finset B)).filter (ValidIncidences d)
  obtain ⟨N₀, hN₀⟩ := exists_valid_incidences (B := B) d horder hd
  have hS : S.Nonempty := ⟨N₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hN₀⟩⟩
  let cost : (V → Finset B) → ℕ := fun N => ∑ b, (rightLoad N b) ^ 2
  obtain ⟨N, hNS, hmin⟩ := Finset.exists_min_image S cost hS
  have hN : ValidIncidences d N := (Finset.mem_filter.mp hNS).2
  refine ⟨N, hN, ?_⟩
  intro x y
  by_contra hnot
  have hgap : rightLoad N y + 2 ≤ rightLoad N x := by omega
  obtain ⟨v, hvx, hvy, hv⟩ := exists_transfer_vertex d N hN x y hgap
  let N' := transfer N v x y
  have hN' : ValidIncidences d N' := transfer_valid d N hN v x y hvx hvy hv
  have hmin' : cost N ≤ cost N' :=
    hmin N' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hN'⟩)
  have hxy : x ≠ y := by rintro rfl; exact hvy hvx
  obtain ⟨hx, hy, hother⟩ := transfer_loads N v x y hvx hvy
  change rightLoad N' x + 1 = rightLoad N x at hx
  change rightLoad N' y = rightLoad N y + 1 at hy
  have hcost : cost N' + (rightLoad N x) ^ 2 + (rightLoad N y) ^ 2 =
      cost N + (rightLoad N' x) ^ 2 + (rightLoad N' y) ^ 2 :=
    sum_change_at_two (fun b => (rightLoad N' b) ^ 2) (fun b => (rightLoad N b) ^ 2)
      x y hxy (fun b hbx hby => congrArg (fun z : ℕ => z ^ 2) (hother b hbx hby))
  rw [← hx, hy] at hcost
  nlinarith

/-- The total right degree counts exactly the prescribed left incidences. -/
theorem sum_rightLoad (N : V → Finset B) :
    ∑ b, rightLoad N b = ∑ v, (N v).card := by
  classical
  calc
    _ = ∑ b, ∑ v : V, if b ∈ N v then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro b _
      simp [rightLoad]
    _ = ∑ v : V, ∑ b : B, if b ∈ N v then 1 else 0 := Finset.sum_comm
    _ = ∑ v, (N v).card := by simp

/-- Balanced integral right degrees are bounded above by the ceiling of
their average. This includes an empty right side, for which the conclusion
has no vertex to test. -/
theorem rightLoad_le_ceil_average (N : V → Finset B)
    (hbalance : ∀ x y, rightLoad N x ≤ rightLoad N y + 1) (b : B) :
    rightLoad N b ≤ Nat.ceil ((∑ y, (rightLoad N y : ℝ)) / Fintype.card B) := by
  classical
  let q := Nat.ceil ((∑ y, (rightLoad N y : ℝ)) / Fintype.card B)
  by_contra hnot
  have hb : q < rightLoad N b := Nat.lt_of_not_ge hnot
  have hall : ∀ y, q ≤ rightLoad N y := by
    intro y
    have h := hbalance b y
    omega
  have hsum : (∑ _y : B, q) < ∑ y, rightLoad N y :=
    Finset.sum_lt_sum (fun y _ => hall y) ⟨b, Finset.mem_univ _, hb⟩
  have hsumR : (Fintype.card B : ℝ) * q < ∑ y, (rightLoad N y : ℝ) := by
    exact_mod_cast (by simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      using hsum)
  have hm : (0 : ℝ) < Fintype.card B := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨b⟩
  have hceil : (∑ y, (rightLoad N y : ℝ)) / Fintype.card B ≤ (q : ℝ) :=
    Nat.le_ceil _
  have hupper := (div_le_iff₀ hm).mp hceil
  nlinarith

omit [Fintype B] in
/-- Every selected incidence contributes two except possibly the unique
neighbor whose original deficiency is one. -/
theorem twice_incidence_card_le_deficiency_sum_add_one
    (d : V → ℕ) (N : V → Finset B) (hN : ValidIncidences d N)
    (S : Finset V) (b : B) :
    2 * (S.filter (fun v => b ∈ N v)).card ≤ (∑ v ∈ S, d v) + 1 := by
  classical
  have hlocal (v : V) : (2 : ℕ) * (if b ∈ N v then 1 else 0) ≤
      d v + (if d v = 1 ∧ b ∈ N v then 1 else 0) := by
    by_cases hv : b ∈ N v
    · have hpos : 0 < d v := by
        rw [← hN.1 v]
        exact Finset.card_pos.mpr ⟨b, hv⟩
      by_cases hdv : d v = 1
      · simp [hv, hdv]
      · simp [hv, hdv]
        omega
    · simp [hv]
  have hsum := Finset.sum_le_sum (s := S) (fun v _ => hlocal v)
  have hunit : (S.filter (fun v => d v = 1 ∧ b ∈ N v)).card ≤ 1 := by
    apply le_trans (Finset.card_le_card ?_) (hN.2 b)
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hv).2⟩
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole, Nat.cast_id] at hsum
  omega

/-- The neighbor sets needed for the auxiliary completion, including the
ceiling bound on every auxiliary degree. -/
theorem exists_auxiliary_neighbors (d : V → ℕ) (m : ℕ)
    (horder : Fintype.card V ≤ m) (hd : ∀ v, d v ≤ m) :
    ∃ N : V → Finset (Fin m), ValidIncidences d N ∧
      (∀ x y, rightLoad N x ≤ rightLoad N y + 1) ∧
      (∀ b, rightLoad N b ≤ Nat.ceil ((∑ v, (d v : ℝ)) / m)) ∧
      (∑ b, rightLoad N b) = ∑ v, d v := by
  classical
  obtain ⟨N, hN, hbalance⟩ := exists_balanced_incidences (B := Fin m) d
    (by simpa using horder) (by simpa using hd)
  have hsum : (∑ b, rightLoad N b) = ∑ v, d v := by
    rw [sum_rightLoad]
    exact Finset.sum_congr rfl (fun v _ => hN.1 v)
  refine ⟨N, hN, hbalance, ?_, hsum⟩
  intro b
  have hsumR : (∑ b, (rightLoad N b : ℝ)) = ∑ v, (d v : ℝ) := by
    exact_mod_cast hsum
  have h := rightLoad_le_ceil_average N hbalance b
  simpa only [hsumR, Fintype.card_fin] using h

end Overfull.AuxiliaryCompletion
