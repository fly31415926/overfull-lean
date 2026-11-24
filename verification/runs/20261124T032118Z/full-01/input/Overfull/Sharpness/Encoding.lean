import Overfull.Sharpness.Petersen

namespace Overfull.Sharpness

def boolValue (b : Bool) : Nat := if b then 1 else 0

theorem boolValue_le_one (b : Bool) : boolValue b ≤ 1 := by
  cases b <;> decide

def maskValue (a b c d e : Bool) : Nat :=
  boolValue a + 2 * boolValue b + 4 * boolValue c +
    8 * boolValue d + 16 * boolValue e

theorem maskValue_lt (a b c d e : Bool) : maskValue a b c d e < 32 := by
  have ha := boolValue_le_one a
  have hb := boolValue_le_one b
  have hc := boolValue_le_one c
  have hd := boolValue_le_one d
  have he := boolValue_le_one e
  unfold maskValue
  omega

def maskOf (f : Fin 5 → Bool) : Fin 32 :=
  ⟨maskValue (f 0) (f 1) (f 2) (f 3) (f 4), maskValue_lt ..⟩

def lookup5 (a b c d e : Bool) (i : Fin 5) : Bool :=
  if i.val = 0 then a else if i.val = 1 then b else if i.val = 2 then c
  else if i.val = 3 then d else e

theorem lookup5_apply (f : Fin 5 → Bool) (i : Fin 5) :
    lookup5 (f 0) (f 1) (f 2) (f 3) (f 4) i = f i := by
  rcases i with ⟨i, hi⟩
  match i with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | n + 5 => omega

theorem maskValue_bit : ∀ a b c d e : Bool, ∀ i : Fin 5,
    bit (maskValue a b c d e) i.val = boolValue (lookup5 a b c d e i) := by
  decide

/-- Binary masks represent arbitrary five-edge subsets, not just a restricted
selection of patterns. -/
theorem bit_maskOf (f : Fin 5 → Bool) (i : Fin 5) :
    bit (maskOf f).val i.val = boolValue (f i) := by
  exact (maskValue_bit (f 0) (f 1) (f 2) (f 3) (f 4) i).trans
    (congrArg boolValue (lookup5_apply f i))

/-- Every compatible pair extends to a degree-one selection by inserting
exactly the spokes at its uncovered indices. -/
theorem compatible_has_matching (outer inner : Fin 32) (h : Compatible outer inner) :
    ∃ spokes : Fin 32, IsPerfectMatching outer inner spokes := by
  refine ⟨maskOf (fun i => decide (outerIncidence outer.val i = 0)), ?_⟩
  intro i
  have hi := h i
  rw [bit_maskOf]
  by_cases hzero : outerIncidence outer.val i = 0
  · simp [boolValue, hzero]
    omega
  · have hone : outerIncidence outer.val i = 1 := by omega
    simp [boolValue, hone]
    omega

/-- Thus compatibility is exactly the condition that the two cycle subsets
are the nonspoke part of a Petersen perfect matching. -/
theorem compatible_iff_has_matching (outer inner : Fin 32) :
    Compatible outer inner ↔ ∃ spokes : Fin 32, IsPerfectMatching outer inner spokes := by
  constructor
  · exact compatible_has_matching outer inner
  · rintro ⟨spokes, h⟩
    exact perfect_matching_compatible outer inner spokes h

end Overfull.Sharpness
