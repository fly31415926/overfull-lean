import Mathlib.Tactic

/-!
# The order of the auxiliary graph

The auxiliary order is the least integer at least `max n (k+1)` having the
same parity as the original order. The choice keeps every requested degree
below the auxiliary order and makes the completed order even.
-/

namespace Overfull.AuxiliaryCompletion

/-- The least permitted auxiliary order with the original parity. -/
def auxiliaryOrder (n k : ℕ) : ℕ :=
  let a := max n (k+1)
  if a % 2 = n % 2 then a else a+1

theorem max_le_auxiliaryOrder (n k : ℕ) :
    max n (k+1) ≤ auxiliaryOrder n k := by
  simp only [auxiliaryOrder]
  split <;> omega

theorem auxiliaryOrder_le_max_add_one (n k : ℕ) :
    auxiliaryOrder n k ≤ max n (k+1)+1 := by
  simp only [auxiliaryOrder]
  split <;> omega

theorem auxiliaryOrder_mod_two (n k : ℕ) :
    auxiliaryOrder n k % 2 = n % 2 := by
  simp only [auxiliaryOrder]
  split <;> omega

theorem auxiliaryOrder_le_of_le_of_mod_two (n k m : ℕ)
    (hm : max n (k+1) ≤ m) (hparity : m % 2 = n % 2) :
    auxiliaryOrder n k ≤ m := by
  simp only [auxiliaryOrder]
  split <;> omega

theorem le_auxiliaryOrder (n k : ℕ) : n ≤ auxiliaryOrder n k :=
  (le_max_left _ _).trans (max_le_auxiliaryOrder n k)

theorem lt_auxiliaryOrder (n k : ℕ) : k < auxiliaryOrder n k := by
  have := (le_max_right n (k+1)).trans (max_le_auxiliaryOrder n k)
  omega

theorem auxiliaryOrder_le_three_mul (n k : ℕ) (hn : 2 ≤ n)
    (hk : k ≤ 2*n) : auxiliaryOrder n k ≤ 3*n := by
  have := auxiliaryOrder_le_max_add_one n k
  omega

theorem auxiliaryOrder_eq_of_lt (n k : ℕ) (hk : k < n) :
    auxiliaryOrder n k = n := by
  simp [auxiliaryOrder, max_eq_left (show k+1 ≤ n by omega)]

end Overfull.AuxiliaryCompletion
