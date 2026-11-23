import Overfull.FourOdd.OriginalGraph

/-! Parity alternatives for two core fibers and one even pair fiber.
Recreated after the unpublished isolated draft was lost; fresh checking is required. -/

namespace Overfull.AssignedParts
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V]

/-- The three fibers partition the actual original vertex type. -/
theorem fiber_card_sum_three (label : V → Fin 3) :
    (univ.filter (fun v => label v = 0)).card +
      (univ.filter (fun v => label v = 1)).card +
      (univ.filter (fun v => label v = 2)).card = Fintype.card V := by
  have hsum := sum_card_fiberwise_eq_card_filter
    (univ : Finset V) (univ : Finset (Fin 3)) label
  simpa [Fin.sum_univ_three, add_assoc] using hsum

/-- Even total order and an even pair fiber give equal core-fiber parity. -/
theorem core_fiber_parity_eq_of_even_total_and_pair (label : V → Fin 3)
    (hV : Even (Fintype.card V))
    (hpair : Even ((univ.filter (fun v => label v = 2)).card)) :
    (univ.filter (fun v => label v = 0)).card % 2 =
      (univ.filter (fun v => label v = 1)).card % 2 := by
  have hsum := fiber_card_sum_three label
  have htotal := Nat.even_iff.mp hV
  have hthird := Nat.even_iff.mp hpair
  omega

/-- The assigned fibers are all even, or exactly the two core fibers are odd. -/
theorem fiber_parity_cases_of_even_total_and_pair (label : V → Fin 3)
    (hV : Even (Fintype.card V))
    (hpair : Even ((univ.filter (fun v => label v = 2)).card)) :
    (∀ i, (univ.filter (fun v => label v = i)).card % 2 = 0) ∨
      (∀ i, (univ.filter (fun v => label v = i)).card % 2 =
        if i = 0 ∨ i = 1 then 1 else 0) := by
  have h01 := core_fiber_parity_eq_of_even_total_and_pair label hV hpair
  have h2 := Nat.even_iff.mp hpair
  by_cases h0 : (univ.filter (fun v => label v = 0)).card % 2 = 0
  · left
    intro i
    fin_cases i
    · exact h0
    · exact h01.symm.trans h0
    · exact h2
  · have h0odd : (univ.filter (fun v => label v = 0)).card % 2 = 1 := by omega
    right
    intro i
    fin_cases i
    · simpa using h0odd
    · simpa using h01.symm.trans h0odd
    · simpa using h2
end Overfull.AssignedParts
