import Overfull.Patterns.Encoding

/-!
# The forest forced by four odd assigned parts

These statements range over the six unordered pairs on four actual
labels and are proved by kernel evaluation of that finite space.
-/

namespace Overfull.Patterns
open Finset Compression

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- A forest on four labels uses at most three joining pairs. -/
theorem label_forest_card : ∀ P : Finset LabelPair, LeafForest P → P.card ≤ 3 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- If all four forest degrees are odd, the forest is a perfect matching
or consists of the three edges through one fixed center. -/
theorem four_odd_label_forest :
    ∀ P : Finset LabelPair, LeafForest P → (∀ i : Fin 4, pairDegree P i % 2 = 1) →
      (P.card = 2 ∧ ∀ i : Fin 4, pairDegree P i = 1) ∨
        ∃ center : Fin 4, P.card = 3 ∧
          ∀ p : LabelPair, p ∈ P ↔ center ∈ p.val := by
  decide

/-- Adding the assigned exceptional vertices cancels their contribution
to the boundary parity. Only the joining-forest degree remains. -/
theorem assigned_order_parity (m a d : ℕ)
    (h : m % 2 = (a+d) % 2) : (m+a) % 2 = d % 2 := by
  omega

end Overfull.Patterns
