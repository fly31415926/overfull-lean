import Mathlib.Tactic

/-!
# Integral signed flows on three vertices

The three singleton cut bounds and zero total demand suffice for an integral
signed flow on a triangle with arbitrary parallel-edge capacities. The proof
chooses one integer in an explicit interval; it uses no flow-existence theorem.

For the compatible-circuit problem on four labels, this is the arithmetic
needed after removing one distinguished label. Turning the integral flow into
actual selected edge copies, and decomposing those copies into circuits, are
separate graph-theoretic steps.
-/

namespace Overfull.CompatibleCircuits

/-- Signed flows on the pairs `01`, `02`, and `12`, with net outflow equal to
the prescribed integer demands. Capacities count actual parallel copies. -/
theorem three_vertex_integer_flow
    (c01 c02 c12 : ℕ) (d0 d1 d2 : ℤ)
    (htotal : d0 + d1 + d2 = 0)
    (h0 : |d0| ≤ (c01 : ℤ) + c02)
    (h1 : |d1| ≤ (c01 : ℤ) + c12)
    (h2 : |d2| ≤ (c02 : ℤ) + c12) :
    ∃ f01 f02 f12 : ℤ,
      |f01| ≤ c01 ∧ |f02| ≤ c02 ∧ |f12| ≤ c12 ∧
      f01 + f02 = d0 ∧ f12 - f01 = d1 ∧ -f02 - f12 = d2 := by
  obtain ⟨h0lo, h0hi⟩ := abs_le.mp h0
  obtain ⟨h1lo, h1hi⟩ := abs_le.mp h1
  obtain ⟨h2lo, h2hi⟩ := abs_le.mp h2
  let x : ℤ := max (-(c01 : ℤ)) (max (d0 - c02) (-d1 - c12))
  have hxlo0 : -(c01 : ℤ) ≤ x := le_max_left _ _
  have hxlo1 : d0 - c02 ≤ x :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hxlo2 : -d1 - c12 ≤ x :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hxhi0 : x ≤ c01 := by
    dsimp [x]
    exact max_le (by omega) (max_le (by omega) (by omega))
  have hxhi1 : x ≤ d0 + c02 := by
    dsimp [x]
    exact max_le (by omega) (max_le (by omega) (by omega))
  have hxhi2 : x ≤ -d1 + c12 := by
    dsimp [x]
    exact max_le (by omega) (max_le (by omega) (by omega))
  refine ⟨x, d0 - x, d1 + x, abs_le.mpr ⟨hxlo0, hxhi0⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact abs_le.mpr ⟨by omega, by omega⟩
  · exact abs_le.mpr ⟨by omega, by omega⟩
  · omega
  · omega
  · omega

end Overfull.CompatibleCircuits
