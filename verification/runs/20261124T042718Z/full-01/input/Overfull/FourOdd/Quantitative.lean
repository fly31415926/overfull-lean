import Overfull.FourOdd.OriginalGraph
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Explicit sufficient error constants for four odd parts

The original boundary bound may be real. Its natural floor is a valid
integer maximum-degree bound. The fixed ratio `1/1000` supplies exactly
the integer inequalities used by both finite constructions.
-/

noncomputable section

namespace Overfull.FourOdd

open Finset Classical

variable {V E : Type*} [Fintype E]

theorem joining_degree_le_floor (G : Multigraph V E) (label : V → Fin 4)
    {a : ℝ} (hdegree : ∀ v, (G.degreeOn (joiningCopies G label) v : ℝ) ≤ a) (v : V) :
    G.degreeOn (joiningCopies G label) v ≤ ⌊a⌋₊ := Nat.le_floor (hdegree v)

theorem floor_boundary_small {h : ℕ} {a : ℝ}
    (ha : 0 ≤ a) (hsmall : 1000 * a ≤ h) : 1000 * ⌊a⌋₊ ≤ h := by
  have hf := Nat.floor_le ha
  have hn : (1000 : ℝ) * (⌊a⌋₊ : ℝ) ≤ h := by linarith
  exact_mod_cast hn

theorem ratio_boundary_small {h : ℕ} {a : ℝ}
    (hh : 0 < h) (hsmall : a / h ≤ (1 : ℝ) / 1000) : 1000 * a ≤ h := by
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  have ht := (div_le_iff₀ hh').mp hsmall
  linarith

theorem ratio_supply_nearly {h r0 : ℕ}
    (hh : 0 < h) (hnearly : ((h : ℝ) - r0) / h ≤ (1 : ℝ) / 1000) :
    999 * h ≤ 1000 * r0 := by
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  have ht := (div_le_iff₀ hh').mp hnearly
  have hn : (999 : ℝ) * h ≤ 1000 * r0 := by linarith
  exact_mod_cast hn

/-- A zero-regular loopless graph has no edge copies at all. -/
theorem edge_type_empty_of_zero_regular (G : Multigraph V E)
    (hregular : ∀ v, G.degree v = 0) : IsEmpty E := by
  refine ⟨fun e => ?_⟩
  have hpos : 0 < G.degree (G.firstEnd e) := by
    apply Finset.card_pos.mpr
    exact ⟨e, (G.mem_incidenceEdges _ _).mpr
      ((G.incident_iff e _).mpr (Or.inl rfl))⟩
  rw [hregular] at hpos
  omega

end Overfull.FourOdd
