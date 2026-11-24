import Overfull.FourOdd.OriginalGraph

/-! Exact labels for three disjoint covering parts, recreated for fresh checking. -/
noncomputable section
namespace Overfull.AssignedParts
open Finset Classical
variable {V : Type*}

def labelOfThreeParts (A0 A1 : Finset V) (v : V) : Fin 3 :=
  if v ∈ A0 then 0 else if v ∈ A1 then 1 else 2

theorem labelOfThreeParts_eq_zero_iff (A0 A1 : Finset V) (v : V) :
    labelOfThreeParts A0 A1 v = 0 ↔ v ∈ A0 := by
  by_cases h0 : v ∈ A0 <;> by_cases h1 : v ∈ A1 <;>
    simp [labelOfThreeParts, h0, h1]

theorem labelOfThreeParts_eq_one_iff (A0 A1 : Finset V) (v : V) :
    labelOfThreeParts A0 A1 v = 1 ↔ v ∉ A0 ∧ v ∈ A1 := by
  by_cases h0 : v ∈ A0 <;> by_cases h1 : v ∈ A1 <;>
    simp [labelOfThreeParts, h0, h1]

theorem labelOfThreeParts_eq_two_iff (A0 A1 : Finset V) (v : V) :
    labelOfThreeParts A0 A1 v = 2 ↔ v ∉ A0 ∧ v ∉ A1 := by
  by_cases h0 : v ∈ A0 <;> by_cases h1 : v ∈ A1 <;>
    simp [labelOfThreeParts, h0, h1]

variable [Fintype V]

theorem labelOfThreeParts_fiber_zero (A0 A1 : Finset V) :
    univ.filter (fun v => labelOfThreeParts A0 A1 v = 0) = A0 := by
  ext v
  simp [labelOfThreeParts_eq_zero_iff]

theorem labelOfThreeParts_fiber_one (A0 A1 : Finset V) (h01 : Disjoint A0 A1) :
    univ.filter (fun v => labelOfThreeParts A0 A1 v = 1) = A1 := by
  ext v
  simp only [mem_filter, mem_univ, true_and, labelOfThreeParts_eq_one_iff]
  constructor
  · exact fun hv => hv.2
  · intro hv
    exact ⟨fun h0 => disjoint_left.mp h01 h0 hv, hv⟩

theorem labelOfThreeParts_fiber_two (A0 A1 B : Finset V)
    (h0B : Disjoint A0 B) (h1B : Disjoint A1 B)
    (hcover : ∀ v, v ∈ A0 ∨ v ∈ A1 ∨ v ∈ B) :
    univ.filter (fun v => labelOfThreeParts A0 A1 v = 2) = B := by
  ext v
  simp only [mem_filter, mem_univ, true_and, labelOfThreeParts_eq_two_iff]
  constructor
  · intro hv
    rcases hcover v with h0 | h1 | hB
    · exact (hv.1 h0).elim
    · exact (hv.2 h1).elim
    · exact hB
  · intro hB
    exact ⟨fun h0 => disjoint_left.mp h0B h0 hB,
      fun h1 => disjoint_left.mp h1B h1 hB⟩

theorem labelOfThreeParts_fibers (A0 A1 B : Finset V)
    (h01 : Disjoint A0 A1) (h0B : Disjoint A0 B) (h1B : Disjoint A1 B)
    (hcover : ∀ v, v ∈ A0 ∨ v ∈ A1 ∨ v ∈ B) :
    (univ.filter (fun v => labelOfThreeParts A0 A1 v = 0) = A0) ∧
      (univ.filter (fun v => labelOfThreeParts A0 A1 v = 1) = A1) ∧
      (univ.filter (fun v => labelOfThreeParts A0 A1 v = 2) = B) := by
  exact ⟨labelOfThreeParts_fiber_zero A0 A1,
    labelOfThreeParts_fiber_one A0 A1 h01,
    labelOfThreeParts_fiber_two A0 A1 B h0B h1B hcover⟩
end Overfull.AssignedParts
