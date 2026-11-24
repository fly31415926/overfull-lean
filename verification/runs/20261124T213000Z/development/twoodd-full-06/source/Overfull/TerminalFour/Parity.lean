import Overfull.Terminal.PartLabels

/-! Exhaustive parity of four actual covering core parts. -/

noncomputable section
namespace Overfull.TerminalFour
open Finset Classical FourOdd

/-- The four fibers partition the original vertex set. -/
theorem fiber_card_sum_four {V : Type*} [Fintype V] (label : V → Fin 4) :
    (univ.filter (fun v => label v = 0)).card +
      (univ.filter (fun v => label v = 1)).card +
      (univ.filter (fun v => label v = 2)).card +
      (univ.filter (fun v => label v = 3)).card = Fintype.card V := by
  have hs := sum_card_fiberwise_eq_card_filter
    (univ : Finset V) (univ : Finset (Fin 4)) label
  simpa [Fin.sum_univ_succ, add_assoc] using hs

/-- Even total order leaves exactly the all-even, two-odd and all-odd cases. -/
theorem four_fiber_parity {V : Type*} [Fintype V]
    (label : V → Fin 4) (hV : Even (Fintype.card V)) :
    (∀ i, (univ.filter (fun v => label v = i)).card % 2 = 0) ∨
      (∃ a b : Fin 4, a ≠ b ∧
        ∀ i, (univ.filter (fun v => label v = i)).card % 2 =
          if i = a ∨ i = b then 1 else 0) ∨
      (∀ i, (univ.filter (fun v => label v = i)).card % 2 = 1) := by
  have hs := fiber_card_sum_four label
  have ht := Nat.even_iff.mp hV
  by_cases h₀ : (univ.filter (fun v => label v = 0)).card % 2 = 0
  all_goals by_cases h₁ : (univ.filter (fun v => label v = 1)).card % 2 = 0
  all_goals by_cases h₂ : (univ.filter (fun v => label v = 2)).card % 2 = 0
  · have hp0 : (univ.filter (fun v => label v = 0)).card % 2 = 0 := by omega
    have hp1 : (univ.filter (fun v => label v = 1)).card % 2 = 0 := by omega
    have hp2 : (univ.filter (fun v => label v = 2)).card % 2 = 0 := by omega
    have hp3 : (univ.filter (fun v => label v = 3)).card % 2 = 0 := by omega
    left
    intro i
    fin_cases i
    · simpa using hp0
    · simpa using hp1
    · simpa using hp2
    · simpa using hp3
  · have hp0 : (univ.filter (fun v => label v = 0)).card % 2 = 0 := by omega
    have hp1 : (univ.filter (fun v => label v = 1)).card % 2 = 0 := by omega
    have hp2 : (univ.filter (fun v => label v = 2)).card % 2 = 1 := by omega
    have hp3 : (univ.filter (fun v => label v = 3)).card % 2 = 1 := by omega
    right; left
    refine ⟨2, 3, by decide, ?_⟩
    intro i
    fin_cases i
    · simpa using hp0
    · simpa using hp1
    · simpa using hp2
    · simpa using hp3
  · have hp0 : (univ.filter (fun v => label v = 0)).card % 2 = 0 := by omega
    have hp1 : (univ.filter (fun v => label v = 1)).card % 2 = 1 := by omega
    have hp2 : (univ.filter (fun v => label v = 2)).card % 2 = 0 := by omega
    have hp3 : (univ.filter (fun v => label v = 3)).card % 2 = 1 := by omega
    right; left
    refine ⟨1, 3, by decide, ?_⟩
    intro i
    fin_cases i
    · simpa using hp0
    · simpa using hp1
    · simpa using hp2
    · simpa using hp3
  · have hp0 : (univ.filter (fun v => label v = 0)).card % 2 = 0 := by omega
    have hp1 : (univ.filter (fun v => label v = 1)).card % 2 = 1 := by omega
    have hp2 : (univ.filter (fun v => label v = 2)).card % 2 = 1 := by omega
    have hp3 : (univ.filter (fun v => label v = 3)).card % 2 = 0 := by omega
    right; left
    refine ⟨1, 2, by decide, ?_⟩
    intro i
    fin_cases i
    · simpa using hp0
    · simpa using hp1
    · simpa using hp2
    · simpa using hp3
  · have hp0 : (univ.filter (fun v => label v = 0)).card % 2 = 1 := by omega
    have hp1 : (univ.filter (fun v => label v = 1)).card % 2 = 0 := by omega
    have hp2 : (univ.filter (fun v => label v = 2)).card % 2 = 0 := by omega
    have hp3 : (univ.filter (fun v => label v = 3)).card % 2 = 1 := by omega
    right; left
    refine ⟨0, 3, by decide, ?_⟩
    intro i
    fin_cases i
    · simpa using hp0
    · simpa using hp1
    · simpa using hp2
    · simpa using hp3
  · have hp0 : (univ.filter (fun v => label v = 0)).card % 2 = 1 := by omega
    have hp1 : (univ.filter (fun v => label v = 1)).card % 2 = 0 := by omega
    have hp2 : (univ.filter (fun v => label v = 2)).card % 2 = 1 := by omega
    have hp3 : (univ.filter (fun v => label v = 3)).card % 2 = 0 := by omega
    right; left
    refine ⟨0, 2, by decide, ?_⟩
    intro i
    fin_cases i
    · simpa using hp0
    · simpa using hp1
    · simpa using hp2
    · simpa using hp3
  · have hp0 : (univ.filter (fun v => label v = 0)).card % 2 = 1 := by omega
    have hp1 : (univ.filter (fun v => label v = 1)).card % 2 = 1 := by omega
    have hp2 : (univ.filter (fun v => label v = 2)).card % 2 = 0 := by omega
    have hp3 : (univ.filter (fun v => label v = 3)).card % 2 = 0 := by omega
    right; left
    refine ⟨0, 1, by decide, ?_⟩
    intro i
    fin_cases i
    · simpa using hp0
    · simpa using hp1
    · simpa using hp2
    · simpa using hp3
  · have hp0 : (univ.filter (fun v => label v = 0)).card % 2 = 1 := by omega
    have hp1 : (univ.filter (fun v => label v = 1)).card % 2 = 1 := by omega
    have hp2 : (univ.filter (fun v => label v = 2)).card % 2 = 1 := by omega
    have hp3 : (univ.filter (fun v => label v = 3)).card % 2 = 1 := by omega
    right; right
    intro i
    fin_cases i
    · simpa using hp0
    · simpa using hp1
    · simpa using hp2
    · simpa using hp3

/-- Exact label fibers transport the parity alternatives to the actual cores. -/
theorem four_core_parity {V : Type*} [Fintype V]
    (U : Fin 4 → Finset V) (label : V → Fin 4)
    (hparts : ∀ i, labelShore label {i} = U i) (hV : Even (Fintype.card V)) :
    (∀ i, (U i).card % 2 = 0) ∨
      (∃ a b : Fin 4, a ≠ b ∧ ∀ i, (U i).card % 2 =
        if i = a ∨ i = b then 1 else 0) ∨
      (∀ i, (U i).card % 2 = 1) := by
  have hf (i : Fin 4) : univ.filter (fun v => label v = i) = U i := by
    simpa only [labelShore, mem_singleton] using hparts i
  simpa only [hf] using four_fiber_parity label hV

end Overfull.TerminalFour
