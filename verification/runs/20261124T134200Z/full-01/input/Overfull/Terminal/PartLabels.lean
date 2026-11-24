import Overfull.AssignedParts.ThreePartLabels
import Overfull.AssignedParts.PairFiberParity

/-!
# Exact labels and parity for three covering parts

The original three parts determine actual vertex labels.  Even ambient
order gives precisely the all-even and two-odd alternatives required by
the joining decompositions.  The joining copies are the union of the cuts
of any two distinct label fibers.
-/

noncomputable section

namespace Overfull.Terminal

open Finset Classical AssignedParts FourOdd Multigraph

variable {V : Type*}

def threeCoreLabel (U : Fin 3 → Finset V) : V → Fin 3 :=
  labelOfThreeParts (U 0) (U 1)

variable [Fintype V]

/-- Disjoint covering parts are exactly the three fibers of their actual
label function. -/
theorem threeCoreLabel_fiber (U : Fin 3 → Finset V)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hcover : ∀ v, ∃ i, v ∈ U i) (i : Fin 3) :
    univ.filter (fun v => threeCoreLabel U v = i) = U i := by
  have hc : ∀ v, v ∈ U 0 ∨ v ∈ U 1 ∨ v ∈ U 2 := by
    intro v
    obtain ⟨j, hj⟩ := hcover v
    fin_cases j
    · exact Or.inl hj
    · exact Or.inr (Or.inl hj)
    · exact Or.inr (Or.inr hj)
  obtain ⟨h₀, h₁, h₂⟩ := labelOfThreeParts_fibers (U 0) (U 1) (U 2)
    (hdisjoint 0 1 (by decide)) (hdisjoint 0 2 (by decide))
    (hdisjoint 1 2 (by decide)) hc
  fin_cases i
  · exact h₀
  · exact h₁
  · exact h₂

theorem threeCoreLabel_eq_iff (U : Fin 3 → Finset V)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hcover : ∀ v, ∃ i, v ∈ U i) (i : Fin 3) (v : V) :
    threeCoreLabel U v = i ↔ v ∈ U i := by
  have h := Finset.ext_iff.mp (threeCoreLabel_fiber U hdisjoint hcover i) v
  simpa only [mem_filter, mem_univ, true_and] using h

theorem threeCoreLabel_shore (U : Fin 3 → Finset V)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hcover : ∀ v, ∃ i, v ∈ U i) (i : Fin 3) :
    labelShore (threeCoreLabel U) {i} = U i := by
  ext v
  simpa only [mem_labelShore, mem_singleton] using
    threeCoreLabel_eq_iff U hdisjoint hcover i v

/-- Three fibers of a finite even-order vertex type are all even, or
exactly two distinct fibers are odd. -/
theorem three_fiber_parity (label : V → Fin 3) (hV : Even (Fintype.card V)) :
    (∀ i, (univ.filter (fun v => label v = i)).card % 2 = 0) ∨
      ∃ a b : Fin 3, a ≠ b ∧
        ∀ i, (univ.filter (fun v => label v = i)).card % 2 =
          if i = a ∨ i = b then 1 else 0 := by
  have hsum := fiber_card_sum_three label
  have htotal := Nat.even_iff.mp hV
  by_cases h₀ : (univ.filter (fun v => label v = 0)).card % 2 = 0
  · by_cases h₁ : (univ.filter (fun v => label v = 1)).card % 2 = 0
    · have h₂ : (univ.filter (fun v => label v = 2)).card % 2 = 0 := by omega
      left
      intro i
      fin_cases i <;> assumption
    · have h₁' : (univ.filter (fun v => label v = 1)).card % 2 = 1 := by omega
      have h₂ : (univ.filter (fun v => label v = 2)).card % 2 = 1 := by omega
      right
      refine ⟨1, 2, by decide, ?_⟩
      intro i
      fin_cases i <;> simp_all
  · have h₀' : (univ.filter (fun v => label v = 0)).card % 2 = 1 := by omega
    by_cases h₁ : (univ.filter (fun v => label v = 1)).card % 2 = 0
    · have h₂ : (univ.filter (fun v => label v = 2)).card % 2 = 1 := by omega
      right
      refine ⟨0, 2, by decide, ?_⟩
      intro i
      fin_cases i <;> simp_all
    · have h₁' : (univ.filter (fun v => label v = 1)).card % 2 = 1 := by omega
      have h₂ : (univ.filter (fun v => label v = 2)).card % 2 = 0 := by omega
      right
      refine ⟨0, 1, by decide, ?_⟩
      intro i
      fin_cases i <;> simp_all

/-- The actual covering core parts inherit the two parity alternatives. -/
theorem three_core_parity (U : Fin 3 → Finset V)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hcover : ∀ v, ∃ i, v ∈ U i) (hV : Even (Fintype.card V)) :
    (∀ i, (U i).card % 2 = 0) ∨
      ∃ a b : Fin 3, a ≠ b ∧
        ∀ i, (U i).card % 2 = if i = a ∨ i = b then 1 else 0 := by
  simpa only [threeCoreLabel_fiber U hdisjoint hcover] using
    three_fiber_parity (threeCoreLabel U) hV

/-- With three labels, the cuts of any two distinct fibers contain exactly
all joining copies. -/
theorem joiningCopies_three_eq_two_cuts {E : Type*} [Fintype E]
    (G : Multigraph V E) (label : V → Fin 3) (a b : Fin 3) (hab : a ≠ b) :
    joiningCopies G label =
      G.cutEdges (labelShore label {a}) ∪ G.cutEdges (labelShore label {b}) := by
  ext e
  simp only [mem_joiningCopies, mem_union, Multigraph.mem_cutEdges,
    mem_labelShore, mem_singleton, ne_eq, eq_iff_iff]
  generalize label (G.firstEnd e) = i
  generalize label (G.secondEnd e) = j
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;> simp_all

theorem threeCoreLabel_joining {E : Type*} [Fintype E]
    (G : Multigraph V E) (U : Fin 3 → Finset V)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hcover : ∀ v, ∃ i, v ∈ U i) (a b : Fin 3) (hab : a ≠ b) :
    joiningCopies G (threeCoreLabel U) = G.cutEdges (U a) ∪ G.cutEdges (U b) := by
  simpa only [threeCoreLabel_shore U hdisjoint hcover] using
    joiningCopies_three_eq_two_cuts G (threeCoreLabel U) a b hab

/-- An empty joining pool makes every label fiber an actual component. -/
theorem fiber_cut_empty_of_joining_empty {E I : Type*} [Fintype E] [DecidableEq I]
    (G : Multigraph V E) (label : V → I)
    (hjoin : joiningCopies G label = ∅) (i : I) :
    G.cutEdges (labelShore label {i}) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  have he' : e ∈ G.cutOn univ (labelShore label {i}) :=
    (G.mem_cutOn univ _ e).mpr ⟨mem_univ _, (G.mem_cutEdges _ e).mp he⟩
  have hj := cut_labelShore_subset_joining G label {i} he'
  rw [hjoin] at hj
  exact notMem_empty e hj

end Overfull.Terminal
