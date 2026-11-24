import Overfull.ColoringExtension.BalanceComponents

/-!
# Class balancing with fixed vertex-forbidden palettes

The finite minimum is taken over actual proper colorings that avoid all
fixed forbidden vertices. Every improving switch remains in this finite
set. Empty forbidden sets give equitable color classes on any finite
loopless multigraph that already has a proper coloring with the palette.
-/

namespace Overfull.Multigraph.EdgeColoring

open Finset Classical
open scoped BigOperators

private theorem balance_sum_change_two {I : Type*} [Fintype I]
    (a b : I → ℤ) (i j : I) (hij : i ≠ j)
    (hother : ∀ r, r ≠ i → r ≠ j → a r = b r) :
    (∑ r, a r) = (∑ r, b r) + (a i - b i) + (a j - b j) := by
  have hpoint (r : I) : a r = b r +
      (if r = i then a i - b i else 0) + (if r = j then a j - b j else 0) := by
    by_cases hri : r = i
    · subst r
      simp [hij]
    · by_cases hrj : r = j
      · subst r
        simp [hri]
      · rw [hother r hri hrj]
        simp [hri, hrj]
  calc
    _ = ∑ r, (b r + (if r = i then a i - b i else 0) +
        (if r = j then a j - b j else 0)) := Finset.sum_congr rfl (fun r _ => hpoint r)
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

variable {V E : Type*} [Fintype V] [Fintype E]
variable {G : Multigraph V E} {k : ℕ}

theorem coveredCount_univ_eq_two_mul_colorClass (c : G.EdgeColoring k) (i : Fin k) :
    c.coveredCount univ i = 2 * ((c.colorClass i).card : ℤ) := by
  rw [c.coveredCount_univ, c.coveredVertices_card]
  simp only [Nat.cast_mul, Nat.cast_ofNat]

/-- Balance actual edge-class sizes while retaining feasibility against
every fixed forbidden-vertex set. An initial feasible coloring is an
explicit input; this theorem does not assume a list-coloring theorem. -/
theorem exists_balanced_avoiding (c₀ : G.EdgeColoring k)
    (F : Fin k → Finset V) (f : ℕ) (hF : ∀ i, (F i).card ≤ f)
    (hc₀ : c₀.AvoidsVertices F) :
    ∃ c : G.EdgeColoring k, c.AvoidsVertices F ∧
      ∀ i j, |((c.colorClass i).card : ℤ) - ((c.colorClass j).card : ℤ)| ≤ (f : ℤ) + 1 := by
  let S : Finset (G.EdgeColoring k) := univ.filter (fun c => c.AvoidsVertices F)
  have hS : S.Nonempty := ⟨c₀, mem_filter.mpr ⟨mem_univ _, hc₀⟩⟩
  obtain ⟨c, hcS, hmin⟩ := Finset.exists_min_image S
    (fun c => ∑ i : Fin k, (c.coveredCount univ i) ^ 2) hS
  have hc : c.AvoidsVertices F := (mem_filter.mp hcS).2
  have hle (i j : Fin k) :
      ((c.colorClass i).card : ℤ) - ((c.colorClass j).card : ℤ) ≤ (f : ℤ) + 1 := by
    by_contra hn
    have hdelta : (f : ℤ) + 1 <
        ((c.colorClass i).card : ℤ) - ((c.colorClass j).card : ℤ) := lt_of_not_ge hn
    have hf : (0 : ℤ) ≤ f := Nat.cast_nonneg _
    have hij : i ≠ j := by intro h; subst j; omega
    have hFZ : ((F j).card : ℤ) ≤ f := by exact_mod_cast hF j
    have hgap : 2 * ((F j).card : ℤ) < c.coveredCount univ i - c.coveredCount univ j := by
      rw [c.coveredCount_univ_eq_two_mul_colorClass, c.coveredCount_univ_eq_two_mul_colorClass]
      omega
    obtain ⟨C, hC, havoid⟩ := c.exists_transfer_two_component_avoiding i j hij (F j) hgap
    let X := c.componentVertices i j C
    let c' := c.swapOn i j X (c.component_closed i j C)
    have hc' : c'.AvoidsVertices F :=
      c.swapOn_avoidsVertices_of_transfer_two F hc i j hij C hC havoid
    have hc'S : c' ∈ S := mem_filter.mpr ⟨mem_univ _, hc'⟩
    have hci : c'.coveredCount univ i = c.coveredCount univ i - 2 := by
      simpa only [c', X, hC] using
        c.swapOn_coveredCount i j X (c.component_closed i j C) univ
    have hcj : c'.coveredCount univ j = c.coveredCount univ j + 2 := by
      simpa only [c', X, hC] using
        c.swapOn_coveredCount_right i j X (c.component_closed i j C) univ
    have henergy := balance_sum_change_two
      (fun r => (c'.coveredCount univ r) ^ 2) (fun r => (c.coveredCount univ r) ^ 2)
      i j hij (by
        intro r hri hrj
        exact congrArg (fun x : ℤ => x ^ 2)
          (c.swapOn_coveredCount_other i j r X (c.component_closed i j C) univ hri hrj))
    simp only [hci, hcj] at henergy
    have hminimal := hmin c' hc'S
    rw [henergy] at hminimal
    have hlarge : 2 < c.coveredCount univ i - c.coveredCount univ j := by
      rw [c.coveredCount_univ_eq_two_mul_colorClass, c.coveredCount_univ_eq_two_mul_colorClass]
      omega
    nlinarith
  refine ⟨c, hc, ?_⟩
  intro i j
  apply abs_le.mpr
  exact ⟨by have h := hle j i; omega, hle i j⟩

/-- Incidence-form interface for a supplied feasible internal extension. -/
theorem exists_balanced_avoiding_incidence (c₀ : G.EdgeColoring k)
    (F : Fin k → Finset V) (f : ℕ) (hF : ∀ i, (F i).card ≤ f)
    (hc₀ : ∀ e v, v ∈ G.edge e → v ∉ F (c₀.color e)) :
    ∃ c : G.EdgeColoring k,
      (∀ e v, v ∈ G.edge e → v ∉ F (c.color e)) ∧
      ∀ i j, |((c.colorClass i).card : ℤ) - ((c.colorClass j).card : ℤ)| ≤ (f : ℤ) + 1 := by
  obtain ⟨c, hc, hspread⟩ := c₀.exists_balanced_avoiding F f hF
    ((c₀.avoidsVertices_iff_incidence F).mpr hc₀)
  exact ⟨c, (c.avoidsVertices_iff_incidence F).mp hc, hspread⟩

/-- Every colorable finite loopless multigraph has an equitable coloring
with the very same palette. Actual parallel edge copies are counted. -/
theorem exists_equitable (c₀ : G.EdgeColoring k) :
    ∃ c : G.EdgeColoring k,
      ∀ i j, |((c.colorClass i).card : ℤ) - ((c.colorClass j).card : ℤ)| ≤ 1 := by
  obtain ⟨c, _hc, hspread⟩ := c₀.exists_balanced_avoiding (fun _ => ∅) 0
    (by intro i; simp) (by intro i v _hv; simp)
  exact ⟨c, by simpa only [Nat.cast_zero, zero_add] using hspread⟩

end Overfull.Multigraph.EdgeColoring
