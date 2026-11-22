import Overfull.ColoringExtension.Deficits

/-!
# Actual footprints of an equitable exterior coloring

Every exterior vertex of degree equal to the palette size is covered by
every color. Thus the core footprint of a color is obtained by subtracting
the same exterior set from its full matching coverage. Equitable edge
classes give the quantitative footprint bound, and even exterior order
gives the parity required by the later internal extension.
-/

namespace Overfull.Multigraph.EdgeColoring

open Finset Classical
open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E]
variable {G : Multigraph V E} {k : ℕ}

/-- The actual core vertices used by one exterior color class. -/
noncomputable def exteriorFootprint (c : G.EdgeColoring k) (U : Finset V)
    (i : Fin k) : Finset V :=
  U ∩ c.coveredVertices i

omit [Fintype E] in
@[simp] theorem mem_exteriorFootprint (c : G.EdgeColoring k) (U : Finset V)
    (i : Fin k) (v : V) :
    v ∈ c.exteriorFootprint U i ↔ v ∈ U ∧ c.Covers i v := by
  simp only [exteriorFootprint, Finset.mem_inter, c.mem_coveredVertices]

omit [Fintype E] in
theorem exteriorFootprint_subset (c : G.EdgeColoring k) (U : Finset V) (i : Fin k) :
    c.exteriorFootprint U i ⊆ U := Finset.inter_subset_left

omit [Fintype E] in
theorem exteriorFootprint_subset_covered (c : G.EdgeColoring k) (U : Finset V)
    (i : Fin k) : c.exteriorFootprint U i ⊆ c.coveredVertices i :=
  Finset.inter_subset_right

/-- Saturation at every exterior vertex follows from its actual degree. -/
theorem exterior_covered (c : G.EdgeColoring k) (U : Finset V)
    (hZ : ∀ v ∈ Uᶜ, G.degree v = k) (i : Fin k) :
    Uᶜ ⊆ c.coveredVertices i := by
  intro v hv
  exact (c.mem_coveredVertices i v).mpr (c.covers_of_degree_eq v (hZ v hv) i)

theorem exteriorFootprint_card_add_exterior (c : G.EdgeColoring k) (U : Finset V)
    (hZ : ∀ v ∈ Uᶜ, G.degree v = k) (i : Fin k) :
    (c.exteriorFootprint U i).card + Uᶜ.card = (c.coveredVertices i).card := by
  have hdiff : c.coveredVertices i \ U = Uᶜ := by
    ext v
    simp only [Finset.mem_sdiff, Finset.mem_compl]
    constructor
    · exact fun hv => hv.2
    · intro hv
      exact ⟨c.exterior_covered U hZ i (Finset.mem_compl.mpr hv), hv⟩
  have hh := Finset.card_inter_add_card_sdiff (c.coveredVertices i) U
  rw [hdiff, Finset.inter_comm] at hh
  exact hh

theorem exteriorFootprint_even (c : G.EdgeColoring k) (U : Finset V)
    (hZ : ∀ v ∈ Uᶜ, G.degree v = k) (hZeven : Even Uᶜ.card) (i : Fin k) :
    Even (c.exteriorFootprint U i).card := by
  have hcard := c.exteriorFootprint_card_add_exterior U hZ i
  have hcover := c.coveredVertices_even i
  rw [Nat.even_iff] at hZeven hcover ⊢
  omega

/-- A core vertex occurs in precisely its actual degree many footprints. -/
theorem exteriorFootprint_incidence (c : G.EdgeColoring k) (U : Finset V)
    (v : V) (hv : v ∈ U) :
    (univ.filter (fun i => v ∈ c.exteriorFootprint U i)).card = G.degree v := by
  simpa only [c.mem_exteriorFootprint, hv, true_and] using c.coveredColors_card v

theorem sum_exteriorFootprint_card (c : G.EdgeColoring k) (U : Finset V) :
    (∑ i, ((c.exteriorFootprint U i).card : ℝ)) = ∑ v ∈ U, (G.degree v : ℝ) := by
  have hh := c.sum_coveredCount U
  simp only [coveredCount] at hh
  exact_mod_cast hh

/-- Equitable full edge classes yield core coverage spread at most two,
because every color covers exactly the same exterior vertex set. -/
theorem exteriorFootprint_spread_le (c : G.EdgeColoring k) (U : Finset V)
    (hZ : ∀ v ∈ Uᶜ, G.degree v = k)
    (hspread : ∀ i j,
      |((c.colorClass i).card : ℤ) - ((c.colorClass j).card : ℤ)| ≤ 1)
    (i j : Fin k) :
    ((c.exteriorFootprint U i).card : ℝ) ≤ (c.exteriorFootprint U j).card + 2 := by
  have hfull := c.coveredVertices_spread_le 1 hspread i j
  have hi : ((c.exteriorFootprint U i).card : ℝ) + Uᶜ.card =
      (c.coveredVertices i).card := by
    exact_mod_cast c.exteriorFootprint_card_add_exterior U hZ i
  have hj : ((c.exteriorFootprint U j).card : ℝ) + Uᶜ.card =
      (c.coveredVertices j).card := by
    exact_mod_cast c.exteriorFootprint_card_add_exterior U hZ j
  norm_num only [Nat.cast_one, mul_one] at hfull
  linarith

/-- Scaled size bound for the actual exterior footprint. The scaled form
also makes sense for an empty palette. -/
theorem exteriorFootprint_scaled_bound (c : G.EdgeColoring k) (U : Finset V)
    (a : ℝ) (hcore : ∀ v ∈ U, (G.degree v : ℝ) ≤ a)
    (hZ : ∀ v ∈ Uᶜ, G.degree v = k)
    (hspread : ∀ i j,
      |((c.colorClass i).card : ℤ) - ((c.colorClass j).card : ℤ)| ≤ 1)
    (i : Fin k) :
    (k : ℝ) * (c.exteriorFootprint U i).card ≤ a * U.card + 2 * k := by
  have hsum := Finset.sum_le_sum
    (fun j (_ : j ∈ (univ : Finset (Fin k))) =>
      c.exteriorFootprint_spread_le U hZ hspread i j)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hsum
  rw [c.sum_exteriorFootprint_card U] at hsum
  have hdegree : (∑ v ∈ U, (G.degree v : ℝ)) ≤ a * U.card := by
    calc
      _ ≤ ∑ _v ∈ U, a := Finset.sum_le_sum (fun v hv => hcore v hv)
      _ = _ := by simp [mul_comm]
  linarith

/-- Dividing the scaled bound is legitimate when the palette is nonempty. -/
theorem exteriorFootprint_card_le (c : G.EdgeColoring k) (U : Finset V)
    (a : ℝ) (hcore : ∀ v ∈ U, (G.degree v : ℝ) ≤ a)
    (hZ : ∀ v ∈ Uᶜ, G.degree v = k)
    (hspread : ∀ i j,
      |((c.colorClass i).card : ℤ) - ((c.colorClass j).card : ℤ)| ≤ 1)
    (hk : 0 < k) (i : Fin k) :
    ((c.exteriorFootprint U i).card : ℝ) ≤ a * U.card / k + 2 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hh := c.exteriorFootprint_scaled_bound U a hcore hZ hspread i
  calc
    _ ≤ (a * U.card + 2 * k) / k :=
      (le_div_iff₀ hkR).mpr (by simpa only [mul_comm] using hh)
    _ = _ := by rw [add_div]; simp [ne_of_gt hkR]

/-- An actual supplied exterior coloring can be made equitable before its
labels are fixed. Its resulting actual core footprints have the required
size, incidence and parity properties. -/
theorem exists_equitable_exterior (c₀ : G.EdgeColoring k) (U : Finset V)
    (a : ℝ) (hcore : ∀ v ∈ U, (G.degree v : ℝ) ≤ a)
    (hZ : ∀ v ∈ Uᶜ, G.degree v = k) (hZeven : Even Uᶜ.card) :
    ∃ c : G.EdgeColoring k,
      (∀ i j, |((c.colorClass i).card : ℤ) - ((c.colorClass j).card : ℤ)| ≤ 1) ∧
      (∀ i, Uᶜ ⊆ c.coveredVertices i) ∧
      (∀ i, (k : ℝ) * (c.exteriorFootprint U i).card ≤ a * U.card + 2 * k) ∧
      (∀ i, Even (c.exteriorFootprint U i).card) ∧
      (∀ v ∈ U, (univ.filter (fun i => v ∈ c.exteriorFootprint U i)).card = G.degree v) := by
  obtain ⟨c, hspread⟩ := c₀.exists_equitable
  refine ⟨c, hspread, c.exterior_covered U hZ, ?_, c.exteriorFootprint_even U hZ hZeven, ?_⟩
  · exact c.exteriorFootprint_scaled_bound U a hcore hZ hspread
  · exact fun v hv => c.exteriorFootprint_incidence U v hv

end Overfull.Multigraph.EdgeColoring
