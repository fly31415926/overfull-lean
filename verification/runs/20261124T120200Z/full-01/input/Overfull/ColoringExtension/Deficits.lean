import Overfull.ColoringExtension.Balance
import Overfull.CriticalMultigraph

/-!
# Quantitative uncovered sets of a balanced internal coloring

All deficits are actual finite sets. Double counting converts the class
spread and the original degree lower bound into per-color and per-vertex
repair bounds. Removing the fixed forbidden footprint preserves the
required even parity when both the order and that footprint are even.
-/

namespace Overfull.Multigraph.EdgeColoring

open Finset Classical
open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E]
variable {G : Multigraph V E} {h : ℕ}

/-- Vertices not covered by the given actual color class. -/
noncomputable def uncoveredVertices (c : G.EdgeColoring h) (i : Fin h) : Finset V :=
  univ \ c.coveredVertices i

omit [Fintype E] in
@[simp] theorem mem_uncoveredVertices (c : G.EdgeColoring h) (i : Fin h) (v : V) :
    v ∈ c.uncoveredVertices i ↔ ¬ c.Covers i v := by
  simp [uncoveredVertices]

omit [Fintype E] in
theorem uncovered_card_add_covered (c : G.EdgeColoring h) (i : Fin h) :
    (c.uncoveredVertices i).card + (c.coveredVertices i).card = Fintype.card V := by
  simpa only [uncoveredVertices, Finset.card_univ] using
    Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (c.coveredVertices i))

theorem sum_coveredVertices_card (c : G.EdgeColoring h) :
    (∑ i, ((c.coveredVertices i).card : ℝ)) = ∑ v, (G.degree v : ℝ) := by
  have hh := c.sum_coveredCount (univ : Finset V)
  simp only [c.coveredCount_univ] at hh
  exact_mod_cast hh

/-- Edge-class spread gives twice that spread in covered vertex counts. -/
theorem coveredVertices_spread_le (c : G.EdgeColoring h) (b : ℕ)
    (hspread : ∀ i j,
      |((c.colorClass i).card : ℤ) - ((c.colorClass j).card : ℤ)| ≤ b)
    (i j : Fin h) :
    ((c.coveredVertices i).card : ℝ) ≤ (c.coveredVertices j).card + 2 * b := by
  have hh := (abs_le.mp (hspread i j)).2
  have hcov : c.coveredCount univ i ≤ c.coveredCount univ j + 2 * (b : ℤ) := by
    rw [c.coveredCount_univ_eq_two_mul_colorClass, c.coveredCount_univ_eq_two_mul_colorClass]
    omega
  simp only [c.coveredCount_univ] at hcov
  exact_mod_cast hcov

/-- The scaled per-color deficit bound needs no division by the palette
size. It follows from actual degree counting and the actual class spread. -/
theorem uncovered_scaled_bound (c : G.EdgeColoring h) (f : ℕ)
    (hspread : ∀ i j,
      |((c.colorClass i).card : ℤ) - ((c.colorClass j).card : ℤ)| ≤ (f : ℤ) + 1)
    (D : ℝ) (hdegree : ∀ v, (h : ℝ) - D ≤ G.degree v) (i : Fin h) :
    (h : ℝ) * (c.uncoveredVertices i).card ≤
      Fintype.card V * D + 2 * h * ((f : ℝ) + 1) := by
  have hcompare (j : Fin h) :
      ((c.coveredVertices j).card : ℝ) ≤ (c.coveredVertices i).card + 2 * ((f : ℝ) + 1) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      c.coveredVertices_spread_le (f + 1)
        (by simpa only [Nat.cast_add, Nat.cast_one] using hspread) j i
  have hupper := Finset.sum_le_sum
    (fun j (_ : j ∈ (univ : Finset (Fin h))) => hcompare j)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hupper
  rw [c.sum_coveredVertices_card] at hupper
  have hlower : (Fintype.card V : ℝ) * ((h : ℝ) - D) ≤ ∑ v, (G.degree v : ℝ) := by
    calc
      _ = ∑ _v : V, ((h : ℝ) - D) := by simp [mul_sub]
      _ ≤ _ := Finset.sum_le_sum (fun v _ => hdegree v)
  have hcard : ((c.uncoveredVertices i).card : ℝ) + (c.coveredVertices i).card =
      Fintype.card V := by exact_mod_cast c.uncovered_card_add_covered i
  have hmul := congrArg (fun x : ℝ => (h : ℝ) * x) hcard
  nlinarith

omit [Fintype V] in
/-- The already defined missing-color set has the exact natural deficit. -/
theorem missingColors_card_eq_sub (c : G.EdgeColoring h) (v : V) :
    (c.missingColors v).card = h - G.degree v := by
  have hh := c.missingColors_card_add_degree v
  omega

omit [Fintype V] in
theorem missingColors_card_le_error (c : G.EdgeColoring h) (D : ℝ)
    (hdegree : ∀ v, (h : ℝ) - D ≤ G.degree v) (v : V) :
    ((c.missingColors v).card : ℝ) ≤ D := by
  have hh : ((c.missingColors v).card : ℝ) + G.degree v = h := by
    exact_mod_cast c.missingColors_card_add_degree v
  linarith [hdegree v]

omit [Fintype E] in
theorem uncoveredColors_eq_missing (c : G.EdgeColoring h) (v : V) :
    univ.filter (fun i => v ∈ c.uncoveredVertices i) = c.missingColors v := by
  ext i
  simp only [mem_filter, mem_univ, true_and, mem_uncoveredVertices, mem_missingColors]

theorem uncovered_incidence_eq_sub (c : G.EdgeColoring h) (v : V) :
    (univ.filter (fun i => v ∈ c.uncoveredVertices i)).card = h - G.degree v := by
  rw [c.uncoveredColors_eq_missing, c.missingColors_card_eq_sub]

theorem uncovered_incidence_le_error (c : G.EdgeColoring h) (D : ℝ)
    (hdegree : ∀ v, (h : ℝ) - D ≤ G.degree v) (v : V) :
    ((univ.filter (fun i => v ∈ c.uncoveredVertices i)).card : ℝ) ≤ D := by
  rw [c.uncoveredColors_eq_missing]
  exact c.missingColors_card_le_error D hdegree v

/-- The vertices still needing repair after the fixed footprint and the
actual internal matching have both been accounted for. -/
noncomputable def repairVertices (c : G.EdgeColoring h)
    (F : Fin h → Finset V) (i : Fin h) : Finset V :=
  univ \ (F i ∪ c.coveredVertices i)

omit [Fintype E] in
@[simp] theorem mem_repairVertices (c : G.EdgeColoring h)
    (F : Fin h → Finset V) (i : Fin h) (v : V) :
    v ∈ c.repairVertices F i ↔ v ∉ F i ∧ ¬ c.Covers i v := by
  simp [repairVertices, not_or]

omit [Fintype E] in
theorem repairVertices_subset_uncovered (c : G.EdgeColoring h)
    (F : Fin h → Finset V) (i : Fin h) :
    c.repairVertices F i ⊆ c.uncoveredVertices i := by
  intro v hv
  exact (c.mem_uncoveredVertices i v).mpr ((c.mem_repairVertices F i v).mp hv).2

omit [Fintype E] in
theorem repairVertices_card_le_uncovered (c : G.EdgeColoring h)
    (F : Fin h → Finset V) (i : Fin h) :
    (c.repairVertices F i).card ≤ (c.uncoveredVertices i).card :=
  Finset.card_le_card (c.repairVertices_subset_uncovered F i)

omit [Fintype E] in
theorem repairVertices_disjoint_forbidden (c : G.EdgeColoring h)
    (F : Fin h → Finset V) (i : Fin h) : Disjoint (c.repairVertices F i) (F i) := by
  apply Finset.disjoint_left.mpr
  intro v hv hF
  exact ((c.mem_repairVertices F i v).mp hv).1 hF

omit [Fintype E] in
theorem repairVertices_disjoint_covered (c : G.EdgeColoring h)
    (F : Fin h → Finset V) (i : Fin h) :
    Disjoint (c.repairVertices F i) (c.coveredVertices i) := by
  apply Finset.disjoint_left.mpr
  intro v hv hc
  exact ((c.mem_repairVertices F i v).mp hv).2 ((c.mem_coveredVertices i v).mp hc)

omit [Fintype E] in
theorem avoidsVertices_disjoint (c : G.EdgeColoring h)
    (F : Fin h → Finset V) (hc : c.AvoidsVertices F) (i : Fin h) :
    Disjoint (F i) (c.coveredVertices i) := by
  apply Finset.disjoint_left.mpr
  intro v hF hv
  exact hc i v ((c.mem_coveredVertices i v).mp hv) hF

omit [Fintype E] in
theorem repairVertices_card_partition (c : G.EdgeColoring h)
    (F : Fin h → Finset V) (hc : c.AvoidsVertices F) (i : Fin h) :
    (c.repairVertices F i).card + (F i).card + (c.coveredVertices i).card =
      Fintype.card V := by
  have hh := Finset.card_sdiff_add_card_eq_card
    (Finset.subset_univ (F i ∪ c.coveredVertices i))
  rw [Finset.card_union_of_disjoint (c.avoidsVertices_disjoint F hc i)] at hh
  simpa only [repairVertices, Finset.card_univ, Nat.add_assoc] using hh

omit [Fintype E] in
theorem repairVertices_card_add_forbidden (c : G.EdgeColoring h)
    (F : Fin h → Finset V) (hc : c.AvoidsVertices F) (i : Fin h) :
    (c.repairVertices F i).card + (F i).card = (c.uncoveredVertices i).card := by
  have h₁ := c.repairVertices_card_partition F hc i
  have h₂ := c.uncovered_card_add_covered i
  omega

omit [Fintype E] in
theorem repairVertices_incidence_le_missing (c : G.EdgeColoring h)
    (F : Fin h → Finset V) (v : V) :
    (univ.filter (fun i => v ∈ c.repairVertices F i)).card ≤ (c.missingColors v).card := by
  apply Finset.card_le_card
  intro i hi
  exact (c.mem_missingColors v i).mpr
    ((c.mem_repairVertices F i v).mp (mem_filter.mp hi).2).2

theorem repairVertices_incidence_le_error (c : G.EdgeColoring h)
    (F : Fin h → Finset V) (D : ℝ)
    (hdegree : ∀ v, (h : ℝ) - D ≤ G.degree v) (v : V) :
    ((univ.filter (fun i => v ∈ c.repairVertices F i)).card : ℝ) ≤ D := by
  have hh : ((univ.filter (fun i => v ∈ c.repairVertices F i)).card : ℝ) ≤
      (c.missingColors v).card := by exact_mod_cast c.repairVertices_incidence_le_missing F v
  exact hh.trans (c.missingColors_card_le_error D hdegree v)

theorem repairVertices_scaled_bound (c : G.EdgeColoring h)
    (F : Fin h → Finset V) (f : ℕ)
    (hspread : ∀ i j,
      |((c.colorClass i).card : ℤ) - ((c.colorClass j).card : ℤ)| ≤ (f : ℤ) + 1)
    (D : ℝ) (hdegree : ∀ v, (h : ℝ) - D ≤ G.degree v) (i : Fin h) :
    (h : ℝ) * (c.repairVertices F i).card ≤
      Fintype.card V * D + 2 * h * ((f : ℝ) + 1) := by
  apply le_trans _ (c.uncovered_scaled_bound f hspread D hdegree i)
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg h)
  exact_mod_cast c.repairVertices_card_le_uncovered F i

/-- Both actual matching coverage and the prescribed footprint have even
size, so their disjoint complement has the required even size. -/
theorem repairVertices_even (c : G.EdgeColoring h)
    (F : Fin h → Finset V) (hc : c.AvoidsVertices F)
    (hm : Even (Fintype.card V)) (hF : ∀ i, Even (F i).card) (i : Fin h) :
    Even (c.repairVertices F i).card := by
  have hpart := c.repairVertices_card_partition F hc i
  have hcover := c.coveredVertices_even i
  have hFi := hF i
  rw [Nat.even_iff] at hm hcover hFi ⊢
  omega

end Overfull.Multigraph.EdgeColoring
