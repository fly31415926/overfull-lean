import Overfull.CompatibleCircuits.EqualBundleSafety
import Overfull.CompatibleCircuits.EqualBundlePair
import Overfull.CompatibleCircuits.UnequalBundleSelection
import Overfull.CompatibleCircuits.SafeSelectionInduction
import Overfull.CompatibleCircuits.VertexRelabeling

/-!
# Compatible circuit partitions on three labels

The original half-cut inequalities and even degrees suffice to partition
every selected actual edge copy into compatible circuits.  A nonempty
admissible residual has a safely removable parallel pair or triangle.
There is no assumed circuit selector in either final theorem.

This proves the three-label case, allowing isolated labels and arbitrary
parallel multiplicities and incidence classes.  It does not prove the
general four-label Fan--Zhang theorem used elsewhere in the manuscript.
-/

namespace Overfull.Multigraph

open Finset Classical

variable {E K : Type*} (Q : Multigraph (Fin 3) E)

/-- Equal positive bundles have a safe compatible pair or triangle. -/
theorem exists_safe_circuit_of_equal_threeLabel_bundles
    (classOf : Fin 3 → E → K) (C : Finset E)
    (hadmissible : Q.AdmissibleOn classOf C)
    (heven : ∀ v, Even (Q.degreeOn C v))
    (hAC : (Q.edgeBundleOn C 0 2).card = (Q.edgeBundleOn C 0 1).card)
    (hBC : (Q.edgeBundleOn C 1 2).card = (Q.edgeBundleOn C 0 1).card)
    (hpos : 0 < (Q.edgeBundleOn C 0 1).card) :
    ∃ D ⊆ C, Q.IsCircuit D ∧ Q.Compatible classOf D ∧
      Q.AdmissibleOn classOf (C \ D) ∧ (D.card = 2 ∨ D.card = 3) := by
  by_cases htight : ∃ v w k, v ≠ w ∧
      Q.degreeOn C w = 2 * (Q.classCutOn classOf C v k {w}).card
  · obtain ⟨D, hDC, hD, hcomp, hsafe, hcard⟩ :=
      Q.exists_safe_triangle_of_equal_bundles_of_nonlocal_tight
        classOf C hadmissible hAC hBC hpos htight
    exact ⟨D, hDC, hD, hcomp, hsafe, Or.inr hcard⟩
  · have hno : ∀ v k w, v ≠ w →
        Q.degreeOn C w ≠ 2 * (Q.classCutOn classOf C v k {w}).card := by
      intro v k w hne heq
      exact htight ⟨v, w, k, hne, heq⟩
    obtain ⟨D, hDC, hD, hcomp, hcard, hsafe⟩ :=
      Q.exists_safe_parallel_pair_of_equal_bundles_no_nonlocal_tight
        classOf C hadmissible heven hAC hBC hpos hno
    exact ⟨D, hDC, hD, hcomp, hsafe, Or.inl hcard⟩

/-- The selector for a graph whose three bundle sizes have been sorted. -/
theorem exists_safe_circuit_of_sorted_threeLabel_bundles
    (classOf : Fin 3 → E → K) (C : Finset E) (hC : C.Nonempty)
    (hadmissible : Q.AdmissibleOn classOf C)
    (heven : ∀ v, Even (Q.degreeOn C v))
    (hxy : (Q.edgeBundleOn C 0 2).card ≤ (Q.edgeBundleOn C 0 1).card)
    (hyz : (Q.edgeBundleOn C 1 2).card ≤ (Q.edgeBundleOn C 0 2).card) :
    ∃ D ⊆ C, Q.IsCircuit D ∧ Q.Compatible classOf D ∧
      Q.AdmissibleOn classOf (C \ D) ∧ (D.card = 2 ∨ D.card = 3) := by
  by_cases hxz : (Q.edgeBundleOn C 1 2).card < (Q.edgeBundleOn C 0 1).card
  · obtain ⟨D, hDC, hD, hcomp, hsafe, hcard⟩ :=
      Q.exists_safe_parallel_pair_of_unequal_threeLabel_bundles
        classOf C hadmissible heven hxz hyz
    exact ⟨D, hDC, hD, hcomp, hsafe, Or.inl hcard⟩
  · have hAC : (Q.edgeBundleOn C 0 2).card = (Q.edgeBundleOn C 0 1).card := by omega
    have hBC : (Q.edgeBundleOn C 1 2).card = (Q.edgeBundleOn C 0 1).card := by omega
    have hpos : 0 < (Q.edgeBundleOn C 0 1).card := by
      by_contra! hz
      have hABzero : Q.edgeBundleOn C 0 1 = ∅ := card_eq_zero.mp (by omega)
      have hACzero : Q.edgeBundleOn C 0 2 = ∅ := card_eq_zero.mp (by omega)
      have hBCzero : Q.edgeBundleOn C 1 2 = ∅ := card_eq_zero.mp (by omega)
      have hcover := Q.threeLabel_bundles_cover C
      rw [hABzero, hACzero, hBCzero, union_empty] at hcover
      exact hC.ne_empty hcover.symm
    exact Q.exists_safe_circuit_of_equal_threeLabel_bundles
      classOf C hadmissible heven hAC hBC hpos

/-- Every nonempty admissible even-degree graph on three labels has a
safe compatible circuit, selected from its original edge copies. -/
theorem exists_threeLabel_safe_circuit
    (classOf : Fin 3 → E → K) (C : Finset E) (hC : C.Nonempty)
    (hadmissible : Q.AdmissibleOn classOf C)
    (heven : ∀ v, Even (Q.degreeOn C v)) :
    ∃ D ⊆ C, Q.IsCircuit D ∧ Q.Compatible classOf D ∧
      Q.AdmissibleOn classOf (C \ D) ∧ (D.card = 2 ∨ D.card = 3) := by
  obtain ⟨φ, hxy, hyz⟩ := exists_threeLabel_sorted_renaming Q C
  let R := Q.renameVertices φ
  let renamedClass : Fin 3 → E → K := fun v e => classOf (φ.symm v) e
  have hRadmissible : R.AdmissibleOn renamedClass C :=
    (Q.renameVertices_admissibleOn φ classOf C).mpr hadmissible
  have hReven : ∀ v, Even (R.degreeOn C v) := by
    intro v
    simpa only [R, Q.renameVertices_degreeOn] using heven (φ.symm v)
  obtain ⟨D, hDC, hD, hcomp, hsafe, hcard⟩ :=
    R.exists_safe_circuit_of_sorted_threeLabel_bundles
      renamedClass C hC hRadmissible hReven hxy hyz
  exact ⟨D, hDC, (Q.renameVertices_isCircuit φ D).mp hD,
    (Q.renameVertices_compatible φ classOf D).mp hcomp,
    (Q.renameVertices_admissibleOn φ classOf (C \ D)).mp hsafe, hcard⟩

/-- Complete compatible circuit decomposition on three labels from the
original half-cut inequalities and even degrees, without a selector input. -/
theorem exists_threeLabel_compatibleCircuitPartition
    (classOf : Fin 3 → E → K) (C : Finset E)
    (hadmissible : Q.AdmissibleOn classOf C)
    (heven : ∀ v, Even (Q.degreeOn C v)) :
    Nonempty (Q.CompatibleCircuitPartition classOf C) := by
  apply Q.exists_compatibleCircuitPartition_of_safe_selection
    classOf C ?_ hadmissible heven
  intro R _ hR hRadmissible hReven
  obtain ⟨D, hDR, hD, hcomp, hsafe, _⟩ :=
    Q.exists_threeLabel_safe_circuit classOf R hR hRadmissible hReven
  exact ⟨D, hDR, hD, hcomp, hsafe⟩

/-- For an even-degree graph on three labels, the exact half-cut bounds
are both necessary and sufficient for a compatible circuit partition. -/
theorem threeLabel_compatibleCircuitPartition_iff_admissible
    (classOf : Fin 3 → E → K) (C : Finset E)
    (heven : ∀ v, Even (Q.degreeOn C v)) :
    Nonempty (Q.CompatibleCircuitPartition classOf C) ↔ Q.AdmissibleOn classOf C := by
  constructor
  · rintro ⟨P⟩
    exact P.admissibleOn Q
  · intro hadmissible
    exact Q.exists_threeLabel_compatibleCircuitPartition classOf C hadmissible heven

end Overfull.Multigraph
