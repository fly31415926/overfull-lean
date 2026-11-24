import Overfull.CompatibleCircuits.FourSupportReduction
import Overfull.CompatibleCircuits.FourStrictDiamond

/-!
# Complete support selection in the strict nonlocal branch

Admissibility and strict nonlocal half-cut inequalities on four labels
force either a compatible pair or triangle, or a complete compatible
partition of all actual copies. The latter alternative is constructed
from equal-size square bundles. No degree or multiplicity bound is used.
-/

namespace Overfull.Multigraph

open Finset Classical CompatibleCircuits FourSupport

variable {V E K : Type*} (G : Multigraph V E)

/-- A support pair is present precisely when its actual bundle is nonempty. -/
theorem edgeBundleOn_nonempty_iff_mem_image (C : Finset E) (u v : V) :
    (G.edgeBundleOn C u v).Nonempty ↔ s(u,v) ∈ C.image G.edge := by
  constructor
  · rintro ⟨e, he⟩
    obtain ⟨heC, heends⟩ := (G.mem_edgeBundleOn C u v e).mp he
    exact mem_image.mpr ⟨e, heC, heends⟩
  · intro h
    obtain ⟨e, heC, heends⟩ := mem_image.mp h
    exact ⟨e, (G.mem_edgeBundleOn C u v e).mpr ⟨heC, heends⟩⟩

/-- An absent support pair has no selected copy in its bundle. -/
theorem edgeBundleOn_eq_empty_of_not_mem_image (C : Finset E) (u v : V)
    (h : s(u,v) ∉ C.image G.edge) : G.edgeBundleOn C u v = ∅ := by
  apply not_nonempty_iff_eq_empty.mp
  intro hne
  exact h ((G.edgeBundleOn_nonempty_iff_mem_image C u v).mp hne)

variable (Q : Multigraph (Fin 4) E)

/-- Every strict four-label input has a short compatible circuit or a
fully constructed compatible partition. This closes all simple support
cases in the strict branch while retaining arbitrary copy multiplicities. -/
theorem short_compatible_circuit_or_partition_of_four_strictNonlocal
    (classOf : Fin 4 → E → K) (C : Finset E)
    (hadmissible : Q.AdmissibleOn classOf C)
    (hstrict : Q.StrictNonlocalOn classOf C) :
    (∃ D : Finset E, D ⊆ C ∧ Q.IsCircuit D ∧
      Q.Compatible classOf D ∧ D.card ≤ 3) ∨
    Nonempty (Q.CompatibleCircuitPartition classOf C) := by
  by_cases hshort : ∃ D : Finset E, D ⊆ C ∧ Q.IsCircuit D ∧
      Q.Compatible classOf D ∧ D.card ≤ 3
  · exact Or.inl hshort
  right
  by_cases hC : C.Nonempty
  · have hnone : ¬ ∃ D : Finset E, D ⊆ C ∧ Q.IsCircuit D ∧
        Q.Compatible classOf D ∧ D.card = 2 := by
      rintro ⟨D, hDC, hD, hc, hn⟩
      exact hshort ⟨D, hDC, hD, hc, by omega⟩
    rcases hstrict.four_support_classification Q hC hadmissible hnone with
      ⟨i, hi⟩ | ⟨i, hi⟩ | hi
    · exact Q.exists_compatibleCircuitPartition_of_strictNonlocal_square_support
        classOf C hadmissible hstrict (squarePermutation i) hi hnone
    · let σ := diamondPermutation i
      let R := Q.renameVertices σ.symm
      let classes := fun v e => classOf (σ v) e
      have hshape : C.image R.edge = diamond :=
        Q.renameVertices_support_of_shape C diamond σ hi
      have hpositive (u v : Fin 4) (huv : s(u,v) ∈ diamond) :
          (R.edgeBundleOn C u v).Nonempty :=
        (R.edgeBundleOn_nonempty_iff_mem_image C u v).mpr (by rwa [hshape])
      have hzero : R.edgeBundleOn C 2 3 = ∅ :=
        R.edgeBundleOn_eq_empty_of_not_mem_image C 2 3 (by rw [hshape]; decide)
      obtain ⟨D, hDC, hD, hc, hn⟩ :=
        R.exists_short_compatible_circuit_of_four_diamond_support classes C
          ((Q.renameVertices_admissibleOn σ.symm classOf C).mpr hadmissible)
          (hstrict.renameVertices Q σ.symm)
          (hpositive 0 1 (by decide)) (hpositive 0 2 (by decide))
          (hpositive 0 3 (by decide)) (hpositive 1 2 (by decide))
          (hpositive 1 3 (by decide)) hzero
      exact False.elim (hshort ⟨D, hDC, (Q.renameVertices_isCircuit σ.symm D).mp hD,
        (Q.renameVertices_compatible σ.symm classOf D).mp hc, hn⟩)
    · have hpositive (u v : Fin 4) (huv : s(u,v) ∈ complete) :
          (Q.edgeBundleOn C u v).Nonempty :=
        (Q.edgeBundleOn_nonempty_iff_mem_image C u v).mpr (by rwa [hi])
      exact False.elim (hshort (Q.exists_short_compatible_circuit_of_four_complete_support
        classOf C hadmissible hstrict (hpositive 0 1 (by decide))
        (hpositive 0 2 (by decide)) (hpositive 0 3 (by decide))
        (hpositive 1 2 (by decide)) (hpositive 1 3 (by decide))
        (hpositive 2 3 (by decide))))
  · have hzero : C = ∅ := not_nonempty_iff_eq_empty.mp hC
    subst C
    exact ⟨CompatibleCircuitPartition.empty Q classOf⟩

end Overfull.Multigraph
