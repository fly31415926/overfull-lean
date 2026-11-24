import Overfull.CompatibleCircuits.FourSupportReduction
import Overfull.CompatibleCircuits.FourStrictDiamond

/-!
# Complete support selection in the strict nonlocal branch

Admissibility and strict nonlocal half-cut inequalities on four labels
force a compatible pair or triangle whenever the selected set is nonempty.
Equal-size square bundles would contradict a strict singleton cut; the
other two support shapes also force a short circuit. No degree or
multiplicity bound is used.
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

/-- A square with no compatible pair has constant equal-size neighboring
bundles, contradicting the strict singleton bound at an adjacent vertex. -/
theorem strictNonlocal_square_support_has_pair
    (classOf : Fin 4 → E → K) (C : Finset E)
    (hadmissible : Q.AdmissibleOn classOf C)
    (hstrict : Q.StrictNonlocalOn classOf C)
    (hshape : C.image Q.edge = square) :
    ∃ D : Finset E, D ⊆ C ∧ Q.IsCircuit D ∧
      Q.Compatible classOf D ∧ D.card = 2 := by
  by_contra hnone
  have hpositive (u v : Fin 4) (huv : s(u,v) ∈ square) :
      (Q.edgeBundleOn C u v).Nonempty := by
    have hp : s(u,v) ∈ C.image Q.edge := by rwa [hshape]
    obtain ⟨e, he, hh⟩ := mem_image.mp hp
    exact ⟨e, (Q.mem_edgeBundleOn C u v e).mpr ⟨he, hh⟩⟩
  have hcover (e : E) (he : e ∈ C) : ∃ i, Q.edge e = UniformCycle.pairs i := by
    have hp : Q.edge e ∈ square := hshape ▸ mem_image.mpr ⟨e, he, rfl⟩
    obtain ⟨i, _, hi⟩ := mem_image.mp hp
    exact ⟨i, hi.symm⟩
  have hinc0 : C.filter (fun e => (0 : Fin 4) ∈ Q.edge e) =
      Q.edgeBundleOn C 0 3 ∪ Q.edgeBundleOn C 0 1 := by
    convert Q.fourCycle_incident_copies C hcover 0 using 1
  have hinc1 : C.filter (fun e => (1 : Fin 4) ∈ Q.edge e) =
      Q.edgeBundleOn C 1 0 ∪ Q.edgeBundleOn C 1 2 := by
    convert Q.fourCycle_incident_copies C hcover 1 using 1
  have h0 := Q.two_neighbor_bundle_structure classOf C hadmissible hnone
    (v := 0) (u := 3) (w := 1) (by decide) (by decide) (by decide)
    (hpositive 0 3 (by decide)) (hpositive 0 1 (by decide))
    (by convert hinc0 using 1; ext e; simp)
    (fun k => hstrict.singleton_bound Q (by decide) (by decide) k)
    (fun k => hstrict.singleton_bound Q (by decide) (by decide) k)
  have h1 := Q.two_neighbor_bundle_structure classOf C hadmissible hnone
    (v := 1) (u := 0) (w := 2) (by decide) (by decide) (by decide)
    (hpositive 1 0 (by decide)) (hpositive 1 2 (by decide))
    (by convert hinc1 using 1; ext e; simp)
    (fun k => hstrict.singleton_bound Q (by decide) (by decide) k)
    (fun k => hstrict.singleton_bound Q (by decide) (by decide) k)
  obtain ⟨k, _, _, hk, _⟩ := h1.2
  have hdegree : Q.degreeOn C 0 =
      (Q.edgeBundleOn C 0 3).card + (Q.edgeBundleOn C 0 1).card := by
    unfold degreeOn
    have hinc := congrArg Finset.card hinc0
    rw [card_union_of_disjoint (Q.edgeBundleOn_disjoint (by decide))] at hinc
    convert hinc using 1
    congr 1
    ext e
    simp
  have hbound := hstrict.singleton_bound Q (by decide)
    (by decide : (1 : Fin 4) ≠ 0) k
  rw [Q.classCutOn_singleton_other classOf C (by decide : (1 : Fin 4) ≠ 0),
    filter_eq_self.mpr hk, Q.edgeBundleOn_swap C 1 0] at hbound
  have hequal := h0.1
  omega

/-- Every nonempty strict four-label input has an actual compatible pair
or triangle. This closes all simple support cases without any degree or
multiplicity bound, or an even-degree hypothesis. -/
theorem exists_short_compatible_circuit_of_four_strictNonlocal
    (classOf : Fin 4 → E → K) (C : Finset E)
    (hC : C.Nonempty)
    (hadmissible : Q.AdmissibleOn classOf C)
    (hstrict : Q.StrictNonlocalOn classOf C) :
    ∃ D : Finset E, D ⊆ C ∧ Q.IsCircuit D ∧
      Q.Compatible classOf D ∧ D.card ≤ 3 := by
  by_contra hshort
  have hnone : ¬ ∃ D : Finset E, D ⊆ C ∧ Q.IsCircuit D ∧
        Q.Compatible classOf D ∧ D.card = 2 := by
      rintro ⟨D, hDC, hD, hc, hn⟩
      exact hshort ⟨D, hDC, hD, hc, by omega⟩
  rcases hstrict.four_support_classification Q hC hadmissible hnone with
      ⟨i, hi⟩ | ⟨i, hi⟩ | hi
  · let σ := squarePermutation i
    let R := Q.renameVertices σ.symm
    let classes := fun v e => classOf (σ v) e
    have hshape : C.image R.edge = square :=
      Q.renameVertices_support_of_shape C square σ hi
    obtain ⟨D, hDC, hD, hc, hn⟩ := R.strictNonlocal_square_support_has_pair classes C
      ((Q.renameVertices_admissibleOn σ.symm classOf C).mpr hadmissible)
      (hstrict.renameVertices Q σ.symm) hshape
    exact hnone ⟨D, hDC, (Q.renameVertices_isCircuit σ.symm D).mp hD,
      (Q.renameVertices_compatible σ.symm classOf D).mp hc, hn⟩
  · let σ := diamondPermutation i
    let R := Q.renameVertices σ.symm
    let classes := fun v e => classOf (σ v) e
    have hshape : C.image R.edge = diamond :=
      Q.renameVertices_support_of_shape C diamond σ hi
    have hpositive (u v : Fin 4) (huv : s(u,v) ∈ diamond) :
        (R.edgeBundleOn C u v).Nonempty := by
      have hp : s(u,v) ∈ C.image R.edge := by rwa [hshape]
      obtain ⟨e, he, hh⟩ := mem_image.mp hp
      exact ⟨e, (R.mem_edgeBundleOn C u v e).mpr ⟨he, hh⟩⟩
    have hzero : R.edgeBundleOn C 2 3 = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro e he
      obtain ⟨heC, heends⟩ := (R.mem_edgeBundleOn C 2 3 e).mp he
      have hp : s(2,3) ∈ C.image R.edge := mem_image.mpr ⟨e, heC, heends⟩
      rw [hshape] at hp
      exact (by decide : s((2 : Fin 4),3) ∉ diamond) hp
    obtain ⟨D, hDC, hD, hc, hn⟩ :=
      R.exists_short_compatible_circuit_of_four_diamond_support classes C
        ((Q.renameVertices_admissibleOn σ.symm classOf C).mpr hadmissible)
        (hstrict.renameVertices Q σ.symm)
        (hpositive 0 1 (by decide)) (hpositive 0 2 (by decide))
        (hpositive 0 3 (by decide)) (hpositive 1 2 (by decide))
        (hpositive 1 3 (by decide)) hzero
    exact hshort ⟨D, hDC, (Q.renameVertices_isCircuit σ.symm D).mp hD,
      (Q.renameVertices_compatible σ.symm classOf D).mp hc, hn⟩
  · have hpositive (u v : Fin 4) (huv : s(u,v) ∈ complete) :
        (Q.edgeBundleOn C u v).Nonempty := by
      have hp : s(u,v) ∈ C.image Q.edge := by rwa [hi]
      obtain ⟨e, he, hh⟩ := mem_image.mp hp
      exact ⟨e, (Q.mem_edgeBundleOn C u v e).mpr ⟨he, hh⟩⟩
    exact hshort (Q.exists_short_compatible_circuit_of_four_complete_support
      classOf C hadmissible hstrict (hpositive 0 1 (by decide))
      (hpositive 0 2 (by decide)) (hpositive 0 3 (by decide))
      (hpositive 1 2 (by decide)) (hpositive 1 3 (by decide))
      (hpositive 2 3 (by decide)))
/-- The empty input supplies its exact partition; every nonempty input
supplies the short circuit proved above. -/
theorem short_compatible_circuit_or_partition_of_four_strictNonlocal
    (classOf : Fin 4 → E → K) (C : Finset E)
    (hadmissible : Q.AdmissibleOn classOf C)
    (hstrict : Q.StrictNonlocalOn classOf C) :
    (∃ D : Finset E, D ⊆ C ∧ Q.IsCircuit D ∧
      Q.Compatible classOf D ∧ D.card ≤ 3) ∨
    Nonempty (Q.CompatibleCircuitPartition classOf C) := by
  by_cases hC : C.Nonempty
  · exact Or.inl (Q.exists_short_compatible_circuit_of_four_strictNonlocal
      classOf C hC hadmissible hstrict)
  · right
    have hzero : C = ∅ := not_nonempty_iff_eq_empty.mp hC
    subst C
    exact ⟨CompatibleCircuitPartition.empty Q classOf⟩

end Overfull.Multigraph
