import Overfull.CompatibleCircuits.FourSupportClassification

/-!
# Relabeling the strict support branches

Vertex equivalences preserve strict nonlocal cut inequalities, all actual
copy sets, and compatible partitions. The square-support endpoint therefore
applies to each labeled square in the finite support classification.
-/

namespace Overfull.Multigraph

open Finset Classical CompatibleCircuits UniformCycle FourSupport

variable {V W E K : Type*} (G : Multigraph V E)

/-- Strictness is invariant under any bijective vertex relabeling. -/
theorem StrictNonlocalOn.renameVertices (φ : V ≃ W)
    {classOf : V → E → K} {C : Finset E}
    (hstrict : G.StrictNonlocalOn classOf C) :
    (G.renameVertices φ).StrictNonlocalOn (fun w e => classOf (φ.symm w) e) C := by
  intro w k X hX
  rw [G.renameVertices_classCutOn, G.renameVertices_cutOn]
  apply hstrict
  obtain ⟨⟨x, hx, hxw⟩, y, hy, hyw⟩ := hX
  refine ⟨⟨φ.symm x, mem_map.mpr ⟨x, hx, rfl⟩,
    fun h => hxw (φ.symm.injective h)⟩, φ.symm y, ?_,
    fun h => hyw (φ.symm.injective h)⟩
  intro h
  obtain ⟨z, hz, hzy⟩ := mem_map.mp h
  have hzy' : z = y := φ.symm.injective hzy
  exact hy (hzy' ▸ hz)

/-- A partition on renamed labels is already a partition of the identical
original copy set, with the original incidence classes. -/
noncomputable def CompatibleCircuitPartition.of_renameVertices
    (φ : V ≃ W) (classOf : V → E → K) {C : Finset E}
    (P : (G.renameVertices φ).CompatibleCircuitPartition
      (fun w e => classOf (φ.symm w) e) C) :
    G.CompatibleCircuitPartition classOf C where
  parts := P.parts
  circuit := fun D hD => (G.renameVertices_isCircuit φ D).mp (P.circuit D hD)
  compatible := fun D hD =>
    (G.renameVertices_compatible φ classOf D).mp (P.compatible D hD)
  disjoint := P.disjoint
  cover := P.cover

variable (Q : Multigraph (Fin 4) E)

/-- Pulling a relabeled support back gives the exact canonical support. -/
theorem renameVertices_support_of_shape (C : Finset E)
    (S : Finset (Sym2 (Fin 4))) (σ : Equiv.Perm (Fin 4))
    (hshape : C.image Q.edge = renamed S σ) :
    C.image (Q.renameVertices σ.symm).edge = S := by
  calc
    _ = (C.image Q.edge).image (Sym2.map σ.symm) := by
      simp only [image_image, renameVertices, Function.comp_def]
    _ = (S.image (Sym2.map σ)).image (Sym2.map σ.symm) := by rw [hshape]; rfl
    _ = S := by simp [image_image, Function.comp_def, Sym2.map_map]

/-- The complete square-support branch in every labeling. No template
is assumed for the original copies, only their exact endpoint support. -/
theorem exists_compatibleCircuitPartition_of_strictNonlocal_square_support
    (classOf : Fin 4 → E → K) (C : Finset E)
    (hadmissible : Q.AdmissibleOn classOf C)
    (hstrict : Q.StrictNonlocalOn classOf C)
    (σ : Equiv.Perm (Fin 4))
    (hshape : C.image Q.edge = renamed square σ)
    (hnone : ¬ ∃ D : Finset E, D ⊆ C ∧ Q.IsCircuit D ∧
      Q.Compatible classOf D ∧ D.card = 2) :
    Nonempty (Q.CompatibleCircuitPartition classOf C) := by
  let R := Q.renameVertices σ.symm
  let classes := fun v e => classOf (σ v) e
  have hRshape : C.image R.edge = square :=
    Q.renameVertices_support_of_shape C square σ hshape
  have hRcover (e : E) (he : e ∈ C) : ∃ i, R.edge e = pairs i := by
    have hp : R.edge e ∈ square := hRshape ▸ mem_image.mpr ⟨e, he, rfl⟩
    obtain ⟨i, _, hi⟩ := mem_image.mp hp
    exact ⟨i, hi.symm⟩
  have hRpositive (i : Fin 4) : (C.filter (fun e => R.edge e = pairs i)).Nonempty := by
    have hp : pairs i ∈ C.image R.edge := by
      rw [hRshape]
      exact mem_image.mpr ⟨i, mem_univ i, rfl⟩
    obtain ⟨e, he, hi⟩ := mem_image.mp hp
    exact ⟨e, mem_filter.mpr ⟨he, hi⟩⟩
  have hRnone : ¬ ∃ D : Finset E, D ⊆ C ∧ R.IsCircuit D ∧
      R.Compatible classes D ∧ D.card = 2 := by
    rintro ⟨D, hDC, hD, hcomp, hcard⟩
    exact hnone ⟨D, hDC, (Q.renameVertices_isCircuit σ.symm D).mp hD,
      (Q.renameVertices_compatible σ.symm classOf D).mp hcomp, hcard⟩
  obtain ⟨P⟩ := R.exists_compatibleCircuitPartition_of_strictNonlocal_four_cycle
    classes C ((Q.renameVertices_admissibleOn σ.symm classOf C).mpr hadmissible)
    (hstrict.renameVertices Q σ.symm) hRcover hRpositive hRnone
  exact ⟨P.of_renameVertices Q σ.symm classOf⟩

end Overfull.Multigraph
