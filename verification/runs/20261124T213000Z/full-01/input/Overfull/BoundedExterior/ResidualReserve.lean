import Overfull.BoundedExterior.ReserveChoice
import Overfull.OrdinaryFactorization.Reduction
import Overfull.OneCore.ResidualShores

/-!
# Transporting reserved labels to the actual residual complement

The residual palette is a reindexing of the original unselected labels.
Its reserved part has the same cardinality, and preservation of each inherited
original label carries the exterior crossing condition through both residual
edge restrictions.
-/

noncomputable section

namespace Overfull.BoundedExterior

open Finset Classical SmallCuts OrdinaryFactorization OneCore

variable {k h : ℕ}

/-- Compressed residual labels whose restored original label is reserved. -/
def residualReservedLabels (labels : Fin h ↪ Fin k) (J : Finset (Fin k)) :
    Finset (Fin (k - h)) :=
  univ.filter (fun i => remainingLabel labels i ∈ J)

@[simp] theorem mem_residualReservedLabels (labels : Fin h ↪ Fin k)
    (J : Finset (Fin k)) (i : Fin (k - h)) :
    i ∈ residualReservedLabels labels J ↔ remainingLabel labels i ∈ J := by
  simp only [residualReservedLabels, mem_filter, mem_univ, true_and]

theorem residualReservedLabels_map (labels : Fin h ↪ Fin k) (J : Finset (Fin k))
    (havoid : ∀ i ∈ J, i ∉ Set.range labels) :
    (residualReservedLabels labels J).map (remainingLabel labels) = J := by
  ext i
  constructor
  · intro hi
    obtain ⟨j, hj, rfl⟩ := mem_map.mp hi
    exact (mem_residualReservedLabels labels J j).mp hj
  · intro hi
    obtain ⟨j, hj⟩ := (remainingLabel_range labels i).mpr (havoid i hi)
    refine mem_map.mpr ⟨j, ?_, hj⟩
    apply (mem_residualReservedLabels labels J j).mpr
    exact hj.symm ▸ hi

theorem residualReservedLabels_card (labels : Fin h ↪ Fin k) (J : Finset (Fin k))
    (havoid : ∀ i ∈ J, i ∉ Set.range labels) :
    (residualReservedLabels labels J).card = J.card := by
  have hcard := congrArg Finset.card (residualReservedLabels_map labels J havoid)
  simpa only [card_map] using hcard

variable {V E : Type*} [Fintype V] [Fintype E]
variable {G : Multigraph V E} {U : Finset V}
variable {α ν τ ξ p σ κ δ μ η : ℝ}

/-- An exterior residual copy with a reserved compressed label crosses the
same ambient cut as its original complementary copy. -/
theorem residualReservedLabels_crossing (C : Core G U)
    (D : FirstHalfData G U C k α ν τ ξ p σ κ δ μ)
    (R : BipartiteResidualData D η) (J : Finset (Fin k)) (ZA : Finset V)
    (hcrossing : ∀ i ∈ J, ∀ e ∈ exteriorClass U D.exteriorColor i,
      e ∈ G.cutEdges
        (D.geometry.left.map (Function.Embedding.subtype (fun v => v ∈ U)) ∪ ZA))
    (f : ↥((coreEdges (residualCrossingCore C D))ᶜ))
    (hf : f.val ∉ D.remaining.internalEdges U)
    (hj : R.complementColor.color f ∈ residualReservedLabels D.labels J) :
    f.val ∈ D.remaining.cutEdges (TwoApexFactorization.leftShore
      (residualShoreEquiv C D) ∪ ZA) := by
  have hinherited : f.val ∈ residualComplementEdges C D.exteriorColor D.labels D.matchings := by
    by_contra hnot
    exact hf (remaining_copy_not_original_complement_internal C D f.val hnot)
  let g : inheritedComplementEdges C D :=
    ⟨f, (mem_inheritedComplementEdges C D f).mpr hinherited⟩
  let original : ↥((coreEdges C)ᶜ) :=
    residualComplementOriginal C D.exteriorColor D.labels D.matchings
      (inheritedComplementOriginal C D g)
  have hrestore : remainingLabel D.labels (R.complementColor.color f) =
      D.exteriorColor.color original := by
    change remainingLabel D.labels (R.complementColor.color g.val) = _
    rw [R.preserves g]
    exact inheritedComplementColoring_restore C D g
  have hlabel : D.exteriorColor.color original ∈ J := by
    rw [← hrestore]
    exact (mem_residualReservedLabels D.labels J _).mp hj
  have houtside : f.val.val ∉ G.internalEdges U := by
    intro hinternal
    apply hf
    exact (D.remaining.mem_internalEdges U f.val).mpr
      ((G.mem_internalEdges U f.val.val).mp hinternal)
  have hexterior : f.val.val ∈ exteriorClass U D.exteriorColor
      (D.exteriorColor.color original) := by
    apply (mem_exteriorClass U D.exteriorColor _ _).mpr
    exact ⟨⟨original, rfl, rfl⟩, houtside⟩
  have hcut := hcrossing _ hlabel _ hexterior
  rw [residualShore_left]
  exact (D.remaining.mem_cutEdges _ f.val).mpr ((G.mem_cutEdges _ f.val.val).mp hcut)

end Overfull.BoundedExterior
