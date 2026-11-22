import Overfull.OrdinaryFactorization.ResidualGeometry
import Overfull.OrdinaryFactorization.Palette
import Overfull.BoundaryExtension.Residual

/-!
# The crossing core inside the actual residual host

Surviving simple edges are embedded by the same original host copies as in
the original core. Complementary copies are kept separate by copy identity,
including when their endpoint pairs coincide with embedded core edges.
-/

noncomputable section

namespace Overfull.OrdinaryFactorization

open Finset Classical SmallCuts SimpleGraph BoundaryExtension MatchingProbability
open BipartitePackingAccounting

variable {V E : Type*} [Fintype V] [Fintype E]
variable {G : Multigraph V E} {U : Finset V} {k : ℕ}
variable {α ν τ ξ p σ κ δ μ : ℝ}
variable (C : Core G U) (D : FirstHalfData G U C k α ν τ ξ p σ κ δ μ)

/-- An embedded original core copy is deleted exactly when a supplied
matching uses its simple edge. Exterior colors cannot remove this copy. -/
theorem coreCopy_deleted_iff (f : C.graph.edgeSet) :
    C.edgeMap f ∈ deleted C D.exteriorColor D.labels D.matchings ↔
      ∃ i, f.val ∈ (D.matchings i).edgeSet := by
  rw [mem_deleted]
  apply exists_congr
  intro i
  constructor
  · intro hf
    rcases mem_union.mp hf with hs | hc
    · exact (Finset.disjoint_left.mp
        (selectedClass_disjoint_coreEdges C D.exteriorColor D.labels i) hs
        ((OneCore.mem_coreEdges C _).mpr ⟨f, rfl⟩)).elim
    · obtain ⟨e, he, hef⟩ := (mem_coreMatchingCopies C (D.matchings i) _).mp hc
      have heq : e = f := C.edgeMap.injective hef
      subst e
      exact (mem_filter.mp he).2
  · intro hf
    apply mem_union_right
    exact (mem_coreMatchingCopies C (D.matchings i) _).mpr
      ⟨f, mem_filter.mpr ⟨mem_univ _, hf⟩, rfl⟩

/-- The simple-edge deletion and the original-copy deletion agree exactly. -/
theorem coreCopy_survives_iff (f : C.graph.edgeSet) :
    C.edgeMap f ∉ deleted C D.exteriorColor D.labels D.matchings ↔
      f.val ∈ (C.graph \ edgeUnion (fun i => (D.matchings i).spanningCoe) univ).edgeSet := by
  rw [coreCopy_deleted_iff]
  rcases f with ⟨⟨u, v⟩, hf⟩
  change (¬ ∃ i, (D.matchings i).Adj u v) ↔
    C.graph.Adj u v ∧ ¬ ∃ i ∈ (univ : Finset (Fin D.count)), (D.matchings i).Adj u v
  simp only [mem_univ, true_and]
  exact (and_iff_right hf).symm

/-- Every residual copy not inherited from the original complement is
an original core copy, so both of its endpoints remain in the core set. -/
theorem remaining_copy_not_original_complement_internal
    (e : ↥((deleted C D.exteriorColor D.labels D.matchings)ᶜ))
    (he : e ∉ residualComplementEdges C D.exteriorColor D.labels D.matchings) :
    e ∈ D.remaining.internalEdges U := by
  have hcore : e.val ∈ OneCore.coreEdges C := by
    by_contra hnot
    exact he ((mem_residualComplementEdges C D.exteriorColor D.labels D.matchings e).mpr
      (mem_compl.mpr hnot))
  apply (D.remaining.mem_internalEdges U e).mpr
  change G.firstEnd e.val ∈ U ∧ G.secondEnd e.val ∈ U
  exact (G.mem_internalEdges U e.val).mp (OneCore.coreEdges_subset_internal C hcore)

/-- Each crossing residual edge is also an edge of the full surviving core. -/
theorem residualCrossing_le_surviving_core :
    residualCrossing C D ≤
      C.graph \ edgeUnion (fun i => (D.matchings i).spanningCoe) univ := by
  intro v w hvw
  exact ⟨hvw.1.1, hvw.2⟩

/-- The original copy chosen for a crossing residual edge was not deleted. -/
theorem residualCrossing_copy_survives (f : (residualCrossing C D).edgeSet) :
    C.edgeMap ⟨f.val, SimpleGraph.edgeSet_mono (residualCrossing_le C D) f.property⟩ ∉
      deleted C D.exteriorColor D.labels D.matchings := by
  apply (coreCopy_survives_iff C D _).mpr
  exact SimpleGraph.edgeSet_mono (residualCrossing_le_surviving_core C D) f.property

/-- The actual crossing residual graph embedded by its surviving original copies. -/
def residualCrossingCore : Core D.remaining U :=
  BoundaryExtension.subcoreInRestriction C (residualCrossing C D) (residualCrossing_le C D)
    (deleted C D.exteriorColor D.labels D.matchings) (residualCrossing_copy_survives C D)

@[simp] theorem residualCrossingCore_graph :
    (residualCrossingCore C D).graph = residualCrossing C D := rfl

/-- The residual embedding has the same original edge-copy value. -/
@[simp] theorem residualCrossingCore_edgeMap_val (f : (residualCrossing C D).edgeSet) :
    ((residualCrossingCore C D).edgeMap f).val =
      C.edgeMap ⟨f.val, SimpleGraph.edgeSet_mono (residualCrossing_le C D) f.property⟩ := rfl

/-- Exact membership in the new core, retaining the original host-copy identity. -/
theorem mem_residualCrossingCore_iff
    (e : ↥((deleted C D.exteriorColor D.labels D.matchings)ᶜ)) :
    e ∈ OneCore.coreEdges (residualCrossingCore C D) ↔
      ∃ f : C.graph.edgeSet, C.edgeMap f = e.val ∧
        f.val ∈ (residualCrossing C D).edgeSet := by
  constructor
  · intro he
    obtain ⟨f, rfl⟩ := (OneCore.mem_coreEdges (residualCrossingCore C D) e).mp he
    exact ⟨⟨f.val, SimpleGraph.edgeSet_mono (residualCrossing_le C D) f.property⟩,
      rfl, f.property⟩
  · rintro ⟨f, hf, hcross⟩
    apply (OneCore.mem_coreEdges (residualCrossingCore C D) e).mpr
    refine ⟨⟨f.val, hcross⟩, ?_⟩
    apply Subtype.ext
    change C.edgeMap f = e.val
    exact hf

theorem residualCrossingCore_copy_original
    (e : ↥((deleted C D.exteriorColor D.labels D.matchings)ᶜ))
    (he : e ∈ OneCore.coreEdges (residualCrossingCore C D)) :
    e.val ∈ OneCore.coreEdges C := by
  obtain ⟨f, hf, _⟩ := (mem_residualCrossingCore_iff C D e).mp he
  exact (OneCore.mem_coreEdges C e.val).mpr ⟨f, hf⟩

theorem coreCopy_mem_residualCrossingCore_iff (f : C.graph.edgeSet)
    (hf : C.edgeMap f ∉ deleted C D.exteriorColor D.labels D.matchings) :
    (⟨C.edgeMap f, mem_compl.mpr hf⟩ : ↥((deleted C D.exteriorColor D.labels D.matchings)ᶜ)) ∈
        OneCore.coreEdges (residualCrossingCore C D) ↔
      f.val ∈ (residualCrossing C D).edgeSet := by
  rw [mem_residualCrossingCore_iff]
  constructor
  · rintro ⟨g, hg, hcross⟩
    have hgf : g = f := C.edgeMap.injective hg
    simpa only [hgf] using hcross
  · intro hcross
    exact ⟨f, rfl, hcross⟩

/-- Original complementary copies remain disjoint from the new embedded core,
even if they have the same unordered endpoints as a core edge. -/
theorem residualComplementEdges_disjoint_crossingCore :
    Disjoint (residualComplementEdges C D.exteriorColor D.labels D.matchings)
      (OneCore.coreEdges (residualCrossingCore C D)) := by
  apply Finset.disjoint_left.mpr
  intro e he hcore
  exact (mem_compl.mp
    ((mem_residualComplementEdges C D.exteriorColor D.labels D.matchings e).mp he))
    (residualCrossingCore_copy_original C D e hcore)

theorem residualComplementEdges_subset_crossingComplement :
    residualComplementEdges C D.exteriorColor D.labels D.matchings ⊆
      (OneCore.coreEdges (residualCrossingCore C D))ᶜ := by
  intro e he
  exact mem_compl.mpr (fun hcore =>
    Finset.disjoint_left.mp (residualComplementEdges_disjoint_crossingCore C D) he hcore)

/-- The actual complement of the new crossing core inside the residual host. -/
def residualCrossingComplement :
    Multigraph V ↥((OneCore.coreEdges (residualCrossingCore C D))ᶜ) :=
  D.remaining.restrictEdges (OneCore.coreEdges (residualCrossingCore C D))ᶜ

/-- The copies in this new complement inherited from the original complement. -/
def inheritedComplementEdges : Finset ↥((OneCore.coreEdges (residualCrossingCore C D))ᶜ) :=
  univ.filter (fun e => e.val ∈ residualComplementEdges C D.exteriorColor D.labels D.matchings)

@[simp] theorem mem_inheritedComplementEdges
    (e : ↥((OneCore.coreEdges (residualCrossingCore C D))ᶜ)) :
    e ∈ inheritedComplementEdges C D ↔
      e.val ∈ residualComplementEdges C D.exteriorColor D.labels D.matchings := by
  simp only [inheritedComplementEdges, mem_filter, mem_univ, true_and]

/-- Forget only the new complement restriction, retaining the same residual copy. -/
def inheritedComplementOriginal : ↥(inheritedComplementEdges C D) ↪
    ↥(residualComplementEdges C D.exteriorColor D.labels D.matchings) where
  toFun e := ⟨e.val.val, (mem_inheritedComplementEdges C D e.val).mp e.property⟩
  inj' := by
    intro e f hef
    have hval : e.val.val = f.val.val :=
      congrArg (fun a : ↥(residualComplementEdges C D.exteriorColor D.labels D.matchings) =>
        a.val) hef
    exact Subtype.ext (Subtype.ext hval)

@[simp] theorem inheritedComplementOriginal_val (e : ↥(inheritedComplementEdges C D)) :
    (inheritedComplementOriginal C D e).val = e.val.val := rfl

/-- Every surviving original complementary copy occurs in the inherited restriction. -/
theorem inheritedComplementOriginal_surjective
    (f : ↥(residualComplementEdges C D.exteriorColor D.labels D.matchings)) :
    ∃ e : ↥(inheritedComplementEdges C D), inheritedComplementOriginal C D e = f := by
  let r : ↥((OneCore.coreEdges (residualCrossingCore C D))ᶜ) :=
    ⟨f.val, residualComplementEdges_subset_crossingComplement C D f.property⟩
  let e : ↥(inheritedComplementEdges C D) :=
    ⟨r, (mem_inheritedComplementEdges C D r).mpr f.property⟩
  exact ⟨e, Subtype.ext rfl⟩

/-- The inherited restriction has its actual compressed original coloring. -/
def inheritedComplementColoring :
    ((residualCrossingComplement C D).restrictEdges (inheritedComplementEdges C D)).EdgeColoring
      (k - D.count) where
  color e := (compressedResidualComplementColoring C D.exteriorColor D.labels D.matchings).color
    (inheritedComplementOriginal C D e)
  proper := by
    intro e f v hef hev hfv
    apply (inheritedComplementOriginal C D).injective
    exact (compressedResidualComplementColoring C D.exteriorColor D.labels D.matchings).proper
      hef hev hfv

/-- Restore the original exterior label after both actual restrictions. -/
theorem inheritedComplementColoring_restore (e : ↥(inheritedComplementEdges C D)) :
    remainingLabel D.labels ((inheritedComplementColoring C D).color e) =
      D.exteriorColor.color (residualComplementOriginal C D.exteriorColor D.labels D.matchings
        (inheritedComplementOriginal C D e)) :=
  compressedResidualComplementColoring_restore C D.exteriorColor D.labels D.matchings _

/-- Every new uncolored complementary copy is internal to the core vertex set.
This is the support hypothesis for the generic greedy extension theorem. -/
theorem inheritedComplement_uncolored_internal :
    (inheritedComplementEdges C D)ᶜ ⊆ (residualCrossingComplement C D).internalEdges U := by
  intro e he
  have hnot : e.val ∉ residualComplementEdges C D.exteriorColor D.labels D.matchings := by
    intro hmem
    exact (mem_compl.mp he) ((mem_inheritedComplementEdges C D e).mpr hmem)
  have hint := remaining_copy_not_original_complement_internal C D e.val hnot
  apply ((residualCrossingComplement C D).mem_internalEdges U e).mpr
  exact (D.remaining.mem_internalEdges U e.val).mp hint

end Overfull.OrdinaryFactorization
