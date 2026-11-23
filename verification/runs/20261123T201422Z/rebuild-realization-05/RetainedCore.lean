import Overfull.NativeReserve.CorePacking
import Overfull.NativeReserve.Residual
import Overfull.BoundaryExtension.Assembly

/-!
# The packed core inside the actual native residual

The host edge type is the subtype of original copies outside the deleted
union. Each retained simple edge is embedded by its original copy map,
and robustness concerns precisely the packing's unused simple graph.
-/

noncomputable section

namespace Overfull.NativeReserve

open Finset Classical BoundaryExtension

variable {V E : Type*} {G : Multigraph V E} {U : Finset V}
variable {q : ℕ} {S : Fin q → Finset U} {θ σ : ℝ}

def subcoreInNativeResidual (C : SmallCuts.Core G U)
    (H : SimpleGraph U) (hH : H ≤ C.graph) (T : Finset E)
    (hsurvive : ∀ e : H.edgeSet,
      C.edgeMap ⟨e.val, SimpleGraph.edgeSet_mono hH e.property⟩ ∉ T) :
    SmallCuts.Core (MultigraphMatchingProbability.remainingGraph G T) U where
  graph := H
  edgeMap :=
    { toFun := fun e => ⟨C.edgeMap ⟨e.val, SimpleGraph.edgeSet_mono hH e.property⟩,
        hsurvive e⟩
      inj' := by
        intro e f hef
        have hcopies := C.edgeMap.injective (congrArg Subtype.val hef)
        exact Subtype.ext (congrArg (fun f : C.graph.edgeSet => f.val) hcopies) }
  map_edge e := C.map_edge ⟨e.val, SimpleGraph.edgeSet_mono hH e.property⟩

theorem packingCopy_survives_iff (C : SmallCuts.Core G U)
    (P : CorePacking C.graph q S θ σ) (T : Finset E)
    (hremoved : ∀ e : C.graph.edgeSet,
      C.edgeMap e ∈ T ↔ ∃ j : Fin q, e.val ∈ (P.matching j).edgeSet)
    (e : C.graph.edgeSet) :
    C.edgeMap e ∉ T ↔ e.val ∈ P.remaining.edgeSet := by
  rw [hremoved]
  rcases e with ⟨⟨u, v⟩, he⟩
  change (¬ ∃ j : Fin q, (P.matching j).Adj u v) ↔
    C.graph.Adj u v ∧ ¬ ∃ j ∈ (univ : Finset (Fin q)), (P.matching j).Adj u v
  simp only [mem_univ, true_and]
  exact (and_iff_right he).symm

def packingRemainderCore (C : SmallCuts.Core G U)
    (P : CorePacking C.graph q S θ σ) (T : Finset E)
    (hremoved : ∀ e : C.graph.edgeSet,
      C.edgeMap e ∈ T ↔ ∃ j : Fin q, e.val ∈ (P.matching j).edgeSet) :
    SmallCuts.Core (MultigraphMatchingProbability.remainingGraph G T) U :=
  subcoreInNativeResidual C P.remaining (show P.remaining ≤ C.graph from sdiff_le) T
    (fun e => (packingCopy_survives_iff C P T hremoved
      ⟨e.val, SimpleGraph.edgeSet_mono (show P.remaining ≤ C.graph from sdiff_le)
        e.property⟩).mpr e.property)

@[simp] theorem packingRemainderCore_graph (C : SmallCuts.Core G U)
    (P : CorePacking C.graph q S θ σ) (T : Finset E)
    (hremoved : ∀ e : C.graph.edgeSet,
      C.edgeMap e ∈ T ↔ ∃ j : Fin q, e.val ∈ (P.matching j).edgeSet) :
    (packingRemainderCore C P T hremoved).graph = P.remaining := rfl

@[simp] theorem packingRemainderCore_edgeMap_val (C : SmallCuts.Core G U)
    (P : CorePacking C.graph q S θ σ) (T : Finset E)
    (hremoved : ∀ e : C.graph.edgeSet,
      C.edgeMap e ∈ T ↔ ∃ j : Fin q, e.val ∈ (P.matching j).edgeSet)
    (e : (packingRemainderCore C P T hremoved).graph.edgeSet) :
    ((packingRemainderCore C P T hremoved).edgeMap e).val =
      C.edgeMap ⟨e.val, SimpleGraph.edgeSet_mono
        (show P.remaining ≤ C.graph from sdiff_le) e.property⟩ := rfl

set_option maxHeartbeats 500000 in
theorem packingRemainderCore_robust (C : SmallCuts.Core G U)
    (P : CorePacking C.graph q S θ σ) (T : Finset E)
    (hremoved : ∀ e : C.graph.edgeSet,
      C.edgeMap e ∈ T ↔ ∃ j : Fin q, e.val ∈ (P.matching j).edgeSet) :
    IsRobustExpander (packingRemainderCore C P T hremoved).graph θ σ := by
  rw [packingRemainderCore_graph]
  convert P.robust using 1

theorem packingRemainderCore_degree_lower (C : SmallCuts.Core G U)
    (P : CorePacking C.graph q S θ σ) (T : Finset E)
    (hremoved : ∀ e : C.graph.edgeSet,
      C.edgeMap e ∈ T ↔ ∃ j : Fin q, e.val ∈ (P.matching j).edgeSet)
    (k : ℕ) (a : ℝ) (hq : q ≤ k)
    (hdegree : ∀ v, (k : ℝ) - a ≤ (C.graph.degree v : ℝ)) (v : U) :
    ((k - q : ℕ) : ℝ) - a ≤
      ((packingRemainderCore C P T hremoved).graph.degree v : ℝ) := by
  have h := P.degree_lower k a hdegree v
  simpa only [packingRemainderCore_graph, Nat.cast_sub hq] using h

def augmentInCore (C : SmallCuts.Core G U) (F : Fin q → Finset E)
    (P : CorePacking C.graph q (fun j => coreFootprint G U (F j)) θ σ)
    (j : Fin q) : Finset E :=
  F j ∪ coreMatchingCopies C (P.matching j)

theorem augmentInCore_removed_iff (C : SmallCuts.Core G U) (F : Fin q → Finset E)
    (P : CorePacking C.graph q (fun j => coreFootprint G U (F j)) θ σ)
    (hout : ∀ j, Disjoint (F j) (OneCore.coreEdges C)) (e : C.graph.edgeSet) :
    C.edgeMap e ∈ removedCopies (augmentInCore C F P) univ ↔
      ∃ j : Fin q, e.val ∈ (P.matching j).edgeSet := by
  simp only [mem_removedCopies, mem_univ, true_and]
  apply exists_congr
  intro j
  constructor
  · intro he
    rcases mem_union.mp he with hb | hc
    · exact (disjoint_left.mp (hout j) hb
        ((OneCore.mem_coreEdges C _).mpr ⟨e, rfl⟩)).elim
    · obtain ⟨f, hf, hfe⟩ := (mem_coreMatchingCopies C (P.matching j) _).mp hc
      have hfe' : f = e := C.edgeMap.injective hfe
      subst f
      exact (mem_filter.mp hf).2
  · intro he
    apply mem_union_right
    exact (mem_coreMatchingCopies C (P.matching j) _).mpr
      ⟨e, mem_filter.mpr ⟨mem_univ _, he⟩, rfl⟩

def augmentInCoreRemainder (C : SmallCuts.Core G U) (F : Fin q → Finset E)
    (P : CorePacking C.graph q (fun j => coreFootprint G U (F j)) θ σ)
    (hout : ∀ j, Disjoint (F j) (OneCore.coreEdges C)) :
    SmallCuts.Core (residualGraph G (augmentInCore C F P) univ) U :=
  packingRemainderCore C P (removedCopies (augmentInCore C F P) univ)
    (augmentInCore_removed_iff C F P hout)

set_option maxHeartbeats 500000 in
theorem augmentInCoreRemainder_robust (C : SmallCuts.Core G U) (F : Fin q → Finset E)
    (P : CorePacking C.graph q (fun j => coreFootprint G U (F j)) θ σ)
    (hout : ∀ j, Disjoint (F j) (OneCore.coreEdges C)) :
    IsRobustExpander (augmentInCoreRemainder C F P hout).graph θ σ := by
  exact packingRemainderCore_robust C P (removedCopies (augmentInCore C F P) univ)
    (augmentInCore_removed_iff C F P hout)

end Overfull.NativeReserve
