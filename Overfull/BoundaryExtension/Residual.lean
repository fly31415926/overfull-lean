import Overfull.BoundaryExtension.Assembly

/-!
# The actual residual multigraph and its embedded packed core

The residual host deletes the union of the completed original edge-copy
classes. Its core degree is computed by exact incidence counting. The
unused simple graph from the packing is embedded by precisely its
surviving original copies, so its robustness is a property of an actual
core of that residual host.
-/

noncomputable section

namespace Overfull.BoundaryExtension

open Finset Classical SmallCuts MatchingProbability BipartitePackingAccounting

variable {V E : Type*} [Fintype E]
variable {G : Multigraph V E} {U : Finset V} {d q : ℕ} {θ σ : ℝ}
variable (c : BoundaryColoring G U d) (C : Core G U) (labels : Fin q ↪ Fin d)
variable (P : CorePacking C.graph q (fun j => c.footprint (labels j)) θ σ)

/-- The original edge copies removed by all completed prescribed colors. -/
def completedUnion : Finset E := univ.biUnion (completedColor c C labels P)

@[simp] theorem mem_completedUnion (e : E) :
    e ∈ completedUnion c C labels P ↔ ∃ j, e ∈ completedColor c C labels P j := by
  simp only [completedUnion, mem_biUnion, mem_univ, true_and]

/-- Boundary deletion is exactly deletion of the selected original labels. -/
theorem completedUnion_boundary (e : G.cutEdges U) :
    e.val ∈ completedUnion c C labels P ↔ ∃ j, c.color e = labels j := by
  rw [mem_completedUnion]
  exact exists_congr (fun j => completedColor_boundary c C labels P j e)

theorem completedUnion_boundary_range (e : G.cutEdges U) :
    e.val ∈ completedUnion c C labels P ↔ c.color e ∈ Set.range labels := by
  rw [completedUnion_boundary, Set.mem_range]
  exact exists_congr (fun _ => eq_comm)

/-- Every selected color removes one incidence at every core vertex. -/
theorem completedUnion_incidence_card (u : U) :
    ((completedUnion c C labels P).filter (fun e => u.val ∈ G.edge e)).card = q := by
  have hsets : (completedUnion c C labels P).filter (fun e => u.val ∈ G.edge e) =
      univ.biUnion (fun j => (completedColor c C labels P j).filter
        (fun e => u.val ∈ G.edge e)) := by
    ext e
    simp only [mem_filter, mem_completedUnion, mem_biUnion, mem_univ, true_and]
    constructor
    · rintro ⟨⟨j, hj⟩, hu⟩
      exact ⟨j, hj, hu⟩
    · rintro ⟨j, hj, hu⟩
      exact ⟨⟨j, hj⟩, hu⟩
  rw [hsets, Finset.card_biUnion]
  · simp only [completedColor_incidence_card, sum_const, card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one]
  · intro i _hi j _hj hij
    exact (completedColor_disjoint c C labels P hij).mono (filter_subset _ _) (filter_subset _ _)

theorem completedUnion_degree (u : U) :
    (G.restrictEdges (completedUnion c C labels P)).degree u.val = q := by
  rw [Multigraph.restrictEdges_degree]
  have hsets : completedUnion c C labels P ∩ G.incidenceEdges u.val =
      (completedUnion c C labels P).filter (fun e => u.val ∈ G.edge e) := by
    ext e
    simp only [mem_inter, Multigraph.mem_incidenceEdges, mem_filter]
  rw [hsets, completedUnion_incidence_card]

/-- Delete exactly the completed actual color classes from the ambient host. -/
def remainingAmbient : Multigraph V ((completedUnion c C labels P)ᶜ : Finset E) :=
  G.restrictEdges (completedUnion c C labels P)ᶜ

/-- Exact degree loss, without any truncation or approximate accounting. -/
theorem remainingAmbient_degree_add (u : U) :
    (remainingAmbient c C labels P).degree u.val + q = G.degree u.val := by
  have h := OneCore.complement_degree_add G (completedUnion c C labels P) u.val
  rw [completedUnion_degree c C labels P u] at h
  exact h

theorem remainingAmbient_regular (hdegree : ∀ u : U, G.degree u.val = d) (u : U) :
    (remainingAmbient c C labels P).degree u.val = d - q := by
  have h := remainingAmbient_degree_add c C labels P u
  rw [hdegree u] at h
  omega

/-- A core copy is deleted precisely when its simple edge occurs in one
of the packed matchings. Boundary deletion cannot remove a core copy. -/
theorem coreCopy_removed_iff (f : C.graph.edgeSet) :
    C.edgeMap f ∈ completedUnion c C labels P ↔
      ∃ j, f.val ∈ (P.matching j).edgeSet := by
  rw [mem_completedUnion]
  apply exists_congr
  intro j
  constructor
  · intro hf
    rcases mem_union.mp hf with hb | hc
    · exact (Finset.disjoint_left.mp (OneCore.coreEdges_disjoint_cut C)
        ((OneCore.mem_coreEdges C _).mpr ⟨f, rfl⟩)
        (c.originalClass_subset_cut (labels j) hb)).elim
    · obtain ⟨e, he, hef⟩ := (mem_coreMatchingCopies C (P.matching j) _).mp hc
      have hh : e = f := C.edgeMap.injective hef
      subst e
      exact (mem_filter.mp he).2
  · intro hf
    apply mem_union_right
    exact (mem_coreMatchingCopies C (P.matching j) _).mpr
      ⟨f, mem_filter.mpr ⟨mem_univ _, hf⟩, rfl⟩

/-- The packing's remaining simple edges are exactly the surviving
original copies among the embedded core edges. -/
theorem coreCopy_survives_iff (f : C.graph.edgeSet) :
    C.edgeMap f ∉ completedUnion c C labels P ↔ f.val ∈ P.remaining.edgeSet := by
  rw [coreCopy_removed_iff]
  rcases f with ⟨⟨u,v⟩, hf⟩
  change (¬ ∃ j, (P.matching j).Adj u v) ↔
    C.graph.Adj u v ∧ ¬ ∃ j ∈ (univ : Finset (Fin q)), (P.matching j).Adj u v
  simp only [mem_univ, true_and]
  exact (and_iff_right hf).symm

omit c labels P in
/-- Restrict an embedded simple core to surviving host copies without
changing its vertex set. -/
def subcoreInRestriction (C : Core G U) (H : SimpleGraph U) (hH : H ≤ C.graph)
    (T : Finset E)
    (hsurvive : ∀ e : H.edgeSet,
      C.edgeMap ⟨e.val, SimpleGraph.edgeSet_mono hH e.property⟩ ∉ T) :
    Core (G.restrictEdges Tᶜ) U where
  graph := H
  edgeMap :=
    { toFun := fun e => ⟨C.edgeMap ⟨e.val, SimpleGraph.edgeSet_mono hH e.property⟩,
        mem_compl.mpr (hsurvive e)⟩
      inj' := by
        intro e f hef
        have hcopies := C.edgeMap.injective (congrArg Subtype.val hef)
        exact Subtype.ext (congrArg (fun f : C.graph.edgeSet => f.val) hcopies) }
  map_edge e := C.map_edge ⟨e.val, SimpleGraph.edgeSet_mono hH e.property⟩

/-- The packed residual simple graph embedded in the actual residual host. -/
def remainingEmbeddedCore : Core (remainingAmbient c C labels P) U :=
  subcoreInRestriction C P.remaining (show P.remaining ≤ C.graph from sdiff_le)
    (completedUnion c C labels P) (fun e =>
      (coreCopy_survives_iff c C labels P
        ⟨e.val, SimpleGraph.edgeSet_mono (show P.remaining ≤ C.graph from sdiff_le)
          e.property⟩).mpr e.property)

@[simp] theorem remainingEmbeddedCore_graph :
    (remainingEmbeddedCore c C labels P).graph = P.remaining := rfl

/-- The residual embedding uses the very same original edge copy. -/
@[simp] theorem remainingEmbeddedCore_edgeMap_val
    (e : (remainingEmbeddedCore c C labels P).graph.edgeSet) :
    ((remainingEmbeddedCore c C labels P).edgeMap e).val =
      C.edgeMap ⟨e.val, SimpleGraph.edgeSet_mono
        (show P.remaining ≤ C.graph from sdiff_le) e.property⟩ := rfl

set_option maxHeartbeats 500000 in
theorem remainingEmbeddedCore_robust :
    IsRobustExpander (remainingEmbeddedCore c C labels P).graph θ σ := by
  rw [remainingEmbeddedCore_graph]
  convert P.robust using 1

/-- Distinct selected labels ensure the natural residual degree agrees
with the real subtraction used in the packing estimate. -/
theorem remainingEmbeddedCore_degree_lower (a : ℝ)
    (hdegree : ∀ u, (d : ℝ) - a ≤ C.graph.degree u) (u : U) :
    ((d - q : ℕ) : ℝ) - a ≤ (remainingEmbeddedCore c C labels P).graph.degree u := by
  have hq : q ≤ d := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective labels labels.injective
  have h := P.degree_lower d a hdegree u
  simpa only [remainingEmbeddedCore_graph, Nat.cast_sub hq] using h

theorem remainingEmbeddedCore_degree_upper
    (hdegree : ∀ u : U, G.degree u.val = d) (u : U) :
    (remainingEmbeddedCore c C labels P).graph.degree u ≤ d - q := by
  have h := OneCore.core_degree_le (remainingEmbeddedCore c C labels P) u
  rwa [remainingAmbient_regular c C labels P hdegree u] at h

/-- The selected triple colors remove exactly their original boundary copies. -/
theorem completedTriples_boundary (c : BoundaryColoring G U d) (C : Core G U)
    (P : CorePacking C.graph c.tripleColors.card
      (fun j => c.footprint (c.tripleLabel j)) θ σ) (e : G.cutEdges U) :
    e.val ∈ completedUnion c C c.tripleLabel P ↔ c.color e ∈ c.tripleColors := by
  rw [completedUnion_boundary, c.tripleLabel_range]
  exact exists_congr (fun _ => eq_comm)

end Overfull.BoundaryExtension
