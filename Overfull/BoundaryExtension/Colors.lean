import Overfull.BoundaryExtension.Contraction
import Overfull.BoundaryExtension.Palette

/-!
# Restoring singleton boundary labels

An actual coloring of the apex contraction supplies all colors at its
apex. Relabeling by those edge copies restores the prescribed singleton
labels. The edge copies are unchanged by contraction, and pulling the
coloring back preserves properness at every original outside endpoint.

These are coloring-transport theorems. They do not assume or assert the
missing factorization theorem that must produce the apex coloring.
-/

noncomputable section

namespace Overfull.BoundaryExtension

open Finset Classical Multigraph

variable {V E C L : Type*}

/-- The contracted and original retained graphs have the same edge-copy
type. Original incidences map to contracted incidences, so a proper
contracted coloring is proper at every original vertex. -/
def pullbackContractColoring (G : Multigraph V E) (U : Finset V)
    (c : PaletteColoring (contract G U) C) :
    PaletteColoring (retainedGraph G U) C :=
  c.pullback id (vertexMap U) Function.injective_id
    (fun e _v hv => contract_incident_of_original G U e hv)

@[simp] theorem pullbackContractColoring_color (G : Multigraph V E) (U : Finset V)
    (c : PaletteColoring (contract G U) C) (e : RetainedEdge G U) :
    (pullbackContractColoring G U c).color e = c.color e := rfl

section FiniteEdges

variable [Fintype E]

/-- The prescribed original label of an apex incidence. -/
def apexLabels (G : Multigraph V E) (U : Finset V)
    (label : G.cutEdges U → L) : (contract G U).incidenceEdges (Sum.inr ()) → L :=
  label ∘ (boundaryApexEquiv G U).symm

theorem apexLabels_injective (G : Multigraph V E) (U : Finset V)
    (label : G.cutEdges U → L) (hinj : Function.Injective label) :
    Function.Injective (apexLabels G U label) :=
  hinj.comp (boundaryApexEquiv G U).symm.injective

@[simp] theorem apexLabels_boundary (G : Multigraph V E) (U : Finset V)
    (label : G.cutEdges U → L) (e : G.cutEdges U) :
    apexLabels G U label (boundaryApexEquiv G U e) = label e := by
  simp only [apexLabels, Function.comp_apply, Equiv.symm_apply_apply]

variable [Fintype C]

/-- Restore distinct singleton labels in the original palette. No
cardinality assumption on that larger palette is needed. -/
def restoreSingletonLabels (G : Multigraph V E) (U : Finset V)
    (c : PaletteColoring (contract G U) C)
    (hboundary : G.cutSize U = Fintype.card C)
    (label : G.cutEdges U → L) (hinj : Function.Injective label) :
    PaletteColoring (retainedGraph G U) L :=
  pullbackContractColoring G U
    (c.alignLabelsAtVertex (Sum.inr ())
      ((degree_apex_eq_cutSize G U).trans hboundary)
      (apexLabels G U label) (apexLabels_injective G U label hinj))

/-- Agreement is on each individual original boundary edge copy. -/
@[simp] theorem restoreSingletonLabels_boundary (G : Multigraph V E) (U : Finset V)
    (c : PaletteColoring (contract G U) C)
    (hboundary : G.cutSize U = Fintype.card C)
    (label : G.cutEdges U → L) (hinj : Function.Injective label) (e : G.cutEdges U) :
    (restoreSingletonLabels G U c hboundary label hinj).color (boundaryLift G U e) =
      label e := by
  have h := c.alignLabelsAtVertex_agrees (Sum.inr ())
    ((degree_apex_eq_cutSize G U).trans hboundary)
    (apexLabels G U label) (apexLabels_injective G U label hinj)
    (boundaryApexEquiv G U e)
  simpa only [restoreSingletonLabels, pullbackContractColoring_color,
    boundaryApexEquiv_val, apexLabels_boundary] using h

/-- Every retained edge uses a surviving boundary label. This supplies
the palette separation needed when the completed colors are reinserted. -/
theorem restoreSingletonLabels_range (G : Multigraph V E) (U : Finset V)
    (c : PaletteColoring (contract G U) C)
    (hboundary : G.cutSize U = Fintype.card C)
    (label : G.cutEdges U → L) (hinj : Function.Injective label)
    (e : RetainedEdge G U) :
    ∃ b : G.cutEdges U,
      (restoreSingletonLabels G U c hboundary label hinj).color e = label b := by
  obtain ⟨b, hb⟩ := c.alignLabelsAtVertex_range (Sum.inr ())
    ((degree_apex_eq_cutSize G U).trans hboundary)
    (apexLabels G U label) (apexLabels_injective G U label hinj) e
  exact ⟨(boundaryApexEquiv G U).symm b, hb⟩

end FiniteEdges

/-- Conditional only on an actual coloring of the contracted graph,
restore all prescribed singleton boundary labels on the original graph.
The conclusion also records that no removed label is introduced. -/
theorem exists_singleton_boundary_extension [Fintype E]
    (G : Multigraph V E) (U : Finset V) (h : ℕ)
    (c : (contract G U).EdgeColoring h) (hboundary : G.cutSize U = h)
    (label : G.cutEdges U → L) (hinj : Function.Injective label) :
    ∃ c' : PaletteColoring (retainedGraph G U) L,
      (∀ e : G.cutEdges U, c'.color (boundaryLift G U e) = label e) ∧
      (∀ e : RetainedEdge G U, ∃ b : G.cutEdges U, c'.color e = label b) := by
  have hcard : G.cutSize U = Fintype.card (Fin h) := by simpa using hboundary
  exact ⟨restoreSingletonLabels G U (PaletteColoring.ofEdgeColoring c) hcard label hinj,
    restoreSingletonLabels_boundary G U (PaletteColoring.ofEdgeColoring c) hcard label hinj,
    restoreSingletonLabels_range G U (PaletteColoring.ofEdgeColoring c) hcard label hinj⟩

/-- Reassemble disjoint actual matching classes with their original
labels, preserving every prescribed boundary label exactly. -/
theorem assemble_prescribed_classes (G : Multigraph V E)
    (M : L → Finset E) (hM : ∀ i, G.IsMatching (M i))
    (hcover : ∀ e, ∃ i, e ∈ M i)
    (hdisjoint : Pairwise (fun i j => Disjoint (M i) (M j)))
    (B : Finset E) (label : B → L) (hlabel : ∀ e : B, e.val ∈ M (label e)) :
    ∃ c : PaletteColoring G L,
      (∀ e i, c.color e = i ↔ e ∈ M i) ∧
      (∀ e : B, c.color e.val = label e) := by
  refine ⟨PaletteColoring.ofMatchingClasses M hM hcover, ?_, ?_⟩
  · exact PaletteColoring.ofMatchingClasses_color_eq_iff M hM hcover hdisjoint
  · intro e
    exact (PaletteColoring.ofMatchingClasses_color_eq_iff M hM hcover hdisjoint
      e.val (label e)).mpr (hlabel e)

end Overfull.BoundaryExtension
