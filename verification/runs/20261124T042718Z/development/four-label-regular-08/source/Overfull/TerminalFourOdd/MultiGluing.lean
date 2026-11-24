import Overfull.TerminalFourOdd.MultiContraction
import Overfull.NativeTerminal.ColoringGlue

/-! Consistent central labels and simultaneous restoration of every odd leaf. -/

noncomputable section

namespace Overfull.TerminalFourOdd.Multi

open Finset Classical Multigraph SmallCuts BoundaryExtension NativeTerminal

variable {V E I : Type*} [Fintype E]

def centralRetainedLift (G : Multigraph V E) (U : Finset V) (label : V → I)
    (e : RetainedEdge G U) : CentralEdge G U label :=
  ⟨e.val,by
    obtain ⟨u,hu⟩ := e.property
    exact central_retained_of_core_incident G U label u.property hu⟩

/-- Central colors also form a proper coloring at original outside vertices. -/
def centralColoringToRetained (G : Multigraph V E) (U : Finset V) (label : V → I) (k : ℕ)
    (c : (centralGraph G U label).EdgeColoring k) :
    PaletteColoring (retainedGraph G U) (Fin k) where
  color e := c.color (centralRetainedLift G U label e)
  proper := by
    intro e f v hc hev hfv
    apply Subtype.ext
    exact congrArg (fun x : CentralEdge G U label => x.val) (c.proper hc
      (central_incident_of_original G U label (centralRetainedLift G U label e) hev)
      (central_incident_of_original G U label (centralRetainedLift G U label f) hfv))

def centralBoundaryLabels (G : Multigraph V E) (U X : Finset V) (label : V → I) (k : ℕ)
    (z : CentralVertex U I) (hfiber : ∀ v, centralMap U label v = z ↔ v ∈ X)
    (c : (centralGraph G U label).EdgeColoring k) (e : G.cutEdges X) : Fin k :=
  c.color (centralBoundaryLift G U X label z hfiber e)

theorem centralBoundaryLabels_injective (G : Multigraph V E) (U X : Finset V) (label : V → I) (k : ℕ)
    (z : CentralVertex U I) (hfiber : ∀ v, centralMap U label v = z ↔ v ∈ X)
    (c : (centralGraph G U label).EdgeColoring k) :
    Function.Injective (centralBoundaryLabels G U X label k z hfiber c) := by
  intro e f h
  apply Subtype.ext
  exact congrArg (fun x : CentralEdge G U label => x.val) (c.proper h
    ((central_incident_fiber_iff G U X label z hfiber _).mpr e.property)
    ((central_incident_fiber_iff G U X label z hfiber _).mpr f.property))


/-- A central coloring and constructed singleton-apex leaf colorings give
a coloring of all original copies, for any finite family of leaves. -/
theorem glue_central_and_leaves (G : Multigraph V E) (U : Finset V)
    (label : V → I) (X : I → Finset V) (k : ℕ)
    (hUX : ∀ i, Disjoint U (X i))
    (hXX : Pairwise (fun i j => Disjoint (X i) (X j)))
    (hcover : ∀ v, v ∈ U ∨ ∃ i, v ∈ X i)
    (hfiber : ∀ i v, centralMap U label v = Sum.inr i ↔ v ∈ X i)
    (hcut : ∀ i, G.cutSize (X i) = k)
    (c : (centralGraph G U label).EdgeColoring k)
    (cX : ∀ i, (contract G (X i)).EdgeColoring k) :
    Nonempty (G.EdgeColoring k) := by
  let labels := fun i => centralBoundaryLabels G U (X i) label k (Sum.inr i) (hfiber i) c
  have hlocal : ∀ i, ∃ d : PaletteColoring (retainedGraph G (X i)) (Fin k),
      ∀ e : G.cutEdges (X i), d.color (boundaryLift G (X i) e) = labels i e := by
    intro i
    obtain ⟨d,hd,_⟩ := exists_singleton_boundary_extension G (X i) k (cX i) (hcut i)
      (labels i) (centralBoundaryLabels_injective G U (X i) label k
        (Sum.inr i) (hfiber i) c)
    exact ⟨d,hd⟩
  choose d hd using hlocal
  let S : Option I → Finset V := fun i => i.elim U X
  let colors : ∀ i, PaletteColoring (retainedGraph G (S i)) (Fin k) :=
    fun i => match i with
      | none => centralColoringToRetained G U label k c
      | some j => d j
  have hS : ∀ v, ∃ i, v ∈ S i := by
    intro v
    rcases hcover v with hv | ⟨i,hi⟩
    · exact ⟨none,hv⟩
    · exact ⟨some i,hi⟩
  obtain ⟨color,_⟩ := exists_glued_retained_coloring G S hS colors (by
    intro i j e hi hj
    cases i with
    | none =>
      cases j with
      | none => rfl
      | some j =>
        have he := (boundary_of_two_retained G U (X j) (hUX j) e hi hj).2
        exact (hd j ⟨e,he⟩).symm
    | some i =>
      cases j with
      | none =>
        have he := (boundary_of_two_retained G U (X i) (hUX i) e hj hi).2
        exact hd i ⟨e,he⟩
      | some j =>
        by_cases hij : i = j
        · subst j
          rfl
        obtain ⟨hei,hej⟩ := boundary_of_two_retained G (X i) (X j) (hXX hij) e hi hj
        exact (hd i ⟨e,hei⟩).trans (hd j ⟨e,hej⟩).symm)
  exact ⟨color.toEdgeColoring⟩

end Overfull.TerminalFourOdd.Multi
