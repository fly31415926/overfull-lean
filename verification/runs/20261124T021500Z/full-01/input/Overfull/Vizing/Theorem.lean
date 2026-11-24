import Vizing.Main
import Overfull.Vizing.Coloring
import Overfull.MainReduction

/-!
Vizing's upper bound for the project's actual proper edge-coloring interface.
The coloring is obtained from the verified Misra--Gries implementation,
transported from adjacency lists to mathlib's unordered edge set.
-/

namespace Overfull

theorem vizing {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    Nonempty (EdgeColoring G (G.maxDegree + 1)) := by
  classical
  let C := _root_.mkEdgeColoring (VizingAdapter.graph G)
  have hcomplete (u v : Fin n) (h : G.Adj u v) :
      (_root_.EdgeColoring.color C (u, v)).isSome := by
    apply _root_.mkEdgeColoring_proper
    exact (_root_.Graph.mem_edgeSet_iff_present _ _).mp
      ((VizingAdapter.present_iff G u v).mpr h)
  exact ⟨VizingAdapter.enlargeColors (VizingAdapter.toColoring C hcomplete)
    (Nat.add_le_add_right (VizingAdapter.maxDegree_le G) 1)⟩

/-- Vizing's upper bound for every finite simple graph. -/
theorem vizing_finite {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Nonempty (EdgeColoring G (G.maxDegree + 1)) := by
  classical
  let H := G.overFin (n := Fintype.card V) rfl
  let f : G ≃g H := G.overFinIso rfl
  have hcolor := vizing H
  have hdegree := iso_maxDegree_eq f
  rw [← hdegree] at hcolor
  exact (iso_edgeColorable_iff f (G.maxDegree + 1)).mpr hcolor

theorem finite_vizing_bound : FiniteVizingBound := by
  classical
  exact fun _ G => vizing G

/-- A conditional reduction of the main theorem to the structural exclusion.
Vizing's bound is proved above; the robust-partition exclusion is still an
explicit hypothesis, so this declaration does not verify `MainTheorem`. -/
theorem mainTheorem_of_criticalExclusion (h : LargeCriticalExclusion) : MainTheorem :=
  mainTheorem_of_vizing_and_criticalExclusion finite_vizing_bound h

end Overfull
