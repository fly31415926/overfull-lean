import Overfull.CompatibleCircuits.FourTightShoreBlocks
import Overfull.CompatibleCircuits.FourTightShoreExpansion

/-!
# Saved closed pieces of a tight shore

An inside piece without a surviving outside copy has every exterior
incidence at the anchor. Its anchor degree is exactly its boundary size,
which is zero or two. Thus all its original degrees are even, and original
compatibility gives a genuine circuit partition of every saved piece.
The final family partition retains the exact original-copy union.
-/

noncomputable section

namespace Overfull.FourOdd

open Finset Classical Overfull.Multigraph

variable {V E K : Type*} [Fintype E]
    (G : Multigraph V E) (classOf : V → E → K)
    {X : Finset V} {w : V} {k : K}

/-- A boundary copy which does not survive the outside contraction has
its original exterior endpoint at the anchor. -/
theorem outside_endpoint_eq_anchor_of_not_joining {D : Finset E} {e : E}
    (hecut : e ∈ G.cutOn D X)
    (hnot : e ∉ joiningCopies G (shoreIntoLabel X w))
    {v : V} (hv : v ∉ X) (hve : v ∈ G.edge e) : v = w := by
  have hlabels : shoreIntoLabel X w (G.firstEnd e) =
      shoreIntoLabel X w (G.secondEnd e) := by
    by_contra hn
    exact hnot ((mem_joiningCopies G (shoreIntoLabel X w) e).mpr hn)
  have hcross := (G.mem_cutOn D X e).mp hecut |>.2
  rcases (G.incident_iff e v).mp hve with ha | hb
  · rw [ha] at hlabels hcross
    have hbX : G.secondEnd e ∈ X := by simpa [hv] using hcross
    simpa only [shoreIntoLabel, if_neg hv, if_pos hbX] using hlabels
  · rw [hb] at hlabels hcross
    have haX : G.firstEnd e ∈ X := by simpa [hv] using hcross
    simpa only [shoreIntoLabel, if_neg hv, if_pos haX] using hlabels.symm

namespace TightShorePieces

variable (P : TightShorePieces G classOf X w k)

/-- Every exterior incidence of a saved piece is at the anchor. -/
theorem closedPart_outside_incidence_eq_anchor {D : Finset E}
    (hD : D ∈ P.closedParts G classOf) {v : V} (hv : v ∉ X)
    {e : E} (he : e ∈ D) (hve : v ∈ G.edge e) : v = w := by
  obtain ⟨hpart, hclosed⟩ := (P.mem_closedParts G classOf D).mp hD
  exact outside_endpoint_eq_anchor_of_not_joining G
    (P.outside_incidence_in_cut G classOf hpart hv he hve)
    (fun hejoin => disjoint_left.mp hclosed he hejoin) hv hve

/-- The anchor degree of a saved piece counts all of its boundary copies. -/
theorem closedPart_anchor_degree {D : Finset E}
    (hw : w ∉ X) (hD : D ∈ P.closedParts G classOf) :
    G.degreeOn D w = (G.cutOn D X).card := by
  have hpart := ((P.mem_closedParts G classOf D).mp hD).1
  rw [P.degreeOn_outside_eq_cut G classOf hpart w hw]
  unfold degreeOn
  congr 1
  apply filter_eq_self.mpr
  intro e he
  have heD := (G.mem_cutOn D X e).mp he |>.1
  have hcross := (G.mem_cutOn D X e).mp he |>.2
  by_cases ha : G.firstEnd e ∈ X
  · have hb : G.secondEnd e ∉ X := by simpa [ha] using hcross
    have hbe : G.secondEnd e ∈ G.edge e :=
      (G.incident_iff e _).mpr (Or.inr rfl)
    have heq := P.closedPart_outside_incidence_eq_anchor G classOf hD hb heD hbe
    exact heq ▸ hbe
  · have hae : G.firstEnd e ∈ G.edge e :=
      (G.incident_iff e _).mpr (Or.inl rfl)
    have heq := P.closedPart_outside_incidence_eq_anchor G classOf hD ha heD hae
    exact heq ▸ hae

/-- Every other exterior vertex has zero degree in a saved piece. -/
theorem closedPart_outside_degree_zero {D : Finset E}
    (hD : D ∈ P.closedParts G classOf) {v : V} (hv : v ∉ X) (hvw : v ≠ w) :
    G.degreeOn D v = 0 := by
  unfold degreeOn
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨heD, hve⟩ := mem_filter.mp he
  exact hvw (P.closedPart_outside_incidence_eq_anchor G classOf hD hv heD hve)

/-- Saved pieces are Eulerian on their original vertices. This includes
boundary-free pieces and paths whose two boundary copies return to the anchor. -/
theorem closedPart_even_degrees (hw : w ∉ X) {D : Finset E}
    (hD : D ∈ P.closedParts G classOf) (v : V) : Even (G.degreeOn D v) := by
  have hpart := ((P.mem_closedParts G classOf D).mp hD).1
  by_cases hv : v ∈ X
  · exact P.even_inside D hpart v hv
  · by_cases hvw : v = w
    · subst v
      rw [P.closedPart_anchor_degree G classOf hw hD]
      rcases P.boundary D hpart with hzero | ⟨htwo, _, _⟩
      · simp [hzero]
      · simp [htwo]
    · rw [P.closedPart_outside_degree_zero G classOf hD hv hvw]
      simp

end TightShorePieces

end Overfull.FourOdd

namespace Overfull.FourOdd.TightShorePieces

open Finset Classical Overfull.Multigraph

variable {E K : Type*} [Fintype E]
    (G : Multigraph (Fin 4) E) (classOf : Fin 4 → E → K)
    {X : Finset (Fin 4)} {w : Fin 4} {k : K}
    (P : TightShorePieces G classOf X w k)

/-- Every saved piece has a genuine partition into compatible original
circuits, without an assumption that the saved piece itself is connected. -/
theorem exists_partition_closedPart (hw : w ∉ X) {D : Finset E}
    (hD : D ∈ P.closedParts G classOf) :
    Nonempty (G.CompatibleCircuitPartition classOf D) := by
  apply G.exists_compatibleCircuitPartition_of_compatible classOf D
  · exact P.compatible D ((P.mem_closedParts G classOf D).mp hD).1
  · exact P.closedPart_even_degrees G classOf hw hD

/-- All saved pieces partition their exact original-copy union. -/
theorem exists_partition_closedParts (hw : w ∉ X) :
    Nonempty (G.CompatibleCircuitPartition classOf
      ((P.closedParts G classOf).biUnion id)) := by
  refine ⟨CompatibleCircuitPartition.refineBlocks G classOf (P.closedParts G classOf)
    (fun D hD => Classical.choice (P.exists_partition_closedPart G classOf hw hD)) ?_⟩
  intro D hD D' hD' hne
  exact P.disjoint D ((P.mem_closedParts G classOf D).mp hD).1
    D' ((P.mem_closedParts G classOf D').mp hD').1 hne

end Overfull.FourOdd.TightShorePieces
