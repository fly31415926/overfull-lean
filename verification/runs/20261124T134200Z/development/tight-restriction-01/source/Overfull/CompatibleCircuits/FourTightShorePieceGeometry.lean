import Overfull.CompatibleCircuits.FourTightShorePairing
import Overfull.CompatibleCircuits.FourTightShoreOutsideGeometry

/-!
# Restoring the exterior incidences of one tight-shore piece

A retained contracted copy belonging to an inside piece is exactly its
unique complementary boundary copy. Restoring that piece gives one original
incidence at each end of the contracted copy and no other exterior
incidences. The incidence classes agree at both retained exterior ends.
-/

noncomputable section

namespace Overfull.FourOdd

open Finset Classical Overfull.Multigraph

variable {V E K : Type*} [Fintype E]
    (G : Multigraph V E) (classOf : V → E → K)
    {X : Finset V} {w : V} {k : K}

namespace TightShorePieces

variable (P : TightShorePieces G classOf X w k)

/-- A surviving outside-contraction copy in an inside piece belongs to
the complementary boundary class, since it was not incident to the anchor. -/
theorem outside_copy_in_complement (hw : w ∉ X)
    {D : Finset E} (hD : D ∈ P.parts)
    (e : joiningCopies G (shoreIntoLabel X w)) (he : e.val ∈ D) :
    e.val ∈ G.cutOn D X \ G.classCutOn classOf D w k X := by
  have htouch := P.copy_touches G classOf hD he
  have hcross := (tightShoreOutside_touches_iff_boundary G X w e).mp htouch
  have hnot := tightShoreOutside_touch_not_anchor G X w hw e htouch
  apply mem_sdiff.mpr
  refine ⟨(G.mem_cutOn D X e.val).mpr
    ⟨he, (G.mem_cutOn univ X e.val |>.mp hcross).2⟩, ?_⟩
  intro hc
  exact hnot (mem_filter.mp hc).2.1

/-- At an exterior vertex the restored piece has degree exactly one
when the selected contracted copy is incident, and degree zero otherwise. -/
theorem outside_degree_eq_indicator (hw : w ∉ X)
    {D : Finset E} (hD : D ∈ P.parts)
    (e : joiningCopies G (shoreIntoLabel X w)) (he : e.val ∈ D)
    (x : V) (hx : x ∉ X) :
    G.degreeOn D x = if x ∈ (tightShoreOutsideGraph G X w).edge e then 1 else 0 := by
  have htouch := P.copy_touches G classOf hD he
  have hnot := tightShoreOutside_touch_not_anchor G X w hw e htouch
  obtain ⟨a, _, hne, hcut, hA, _⟩ :=
    P.boundary_pair_of_complement G classOf hD
      (P.outside_copy_in_complement G classOf hw hD e he)
  have haA : a ∈ G.classCutOn classOf D w k X := by rw [hA]; simp
  have haCut := (mem_filter.mp haA).1
  have hwa := (mem_filter.mp haA).2.1
  have hxa : x ∈ G.edge a ↔ x = w := by
    constructor
    · intro h
      exact G.outside_incident_eq_of_cut haCut hw hx hwa h
    · intro h
      exact h ▸ hwa
  rw [P.degreeOn_outside_eq_cut G classOf hD x hx, hcut]
  by_cases hxw : x = w
  · subst x
    have hH := (tightShoreOutside_redirected_incidence G classOf X w k e htouch).1
    simp [degreeOn, filter_insert, filter_singleton, hwa, hnot, hH]
  · have hxa' : x ∉ G.edge a := fun h => hxw (hxa.mp h)
    by_cases hxe : x ∈ G.edge e.val
    · have hH := (tightShoreOutside_original_incidence G classOf X w k e x hx hxe).1
      simp [degreeOn, filter_insert, filter_singleton, hxa', hxe, hH]
    · have hH : x ∉ (tightShoreOutsideGraph G X w).edge e := by
        rw [tightShoreOutside_incident_iff G X w e x hx]
        simp [hxe, hxw]
      simp [degreeOn, filter_insert, filter_singleton, hxa', hxe, hH]

/-- Every restored exterior incidence has the exact original class
prescribed by its contracted copy, at the anchor as well as the other end. -/
theorem outside_incidence_class (hw : w ∉ X)
    {D : Finset E} (hD : D ∈ P.parts)
    (e : joiningCopies G (shoreIntoLabel X w)) (he : e.val ∈ D)
    (x : V) (hx : x ∉ X) (f : E) (hf : f ∈ D) (hxf : x ∈ G.edge f) :
    x ∈ (tightShoreOutsideGraph G X w).edge e ∧
      tightShoreOutsideClass G classOf X w k x e = classOf x f := by
  have htouch := P.copy_touches G classOf hD he
  obtain ⟨a, _, _, hcut, hA, _⟩ :=
    P.boundary_pair_of_complement G classOf hD
      (P.outside_copy_in_complement G classOf hw hD e he)
  have haA : a ∈ G.classCutOn classOf D w k X := by rw [hA]; simp
  have haCut := (mem_filter.mp haA).1
  have hwa := (mem_filter.mp haA).2.1
  have hak := (mem_filter.mp haA).2.2
  have hfcut := P.outside_incidence_in_cut G classOf hD hx hf hxf
  rw [hcut] at hfcut
  rcases mem_insert.mp hfcut with hfa | hfe
  · subst f
    have hxw := G.outside_incident_eq_of_cut haCut hw hx hwa hxf
    subst x
    obtain ⟨hinc, hclass⟩ := tightShoreOutside_redirected_incidence G classOf X w k e htouch
    exact ⟨hinc, hclass.trans hak.symm⟩
  · have hfe' : f = e.val := mem_singleton.mp hfe
    subst f
    exact tightShoreOutside_original_incidence G classOf X w k e x hx hxf

end TightShorePieces

end Overfull.FourOdd
