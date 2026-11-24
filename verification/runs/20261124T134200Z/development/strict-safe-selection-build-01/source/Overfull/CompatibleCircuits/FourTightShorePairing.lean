import Overfull.CompatibleCircuits.FourTightShorePieces
import Overfull.CompatibleCircuits.FourDegreeTwoParallel

/-!
# Exact boundary pairs of the tight-shore pieces

Every open piece has a unique prescribed-class boundary copy and a unique
complementary boundary copy. Outside the shore its degrees are exactly
the incidences of these two copies. These identities support restoration
without any arbitrary splitting of an incidence class.
-/

noncomputable section

namespace Overfull.FourOdd

open Finset Classical
open Overfull.Multigraph

variable {V E K : Type*} [Fintype V] [Fintype E]
    (G : Multigraph V E) (classOf : V → E → K)
    {X : Finset V} {w : V} {k : K}

namespace TightShorePieces

variable (P : TightShorePieces G classOf X w k)

/-- Every member of a constructed piece touches the shore. -/
theorem copy_touches {D : Finset E} (hD : D ∈ P.parts) {e : E} (he : e ∈ D) :
    G.firstEnd e ∈ X ∨ G.secondEnd e ∈ X := by
  have h : e ∈ P.parts.biUnion id := mem_biUnion.mpr ⟨D,hD,he⟩
  rw [P.cover] at h
  exact (mem_filter.mp h).2

/-- An outside incidence in a piece is necessarily a boundary incidence. -/
theorem outside_incidence_in_cut {D : Finset E} (hD : D ∈ P.parts)
    {x : V} (hx : x ∉ X) {e : E} (he : e ∈ D) (hxe : x ∈ G.edge e) :
    e ∈ G.cutOn D X := by
  have htouch := P.copy_touches G classOf hD he
  apply (G.mem_cutOn D X e).mpr
  refine ⟨he,?_⟩
  rcases (G.incident_iff e x).mp hxe with ha | hb
  · have haX : G.firstEnd e ∉ X := ha ▸ hx
    have hbX := htouch.resolve_left haX
    simp [haX,hbX]
  · have hbX : G.secondEnd e ∉ X := hb ▸ hx
    have haX := htouch.resolve_right hbX
    simp [haX,hbX]

/-- The boundary retains every outside incidence of an original piece. -/
theorem degreeOn_outside_eq_cut {D : Finset E} (hD : D ∈ P.parts)
    (x : V) (hx : x ∉ X) :
    G.degreeOn D x = G.degreeOn (G.cutOn D X) x := by
  unfold degreeOn
  congr 1
  ext e
  simp only [mem_filter]
  constructor
  · rintro ⟨he,hxe⟩
    exact ⟨P.outside_incidence_in_cut G classOf hD hx he hxe,hxe⟩
  · rintro ⟨he,hxe⟩
    exact ⟨(G.mem_cutOn D X e |>.mp he).1,hxe⟩

/-- A nonempty boundary has a unique actual A-copy and a unique B-copy. -/
theorem exists_boundary_pair {D : Finset E} (hD : D ∈ P.parts)
    (hboundary : (G.cutOn D X).Nonempty) :
    ∃ a b : E, a ∈ D ∧ b ∈ D ∧ a ≠ b ∧
      G.cutOn D X = {a,b} ∧ G.classCutOn classOf D w k X = {a} ∧
      (G.cutOn D X \ G.classCutOn classOf D w k X) = {b} := by
  classical
  rcases P.boundary D hD with hzero | ⟨_,hA,hB⟩
  · have hpos := card_pos.mpr hboundary
    omega
  · obtain ⟨a,ha⟩ := card_eq_one.mp hA
    obtain ⟨b,hb⟩ := card_eq_one.mp hB
    have haA : a ∈ G.classCutOn classOf D w k X := by rw [ha]; simp
    have hbB : b ∈ G.cutOn D X \ G.classCutOn classOf D w k X := by rw [hb]; simp
    have haCut := (mem_filter.mp haA).1
    have hbCut := (mem_sdiff.mp hbB).1
    have hab : a ≠ b := by
      intro hab
      exact (mem_sdiff.mp hbB).2 (hab ▸ haA)
    refine ⟨a,b,(G.mem_cutOn D X a |>.mp haCut).1,
      (G.mem_cutOn D X b |>.mp hbCut).1,hab,?_,ha,hb⟩
    have hsub : G.classCutOn classOf D w k X ⊆ G.cutOn D X := filter_subset _ _
    have hcover := union_sdiff_of_subset hsub
    rw [ha,hb] at hcover
    simpa only [singleton_union] using hcover.symm

/-- A selected complementary boundary copy identifies the pair uniquely. -/
theorem boundary_pair_of_complement {D : Finset E} (hD : D ∈ P.parts)
    {b : E} (hb : b ∈ G.cutOn D X \ G.classCutOn classOf D w k X) :
    ∃ a : E, a ∈ D ∧ a ≠ b ∧ G.cutOn D X = {a,b} ∧
      G.classCutOn classOf D w k X = {a} ∧
      (G.cutOn D X \ G.classCutOn classOf D w k X) = {b} := by
  obtain ⟨a,b',ha,hb',hab,hcut,hA,hB⟩ :=
    P.exists_boundary_pair G classOf hD ⟨b,(mem_sdiff.mp hb).1⟩
  have hbb' : b = b' := by rw [hB] at hb; exact mem_singleton.mp hb
  subst b'
  exact ⟨a,ha,hab,hcut,hA,hB⟩

/-- No original copy belongs to two different pieces. -/
theorem part_eq_of_common_copy {D D' : Finset E} (hD : D ∈ P.parts)
    (hD' : D' ∈ P.parts) {e : E} (he : e ∈ D) (he' : e ∈ D') : D = D' := by
  by_contra hne
  exact disjoint_left.mp (P.disjoint D hD D' hD' hne) he he'

/-- All degrees of a boundary-free piece are even in the original graph. -/
theorem even_degrees_of_boundary_empty {D : Finset E} (hD : D ∈ P.parts)
    (hcut : (G.cutOn D X).card = 0) (x : V) : Even (G.degreeOn D x) := by
  by_cases hx : x ∈ X
  · exact P.even_inside D hD x hx
  · rw [P.degreeOn_outside_eq_cut G classOf hD x hx,card_eq_zero.mp hcut]
    simp [degreeOn]

end TightShorePieces

end Overfull.FourOdd

namespace Overfull.Multigraph

open Finset Classical

variable {V E K : Type*} (G : Multigraph V E)

/-- A boundary copy has only one endpoint outside its shore. -/
theorem outside_incident_eq_of_cut {D : Finset E} {X : Finset V} {e : E}
    (he : e ∈ G.cutOn D X) {v x : V} (hv : v ∉ X) (hx : x ∉ X)
    (hve : v ∈ G.edge e) (hxe : x ∈ G.edge e) : x = v := by
  by_contra hne
  have hedge := (G.incident_pair_iff_edge_eq hne e).mp ⟨hxe,hve⟩
  have hcut := (G.mem_cutOn_of_edge_eq hedge D X).mp he
  exact hcut.2 (propext (by simp [hx,hv]))

end Overfull.Multigraph
