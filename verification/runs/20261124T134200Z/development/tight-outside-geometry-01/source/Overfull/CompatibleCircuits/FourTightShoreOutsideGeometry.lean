import Overfull.CompatibleCircuits.FourTightShoreOutside

/-!
# Exact geometry of the outside contraction

Every retained copy touching the contracted shore is a boundary copy whose
original outside endpoint is different from the anchor.  Its new endpoint
at the anchor has the designated class.  Original outside incidences retain
their classes, and copies avoiding the shore retain their exact endpoints.
These identities supply the original-copy block restoration interface.
-/

noncomputable section

namespace Overfull.FourOdd

open Finset Classical Overfull.Multigraph

variable {V E K : Type*} [Fintype E] (G : Multigraph V E)

/-- A retained outside copy touches the shore exactly when it crosses it.
Two original endpoints in the shore would have the same contracted label. -/
theorem tightShoreOutside_touches_iff_boundary (X : Finset V) (w : V)
    (e : joiningCopies G (shoreIntoLabel X w)) :
    (G.firstEnd e.val ∈ X ∨ G.secondEnd e.val ∈ X) ↔
      e.val ∈ G.cutOn univ X := by
  have hn := (mem_joiningCopies G (shoreIntoLabel X w) e.val).mp e.property
  by_cases ha : G.firstEnd e.val ∈ X <;> by_cases hb : G.secondEnd e.val ∈ X
  · simp [shoreIntoLabel, ha, hb] at hn
  · simp [mem_cutOn, ha, hb]
  · simp [mem_cutOn, ha, hb]
  · simp [mem_cutOn, ha, hb]

/-- A retained redirected copy cannot originally be incident with the
anchor: such a copy would become a loop and would not be retained. -/
theorem tightShoreOutside_touch_not_anchor (X : Finset V) (w : V) (hw : w ∉ X)
    (e : joiningCopies G (shoreIntoLabel X w))
    (htouch : G.firstEnd e.val ∈ X ∨ G.secondEnd e.val ∈ X) :
    w ∉ G.edge e.val := by
  have hn := (mem_joiningCopies G (shoreIntoLabel X w) e.val).mp e.property
  intro hwe
  rcases (G.incident_iff e.val w).mp hwe with ha | hb
  · rw [ha] at hn htouch
    have hbX := htouch.resolve_left hw
    simp [shoreIntoLabel, hw, hbX] at hn
  · rw [hb] at hn htouch
    have haX := htouch.resolve_right hw
    simp [shoreIntoLabel, hw, haX] at hn

/-- Exact incidence at each vertex outside the shore.  The only added
incidence is the anchor of a redirected copy. -/
theorem tightShoreOutside_incident_iff (X : Finset V) (w : V)
    (e : joiningCopies G (shoreIntoLabel X w)) (v : V) (hv : v ∉ X) :
    v ∈ (tightShoreOutsideGraph G X w).edge e ↔
      v ∈ G.edge e.val ∨
        (v = w ∧ (G.firstEnd e.val ∈ X ∨ G.secondEnd e.val ∈ X)) := by
  have hlabel (t : V) : shoreIntoLabel X w t = v ↔ t = v ∨ (v = w ∧ t ∈ X) := by
    by_cases ht : t ∈ X
    · have htv : t ≠ v := fun h => hv (h ▸ ht)
      simp [shoreIntoLabel, ht, htv, eq_comm]
    · simp [shoreIntoLabel, ht]
  change v ∈ ((joiningGraph G (shoreIntoLabel X w)).labelQuotient
    (shoreIntoLabel X w) (joiningGraph_join G (shoreIntoLabel X w))).edge e ↔ _
  rw [(joiningGraph G (shoreIntoLabel X w)).labelQuotient_incident_iff]
  simp only [joiningGraph_firstEnd, joiningGraph_secondEnd, hlabel, G.incident_iff]
  tauto

/-- An original endpoint supplies its exact contracted incidence and
class, before separating exterior and redirected cases. -/
theorem tightShoreOutside_incidence_class_of_endpoint
    (classOf : V → E → K) (X : Finset V) (w : V) (k : K)
    (e : joiningCopies G (shoreIntoLabel X w)) (t : V)
    (ht : t ∈ G.edge e.val) :
    shoreIntoLabel X w t ∈ (tightShoreOutsideGraph G X w).edge e ∧
      tightShoreOutsideClass G classOf X w k (shoreIntoLabel X w t) e =
        if t ∈ X then k else classOf t e.val := by
  have h := ((joiningGraph G (shoreIntoLabel X w)).labelQuotient_endpointClass_incident_iff
    (shoreIntoLabel X w) (joiningGraph_join G (shoreIntoLabel X w))
    e (shoreIntoLabel X w t) t).mpr ⟨rfl, ht⟩
  refine ⟨h.1, ?_⟩
  unfold tightShoreOutsideClass
  rw [h.2]

/-- Every original outside incidence survives and keeps its original
class, including an original incidence at the anchor. -/
theorem tightShoreOutside_original_incidence
    (classOf : V → E → K) (X : Finset V) (w : V) (k : K)
    (e : joiningCopies G (shoreIntoLabel X w)) (v : V)
    (hv : v ∉ X) (hve : v ∈ G.edge e.val) :
    v ∈ (tightShoreOutsideGraph G X w).edge e ∧
      tightShoreOutsideClass G classOf X w k v e = classOf v e.val := by
  simpa only [shoreIntoLabel, if_neg hv] using
    tightShoreOutside_incidence_class_of_endpoint G classOf X w k e v hve

/-- A redirected copy has the designated class at the anchor. -/
theorem tightShoreOutside_redirected_incidence
    (classOf : V → E → K) (X : Finset V) (w : V) (k : K)
    (e : joiningCopies G (shoreIntoLabel X w))
    (htouch : G.firstEnd e.val ∈ X ∨ G.secondEnd e.val ∈ X) :
    w ∈ (tightShoreOutsideGraph G X w).edge e ∧
      tightShoreOutsideClass G classOf X w k w e = k := by
  rcases htouch with ha | hb
  · have ht : G.firstEnd e.val ∈ G.edge e.val :=
      (G.incident_iff e.val _).mpr (Or.inl rfl)
    simpa only [shoreIntoLabel, if_pos ha] using
      tightShoreOutside_incidence_class_of_endpoint G classOf X w k e _ ht
  · have ht : G.secondEnd e.val ∈ G.edge e.val :=
      (G.incident_iff e.val _).mpr (Or.inr rfl)
    simpa only [shoreIntoLabel, if_pos hb] using
      tightShoreOutside_incidence_class_of_endpoint G classOf X w k e _ ht

/-- Copies with both endpoints outside the shore retain their exact
original unordered pair of endpoints. -/
theorem tightShoreOutside_edge_of_not_touch (X : Finset V) (w : V)
    (e : joiningCopies G (shoreIntoLabel X w))
    (htouch : ¬ (G.firstEnd e.val ∈ X ∨ G.secondEnd e.val ∈ X)) :
    (tightShoreOutsideGraph G X w).edge e = G.edge e.val := by
  change s(shoreIntoLabel X w (G.firstEnd e.val),
    shoreIntoLabel X w (G.secondEnd e.val)) = G.edge e.val
  simp only [shoreIntoLabel, if_neg (not_or.mp htouch).1,
    if_neg (not_or.mp htouch).2, G.edge_eq]

/-- Every redirected copy has one original interior endpoint and one
unique exterior endpoint other than the anchor, whose identity is retained. -/
theorem tightShoreOutside_boundary_endpoints (X : Finset V) (w : V) (hw : w ∉ X)
    (e : joiningCopies G (shoreIntoLabel X w))
    (htouch : G.firstEnd e.val ∈ X ∨ G.secondEnd e.val ∈ X) :
    ∃ x z : V, x ∈ X ∧ z ∉ X ∧ z ≠ w ∧
      G.edge e.val = s(x, z) ∧
      (tightShoreOutsideGraph G X w).edge e = s(w, z) ∧
      ∀ y, y ∉ X → y ∈ G.edge e.val → y = z := by
  have hbound := (tightShoreOutside_touches_iff_boundary G X w e).mp htouch
  have hcross := (G.mem_cutOn univ X e.val).mp hbound |>.2
  have hwne := tightShoreOutside_touch_not_anchor G X w hw e htouch
  have hbuild (x z : V) (hx : x ∈ X) (hz : z ∉ X)
      (he : G.edge e.val = s(x, z)) :
      ∃ x z : V, x ∈ X ∧ z ∉ X ∧ z ≠ w ∧
        G.edge e.val = s(x, z) ∧
        (tightShoreOutsideGraph G X w).edge e = s(w, z) ∧
        ∀ y, y ∉ X → y ∈ G.edge e.val → y = z := by
    refine ⟨x, z, hx, hz, ?_, he, ?_, ?_⟩
    · intro hzw
      apply hwne
      simp [he, hzw]
    · change ((joiningGraph G (shoreIntoLabel X w)).labelQuotient
        (shoreIntoLabel X w) (joiningGraph_join G (shoreIntoLabel X w))).edge e = _
      rw [(joiningGraph G (shoreIntoLabel X w)).labelQuotient_edge]
      simp only [joiningGraph_edge, he, Sym2.map_pair_eq,
        shoreIntoLabel, if_pos hx, if_neg hz]
    · intro y hy hye
      rw [he] at hye
      rcases Sym2.mem_iff.mp hye with rfl | rfl
      · exact False.elim (hy hx)
      · rfl
  rcases htouch with ha | hb
  · have hb : G.secondEnd e.val ∉ X := by simpa [ha] using hcross
    exact hbuild _ _ ha hb (G.edge_eq e.val).symm
  · have ha : G.firstEnd e.val ∉ X := by simpa [hb] using hcross
    apply hbuild _ _ hb ha
    exact (G.edge_eq e.val).symm.trans (Sym2.eq_swap)

end Overfull.FourOdd
