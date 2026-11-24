import Overfull.CompatibleCircuits.Basic
import Overfull.MatchingPolytope

/-!
# Lifting compatible quotient circuits to actual matchings

The quotient keeps the original edge type, so parallel copies remain
distinct.  Its incidence class at a core label records the actual original
endpoint.  Compatibility is exactly the original matching condition.
-/

namespace Overfull.Multigraph

open Finset Classical

variable {V E I : Type*} (G : Multigraph V E)

/-- Contract vertex labels without identifying any edge copies.  Only
joining edges, whose labels are distinct, are included in this interface. -/
noncomputable def labelQuotient (label : V → I)
    (hjoin : ∀ e, label (G.firstEnd e) ≠ label (G.secondEnd e)) :
    Multigraph I E where
  edge e := s(label (G.firstEnd e), label (G.secondEnd e))
  loopless e := by simpa using hjoin e

@[simp] theorem labelQuotient_incident_iff (label : V → I)
    (hjoin : ∀ e, label (G.firstEnd e) ≠ label (G.secondEnd e))
    (e : E) (i : I) :
    i ∈ (G.labelQuotient label hjoin).edge e ↔
      label (G.firstEnd e) = i ∨ label (G.secondEnd e) = i := by
  simp [labelQuotient, Sym2.mem_iff, eq_comm]

theorem labelQuotient_edge (label : V → I)
    (hjoin : ∀ e, label (G.firstEnd e) ≠ label (G.secondEnd e)) (e : E) :
    (G.labelQuotient label hjoin).edge e = (G.edge e).map label := by
  rw [← G.edge_eq e]
  rfl

/-- The incidence class records the original endpoint.  The value at a
nonincident quotient label is harmless and is never used for compatibility. -/
noncomputable def endpointClass (label : V → I) (i : I) (e : E) : V :=
  if label (G.firstEnd e) = i then G.firstEnd e else G.secondEnd e

theorem endpointClass_mem (label : V → I) (i : I) (e : E) :
    G.endpointClass label i e ∈ G.edge e := by
  rw [G.incident_iff]
  unfold endpointClass
  split_ifs <;> simp

theorem endpointClass_eq_of_incident (label : V → I)
    (hjoin : ∀ e, label (G.firstEnd e) ≠ label (G.secondEnd e))
    {e : E} {v : V} (hv : v ∈ G.edge e) :
    G.endpointClass label (label v) e = v := by
  rcases (G.incident_iff e v).mp hv with h | h
  · rw [← h]
    simp [endpointClass]
  · rw [← h]
    simp [endpointClass, hjoin e]

theorem label_incident_of_incident (label : V → I)
    (hjoin : ∀ e, label (G.firstEnd e) ≠ label (G.secondEnd e))
    {e : E} {v : V} (hv : v ∈ G.edge e) :
    label v ∈ (G.labelQuotient label hjoin).edge e := by
  rw [G.labelQuotient_incident_iff]
  exact (G.incident_iff e v).mp hv |>.imp (congrArg label) (congrArg label)

/-- Compatibility with endpoint classes is equivalent to the original
edge-copy set being a matching, not just a matching of quotient labels. -/
theorem compatible_endpointClass_iff (label : V → I)
    (hjoin : ∀ e, label (G.firstEnd e) ≠ label (G.secondEnd e)) (C : Finset E) :
    (G.labelQuotient label hjoin).Compatible (G.endpointClass label) C ↔
      G.IsMatching C := by
  constructor
  · intro h e he f hf v hve hvf
    apply h (label v) e he (G.label_incident_of_incident label hjoin hve)
      f hf (G.label_incident_of_incident label hjoin hvf)
    rw [G.endpointClass_eq_of_incident label hjoin hve,
      G.endpointClass_eq_of_incident label hjoin hvf]
  · intro h i e he _ f hf _ hclass
    apply h e he f hf (G.endpointClass label i e) (G.endpointClass_mem label i e)
    rw [hclass]
    exact G.endpointClass_mem label i f

/-- Every part of an actual compatible quotient partition is an actual
matching in the original graph. -/
theorem CompatibleCircuitPartition.isMatching (label : V → I)
    (hjoin : ∀ e, label (G.firstEnd e) ≠ label (G.secondEnd e)) {C : Finset E}
    (P : (G.labelQuotient label hjoin).CompatibleCircuitPartition
      (G.endpointClass label) C) {D : Finset E} (hD : D ∈ P.parts) :
    G.IsMatching D :=
  (G.compatible_endpointClass_iff label hjoin D).mp (P.compatible D hD)

/-- The original matching has at most as many copies as there are labels. -/
theorem CompatibleCircuitPartition.card_le [Fintype I] (label : V → I)
    (hjoin : ∀ e, label (G.firstEnd e) ≠ label (G.secondEnd e)) {C : Finset E}
    (P : (G.labelQuotient label hjoin).CompatibleCircuitPartition
      (G.endpointClass label) C) {D : Finset E} (hD : D ∈ P.parts) :
    D.card ≤ Fintype.card I :=
  (P.circuit D hD).card_le

variable {F K : Type*}

/-- A version that also permits virtual copies in the quotient.  The
injection retains each original copy and its incidence class records its
original endpoint.  Only the selected original copies are lifted. -/
theorem isMatching_of_compatible_embedding (H : Multigraph I F)
    (classOf : I → F → K) (label : V → I) (endpoint : V ↪ K) (copy : E ↪ F)
    (hinc : ∀ e v, v ∈ G.edge e → label v ∈ H.edge (copy e))
    (hclass : ∀ e v, v ∈ G.edge e → classOf (label v) (copy e) = endpoint v)
    {C : Finset F} (hC : H.Compatible classOf C)
    {M : Finset E} (hM : ∀ e ∈ M, copy e ∈ C) : G.IsMatching M := by
  intro e he f hf v hve hvf
  apply copy.injective
  apply hC (label v) (copy e) (hM e he) (hinc e v hve)
    (copy f) (hM f hf) (hinc f v hvf)
  rw [hclass e v hve, hclass f v hvf]

end Overfull.Multigraph
