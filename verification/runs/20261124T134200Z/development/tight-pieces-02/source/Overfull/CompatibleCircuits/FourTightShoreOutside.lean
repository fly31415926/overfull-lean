import Overfull.CompatibleCircuits.FourTightShoreContraction
import Overfull.CompatibleCircuits.FourDegreeTwoSupport

/-!
# The outside graph of a tight nonlocal shore

Contract the entire shore into its designated outside class vertex. The
surviving original copies remain distinct. At that vertex give every
redirected incidence the tight class; retain the other original classes.
The tight shore identity proves all class-cut bounds of this outside graph.
-/

noncomputable section

namespace Overfull.Multigraph

open Finset Classical
open scoped BigOperators

variable {V E K : Type*} (G : Multigraph V E)

/-- Copies crossing `T` with an endpoint in `X`. For disjoint shores these
are precisely the copies between the two shores. -/
def betweenShoreCopies (C : Finset E) (X T : Finset V) : Finset E :=
  (G.cutOn C T).filter (fun e => G.firstEnd e ∈ X ∨ G.secondEnd e ∈ X)

/-- The exact cut identity for disjoint shores counts every parallel copy. -/
theorem cutOn_union_card_of_disjoint (C : Finset E) (X T : Finset V)
    (hXT : Disjoint X T) :
    (G.cutOn C (T ∪ X)).card + 2 * (G.betweenShoreCopies C X T).card =
      (G.cutOn C T).card + (G.cutOn C X).card := by
  simp only [betweenShoreCopies, cutOn, filter_filter, card_eq_sum_ones, sum_filter,
    mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro e _
  have ha := disjoint_left.mp hXT (a := G.firstEnd e)
  have hb := disjoint_left.mp hXT (a := G.secondEnd e)
  by_cases haX : G.firstEnd e ∈ X <;> by_cases haT : G.firstEnd e ∈ T <;>
    by_cases hbX : G.secondEnd e ∈ X <;> by_cases hbT : G.secondEnd e ∈ T <;>
    simp_all

/-- When its class vertex is outside both disjoint shores, its two class
cuts are disjoint. -/
theorem classCutOn_disjoint_shores (classOf : V → E → K) (C : Finset E)
    (v : V) (k : K) (X T : Finset V) (hXT : Disjoint X T)
    (hvX : v ∉ X) (hvT : v ∉ T) :
    Disjoint (G.classCutOn classOf C v k X) (G.classCutOn classOf C v k T) := by
  apply disjoint_left.mpr
  intro e heX heT
  obtain ⟨heX, hv, _⟩ := mem_filter.mp heX
  obtain ⟨heT, _, _⟩ := mem_filter.mp heT
  have hx := (G.mem_cutOn C X e).mp heX |>.2
  have ht := (G.mem_cutOn C T e).mp heT |>.2
  rcases (G.incident_iff e v).mp hv with ha | hb
  · rw [ha] at hx ht
    have hbx : G.secondEnd e ∈ X := by simpa [hvX] using hx
    have hbt : G.secondEnd e ∈ T := by simpa [hvT] using ht
    exact disjoint_left.mp hXT hbx hbt
  · rw [hb] at hx ht
    have hax : G.firstEnd e ∈ X := by simpa [hvX] using hx
    have hat : G.firstEnd e ∈ T := by simpa [hvT] using ht
    exact disjoint_left.mp hXT hax hat

theorem classCutOn_union_of_outside (classOf : V → E → K) (C : Finset E)
    (v : V) (k : K) (X T : Finset V) (hvX : v ∉ X) (hvT : v ∉ T) :
    G.classCutOn classOf C v k (T ∪ X) =
      G.classCutOn classOf C v k T ∪ G.classCutOn classOf C v k X := by
  ext e
  by_cases hv : v ∈ G.edge e
  · rcases (G.incident_iff e v).mp hv with ha | hb <;>
      simp [classCutOn, mem_cutOn, ha, hb, hvX, hvT, hv, or_and_right, and_or_left]
  · simp [classCutOn, hv]

/-- A tight class on `X` pays for all incidences redirected from `X`
towards a disjoint shore `T`. -/
theorem tight_shore_redirected_class_bound
    (classOf : V → E → K) {C : Finset E} (v : V) (k : K) (X T : Finset V)
    (hadmissible : G.AdmissibleOn classOf C)
    (hXT : Disjoint X T) (hvX : v ∉ X) (hvT : v ∉ T)
    (htight : 2 * (G.classCutOn classOf C v k X).card = (G.cutOn C X).card) :
    2 * ((G.classCutOn classOf C v k T).card +
      (G.betweenShoreCopies C X T).card) ≤ (G.cutOn C T).card := by
  have h := hadmissible v k (T ∪ X)
  rw [G.classCutOn_union_of_outside classOf C v k X T hvX hvT,
    card_union_of_disjoint (G.classCutOn_disjoint_shores classOf C v k X T hXT hvX hvT).symm]
    at h
  have hcut := G.cutOn_union_card_of_disjoint C X T hXT
  omega

end Overfull.Multigraph

namespace Overfull.FourOdd

open Finset Classical Overfull.Multigraph

variable {V E K : Type*} [Fintype V] [Fintype E]
    (G : Multigraph V E) (classOf : V → E → K)

/-- Contract the shore into the specified exterior vertex. -/
def shoreIntoLabel (X : Finset V) (w : V) (v : V) : V :=
  if v ∈ X then w else v

def tightShoreOutsideGraph (X : Finset V) (w : V) :
    Multigraph V (joiningCopies G (shoreIntoLabel X w)) :=
  joiningQuotient G (shoreIntoLabel X w)

/-- Redirected incidences receive the designated class; all other
incidences retain their original class. -/
def tightShoreOutsideClass (X : Finset V) (w : V) (k : K)
    (v : V) (e : joiningCopies G (shoreIntoLabel X w)) : K :=
  let t := (joiningGraph G (shoreIntoLabel X w)).endpointClass (shoreIntoLabel X w) v e
  if t ∈ X then k else classOf t e.val

theorem shoreIntoLabel_not_mem (X : Finset V) (w : V) (hw : w ∉ X) (v : V) :
    shoreIntoLabel X w v ∉ X := by
  by_cases hv : v ∈ X <;> simp [shoreIntoLabel, hv, hw]

theorem labelShore_shoreIntoLabel_disjoint (X : Finset V) (w : V)
    (A : Finset V) (hwA : w ∉ A) :
    Disjoint X (labelShore (shoreIntoLabel X w) A) := by
  apply disjoint_left.mpr
  intro v hv ht
  have h := mem_labelShore (shoreIntoLabel X w) A v |>.mp ht
  exact hwA (by simpa [shoreIntoLabel, hv] using h)

theorem labelShore_shoreIntoLabel_anchor_not_mem (X : Finset V) (w : V)
    (A : Finset V) (hwA : w ∉ A) :
    w ∉ labelShore (shoreIntoLabel X w) A := by
  simp [shoreIntoLabel, hwA]

theorem tightShoreOutsideClass_incident
    (X : Finset V) (w : V) (k : K)
    (v : V) (e : joiningCopies G (shoreIntoLabel X w))
    (hv : v ∈ (tightShoreOutsideGraph G X w).edge e) :
    ∃ t, t ∈ G.edge e.val ∧ shoreIntoLabel X w t = v ∧
      tightShoreOutsideClass G classOf X w k v e =
        if t ∈ X then k else classOf t e.val := by
  let label := shoreIntoLabel X w
  let t := (joiningGraph G label).endpointClass label v e
  have h := ((joiningGraph G label).labelQuotient_endpointClass_incident_iff
    label (joiningGraph_join G label) e v t).mp ⟨hv, rfl⟩
  exact ⟨t, h.2, h.1, rfl⟩

end Overfull.FourOdd
