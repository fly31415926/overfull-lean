import Overfull.CompatibleCircuits.LocalCoarsening
import Overfull.CompatibleCircuits.ThreeLabelBundles
import Overfull.FourOdd.CutBounds

/-!
# Tight local coarsening preserves every cut inequality

At a vertex with a tight incidence class, replace its classes by that class
and its complement. The complement satisfies every half-cut bound because
the original tight class satisfies the bound on the shore with that vertex
toggled. Thus local coarsenings may be chosen simultaneously while preserving
global admissibility. This holds for arbitrary vertex types and degrees;
it supplies a reduction for the four-label problem, not its existence theorem.
-/

namespace Overfull.Multigraph

open Finset Classical
open Overfull.CompatibleCircuits

variable {V E K : Type*} (G : Multigraph V E)

/-- The toggle identity expressed in the actual-copy cut and degree API. -/
theorem cutOn_toggle_card (C : Finset E) (X : Finset V) (v : V) :
    (G.cutOn C (MatchingProbability.toggle X v)).card +
        2 * G.degreeOn (G.cutOn C X) v =
      (G.cutOn C X).card + G.degreeOn C v := by
  simpa only [FourOdd.degreeOn_eq_probability_incident G,
    FourOdd.cutOn_eq_probability_cut G, MultigraphMatchingProbability.cutCount]
    using MultigraphMatchingProbability.cut_toggle (G := G) C X v

/-- Toggling a class's own vertex exchanges its crossing and noncrossing
incidences, including all parallel copies. -/
theorem classCutOn_card_add_toggle_card (classOf : V → E → K)
    (C : Finset E) (v : V) (k : K) (X : Finset V) :
    (G.classCutOn classOf C v k X).card +
        (G.classCutOn classOf C v k (MatchingProbability.toggle X v)).card =
      (C.filter (fun e => v ∈ G.edge e ∧ classOf v e = k)).card := by
  let A := C.filter (fun e => v ∈ G.edge e ∧ classOf v e = k)
  have hcut (Y : Finset V) : G.cutOn A Y = G.classCutOn classOf C v k Y := by
    ext e
    simp only [A, cutOn, classCutOn, mem_filter]
    tauto
  have hdegree : G.degreeOn A v = A.card := by
    unfold degreeOn
    congr 1
    apply filter_eq_self.mpr
    intro e he
    exact (mem_filter.mp he).2.1
  have hcutdegree : G.degreeOn (G.cutOn A X) v = (G.cutOn A X).card := by
    unfold degreeOn
    congr 1
    apply filter_eq_self.mpr
    intro e he
    exact (mem_filter.mp (G.mem_cutOn A X e |>.mp he).1).2.1
  have ht := G.cutOn_toggle_card A X v
  rw [hdegree, hcutdegree, hcut, hcut] at ht
  change _ = A.card
  omega

/-- If one local incidence class occupies exactly half the degree, its
complement satisfies the half-cut inequality on every shore. -/
theorem complement_class_cut_bound_of_local_tight
    (classOf : V → E → K) {C : Finset E}
    (hadmissible : G.AdmissibleOn classOf C) (v : V) (k : K)
    (htight : 2 * (C.filter (fun e => v ∈ G.edge e ∧ classOf v e = k)).card =
      G.degreeOn C v) (X : Finset V) :
    2 * ((G.cutOn C X).filter
      (fun e => v ∈ G.edge e ∧ classOf v e ≠ k)).card ≤ (G.cutOn C X).card := by
  have htoggle := G.cutOn_toggle_card C X v
  have hclass := G.classCutOn_card_add_toggle_card classOf C v k X
  have hother := hadmissible v k (MatchingProbability.toggle X v)
  have hpart : (G.classCutOn classOf C v k X).card +
      ((G.cutOn C X).filter (fun e => v ∈ G.edge e ∧ classOf v e ≠ k)).card =
      G.degreeOn (G.cutOn C X) v := by
    simpa only [classCutOn, degreeOn, filter_filter, ne_eq] using
      ((G.cutOn C X).filter (fun e => v ∈ G.edge e)).filter_card_add_filter_neg_card_eq_card
        (fun e => classOf v e = k)
  omega

/-- Simultaneous tight local coarsenings preserve all global half-cut
bounds, without a restriction on the number of vertices. -/
theorem admissibleOn_localCoarsening (classOf : V → E → K)
    (C : Finset E) (hadmissible : G.AdmissibleOn classOf C)
    (L : ∀ v, LocalCoarsening (C.filter (fun e => v ∈ G.edge e)) (classOf v)) :
    G.AdmissibleOn (fun v e => (L v).coarse e) C := by
  intro v q X
  rcases (L v).identity_or_tight with hid | ⟨k, htight, hmap⟩
  · rcases q with q | q
    · simpa only [classCutOn, hid, Sum.inl.injEq] using hadmissible v q X
    · simp [classCutOn, hid]
  · have htight' :
        2 * (C.filter (fun e => v ∈ G.edge e ∧ classOf v e = k)).card =
          G.degreeOn C v := by
      simpa only [filter_filter, degreeOn] using htight
    rcases q with q | q
    · simp [classCutOn, hmap]
    · cases q
      · simpa [classCutOn, hmap] using
          G.complement_class_cut_bound_of_local_tight classOf hadmissible v k htight' X
      · simpa [classCutOn, hmap] using hadmissible v k X

/-- Coarse compatibility implies original compatibility on the exact same
edge-copy set. -/
theorem Compatible.of_localCoarsening (classOf : V → E → K)
    (C : Finset E)
    (L : ∀ v, LocalCoarsening (C.filter (fun e => v ∈ G.edge e)) (classOf v))
    {D : Finset E} (hD : G.Compatible (fun v e => (L v).coarse e) D) :
    G.Compatible classOf D := by
  intro v e he hve f hf hvf hclass
  apply hD v e he hve f hf hvf
  by_contra hne
  exact (L v).refines e f hne hclass

/-- Any partition constructed after local coarsening gives a partition of
the original copies with their original incidence classes. -/
def CompatibleCircuitPartition.of_localCoarsening (classOf : V → E → K)
    (C : Finset E)
    (L : ∀ v, LocalCoarsening (C.filter (fun e => v ∈ G.edge e)) (classOf v))
    (P : G.CompatibleCircuitPartition (fun v e => (L v).coarse e) C) :
    G.CompatibleCircuitPartition classOf C where
  parts := P.parts
  circuit := P.circuit
  compatible := fun D hD => (P.compatible D hD).of_localCoarsening G classOf C L
  disjoint := P.disjoint
  cover := P.cover

/-- Admissibility supplies simultaneous coarse classes meeting every tight
local class, and those coarse classes remain globally admissible. -/
theorem exists_globally_admissible_localCoarsening
    (classOf : V → E → K) (C : Finset E)
    (hadmissible : G.AdmissibleOn classOf C) :
    ∃ L : ∀ v, LocalCoarsening (C.filter (fun e => v ∈ G.edge e)) (classOf v),
      G.AdmissibleOn (fun v e => (L v).coarse e) C := by
  have hex (v : V) : Nonempty
      (LocalCoarsening (C.filter (fun e => v ∈ G.edge e)) (classOf v)) := by
    apply exists_localCoarsening
    intro k
    simpa only [filter_filter, degreeOn] using hadmissible.local_class_bound G v k
  let L := fun v => Classical.choice (hex v)
  exact ⟨L, G.admissibleOn_localCoarsening classOf C hadmissible L⟩

end Overfull.Multigraph
