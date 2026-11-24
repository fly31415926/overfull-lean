import Overfull.CompatibleCircuits.QuotientCuts
import Overfull.CompatibleCircuits.FourGlobalCoarsening
import Overfull.CompatibleCircuits.AtMostThree

/-!
# Contraction with original incidence classes

The quotient retains every crossing copy separately.  Its class at a
quotient vertex records both the original endpoint and the original
incidence class.  Consequently every quotient class-cut inequality is
one original class-cut inequality.  This supplies the inside graph in a
tight-shore reduction; it does not assert the full four-label theorem.
-/

noncomputable section

namespace Overfull.FourOdd

open Finset Classical
open Overfull.Multigraph

variable {V E I K : Type*} [Fintype V] [Fintype E] [DecidableEq I]
    (G : Multigraph V E) (label : V → I) (classOf : V → E → K)

/-- A contracted incidence keeps its original endpoint and class. -/
def joiningIncidenceClass (i : I) (e : joiningCopies G label) : V × K :=
  let v := (joiningGraph G label).endpointClass label i e
  (v, classOf v e.val)

omit [Fintype V] in
/-- Exact identification of one contracted incidence class. -/
theorem joiningIncidenceClass_incident_iff
    (i : I) (e : joiningCopies G label) (v : V) (k : K) :
    (i ∈ (joiningQuotient G label).edge e ∧
      joiningIncidenceClass G label classOf i e = (v,k)) ↔
      label v = i ∧ v ∈ G.edge e.val ∧ classOf v e.val = k := by
  classical
  change (i ∈ ((joiningGraph G label).labelQuotient label
    (joiningGraph_join G label)).edge e ∧
    ((joiningGraph G label).endpointClass label i e,
      classOf ((joiningGraph G label).endpointClass label i e) e.val) = (v,k)) ↔ _
  constructor
  · rintro ⟨hi,hclass⟩
    have hv := congrArg Prod.fst hclass
    have hk := congrArg Prod.snd hclass
    change (joiningGraph G label).endpointClass label i e = v at hv
    change classOf ((joiningGraph G label).endpointClass label i e) e.val = k at hk
    have h := ((joiningGraph G label).labelQuotient_endpointClass_incident_iff
      label (joiningGraph_join G label) e i v).mp ⟨hi,hv⟩
    refine ⟨h.1,h.2,?_⟩
    simpa only [hv] using hk
  · rintro ⟨hlabel,hv,hk⟩
    have h := ((joiningGraph G label).labelQuotient_endpointClass_incident_iff
      label (joiningGraph_join G label) e i v).mpr ⟨hlabel,hv⟩
    exact ⟨h.1,by rw [h.2,hk]⟩

/-- The image is exactly the original class cut, or empty off the fiber. -/
theorem joiningIncidenceClass_classCutOn_image
    (i : I) (v : V) (k : K) (A : Finset I) :
    ((joiningQuotient G label).classCutOn
      (joiningIncidenceClass G label classOf) univ i (v,k) A).image Subtype.val =
      if label v = i then G.classCutOn classOf univ v k (labelShore label A)
      else ∅ := by
  classical
  by_cases hlabel : label v = i
  · rw [if_pos hlabel]
    ext e
    constructor
    · intro he
      obtain ⟨f,hf,rfl⟩ := mem_image.mp he
      simp only [classCutOn,mem_filter] at hf
      obtain ⟨hf,hinc,hclass⟩ := hf
      have h := (joiningIncidenceClass_incident_iff G label classOf i f v k).mp
        ⟨hinc,hclass⟩
      simp only [classCutOn,mem_filter]
      refine ⟨?_,h.2⟩
      rw [← joiningCut_image G label A]
      exact mem_image.mpr ⟨f,hf,rfl⟩
    · intro he
      simp only [classCutOn,mem_filter] at he
      obtain ⟨he,hv,hk⟩ := he
      rw [← joiningCut_image G label A] at he
      obtain ⟨f,hf,rfl⟩ := mem_image.mp he
      refine mem_image.mpr ⟨f,?_,rfl⟩
      simp only [classCutOn,mem_filter]
      refine ⟨hf,?_⟩
      exact (joiningIncidenceClass_incident_iff G label classOf i f v k).mpr
        ⟨hlabel,hv,hk⟩
  · rw [if_neg hlabel]
    apply eq_empty_iff_forall_notMem.mpr
    intro e he
    obtain ⟨f,hf,_⟩ := mem_image.mp he
    simp only [classCutOn,mem_filter] at hf
    obtain ⟨_,hinc,hclass⟩ := hf
    exact hlabel ((joiningIncidenceClass_incident_iff G label classOf i f v k).mp
      ⟨hinc,hclass⟩).1

/-- Contraction preserves the half-cut inequalities for tagged original classes. -/
theorem joiningIncidenceClass_admissible
    (hadmissible : G.AdmissibleOn classOf univ) :
    (joiningQuotient G label).AdmissibleOn
      (joiningIncidenceClass G label classOf) univ := by
  classical
  intro i q A
  obtain ⟨v,k⟩ := q
  have hclass := congrArg Finset.card
    (joiningIncidenceClass_classCutOn_image G label classOf i v k A)
  rw [card_image_of_injective _ Subtype.val_injective] at hclass
  change 2 * _ ≤ (joiningCut G label A).card
  rw [hclass,joiningCut_card]
  by_cases hlabel : label v = i
  · rw [if_pos hlabel]
    exact hadmissible v k (labelShore label A)
  · simp [hlabel]

/-- Even original degrees give even contracted degrees in every fiber. -/
theorem joiningQuotient_even_degrees_of_even_degrees
    (heven : ∀ v, Even (G.degreeOn univ v)) (i : I) :
    Even ((joiningQuotient G label).degreeOn univ i) := by
  change Even ((joiningQuotient G label).degree i)
  rw [joiningQuotient_degree_eq_cut]
  exact G.even_cutOn_of_even_degrees heven _

end Overfull.FourOdd

namespace Overfull.Multigraph

open Finset Classical

variable {V E K : Type*} (G : Multigraph V E)

/-- Replace one vertex's classes by a designated class and its complement. -/
def coarsenTightClassAt (classOf : V → E → K) (v : V) (k : K) :
    V → E → K ⊕ Bool :=
  fun x e => if x = v then Sum.inr (decide (classOf v e = k))
    else Sum.inl (classOf x e)

/-- The designated local tight class may be coarsened without losing any
global class-cut inequality. -/
theorem admissibleOn_coarsenTightClassAt
    (classOf : V → E → K) {C : Finset E}
    (hadmissible : G.AdmissibleOn classOf C) (v : V) (k : K)
    (htight : 2 * (C.filter (fun e => v ∈ G.edge e ∧ classOf v e = k)).card =
      G.degreeOn C v) :
    G.AdmissibleOn (coarsenTightClassAt classOf v k) C := by
  classical
  intro x q X
  by_cases hx : x = v
  · subst x
    rcases q with q | q
    · simp [classCutOn,coarsenTightClassAt]
    · cases q
      · simpa [classCutOn,coarsenTightClassAt] using
          G.complement_class_cut_bound_of_local_tight classOf hadmissible v k htight X
      · simpa [classCutOn,coarsenTightClassAt] using hadmissible v k X
  · rcases q with q | q
    · simpa [classCutOn,coarsenTightClassAt,hx] using hadmissible x q X
    · simp [classCutOn,coarsenTightClassAt,hx]

/-- A compatible circuit through the coarsened vertex uses one actual
copy of the tight class and one actual copy of its complement. -/
theorem IsCircuit.coarsenTightClassAt_counts
    (classOf : V → E → K) (v : V) (k : K) {D : Finset E}
    (hD : G.IsCircuit D) (hcomp : G.Compatible (coarsenTightClassAt classOf v k) D)
    (hv : v ∈ G.edgeSupport D) :
    (D.filter (fun e => v ∈ G.edge e ∧ classOf v e = k)).card = 1 ∧
      (D.filter (fun e => v ∈ G.edge e ∧ classOf v e ≠ k)).card = 1 := by
  classical
  have htrue := hcomp.classCutOn_card_le_one G v (Sum.inr true) {v}
  have hfalse := hcomp.classCutOn_card_le_one G v (Sum.inr false) {v}
  rw [G.classCutOn_singleton_self] at htrue hfalse
  simp [coarsenTightClassAt] at htrue hfalse
  have hsum := (D.filter (fun e => v ∈ G.edge e)).filter_card_add_filter_neg_card_eq_card
    (fun e => classOf v e = k)
  simp only [filter_filter] at hsum
  have hdegree := hD.2.1 v hv
  change (D.filter (fun e => v ∈ G.edge e)).card = 2 at hdegree
  omega

end Overfull.Multigraph
