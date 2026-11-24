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
  have ha : ¬ (G.firstEnd e ∈ X ∧ G.firstEnd e ∈ T) :=
    fun h => disjoint_left.mp hXT h.1 h.2
  have hb : ¬ (G.secondEnd e ∈ X ∧ G.secondEnd e ∈ T) :=
    fun h => disjoint_left.mp hXT h.1 h.2
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
  · rcases (G.incident_iff e v).mp hv with ha | ha <;>
      simp [classCutOn, mem_cutOn, ha, hvX, hvT, hv] <;> tauto
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

omit [Fintype V] in
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

omit [Fintype V] in
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

/-- The image of an outside class cut is contained in its original class
cut, with precisely the possible additional redirected class copies. -/
theorem tightShoreOutside_classCutOn_image_subset
    (X : Finset V) (w : V) (k : K) (A : Finset V)
    (v : V) (q : K) :
    ((tightShoreOutsideGraph G X w).classCutOn
      (tightShoreOutsideClass G classOf X w k) univ v q A).image Subtype.val ⊆
        G.classCutOn classOf univ v q (labelShore (shoreIntoLabel X w) A) ∪
          if v = w ∧ q = k then
            G.betweenShoreCopies univ X (labelShore (shoreIntoLabel X w) A) else ∅ := by
  intro e he
  obtain ⟨f, hf, rfl⟩ := mem_image.mp he
  obtain ⟨hcut, hv, hclass⟩ := mem_filter.mp hf
  have hcut' : f.val ∈ G.cutOn univ (labelShore (shoreIntoLabel X w) A) := by
    rw [← joiningCut_image G (shoreIntoLabel X w) A]
    exact mem_image.mpr ⟨f, hcut, rfl⟩
  obtain ⟨t, ht, hlabel, hvalue⟩ :=
    tightShoreOutsideClass_incident G classOf X w k v f hv
  by_cases htX : t ∈ X
  · have hvw : v = w := by simpa [shoreIntoLabel, htX] using hlabel.symm
    have hqk : q = k := by simpa [hvalue, htX] using hclass.symm
    apply mem_union_right
    rw [if_pos ⟨hvw, hqk⟩]
    apply mem_filter.mpr
    refine ⟨hcut', ?_⟩
    rcases (G.incident_iff f.val t).mp ht with h | h
    · exact Or.inl (h.symm ▸ htX)
    · exact Or.inr (h.symm ▸ htX)
  · have htv : t = v := by simpa [shoreIntoLabel, htX] using hlabel
    apply mem_union_left
    apply mem_filter.mpr
    refine ⟨hcut', htv ▸ ht, ?_⟩
    rw [hvalue, if_neg htX] at hclass
    simpa only [htv] using hclass

/-- Every class-cut bound of the actual outside contraction follows from
the original bounds and the one tight nonlocal cut. -/
theorem tightShoreOutside_admissible (X : Finset V) (w : V) (k : K)
    (hadmissible : G.AdmissibleOn classOf univ) (hw : w ∉ X)
    (htight : 2 * (G.classCutOn classOf univ w k X).card = (G.cutOn univ X).card) :
    (tightShoreOutsideGraph G X w).AdmissibleOn
      (tightShoreOutsideClass G classOf X w k) univ := by
  let H := tightShoreOutsideGraph G X w
  let c := tightShoreOutsideClass G classOf X w k
  have hside (v : V) (q : K) (A : Finset V) (hwA : w ∉ A) :
      2 * (H.classCutOn c univ v q A).card ≤ (H.cutOn univ A).card := by
    let T := labelShore (shoreIntoLabel X w) A
    have hcut : (H.cutOn univ A).card = (G.cutOn univ T).card :=
      joiningCut_card G (shoreIntoLabel X w) A
    have hbound := card_le_card
      (tightShoreOutside_classCutOn_image_subset G classOf X w k A v q)
    rw [card_image_of_injective _ Subtype.val_injective] at hbound
    change (H.classCutOn c univ v q A).card ≤
      (G.classCutOn classOf univ v q T ∪
        if v = w ∧ q = k then G.betweenShoreCopies univ X T else ∅).card at hbound
    rw [hcut]
    by_cases hspecial : v = w ∧ q = k
    · obtain ⟨hvw, hqk⟩ := hspecial
      subst v
      subst q
      rw [if_pos ⟨rfl, rfl⟩] at hbound
      have hcard := card_union_le (G.classCutOn classOf univ w k T)
        (G.betweenShoreCopies univ X T)
      have hredirect := G.tight_shore_redirected_class_bound classOf w k X T
        hadmissible (labelShore_shoreIntoLabel_disjoint X w A hwA) hw
        (labelShore_shoreIntoLabel_anchor_not_mem X w A hwA) htight
      omega
    · rw [if_neg hspecial, union_empty] at hbound
      have h := hadmissible v q T
      omega
  intro v q A
  by_cases hwA : w ∈ A
  · have h := hside v q Aᶜ (by simpa using hwA)
    simpa only [H.classCutOn_compl, H.cutOn_compl] using h
  · exact hside v q A hwA

theorem tightShoreOutside_even_degrees (X : Finset V) (w : V)
    (heven : ∀ v, Even (G.degreeOn univ v)) (v : V) :
    Even ((tightShoreOutsideGraph G X w).degreeOn univ v) :=
  joiningQuotient_even_degrees_of_even_degrees G (shoreIntoLabel X w) heven v

theorem tightShoreOutside_support_subset (X : Finset V) (w : V) (hw : w ∉ X) :
    (tightShoreOutsideGraph G X w).edgeSupport univ ⊆ Xᶜ := by
  intro v hv
  obtain ⟨e, _, hve⟩ := mem_edgeSupport _ _ _ |>.mp hv
  change v ∈ ((joiningGraph G (shoreIntoLabel X w)).labelQuotient
    (shoreIntoLabel X w) (joiningGraph_join G (shoreIntoLabel X w))).edge e at hve
  rw [(joiningGraph G (shoreIntoLabel X w)).labelQuotient_incident_iff] at hve
  apply mem_compl.mpr
  rcases hve with h | h
  · exact h ▸ shoreIntoLabel_not_mem X w hw _
  · exact h ▸ shoreIntoLabel_not_mem X w hw _

/-- Construct the second partition of the tight-shore reduction on at
most four original labels and a nonempty tight shore. -/
theorem exists_tightShoreOutside_partition (hV : Fintype.card V ≤ 4)
    (X : Finset V) (hX : X.Nonempty) (w : V) (k : K)
    (hadmissible : G.AdmissibleOn classOf univ)
    (heven : ∀ v, Even (G.degreeOn univ v)) (hw : w ∉ X)
    (htight : 2 * (G.classCutOn classOf univ w k X).card = (G.cutOn univ X).card) :
    Nonempty ((tightShoreOutsideGraph G X w).CompatibleCircuitPartition
      (tightShoreOutsideClass G classOf X w k) univ) := by
  apply (tightShoreOutsideGraph G X w).exists_compatibleCircuitPartition_of_support_card_le_three
    (tightShoreOutsideClass G classOf X w k) univ
  · have hbound := card_le_card (tightShoreOutside_support_subset G X w hw)
    have hcard := card_compl X
    have hpos := card_pos.mpr hX
    omega
  · exact tightShoreOutside_admissible G classOf X w k hadmissible hw htight
  · exact tightShoreOutside_even_degrees G X w heven

end Overfull.FourOdd
