import Overfull.FourOdd.Basic
import Overfull.FourOdd.MinorityPairing

/-!
# The canonical matching case of the four-odd-parts decomposition

The distinguished label pairs are `01` and `23`.  The other four pools form
a bipartite boundary, with two refinement labels on each side.  The minority
pairing counts exactly the singleton copies saved in each distinguished
pool.  Every surplus piece is an actual matching parallel pair.
-/

noncomputable section

namespace Overfull.FourOdd

open Finset Classical Compression CircuitPatterns
open scoped BigOperators

/-- The two sides of the canonical `01 | 23` split. -/
def matchingSide (i : Fin 4) : Bool := decide (2 ≤ i.val)

/-- The two labels within either side of the canonical split. -/
def matchingRefinement (i : Fin 4) : Bool := decide (i.val % 2 = 1)

/-- Recover one of the four labels from its side and refinement. -/
def matchingLabel (s b : Bool) : Fin 4 :=
  if s then (if b then 3 else 2) else (if b then 1 else 0)

theorem matchingLabel_coordinates :
    ∀ i, matchingLabel (matchingSide i) (matchingRefinement i) = i := by decide

@[simp] theorem matchingSide_matchingLabel : ∀ s b, matchingSide (matchingLabel s b) = s := by
  decide

@[simp] theorem matchingRefinement_matchingLabel :
    ∀ s b, matchingRefinement (matchingLabel s b) = b := by decide

def matchingLeftPair : LabelPair := ⟨{0, 1}, by decide⟩

def matchingRightPair : LabelPair := ⟨{2, 3}, by decide⟩

/-- A label pair crossing the canonical split, indexed by its row and column. -/
def matchingCrossPair (row column : Bool) : LabelPair :=
  ⟨{if row then 1 else 0, if column then 3 else 2},
    by cases row <;> cases column <;> decide⟩

theorem matchingCrossPair_injective :
    ∀ a b c d, matchingCrossPair a b = matchingCrossPair c d ↔ a = c ∧ b = d := by
  decide

theorem matching_cross_disjoint :
    ∀ a b c d, a ≠ c → b ≠ d →
      Disjoint (matchingCrossPair a b).val (matchingCrossPair c d).val := by
  decide

theorem matching_cross_opposite_shape :
    ∀ a b c d, a ≠ c → b ≠ d →
      LabelForestShape {matchingCrossPair a b, matchingCrossPair c d} := by
  decide

theorem matching_sameRow_shape :
    ∀ a b d, b ≠ d →
      LabelForestShape {matchingCrossPair a b, matchingCrossPair a d, matchingLeftPair} := by
  decide

theorem matching_sameColumn_shape :
    ∀ a b c, a ≠ c →
      LabelForestShape {matchingCrossPair a b, matchingCrossPair c b, matchingRightPair} := by
  decide

theorem matching_left_right_shape :
    LabelForestShape {matchingLeftPair, matchingRightPair} := by
  decide

theorem matching_cross_ne_left : ∀ a b, matchingCrossPair a b ≠ matchingLeftPair := by
  decide

theorem matching_cross_ne_right : ∀ a b, matchingCrossPair a b ≠ matchingRightPair := by
  decide

theorem matching_left_ne_right : matchingLeftPair ≠ matchingRightPair := by decide

variable {V E : Type*}

private theorem isPrimary_pair {label : E → LabelPair} {e f : E}
    (hne : label e ≠ label f) (hshape : LabelForestShape {label e, label f}) :
    IsPrimary label {e, f} := by
  refine ⟨?_, by simpa using hshape⟩
  intro x hx y hy hxy
  simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · rfl
  · exact (hne hxy).elim
  · exact (hne hxy.symm).elim
  · rfl

private theorem isPrimary_triple {label : E → LabelPair} {e f g : E}
    (hef : label e ≠ label f) (heg : label e ≠ label g) (hfg : label f ≠ label g)
    (hshape : LabelForestShape {label e, label f, label g}) :
    IsPrimary label {e, f, g} := by
  refine ⟨?_, by simpa using hshape⟩
  intro x hx y hy hxy
  simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
  · rfl
  · exact (hef hxy).elim
  · exact (heg hxy).elim
  · exact (hef hxy.symm).elim
  · rfl
  · exact (hfg hxy).elim
  · exact (heg hxy.symm).elim
  · exact (hfg hxy.symm).elim
  · rfl

private theorem primary_cross_opposite {label : E → LabelPair} {e f : E}
    {a b c d : Bool} (he : label e = matchingCrossPair a b)
    (hf : label f = matchingCrossPair c d) (hac : a ≠ c) (hbd : b ≠ d) :
    IsPrimary label {e, f} := by
  apply isPrimary_pair
  · rw [he, hf]
    exact fun h => hac ((matchingCrossPair_injective a b c d).mp h).1
  · rw [he, hf]
    exact matching_cross_opposite_shape a b c d hac hbd

private theorem primary_sameRow {label : E → LabelPair} {e f g : E}
    {a b d : Bool} (he : label e = matchingCrossPair a b)
    (hf : label f = matchingCrossPair a d) (hg : label g = matchingLeftPair)
    (hbd : b ≠ d) : IsPrimary label {e, f, g} := by
  apply isPrimary_triple
  · rw [he, hf]
    exact fun h => hbd ((matchingCrossPair_injective a b a d).mp h).2
  · rw [he, hg]
    exact matching_cross_ne_left a b
  · rw [hf, hg]
    exact matching_cross_ne_left a d
  · rw [he, hf, hg]
    exact matching_sameRow_shape a b d hbd

private theorem primary_sameColumn {label : E → LabelPair} {e f g : E}
    {a b c : Bool} (he : label e = matchingCrossPair a b)
    (hf : label f = matchingCrossPair c b) (hg : label g = matchingRightPair)
    (hac : a ≠ c) : IsPrimary label {e, f, g} := by
  apply isPrimary_triple
  · rw [he, hf]
    exact fun h => hac ((matchingCrossPair_injective a b c b).mp h).1
  · rw [he, hg]
    exact matching_cross_ne_right a b
  · rw [hf, hg]
    exact matching_cross_ne_right c b
  · rw [he, hf, hg]
    exact matching_sameColumn_shape a b c hac

theorem primary_left_right {label : E → LabelPair} {e f : E}
    (he : label e = matchingLeftPair) (hf : label f = matchingRightPair) :
    IsPrimary label {e, f} := by
  apply isPrimary_pair
  · rw [he, hf]
    exact matching_left_ne_right
  · rw [he, hf]
    exact matching_left_right_shape

namespace MinorityPairing

variable {W F : Type*} [Fintype F] {H : Multigraph W F}
    {side refinement : W → Bool} {k : ℕ} (P : MinorityPairing H side refinement k)
    (copy : F → E) (label : E → LabelPair)
    (hlabel : ∀ e, label (copy e) = matchingCrossPair
      (sideLabel H side refinement false e) (sideLabel H side refinement true e))

include hlabel

theorem opposite_primary (i : Fin k) (hrow : P.Mixed false i) (hcolumn : P.Mixed true i) :
    IsPrimary label ((P.pair i).image copy) := by
  obtain ⟨e, f, hef, hpair⟩ := Finset.card_eq_two.mp (P.card_pair i)
  have he : e ∈ P.pair i := by rw [hpair]; simp
  have hf : f ∈ P.pair i := by rw [hpair]; simp
  have hrow' := (P.mixed_iff_labels_ne false i he hf hef).mp hrow
  have hcolumn' := (P.mixed_iff_labels_ne true i he hf hef).mp hcolumn
  rw [hpair]
  simp only [Finset.image_insert, Finset.image_singleton]
  exact primary_cross_opposite (hlabel e) (hlabel f) hrow' hcolumn'

theorem sameRow_primary (i : Fin k) (hrow : ¬ P.Mixed false i)
    (hcolumn : P.Mixed true i) {g : E} (hg : label g = matchingLeftPair) :
    IsPrimary label ((P.pair i).image copy ∪ {g}) := by
  obtain ⟨e, f, hef, hpair⟩ := Finset.card_eq_two.mp (P.card_pair i)
  have he : e ∈ P.pair i := by rw [hpair]; simp
  have hf : f ∈ P.pair i := by rw [hpair]; simp
  have hrow' : sideLabel H side refinement false e = sideLabel H side refinement false f := by
    by_contra h
    exact hrow ((P.mixed_iff_labels_ne false i he hf hef).mpr h)
  have hcolumn' := (P.mixed_iff_labels_ne true i he hf hef).mp hcolumn
  rw [hpair]
  simp only [Finset.image_insert, Finset.image_singleton, Finset.insert_union,
    Finset.singleton_union]
  exact primary_sameRow (hlabel e) (by rw [hlabel f, ← hrow']) hg hcolumn'

theorem sameColumn_primary (i : Fin k) (hrow : P.Mixed false i)
    (hcolumn : ¬ P.Mixed true i) {g : E} (hg : label g = matchingRightPair) :
    IsPrimary label ((P.pair i).image copy ∪ {g}) := by
  obtain ⟨e, f, hef, hpair⟩ := Finset.card_eq_two.mp (P.card_pair i)
  have he : e ∈ P.pair i := by rw [hpair]; simp
  have hf : f ∈ P.pair i := by rw [hpair]; simp
  have hcolumn' : sideLabel H side refinement true e = sideLabel H side refinement true f := by
    by_contra h
    exact hcolumn ((P.mixed_iff_labels_ne true i he hf hef).mpr h)
  have hrow' := (P.mixed_iff_labels_ne false i he hf hef).mp hrow
  rw [hpair]
  simp only [Finset.image_insert, Finset.image_singleton, Finset.insert_union,
    Finset.singleton_union]
  exact primary_sameColumn (hlabel e) (by rw [hlabel f, ← hcolumn']) hg hrow'

theorem parallel_pair (hinj : Function.Injective copy) (i : Fin k)
    (hrow : ¬ P.Mixed false i) (hcolumn : ¬ P.Mixed true i) :
    IsParallelPair label ((P.pair i).image copy) := by
  refine ⟨by rw [Finset.card_image_of_injective _ hinj, P.card_pair], ?_⟩
  intro x hx y hy
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hy
  have hrow' : sideLabel H side refinement false e = sideLabel H side refinement false f := by
    by_contra h
    exact hrow ⟨e, he, f, hf, h⟩
  have hcolumn' : sideLabel H side refinement true e = sideLabel H side refinement true f := by
    by_contra h
    exact hcolumn ⟨e, he, f, hf, h⟩
  rw [hlabel e, hlabel f, hrow', hcolumn']

end MinorityPairing

/-- Canonical side/refinement labels are the actual four quotient labels. -/
theorem matching_sideLabel_iff_incident (G : Multigraph V E) (vertexLabel : V → Fin 4)
    (hjoin : ∀ e, vertexLabel (G.firstEnd e) ≠ vertexLabel (G.secondEnd e))
    (hcross : ∀ e, matchingSide (vertexLabel (G.firstEnd e)) ≠
      matchingSide (vertexLabel (G.secondEnd e))) (s b : Bool) (e : E) :
    sideLabel G (matchingSide ∘ vertexLabel) (matchingRefinement ∘ vertexLabel) s e = b ↔
      matchingLabel s b ∈ (G.labelQuotient vertexLabel hjoin).edge e := by
  let side := matchingSide ∘ vertexLabel
  let refinement := matchingRefinement ∘ vertexLabel
  constructor
  · intro hb
    let v := sideEndpoint G side s e
    have hv : v ∈ G.edge e := sideEndpoint_mem G side s e
    have hs : matchingSide (vertexLabel v) = s := sideEndpoint_side G side hcross s e
    have hb' : matchingRefinement (vertexLabel v) = b := hb
    have hcode : vertexLabel v = matchingLabel s b := by
      rw [← matchingLabel_coordinates (vertexLabel v), hs, hb']
    rw [← hcode]
    exact G.label_incident_of_incident vertexLabel hjoin hv
  · intro hlabel
    have hex : ∃ v, v ∈ G.edge e ∧ vertexLabel v = matchingLabel s b := by
      rcases (G.labelQuotient_incident_iff vertexLabel hjoin e _).mp hlabel with h | h
      · exact ⟨G.firstEnd e, (G.incident_iff e _).mpr (Or.inl rfl), h⟩
      · exact ⟨G.secondEnd e, (G.incident_iff e _).mpr (Or.inr rfl), h⟩
    obtain ⟨v, hv, hcode⟩ := hex
    have hs : side v = s := by simp [side, hcode]
    have hend : sideEndpoint G side s e = v := by
      rw [← hs]
      exact sideEndpoint_eq_of_incident G side hcross hv
    change matchingRefinement (vertexLabel (sideEndpoint G side s e)) = b
    rw [hend, hcode, matchingRefinement_matchingLabel]

/-- The actual quotient pair of a crossing copy is its row-column code. -/
theorem matching_cross_projection (G : Multigraph V E) (vertexLabel : V → Fin 4)
    (hjoin : ∀ e, vertexLabel (G.firstEnd e) ≠ vertexLabel (G.secondEnd e))
    (hcross : ∀ e, matchingSide (vertexLabel (G.firstEnd e)) ≠
      matchingSide (vertexLabel (G.secondEnd e))) (e : E) :
    (G.labelQuotient vertexLabel hjoin).edgeLabelPair e =
      matchingCrossPair
        (sideLabel G (matchingSide ∘ vertexLabel) (matchingRefinement ∘ vertexLabel) false e)
        (sideLabel G (matchingSide ∘ vertexLabel) (matchingRefinement ∘ vertexLabel) true e) := by
  let Q := G.labelQuotient vertexLabel hjoin
  let a := sideLabel G (matchingSide ∘ vertexLabel) (matchingRefinement ∘ vertexLabel) false e
  let b := sideLabel G (matchingSide ∘ vertexLabel) (matchingRefinement ∘ vertexLabel) true e
  have ha : matchingLabel false a ∈ (Q.edgeLabelPair e).val := by
    rw [Q.mem_edgeLabelPair]
    exact (matching_sideLabel_iff_incident G vertexLabel hjoin hcross false a e).mp rfl
  have hb : matchingLabel true b ∈ (Q.edgeLabelPair e).val := by
    rw [Q.mem_edgeLabelPair]
    exact (matching_sideLabel_iff_incident G vertexLabel hjoin hcross true b e).mp rfl
  have hne : matchingLabel false a ≠ matchingLabel true b := by
    intro h
    have hh := congrArg matchingSide h
    simp at hh
  have hpair : {matchingLabel false a, matchingLabel true b} = (Q.edgeLabelPair e).val := by
    apply eq_of_subset_of_card_le
    · exact insert_subset_iff.mpr ⟨ha, singleton_subset_iff.mpr hb⟩
    · rw [(Q.edgeLabelPair e).property]
      simp [hne]
  apply Subtype.ext
  exact hpair.symm

/-- Edge-copy totals in the two refinements equal actual quotient incidences
inside a restricted crossing pool. -/
theorem matching_sideEdges_card [Fintype E] (G : Multigraph V E)
    (vertexLabel : V → Fin 4)
    (hjoin : ∀ e, vertexLabel (G.firstEnd e) ≠ vertexLabel (G.secondEnd e))
    (X : Finset E)
    (hcross : ∀ e : X, matchingSide (vertexLabel (G.firstEnd e.val)) ≠
      matchingSide (vertexLabel (G.secondEnd e.val))) (s b : Bool) :
    (sideEdges (G.restrictEdges X) (matchingSide ∘ vertexLabel)
      (matchingRefinement ∘ vertexLabel) s b).card =
      (G.labelQuotient vertexLabel hjoin).degreeOn X (matchingLabel s b) := by
  let H := G.restrictEdges X
  let Q := G.labelQuotient vertexLabel hjoin
  let S := sideEdges H (matchingSide ∘ vertexLabel) (matchingRefinement ∘ vertexLabel) s b
  have hchar (e : X) :
      sideLabel H (matchingSide ∘ vertexLabel) (matchingRefinement ∘ vertexLabel) s e = b ↔
        matchingLabel s b ∈ Q.edge e.val :=
    matching_sideLabel_iff_incident H vertexLabel (fun e => hjoin e.val) hcross s b e
  have himage : S.image Subtype.val = X.filter (fun e => matchingLabel s b ∈ Q.edge e) := by
    ext e
    constructor
    · intro he
      obtain ⟨f, hf, rfl⟩ := mem_image.mp he
      exact mem_filter.mpr ⟨f.property, (hchar f).mp ((mem_sideEdges _ _ _ _ _ _).mp hf)⟩
    · intro he
      obtain ⟨heX, heQ⟩ := mem_filter.mp he
      exact mem_image.mpr ⟨⟨e, heX⟩,
        (mem_sideEdges _ _ _ _ _ _).mpr ((hchar ⟨e, heX⟩).mpr heQ), rfl⟩
  unfold Multigraph.degreeOn
  convert (card_image_of_injective S Subtype.val_injective).symm.trans
    (congrArg Finset.card himage) using 1
  congr 1
  ext e
  simp [Q, Multigraph.labelQuotient, Sym2.mem_iff]

/-- The generous constants absorb the cap's parity adjustment and all
endpoint-avoidance losses. -/
theorem matching_parameter_bounds {h D r0 : ℕ} (hD : 0 < D)
    (hsmall : 1000 * D ≤ h) (hsupply : 999 * h ≤ 1000 * r0) :
    let B := 2 * D + (h - r0)
    2 * D ≤ B ∧ h ≤ r0 + B ∧ 8 * (B + 1) + 4 * D ≤ h := by
  dsimp
  omega

end Overfull.FourOdd
