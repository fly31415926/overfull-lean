import Overfull.FourOdd.CutBounds
import Overfull.FourOdd.Pools

/-!
# Passing from the regular graph to its actual joining copies

The restriction retains the original vertices and all original joining
edge copies. Quotient degrees are exactly the original cuts of label
fibers; quotient cuts are exactly the original cuts of unions of fibers.
These identities transfer the regular odd-cut and even-cut bounds without
an assumption on the existence of a quotient or on its numerical data.
-/

noncomputable section

namespace Overfull.FourOdd

open Finset Classical
open scoped BigOperators

variable {V E I : Type*} [Fintype E] [DecidableEq I]

def joiningCopies (G : Multigraph V E) (label : V → I) : Finset E :=
  univ.filter (fun e => label (G.firstEnd e) ≠ label (G.secondEnd e))

@[simp] theorem mem_joiningCopies (G : Multigraph V E) (label : V → I) (e : E) :
    e ∈ joiningCopies G label ↔ label (G.firstEnd e) ≠ label (G.secondEnd e) := by
  simp [joiningCopies]

def joiningGraph (G : Multigraph V E) (label : V → I) :
    Multigraph V (joiningCopies G label) := G.restrictEdges (joiningCopies G label)

@[simp] theorem joiningGraph_firstEnd (G : Multigraph V E) (label : V → I)
    (e : joiningCopies G label) :
    (joiningGraph G label).firstEnd e = G.firstEnd e.val := rfl

@[simp] theorem joiningGraph_secondEnd (G : Multigraph V E) (label : V → I)
    (e : joiningCopies G label) :
    (joiningGraph G label).secondEnd e = G.secondEnd e.val := rfl

@[simp] theorem joiningGraph_edge (G : Multigraph V E) (label : V → I)
    (e : joiningCopies G label) :
    (joiningGraph G label).edge e = G.edge e.val := rfl

theorem joiningGraph_join (G : Multigraph V E) (label : V → I)
    (e : joiningCopies G label) :
    label ((joiningGraph G label).firstEnd e) ≠
      label ((joiningGraph G label).secondEnd e) :=
  (mem_joiningCopies G label e.val).mp e.property

def joiningQuotient (G : Multigraph V E) (label : V → I) :
    Multigraph I (joiningCopies G label) :=
  (joiningGraph G label).labelQuotient label (joiningGraph_join G label)

theorem joiningGraph_degree_eq (G : Multigraph V E) (label : V → I) (v : V) :
    (joiningGraph G label).degree v = G.degreeOn (joiningCopies G label) v :=
  restrictEdges_degree_eq_degreeOn G _ v

theorem joiningGraph_degree_le (G : Multigraph V E) (label : V → I) {D : ℕ}
    (hD : ∀ v, G.degreeOn (joiningCopies G label) v ≤ D) (v : V) :
    (joiningGraph G label).degree v ≤ D := by
  rw [joiningGraph_degree_eq]
  exact hD v

variable [Fintype V]

def labelShore (label : V → I) (A : Finset I) : Finset V :=
  univ.filter (fun v => label v ∈ A)

@[simp] theorem mem_labelShore (label : V → I) (A : Finset I) (v : V) :
    v ∈ labelShore label A ↔ label v ∈ A := by
  simp [labelShore]

theorem labelShore_card (label : V → I) (A : Finset I) :
    (labelShore label A).card =
      ∑ i ∈ A, (univ.filter (fun v => label v = i)).card := by
  exact (sum_card_fiberwise_eq_card_filter univ A label).symm

theorem labelShore_card_parity (label : V → I)
    (hodd : ∀ i, (univ.filter (fun v => label v = i)).card % 2 = 1)
    (A : Finset I) : (labelShore label A).card % 2 = A.card % 2 := by
  rw [labelShore_card, sum_nat_mod]
  simp only [hodd, sum_const, smul_eq_mul, mul_one]

theorem labelShore_pair_even (label : V → I)
    (hodd : ∀ i, (univ.filter (fun v => label v = i)).card % 2 = 1)
    {i j : I} (hij : i ≠ j) :
    (labelShore label {i, j}).card % 2 = 0 := by
  rw [labelShore_card_parity label hodd]
  simp [hij]

omit [Fintype V] [Fintype E] [DecidableEq I] in
theorem labelQuotient_mem_cutOn_iff (G : Multigraph V E) (label : V → I)
    (hjoin : ∀ e, label (G.firstEnd e) ≠ label (G.secondEnd e))
    (C : Finset E) (A : Finset I) (e : E) :
    e ∈ (G.labelQuotient label hjoin).cutOn C A ↔
      e ∈ C ∧ (label (G.firstEnd e) ∈ A) ≠ (label (G.secondEnd e) ∈ A) := by
  rw [Multigraph.mem_cutOn]
  have he := (G.labelQuotient label hjoin).edge_eq e
  change s((G.labelQuotient label hjoin).firstEnd e,
    (G.labelQuotient label hjoin).secondEnd e) =
      s(label (G.firstEnd e), label (G.secondEnd e)) at he
  rcases Sym2.eq_iff.mp he with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [ha, hb]
  · rw [ha, hb, ne_comm]

def joiningCut (G : Multigraph V E) (label : V → I) (A : Finset I) :
    Finset (joiningCopies G label) := (joiningQuotient G label).cutOn univ A

omit [Fintype V] in
@[simp] theorem mem_joiningCut (G : Multigraph V E) (label : V → I)
    (A : Finset I) (e : joiningCopies G label) :
    e ∈ joiningCut G label A ↔
      (label (G.firstEnd e.val) ∈ A) ≠ (label (G.secondEnd e.val) ∈ A) := by
  simp only [joiningCut, joiningQuotient, labelQuotient_mem_cutOn_iff,
    mem_univ, true_and, joiningGraph_firstEnd, joiningGraph_secondEnd]

theorem cut_labelShore_subset_joining (G : Multigraph V E) (label : V → I)
    (A : Finset I) : G.cutOn univ (labelShore label A) ⊆ joiningCopies G label := by
  intro e he
  have hc := (G.mem_cutOn univ (labelShore label A) e).mp he |>.2
  apply (mem_joiningCopies G label e).mpr
  intro h
  apply hc
  simp [h]

theorem joiningCut_image (G : Multigraph V E) (label : V → I) (A : Finset I) :
    (joiningCut G label A).image Subtype.val = G.cutOn univ (labelShore label A) := by
  ext e
  constructor
  · intro he
    obtain ⟨f, hf, rfl⟩ := mem_image.mp he
    apply (G.mem_cutOn univ (labelShore label A) f.val).mpr
    exact ⟨mem_univ _, by simpa only [mem_labelShore] using (mem_joiningCut G label A f).mp hf⟩
  · intro he
    let f : joiningCopies G label := ⟨e, cut_labelShore_subset_joining G label A he⟩
    refine mem_image.mpr ⟨f, ?_, rfl⟩
    apply (mem_joiningCut G label A f).mpr
    simpa only [mem_labelShore] using (G.mem_cutOn univ (labelShore label A) e).mp he |>.2

theorem joiningCut_card (G : Multigraph V E) (label : V → I) (A : Finset I) :
    (joiningCut G label A).card = (G.cutOn univ (labelShore label A)).card := by
  rw [← joiningCut_image G label A, card_image_of_injective _ Subtype.val_injective]

omit [Fintype V] in
theorem joiningGraph_degreeOn_image (G : Multigraph V E) (label : V → I)
    (C : Finset (joiningCopies G label)) (v : V) :
    (joiningGraph G label).degreeOn C v = G.degreeOn (C.image Subtype.val) v := by
  have himage : (C.filter (fun e => v ∈ (joiningGraph G label).edge e)).image Subtype.val =
      (C.image Subtype.val).filter (fun e => v ∈ G.edge e) := by
    ext e
    simp only [mem_image, mem_filter, joiningGraph_edge]
    constructor
    · rintro ⟨f, ⟨hf, hv⟩, rfl⟩
      exact ⟨⟨f, hf, rfl⟩, hv⟩
    · rintro ⟨⟨f, hf, rfl⟩, hv⟩
      exact ⟨f, ⟨hf, hv⟩, rfl⟩
  unfold Multigraph.degreeOn
  rw [← himage, card_image_of_injective _ Subtype.val_injective]

theorem joiningCut_degreeOn (G : Multigraph V E) (label : V → I)
    (A : Finset I) (v : V) :
    (joiningGraph G label).degreeOn (joiningCut G label A) v =
      G.degreeOn (G.cutOn univ (labelShore label A)) v := by
  rw [joiningGraph_degreeOn_image, joiningCut_image]

theorem joiningQuotient_incidence_image (G : Multigraph V E) (label : V → I) (i : I) :
    ((joiningQuotient G label).incidenceEdges i).image Subtype.val =
      G.cutOn univ (labelShore label {i}) := by
  have hset : (joiningQuotient G label).incidenceEdges i = joiningCut G label {i} := by
    ext e
    simp only [Multigraph.mem_incidenceEdges, joiningQuotient,
      Multigraph.labelQuotient_incident_iff, joiningGraph_firstEnd,
      joiningGraph_secondEnd, mem_joiningCut, mem_singleton]
    have hn := (mem_joiningCopies G label e.val).mp e.property
    by_cases ha : label (G.firstEnd e.val) = i <;>
      by_cases hb : label (G.secondEnd e.val) = i <;> simp_all
  rw [hset, joiningCut_image]

theorem joiningQuotient_degree_eq_cut (G : Multigraph V E) (label : V → I) (i : I) :
    (joiningQuotient G label).degree i =
      (G.cutOn univ (labelShore label {i})).card := by
  rw [Multigraph.degree, ← joiningQuotient_incidence_image G label i,
    card_image_of_injective _ Subtype.val_injective]

theorem joiningQuotient_degree_lower (G : Multigraph V E) (label : V → I)
    {h : ℕ} (hregular : ∀ v, G.degree v = h)
    (hno : ∀ X : Finset V, ¬ G.IsOverfull h X)
    (hodd : ∀ i, (univ.filter (fun v => label v = i)).card % 2 = 1) (i : I) :
    h ≤ (joiningQuotient G label).degree i := by
  rw [joiningQuotient_degree_eq_cut]
  apply regular_odd_cut_lower G hregular hno
  simpa [labelShore] using hodd i

theorem joiningQuotient_degree_parity (G : Multigraph V E) (label : V → I)
    {h : ℕ} (hregular : ∀ v, G.degree v = h)
    (hodd : ∀ i, (univ.filter (fun v => label v = i)).card % 2 = 1) (i : I) :
    (joiningQuotient G label).degree i % 2 = h % 2 := by
  rw [joiningQuotient_degree_eq_cut]
  apply regular_odd_cut_parity G hregular
  simpa [labelShore] using hodd i

theorem joiningCut_even_parity (G : Multigraph V E) (label : V → I)
    {h : ℕ} (hregular : ∀ v, G.degree v = h)
    (A : Finset I) (hA : (labelShore label A).card % 2 = 0) :
    (joiningCut G label A).card % 2 = 0 := by
  rw [joiningCut_card]
  exact regular_even_cut_parity G hregular _ hA

theorem joiningCut_even_degree_le_half (G : Multigraph V E) (label : V → I)
    {h : ℕ} (hregular : ∀ v, G.degree v = h)
    (hno : ∀ X : Finset V, ¬ G.IsOverfull h X)
    (A : Finset I) (hA : (labelShore label A).card % 2 = 0) (v : V) :
    (joiningGraph G label).degreeOn (joiningCut G label A) v ≤
      (joiningCut G label A).card / 2 := by
  rw [joiningCut_degreeOn, joiningCut_card]
  exact regular_even_cut_degree_le_half G hregular hno _ hA v

theorem joiningCut_pair_parity (G : Multigraph V E) (label : V → I)
    {h : ℕ} (hregular : ∀ v, G.degree v = h)
    (hodd : ∀ i, (univ.filter (fun v => label v = i)).card % 2 = 1)
    {i j : I} (hij : i ≠ j) : (joiningCut G label {i, j}).card % 2 = 0 :=
  joiningCut_even_parity G label hregular _ (labelShore_pair_even label hodd hij)

theorem joiningCut_pair_degree_le_half (G : Multigraph V E) (label : V → I)
    {h : ℕ} (hregular : ∀ v, G.degree v = h)
    (hno : ∀ X : Finset V, ¬ G.IsOverfull h X)
    (hodd : ∀ i, (univ.filter (fun v => label v = i)).card % 2 = 1)
    {i j : I} (hij : i ≠ j) (v : V) :
    (joiningGraph G label).degreeOn (joiningCut G label {i, j}) v ≤
      (joiningCut G label {i, j}).card / 2 :=
  joiningCut_even_degree_le_half G label hregular hno _
    (labelShore_pair_even label hodd hij) v

end Overfull.FourOdd
