import Overfull.FourOdd.Basic
import Overfull.CircuitPatterns.IncidenceLoad
import Overfull.CircuitPatterns.PairedForests

/-!
# Actual primary pieces for the canonical star

Three equal pools on the three arms of the label star can be paired twice
by Hall's theorem. The endpoint-conflict bounds come from the original
vertex degrees. Opposite label pools need no endpoint adjustment.
-/

noncomputable section
namespace Overfull.FourOdd
open Finset Classical Compression CircuitPatterns

/-- The three label pairs incident with label zero. -/
def starPair : Fin 3 → LabelPair :=
  ![⟨{0, 1}, by decide⟩, ⟨{0, 2}, by decide⟩, ⟨{0, 3}, by decide⟩]

/-- The pair opposite each arm of the label-zero star. -/
def oppositePair : Fin 3 → LabelPair :=
  ![⟨{2, 3}, by decide⟩, ⟨{1, 3}, by decide⟩, ⟨{1, 2}, by decide⟩]

theorem starPair_injective : Function.Injective starPair := by decide

theorem oppositePair_injective : Function.Injective oppositePair := by decide

theorem starPair_ne_oppositePair (i j : Fin 3) : starPair i ≠ oppositePair j := by
  revert i j
  decide

theorem oppositePair_disjoint (i : Fin 3) :
    Disjoint (starPair i).val (oppositePair i).val := by
  revert i
  decide

theorem oppositePair_primary (i : Fin 3) :
    LabelForestShape {starPair i, oppositePair i} := by
  revert i
  decide

theorem starPair_shape : LabelForestShape {starPair 0, starPair 1, starPair 2} := by
  right
  exact ⟨0, by decide⟩

theorem starPair_oppositePair_cover (p : LabelPair) :
    (∃ i, p = starPair i) ∨ ∃ i, p = oppositePair i := by
  revert p
  decide

variable {V E : Type*}

private theorem singleton_matching (G : Multigraph V E) (e : E) :
    G.IsMatching {e} := by
  intro f hf g hg _ _ _
  exact (mem_singleton.mp hf).trans (mem_singleton.mp hg).symm

private theorem singleton_family_disjoint (A : Finset E) :
    Pairwise (fun e f : A => Disjoint ({e.val} : Finset E) {f.val}) := by
  intro e f hef
  simp only [disjoint_singleton]
  exact fun h => hef (Subtype.ext h)

private theorem singleton_family_cover (A : Finset E) :
    univ.biUnion (fun e : A => ({e.val} : Finset E)) = A := by
  ext e
  simp only [mem_biUnion, mem_univ, true_and, mem_singleton]
  constructor
  · rintro ⟨f, rfl⟩
    exact f.property
  · intro he
    exact ⟨⟨e, he⟩, rfl⟩

private theorem distinct_label_pools {label : E → LabelPair}
    {A B : Finset E} {p q : LabelPair}
    (hA : ∀ e ∈ A, label e = p) (hB : ∀ e ∈ B, label e = q) (hpq : p ≠ q) :
    Disjoint A B := by
  apply disjoint_left.mpr
  intro e heA heB
  exact hpq ((hA e heA).symm.trans (hB e heB))

private theorem primary_three {label : E → LabelPair} {e f g : E}
    (he : label e = starPair 0) (hf : label f = starPair 1)
    (hg : label g = starPair 2) : IsPrimary label ({e} ∪ {f} ∪ {g}) := by
  have h01 : starPair 0 ≠ starPair 1 := by decide
  have h02 : starPair 0 ≠ starPair 2 := by decide
  have h12 : starPair 1 ≠ starPair 2 := by decide
  refine ⟨?_, ?_⟩
  · intro x hx y hy hxy
    simp only [Finset.mem_coe, mem_union, mem_singleton] at hx hy
    rcases hx with (rfl | rfl) | rfl <;>
      rcases hy with (rfl | rfl) | rfl <;>
      simp_all
  · have himage : ({e} ∪ {f} ∪ {g} : Finset E).image label =
        {starPair 0, starPair 1, starPair 2} := by
      ext p
      simp [he, hf, hg, or_comm, or_left_comm]
    rw [himage]
    exact starPair_shape

/-- Two Hall pairings turn three equal arm pools into exact actual star
matchings. No compatibility or matching conclusion is an input. -/
theorem exists_equal_star_pool_decomposition [Fintype E]
    (G : Multigraph V E) (label : E → LabelPair) (A B C : Finset E) (D : ℕ)
    (hA : ∀ e ∈ A, label e = starPair 0)
    (hB : ∀ e ∈ B, label e = starPair 1)
    (hC : ∀ e ∈ C, label e = starPair 2)
    (hAB : A.card = B.card) (hAC : A.card = C.card)
    (hdegree : ∀ v, G.degree v ≤ D) (hlarge : 12 * D < A.card) :
    Nonempty (Decomposition G label (A ∪ B ∪ C) A.card) := by
  let X : A → Finset E := fun e => {e.val}
  let Y : B → Finset E := fun e => {e.val}
  let Z : C → Finset E := fun e => {e.val}
  have hd (v : V) : G.degreeOn univ v ≤ D := by
    simpa only [Multigraph.degreeOn, Multigraph.degree, Multigraph.incidenceEdges]
      using hdegree v
  have hXY : ∀ i j, Disjoint (X i) (Y j) := by
    intro i j
    exact (distinct_label_pools hA hB (by decide)).mono
      (singleton_subset_iff.mpr i.property) (singleton_subset_iff.mpr j.property)
  have hXZ : ∀ i j, Disjoint (X i) (Z j) := by
    intro i j
    exact (distinct_label_pools hA hC (by decide)).mono
      (singleton_subset_iff.mpr i.property) (singleton_subset_iff.mpr j.property)
  have hYZ : ∀ i j, Disjoint (Y i) (Z j) := by
    intro i j
    exact (distinct_label_pools hB hC (by decide)).mono
      (singleton_subset_iff.mpr i.property) (singleton_subset_iff.mpr j.property)
  obtain ⟨f, _, hf⟩ := exists_three_edge_pairing_of_degree_bound G univ X Y D
    (by simpa using hAB) (fun i => singleton_matching G i.val)
    (fun i => singleton_matching G i.val) (by intro i; simp [X])
    (by intro i; simp [Y]) (singleton_family_disjoint A) (singleton_family_disjoint B)
    (fun _ => subset_univ _) (fun _ => subset_univ _) hd (by simpa using hlarge)
  let XY : A → Finset E := fun i => X i ∪ Y (f i)
  have hXYdis : Pairwise (fun i j => Disjoint (XY i) (XY j)) :=
    paired_unions_pairwise_disjoint X Y f.toEmbedding
      (singleton_family_disjoint A) (singleton_family_disjoint B) hXY
  have hXYsize (i : A) : (XY i).card ≤ 3 := by
    exact (card_union_le (X i) (Y (f i))).trans (by simp [X, Y])
  obtain ⟨g, _, hg⟩ := exists_three_edge_pairing_of_degree_bound G univ XY Z D
    (by simpa using hAC) hf (fun i => singleton_matching G i.val)
    hXYsize (by intro i; simp [Z]) hXYdis (singleton_family_disjoint C)
    (fun _ => subset_univ _) (fun _ => subset_univ _) hd (by simpa using hlarge)
  have hXYZ : ∀ i j, Disjoint (XY i) (Z j) := by
    intro i j
    exact disjoint_union_left.mpr ⟨hXZ i j, hYZ (f i) j⟩
  have hdis := paired_unions_pairwise_disjoint XY Z g.toEmbedding
    hXYdis (singleton_family_disjoint C) hXYZ
  have hshape (i : A) : IsPrimary label (XY i ∪ Z (g i)) :=
    primary_three (hA _ i.property) (hB _ (f i).property) (hC _ (g i).property)
  let P := Decomposition.ofPrimaryFamily G label (fun i => XY i ∪ Z (g i)) hg hshape hdis
  have hcover : univ.biUnion (fun i => XY i ∪ Z (g i)) = A ∪ B ∪ C := by
    rw [paired_unions_cover XY Z g]
    change univ.biUnion (fun i => X i ∪ Y (f i)) ∪ univ.biUnion Z = _
    rw [paired_unions_cover X Y f]
    change univ.biUnion (fun e : A => {e.val}) ∪
      univ.biUnion (fun e : B => {e.val}) ∪
      univ.biUnion (fun e : C => {e.val}) = _
    rw [singleton_family_cover, singleton_family_cover, singleton_family_cover]
  exact ⟨P.cast hcover (by simp)⟩

/-- Pair equal opposite label pools without changing any edge-copy identity.
Their endpoints lie in disjoint original vertex parts. -/
theorem exists_opposite_pool_decomposition
    (G : Multigraph V E) (vlabel : V → Fin 4)
    (hjoin : ∀ e, vlabel (G.firstEnd e) ≠ vlabel (G.secondEnd e))
    (i : Fin 3) (A T : Finset E)
    (hA : ∀ e ∈ A, (G.labelQuotient vlabel hjoin).edgeLabelPair e = oppositePair i)
    (hT : ∀ e ∈ T, (G.labelQuotient vlabel hjoin).edgeLabelPair e = starPair i)
    (hcard : A.card = T.card) :
    Nonempty (Decomposition G (G.labelQuotient vlabel hjoin).edgeLabelPair
      (A ∪ T) A.card) := by
  let Q := G.labelQuotient vlabel hjoin
  let f : A ≃ T := Fintype.equivOfCardEq (by simpa using hcard)
  let X : A → Finset E := fun e => {e.val}
  let Y : T → Finset E := fun e => {e.val}
  have hcross : ∀ a t, Disjoint (X a) (Y t) := by
    intro a t
    exact (distinct_label_pools hA hT (starPair_ne_oppositePair i i).symm).mono
      (singleton_subset_iff.mpr a.property) (singleton_subset_iff.mpr t.property)
  have hmatching (a : A) : G.IsMatching (X a ∪ Y (f a)) := by
    apply isMatching_union_of_disjoint_support G _ _
      (singleton_matching G _) (singleton_matching G _)
    apply disjoint_left.mpr
    intro v hvX hvY
    obtain ⟨e, he, hev⟩ := (G.mem_edgeSupport (X a) v).mp hvX
    obtain ⟨g, hg, hgv⟩ := (G.mem_edgeSupport (Y (f a)) v).mp hvY
    have hea : e = a.val := mem_singleton.mp he
    have hgt : g = (f a).val := mem_singleton.mp hg
    have h₁ := Q.mem_edgeLabelPair e (vlabel v) |>.mpr
      (G.label_incident_of_incident vlabel hjoin hev)
    have h₂ := Q.mem_edgeLabelPair g (vlabel v) |>.mpr
      (G.label_incident_of_incident vlabel hjoin hgv)
    rw [hea, hA _ a.property] at h₁
    rw [hgt, hT _ (f a).property] at h₂
    exact disjoint_left.mp (oppositePair_disjoint i) h₂ h₁
  have hshape (a : A) : IsPrimary Q.edgeLabelPair (X a ∪ Y (f a)) := by
    have hneq := starPair_ne_oppositePair i i
    refine ⟨?_, ?_⟩
    · intro e he g hg heg
      change e ∈ ({a.val} ∪ {(f a).val} : Finset E) at he
      change g ∈ ({a.val} ∪ {(f a).val} : Finset E) at hg
      simp only [mem_union, mem_singleton] at he hg
      rcases he with rfl | rfl <;> rcases hg with rfl | rfl
      · rfl
      · exact (hneq ((hT _ (f a).property).symm.trans
          (heg.symm.trans (hA _ a.property)))).elim
      · exact (hneq ((hT _ (f a).property).symm.trans
          (heg.trans (hA _ a.property)))).elim
      · rfl
    · have himage : (X a ∪ Y (f a)).image Q.edgeLabelPair =
          {starPair i, oppositePair i} := by
        ext p
        simp [X, Y, Q, hA _ a.property, hT _ (f a).property, or_comm]
      rw [himage]
      exact oppositePair_primary i
  have hdis := paired_unions_pairwise_disjoint X Y f.toEmbedding
    (singleton_family_disjoint A) (singleton_family_disjoint T) hcross
  let P := Decomposition.ofPrimaryFamily G Q.edgeLabelPair
    (fun a => X a ∪ Y (f a)) hmatching hshape hdis
  have hcover : univ.biUnion (fun a => X a ∪ Y (f a)) = A ∪ T := by
    rw [paired_unions_cover X Y f]
    change univ.biUnion (fun e : A => {e.val}) ∪
      univ.biUnion (fun e : T => {e.val}) = _
    rw [singleton_family_cover, singleton_family_cover]
  exact ⟨P.cast hcover (by simp)⟩

end Overfull.FourOdd
