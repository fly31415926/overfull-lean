import Overfull.Dense.TripartiteGraph
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Signed corrections on the links of a tripartite graph

For each vertex in the third part, the link is an actual bipartite graph
on its neighbors in the first two parts. The degree and local-balance
hypotheses give the signed flow in that link. Extending the flows by zero
produces weights on actual triangles with the prescribed incidence sums.
-/

namespace Overfull.TripartiteGraph

open Finset Classical

variable {A B W : Type*} [Fintype A] [Fintype B] [Fintype W]
variable (G : TripartiteGraph A B W)

/-- The actual bipartite link of a vertex in the third part. -/
noncomputable def linkGraph (w : W) : SimpleGraph ((G.linkA w) ⊕ (G.linkB w)) where
  Adj x y := match x, y with
    | .inl a, .inr b => G.ab a.val b.val
    | .inr b, .inl a => G.ab a.val b.val
    | _, _ => False
  symm := by intro x y h; cases x <;> cases y <;> exact h
  loopless := by intro x; cases x <;> exact not_false

omit [Fintype W] in
private theorem link_right_neighbors_card (w : W) (a : G.linkA w) :
    (rightNeighbors (G.linkGraph w) a).card =
      (G.neighborsB a.val ∩ G.linkB w).card := by
  have himage : (rightNeighbors (G.linkGraph w) a).image Subtype.val =
      G.neighborsB a.val ∩ G.linkB w := by
    ext b
    simp only [Finset.mem_image, rightNeighbors, Finset.mem_filter, Finset.mem_univ,
      true_and, linkGraph, Finset.mem_inter, neighborsB, linkB]
    constructor
    · rintro ⟨b', hab', rfl⟩
      exact ⟨hab', (Finset.mem_filter.mp b'.property).2⟩
    · rintro ⟨hab, hbw⟩
      exact ⟨⟨b, by simp [hbw]⟩, hab, rfl⟩
  rw [← Finset.card_image_of_injective _ Subtype.val_injective, himage]

omit [Fintype W] in
private theorem link_left_neighbors_card (w : W) (b : G.linkB w) :
    (leftNeighbors (G.linkGraph w) b).card =
      (G.neighborsA b.val ∩ G.linkA w).card := by
  have himage : (leftNeighbors (G.linkGraph w) b).image Subtype.val =
      G.neighborsA b.val ∩ G.linkA w := by
    ext a
    simp only [Finset.mem_image, leftNeighbors, Finset.mem_filter, Finset.mem_univ,
      true_and, linkGraph, Finset.mem_inter, neighborsA, linkA]
    constructor
    · rintro ⟨a', ha'b, rfl⟩
      exact ⟨ha'b, (Finset.mem_filter.mp a'.property).2⟩
    · rintro ⟨hab, haw⟩
      exact ⟨⟨a, by simp [haw]⟩, hab, rfl⟩
  rw [← Finset.card_image_of_injective _ Subtype.val_injective, himage]

private theorem link_degree_bounds (η ε : ℝ) (hε : ε ≤ η)
    (hG : G.DensityConditions η ε) (w : W) :
    (∀ a : G.linkA w, (Fintype.card (G.linkA w) : ℝ) / 2 +
        η * Fintype.card A / 2 ≤ (rightNeighbors (G.linkGraph w) a).card) ∧
    (∀ b : G.linkB w, (Fintype.card (G.linkA w) : ℝ) / 2 +
        η * Fintype.card A / 2 ≤ (leftNeighbors (G.linkGraph w) b).card) := by
  have hm : (0 : ℝ) ≤ Fintype.card A := Nat.cast_nonneg _
  have hεm := mul_le_mul_of_nonneg_right hε hm
  have hlink : (G.linkA w).card = (G.linkB w).card := hG.localBalance.2.2 w
  constructor
  · intro a
    rw [Fintype.card_coe, link_right_neighbors_card]
    have hcount := Finset.card_inter_add_card_union (G.neighborsB a.val) (G.linkB w)
    have hunion := Finset.card_le_univ (G.neighborsB a.val ∪ G.linkB w)
    rw [← hG.partSizes] at hunion
    have hcount' : (G.neighborsB a.val).card + (G.linkB w).card ≤
        (G.neighborsB a.val ∩ G.linkB w).card + Fintype.card A := by omega
    have hcountR : ((G.neighborsB a.val).card : ℝ) + (G.linkB w).card ≤
        (G.neighborsB a.val ∩ G.linkB w).card + Fintype.card A := by exact_mod_cast hcount'
    have hlinkR : ((G.linkA w).card : ℝ) = (G.linkB w).card := by exact_mod_cast hlink
    have hdeg := hG.degreeA a.val
    have hmissing := hG.missingWB w
    linarith
  · intro b
    rw [Fintype.card_coe, link_left_neighbors_card]
    have hcount := Finset.card_inter_add_card_union (G.neighborsA b.val) (G.linkA w)
    have hunion := Finset.card_le_univ (G.neighborsA b.val ∪ G.linkA w)
    have hcount' : (G.neighborsA b.val).card + (G.linkA w).card ≤
        (G.neighborsA b.val ∩ G.linkA w).card + Fintype.card A := by omega
    have hcountR : ((G.neighborsA b.val).card : ℝ) + (G.linkA w).card ≤
        (G.neighborsA b.val ∩ G.linkA w).card + Fintype.card A := by exact_mod_cast hcount'
    have hdeg := hG.degreeB b.val
    have hmissing := hG.missingWA w
    linarith

private theorem link_weight_total
    (r : EdgePosition (A := A) (B := B) (W := W) → ℝ)
    (hr : G.BalancedWeight r) (w : W) :
    (∑ a : G.linkA w, r (awPos a.val w)) = ∑ b : G.linkB w, r (bwPos b.val w) := by
  have hA : (∑ a : G.linkA w, r (awPos a.val w)) = ∑ a : A, r (awPos a w) := by
    rw [Finset.sum_coe_sort (G.linkA w) (fun a : A => r (awPos a w))]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro a _ ha
    exact hr.2.1 a w (by simpa [linkA] using ha)
  have hB : (∑ b : G.linkB w, r (bwPos b.val w)) = ∑ b : B, r (bwPos b w) := by
    rw [Finset.sum_coe_sort (G.linkB w) (fun b : B => r (bwPos b w))]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro b _ hb
    exact hr.2.2.1 b w (by simpa [linkB] using hb)
  rw [hA, hB]
  exact hr.2.2.2.2.2 w

private theorem sum_extend_subtype {U : Type*} [Fintype U]
    (S : Finset U) (f : S → ℝ) :
    (∑ u : U, if hu : u ∈ S then f ⟨u, hu⟩ else 0) = ∑ u : S, f u := by
  simpa only [Finset.univ_eq_attach] using (Finset.sum_attach_eq_sum_dite S f).symm

/-- The first correction in Lemma 5.7. It prescribes all incidences with the
third part by solving the actual link graphs, with the uniform bound obtained
from their degree gap. -/
theorem exists_link_correction (η ε : ℝ) (hη : 0 < η) (hε : ε ≤ η)
    (hm : 0 < Fintype.card A) (hG : G.DensityConditions η ε)
    (r : EdgePosition (A := A) (B := B) (W := W) → ℝ)
    (hr : G.BalancedWeight r) (d : ℝ) (hd : 0 ≤ d)
    (hbound : ∀ e, |r e| ≤ d) :
    ∃ p : G.Triangle → ℝ,
      (∀ a w, G.incidence p (awPos a w) = r (awPos a w)) ∧
      (∀ b w, G.incidence p (bwPos b w) = r (bwPos b w)) ∧
      ∀ t, |p t| ≤ 2 * d / (η * Fintype.card A) := by
  have hmR : (0 : ℝ) < Fintype.card A := by exact_mod_cast hm
  have hgap : 0 < η * Fintype.card A / 2 := by positivity
  have hflows : ∀ w : W, ∃ z : G.linkA w → G.linkB w → ℝ,
      (∀ a b, ¬G.ab a.val b.val → z a b = 0) ∧
      (∀ a, ∑ b, z a b = r (awPos a.val w)) ∧
      (∀ b, ∑ a, z a b = r (bwPos b.val w)) ∧
      ∀ a b, |z a b| ≤ 2 * d / (η * Fintype.card A) := by
    intro w
    obtain ⟨hleft, hright⟩ := link_degree_bounds G η ε hε hG w
    have hbalance : Fintype.card (G.linkA w) = Fintype.card (G.linkB w) := by
      simpa using hG.localBalance.2.2 w
    obtain ⟨z, hz0, hzrow, hzcol, hzbound⟩ := dense_signed_flow (G.linkGraph w)
      (η * Fintype.card A / 2) d hgap hbalance hleft hright
      (fun a => r (awPos a.val w)) (fun b => r (bwPos b.val w))
      (fun a => hbound (awPos a.val w)) (fun b => hbound (bwPos b.val w))
      (link_weight_total G r hr w)
    refine ⟨z, hz0, hzrow, hzcol, ?_⟩
    intro a b
    simpa only [div_div_eq_mul_div, mul_comm] using hzbound a b
  choose z hz0 hzrow hzcol hzbound using hflows
  let P : A → B → W → ℝ := fun a b w =>
    if ha : a ∈ G.linkA w then
      if hb : b ∈ G.linkB w then z w ⟨a, ha⟩ ⟨b, hb⟩ else 0
    else 0
  have hProw : ∀ a w, ∑ b, P a b w = r (awPos a w) := by
    intro a w
    by_cases ha : a ∈ G.linkA w
    · simp only [P, dif_pos ha]
      exact (sum_extend_subtype (G.linkB w) (z w ⟨a, ha⟩)).trans (hzrow w ⟨a, ha⟩)
    · have hrzero := hr.2.1 a w (by simpa [linkA] using ha)
      simp [P, ha, hrzero]
  have hPcol : ∀ b w, ∑ a, P a b w = r (bwPos b w) := by
    intro b w
    by_cases hb : b ∈ G.linkB w
    · simp only [P, dif_pos hb]
      exact (sum_extend_subtype (G.linkA w) (fun a => z w a ⟨b, hb⟩)).trans
        (hzcol w ⟨b, hb⟩)
    · have hrzero := hr.2.2.1 b w (by simpa [linkB] using hb)
      simp [P, hb, hrzero]
  have hPsupport : ∀ a b w, ¬G.IsTriangle a b w → P a b w = 0 := by
    intro a b w htri
    by_cases ha : a ∈ G.linkA w
    · by_cases hb : b ∈ G.linkB w
      · have hab : ¬G.ab a b := by
          intro hab
          exact htri ⟨hab, (Finset.mem_filter.mp ha).2, (Finset.mem_filter.mp hb).2⟩
        simpa only [P, dif_pos ha, dif_pos hb] using hz0 w ⟨a, ha⟩ ⟨b, hb⟩ hab
      · simp [P, ha, hb]
    · simp [P, ha]
  have hPbound : ∀ a b w, |P a b w| ≤ 2 * d / (η * Fintype.card A) := by
    intro a b w
    by_cases ha : a ∈ G.linkA w
    · by_cases hb : b ∈ G.linkB w
      · simpa only [P, dif_pos ha, dif_pos hb] using hzbound w ⟨a, ha⟩ ⟨b, hb⟩
      · simp only [P, dif_pos ha, dif_neg hb, abs_zero]
        positivity
    · simp only [P, dif_neg ha, abs_zero]
      positivity
  refine ⟨G.restrictTriangles P, ?_, ?_, ?_⟩
  · intro a w
    simpa only [incidence, awPos, G.extend_restrictTriangles P hPsupport] using hProw a w
  · intro b w
    simpa only [incidence, bwPos, G.extend_restrictTriangles P hPsupport] using hPcol b w
  · intro t
    exact hPbound t.val.1 t.val.2.1 t.val.2.2

end Overfull.TripartiteGraph
