import Overfull.OrdinaryPackingDeficiency
import Overfull.BipartitePackingAccounting

/-!
# The actual working matching for an ordinary robust core

The working graph deletes the original reserve, all previously used edges,
and the current forbidden vertices. Its degrees are derived from those
operations. The returned matching is an actual subgraph of the original
host and covers every surviving saturated vertex.
-/

namespace Overfull.OrdinaryPackingWorking

open Finset Classical SimpleGraph
open scoped BigOperators
open BipartitePackingAccounting

variable {V I : Type*}

abbrev Remaining (S : Finset V) := ↥((↑S : Set V)ᶜ)

/-- Lift an actual matching from the induced remaining graph. -/
def liftMatching (G : SimpleGraph V) (S : Finset V)
    (M : (G.induce (↑S : Set V)ᶜ).Subgraph) : G.Subgraph :=
  M.map (SimpleGraph.Hom.comap Subtype.val G)

theorem liftMatching_isMatching (G : SimpleGraph V) (S : Finset V)
    (M : (G.induce (↑S : Set V)ᶜ).Subgraph) (hM : M.IsMatching) :
    (liftMatching G S M).IsMatching := hM.map _ Subtype.val_injective

@[simp] theorem liftMatching_verts (G : SimpleGraph V) (S : Finset V)
    (M : (G.induce (↑S : Set V)ᶜ).Subgraph) :
    (liftMatching G S M).verts = Subtype.val '' M.verts := rfl

theorem liftMatching_verts_subset (G : SimpleGraph V) (S : Finset V)
    (M : (G.induce (↑S : Set V)ᶜ).Subgraph) :
    (liftMatching G S M).verts ⊆ (↑S : Set V)ᶜ := by
  rintro v ⟨w, _, rfl⟩
  exact w.property

@[simp] theorem liftMatching_mem_verts (G : SimpleGraph V) (S : Finset V)
    (M : (G.induce (↑S : Set V)ᶜ).Subgraph) (v : Remaining S) :
    v.val ∈ (liftMatching G S M).verts ↔ v ∈ M.verts := by
  constructor
  · rintro ⟨w, hw, heq⟩
    exact Subtype.val_injective heq ▸ hw
  · intro hv
    exact ⟨v, hv, rfl⟩

variable [Fintype V]

/-- The vertices neither forbidden nor covered by a current matching. -/
noncomputable def uncoveredOutside (G : SimpleGraph V) (M : G.Subgraph)
    (S : Finset V) : Finset V := univ.filter (fun v => v ∉ S ∧ v ∉ M.verts)

theorem remaining_order (S : Finset V) :
    Fintype.card (Remaining S) = Fintype.card V - S.card := by
  classical
  have h := Set.ncard_add_ncard_compl (↑S : Set V)
  have hcard : Fintype.card (Remaining S) = ((↑S : Set V)ᶜ).ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  simp only [Set.ncard_coe_finset, Nat.card_eq_fintype_card] at h
  omega

theorem sum_remaining_le_sum (S : Finset V) (u : V → ℝ) (hu : ∀ v, 0 ≤ u v) :
    (∑ v : Remaining S, u v.val) ≤ ∑ v : V, u v := by
  classical
  calc
    _ = ∑ v ∈ (univ : Finset (Remaining S)).image Subtype.val, u v := by
      rw [Finset.sum_image]
      intro v _ w _ hvw
      exact Subtype.val_injective hvw
    _ ≤ ∑ v : V, u v := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun v _ _ => hu v)

theorem liftMatching_uncovered_card (G : SimpleGraph V) (S : Finset V)
    (M : (G.induce (↑S : Set V)ᶜ).Subgraph) :
    (uncoveredOutside G (liftMatching G S M) S).card = M.vertsᶜ.ncard := by
  classical
  have himage : (M.vertsᶜ.toFinset).image Subtype.val =
      uncoveredOutside G (liftMatching G S M) S := by
    ext v
    simp only [Finset.mem_image, Set.mem_toFinset, Set.mem_compl_iff,
      uncoveredOutside, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.property, fun h => hw ((liftMatching_mem_verts G S M w).mp h)⟩
    · rintro ⟨hvS, hvM⟩
      refine ⟨⟨v, hvS⟩, ?_, rfl⟩
      intro hv
      exact hvM ((liftMatching_mem_verts G S M ⟨v, hvS⟩).mpr hv)
  rw [← himage, Finset.card_image_of_injective _ Subtype.val_injective]
  exact (Set.ncard_eq_toFinset_card' _).symm

/-- Construct the maximum working matching, lift it to the original graph,
and obtain the exact Tutte–Berge bound and its manuscript scaling. -/
theorem exists_large_matching_outside_reserve
    (G R : SimpleGraph V) (hRG : R ≤ G) (M : I → G.Subgraph) (T : Finset I)
    (hM : ∀ i ∈ T, (M i).IsMatching)
    (hdisj : ∀ i ∈ T, ∀ j ∈ T, i ≠ j →
      Disjoint (M i).spanningCoe (M j).spanningCoe)
    (S : Finset V) (m r : ℕ) (Δ p ε γ : ℝ)
    (hm : 0 < m) (hr : 0 < r) (hε : 0 ≤ ε) (hγ : 0 < γ)
    (hεγ : ε ≤ γ / 40) (hεm : 1 ≤ ε * m)
    (horder : Fintype.card V ≤ m) (hparity : Even (Fintype.card V - S.card))
    (hG : ∀ v, Δ - ε * m ≤ (G.degree v : ℝ) ∧ (G.degree v : ℝ) ≤ Δ + ε * m)
    (hR : ∀ v, |(R.degree v : ℝ) - p * Δ| ≤ 2 * ε * m)
    (hmissing : ∀ v, (missingCount G M T v : ℝ) ≤ ε * m)
    (hS : (S.card : ℝ) ≤ ε * m)
    (hd : γ * m / 2 ≤ (1 - p) * Δ - T.card)
    (hbudget : 2 * (∑ v, (reserveLoad G R M T v : ℝ)) <
      (r : ℝ) * ((1 - p) * Δ - T.card - 4 * ε * m)) :
    ∃ N : G.Subgraph,
      N.IsMatching ∧ N.verts ⊆ (↑S : Set V)ᶜ ∧
      Disjoint N.spanningCoe R ∧
      Disjoint N.spanningCoe (edgeUnion (fun i => (M i).spanningCoe) T) ∧
      (∀ v, v ∉ S → r ≤ reserveLoad G R M T v → v ∈ N.verts) ∧
      Even (uncoveredOutside G N S).card ∧
      ((uncoveredOutside G N S).card : ℝ) ≤
        (m + 8 * ε * (m : ℝ) ^ 2 + ∑ v, (reserveLoad G R M T v : ℝ)) /
          ((1 - p) * Δ - T.card - 4 * ε * m + 1) ∧
      ((uncoveredOutside G N S).card : ℝ) ≤
        30 / γ * (ε * m + (∑ v, (reserveLoad G R M T v : ℝ)) / m) := by
  classical
  let H := residualGraph G R M T
  let W := H.induce (↑S : Set V)ᶜ
  let u : Remaining S → ℝ := fun v => reserveLoad G R M T v.val
  let d : ℝ := (1 - p) * Δ - T.card
  let t : ℝ := ∑ v, (reserveLoad G R M T v : ℝ)
  have hHG : H ≤ G := by intro v w hvw; exact hvw.1
  have hu : ∀ v, 0 ≤ u v := fun _ => Nat.cast_nonneg _
  have ht : 0 ≤ t := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hload : ∑ v : Remaining S, u v ≤ t :=
    sum_remaining_le_sum S (fun v => (reserveLoad G R M T v : ℝ))
      (fun _ => Nat.cast_nonneg _)
  have hdegrees : ∀ v : Remaining S, d - 4 * ε * m ≤ (W.degree v : ℝ) ∧
      (W.degree v : ℝ) ≤ d + 4 * ε * m + u v := by
    intro v
    have h := working_degree_bounds G R M T hRG hM hdisj S Δ p ε m
      hG hR hmissing hS v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using h
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hden : 0 < d - 4 * ε * m + 1 := by
    have hsmall := mul_le_mul_of_nonneg_right hεγ hmR.le
    have hpos : (0 : ℝ) < γ * m := mul_pos hγ hmR
    nlinarith
  have ha : (0 : ℝ) ≤ 4 * ε * m := by positivity
  have hWorder : Fintype.card (Remaining S) ≤ m :=
    (Fintype.card_subtype_le _).trans horder
  obtain ⟨N, hN, hcover, hdef⟩ :=
    OrdinaryPackingDeficiency.exists_matching_covering_saturated_load W
      m d (4 * ε * m) r t u hden ha hrR hu hWorder
      (fun v => (hdegrees v).1) (fun v => (hdegrees v).2) hload hbudget
  have hdef' : (N.vertsᶜ.ncard : ℝ) ≤
      (m + 8 * ε * (m : ℝ) ^ 2 + t) / (d - 4 * ε * m + 1) := by
    convert hdef using 1
    congr 1
    ring
  have hcoarse := OrdinaryPackingDeficiency.deficiency_scale N.vertsᶜ.ncard m d ε γ t
    hm hε hγ ht hεγ hεm hd hdef'
  have hNparity : Even N.vertsᶜ.ncard :=
    OrdinaryPackingDeficiency.matching_uncovered_even W N hN.1
      (by rw [remaining_order]; exact hparity)
  let L := liftMatching H S N
  let K : G.Subgraph :=
    { verts := L.verts
      Adj := L.Adj
      adj_sub := fun h => hHG (L.adj_sub h)
      edge_vert := L.edge_vert
      symm := L.symm }
  have hK : K.IsMatching := liftMatching_isMatching H S N hN.1
  have hKS : K.verts ⊆ (↑S : Set V)ᶜ := liftMatching_verts_subset H S N
  have hKR : Disjoint K.spanningCoe R := by
    apply disjoint_iff_inf_le.mpr
    intro v w hvw
    have hres : G.Adj v w ∧ ¬(R.Adj v w ∨
        (edgeUnion (fun i => (M i).spanningCoe) T).Adj v w) := L.adj_sub hvw.1
    exact hres.2 (Or.inl hvw.2)
  have hKU : Disjoint K.spanningCoe (edgeUnion (fun i => (M i).spanningCoe) T) := by
    apply disjoint_iff_inf_le.mpr
    intro v w hvw
    have hres : G.Adj v w ∧ ¬(R.Adj v w ∨
        (edgeUnion (fun i => (M i).spanningCoe) T).Adj v w) := L.adj_sub hvw.1
    exact hres.2 (Or.inr hvw.2)
  have hKcover : ∀ v, v ∉ S → r ≤ reserveLoad G R M T v → v ∈ K.verts := by
    intro v hv hrload
    have hloadv : (r : ℝ) ≤ u ⟨v, hv⟩ := by
      dsimp [u]
      exact_mod_cast hrload
    exact ⟨⟨v, hv⟩, hcover ⟨v, hv⟩ hloadv, rfl⟩
  have hcard : (uncoveredOutside G K S).card = N.vertsᶜ.ncard := by
    exact liftMatching_uncovered_card H S N
  refine ⟨K, hK, hKS, hKR, hKU, hKcover, ?_, ?_, ?_⟩
  · rw [hcard]
    exact hNparity
  · rw [hcard]
    exact hdef'
  · rw [hcard]
    exact hcoarse

end Overfull.OrdinaryPackingWorking
