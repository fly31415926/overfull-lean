import Overfull.BipartitePackingDeletion
import Overfull.BipartitePackingStep

/-!
# The large matching outside the reserve

This assembles the graph and degree accounting with the maximum-matching
and deficiency results. The returned matching is a subgraph of the original
graph, avoids the reserve and all previously used edges, and covers the
saturated vertices outside the current forbidden set.
-/

set_option maxHeartbeats 200000

namespace Overfull.BipartitePackingWorking

open Finset Classical SimpleGraph
open scoped BigOperators
open BipartitePackingAccounting BipartitePackingDeletion

variable {A B I : Type*} [Fintype A] [Fintype B]

noncomputable def uncoveredLeftOutside (G : SimpleGraph (A ⊕ B))
    (N : G.Subgraph) (S : Finset (A ⊕ B)) : Finset A :=
  univ.filter (fun a => (.inl a : A ⊕ B) ∉ S ∧ (.inl a : A ⊕ B) ∉ N.verts)

noncomputable def uncoveredRightOutside (G : SimpleGraph (A ⊕ B))
    (N : G.Subgraph) (S : Finset (A ⊕ B)) : Finset B :=
  univ.filter (fun b => (.inr b : A ⊕ B) ∉ S ∧ (.inr b : A ⊕ B) ∉ N.verts)

theorem sum_remaining_le_sum (S : Finset (A ⊕ B)) (u : A ⊕ B → ℝ)
    (hu : ∀ v, 0 ≤ u v) :
    (∑ v : RemainingLeft S ⊕ RemainingRight S, u (remainingVertex S v)) ≤ ∑ v, u v := by
  calc
    _ = ∑ v ∈ (univ : Finset (RemainingLeft S ⊕ RemainingRight S)).image
          (remainingVertex S), u v := by
      rw [Finset.sum_image]
      intro v _ w _ hvw
      exact (remainingVertex S).injective hvw
    _ ≤ ∑ v, u v := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun v _ _ => hu v)

theorem exists_large_matching_outside_reserve
    (G R : SimpleGraph (A ⊕ B))
    (hbip : G.IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr))
    (hRG : R ≤ G) (M : I → G.Subgraph) (T : Finset I)
    (hM : ∀ i ∈ T, (M i).IsMatching)
    (hdisj : ∀ i ∈ T, ∀ j ∈ T, i ≠ j →
      Disjoint (M i).spanningCoe (M j).spanningCoe)
    (S : Finset (A ⊕ B)) (m r : ℕ) (Δ p ε γ c₀ : ℝ)
    (hm : 0 < m) (hr : 0 < r) (hε : 0 ≤ ε) (hγ : 0 < γ)
    (hA : Fintype.card A = m) (hB : Fintype.card B = m)
    (hbalanced : (univ.filter (fun a : A => (.inl a : A ⊕ B) ∈ S)).card =
      (univ.filter (fun b : B => (.inr b : A ⊕ B) ∈ S)).card)
    (hG : ∀ v, Δ - ε * m ≤ (G.degree v : ℝ) ∧ (G.degree v : ℝ) ≤ Δ + ε * m)
    (hR : ∀ v, |(R.degree v : ℝ) - p * Δ| ≤ 2 * ε * m)
    (hmissing : ∀ v, (missingCount G M T v : ℝ) ≤ ε * m)
    (hS : (S.card : ℝ) ≤ ε * m)
    (hd : γ * m / 2 ≤ (1 - p) * Δ - T.card)
    (hload : (∑ v, (reserveLoad G R M T v : ℝ)) ≤ c₀ * ε * (m : ℝ) ^ 2)
    (hbudget : 2 * (c₀ * ε * (m : ℝ) ^ 2) <
      (r : ℝ) * ((1 - p) * Δ - T.card - 4 * ε * m)) :
    ∃ N : G.Subgraph,
      N.IsMatching ∧ N.verts ⊆ (↑S : Set (A ⊕ B))ᶜ ∧
      Disjoint N.spanningCoe R ∧
      Disjoint N.spanningCoe (edgeUnion (fun i => (M i).spanningCoe) T) ∧
      (∀ v, v ∉ S → r ≤ reserveLoad G R M T v → v ∈ N.verts) ∧
      (uncoveredLeftOutside G N S).card = (uncoveredRightOutside G N S).card ∧
      ((uncoveredLeftOutside G N S).card : ℝ) ≤
        (8 * ε * (m : ℝ) ^ 2 + ∑ v, (reserveLoad G R M T v : ℝ)) /
          ((1 - p) * Δ - T.card) ∧
      ((uncoveredLeftOutside G N S).card : ℝ) ≤ (16 + 2 * c₀) * ε * m / γ := by
  let H := residualGraph G R M T
  let W := deletedGraph H S
  let u : RemainingLeft S ⊕ RemainingRight S → ℝ :=
    fun v => reserveLoad G R M T (remainingVertex S v)
  let d : ℝ := (1 - p) * Δ - T.card
  let t : ℝ := ∑ v, (reserveLoad G R M T v : ℝ)
  have hHG : H ≤ G := by
    intro v w hvw
    exact hvw.1
  have hH : H.IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr) := by
    constructor
    · exact hbip.disjoint
    · intro v w hvw
      exact hbip.mem_of_adj (hHG hvw)
  have hW : W.IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr) :=
    deletedGraph_bipartite H S hH
  have hAB : Fintype.card A = Fintype.card B := hA.trans hB.symm
  have hbalance := remaining_sides_balanced S hAB hbalanced
  have hAc : Fintype.card (RemainingLeft S) ≤ m := (remainingLeft_card_le S).trans hA.le
  have hBc : Fintype.card (RemainingRight S) ≤ m := (remainingRight_card_le S).trans hB.le
  have hu : ∀ v, 0 ≤ u v := fun _ => Nat.cast_nonneg _
  have ht : ∑ v, u v ≤ t :=
    sum_remaining_le_sum S (fun v => (reserveLoad G R M T v : ℝ)) (fun _ => Nat.cast_nonneg _)
  have hdegrees : ∀ v, d - 4 * ε * m ≤ (W.degree v : ℝ) ∧
      (W.degree v : ℝ) ≤ d + 4 * ε * m + u v := by
    intro v
    have h := working_degree_bounds G R M T hRG hM hdisj S Δ p ε m
      hG hR hmissing hS (sideDeletionEquiv S v)
    have hdeg : (W.degree v : ℝ) =
        (H.induce (↑S : Set (A ⊕ B))ᶜ).degree (sideDeletionEquiv S v) := by
      exact_mod_cast deletedGraph_degree H S v
    rw [hdeg]
    constructor
    · refine h.1.trans ?_
      apply le_of_eq
      apply congrArg (fun n : ℕ => (n : ℝ))
      simp only [← SimpleGraph.card_neighborSet_eq_degree]
      exact congrArg (@Fintype.card _) (Subsingleton.elim _ _)
    · refine le_trans ?_ h.2
      apply le_of_eq
      apply congrArg (fun n : ℕ => (n : ℝ))
      simp only [← SimpleGraph.card_neighborSet_eq_degree]
      exact congrArg (@Fintype.card _) (Subsingleton.elim _ _)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hd0 : 0 < d := (by positivity : (0 : ℝ) < γ * m / 2).trans_le hd
  have ha : (0 : ℝ) ≤ 4 * ε * m := by positivity
  have hbudget' : 2 * t < (r : ℝ) * (d - 4 * ε * m) := by
    change 2 * (c₀ * ε * (m : ℝ) ^ 2) < (r : ℝ) * (d - 4 * ε * m) at hbudget
    have hload' : t ≤ c₀ * ε * (m : ℝ) ^ 2 := hload
    linarith
  obtain ⟨N, hN, hcover, hmax, hdef⟩ :=
    BipartitePackingStep.exists_matching_covering_saturated_load W hW m d (4 * ε * m)
      r t u hd0 ha hrR hu hAc hBc (fun v => (hdegrees v).1) (fun v => (hdegrees v).2)
      ht hbudget'
  have hdef' : ((uncoveredLeft N).card : ℝ) ≤ (8 * ε * (m : ℝ) ^ 2 + t) / d := by
    convert hdef using 1
    congr 1
    ring
  have hcoarse : ((uncoveredLeft N).card : ℝ) ≤ (16 + 2 * c₀) * ε * m / γ :=
    BipartitePackingStep.deficiency_scale (uncoveredLeft N).card m d ε γ c₀ t
      hm hd0 hγ hd hload hdef'
  have hequal := BipartitePackingDeficiency.matching_uncovered_sides_eq W hW hbalance N hN
  let L := liftMatching H S N
  let K : G.Subgraph :=
    { verts := L.verts
      Adj := L.Adj
      adj_sub := fun h => hHG (L.adj_sub h)
      edge_vert := L.edge_vert
      symm := L.symm }
  have hK : K.IsMatching := liftMatching_isMatching H S N hN
  have hKS : K.verts ⊆ (↑S : Set (A ⊕ B))ᶜ := liftMatching_verts_subset H S N
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
    obtain ⟨w, hw⟩ := (sideDeletionEquiv S).surjective ⟨v, hv⟩
    have hwval : remainingVertex S w = v := congrArg Subtype.val hw
    have hloadw : (r : ℝ) ≤ u w := by
      dsimp [u]
      rw [hwval]
      exact_mod_cast hrload
    exact ⟨w, hcover w hloadw, hwval⟩
  have hleft : (uncoveredLeftOutside G K S).card = (uncoveredLeft N).card := by
    exact liftMatching_uncoveredLeft_card H S N
  have hright : (uncoveredRightOutside G K S).card =
      (univ.filter (fun b : RemainingRight S =>
        (.inr b : RemainingLeft S ⊕ RemainingRight S) ∉ N.verts)).card := by
    exact liftMatching_uncoveredRight_card H S N
  refine ⟨K, hK, hKS, hKR, hKU, hKcover, ?_, ?_, ?_⟩
  · rw [hleft, hright]
    exact hequal
  · rw [hleft]
    exact hdef'
  · rw [hleft]
    exact hcoarse

end Overfull.BipartitePackingWorking
