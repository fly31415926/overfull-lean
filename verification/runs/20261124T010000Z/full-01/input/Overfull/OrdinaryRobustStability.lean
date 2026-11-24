import Overfull.RobustStability
import Overfull.BipartitePackingAccounting

/-!
# Ordinary robust expansion after deletions

The surviving graph is an actual induced graph, and all losses refer to
its original vertices and the edges already used by the matching family.
-/

namespace Overfull

open Finset Classical SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem IsRobustExpander.mono_parameter (G : SimpleGraph V) [DecidableRel G.Adj]
    {ν μ τ : ℝ} (hG : IsRobustExpander G ν τ) (hμν : μ ≤ ν) :
    IsRobustExpander G μ τ := by
  intro S hS hS'
  have h := hG S hS hS'
  have hc : ((robustNeighbors G ν S).card : ℝ) ≤ (robustNeighbors G μ S).card := by
    exact_mod_cast Finset.card_le_card (robustNeighbors_mono_parameter G ν μ hμν S)
  have hm := mul_le_mul_of_nonneg_right hμν (Nat.cast_nonneg (Fintype.card V))
  linarith

theorem IsRobustExpander.mono_range (G : SimpleGraph V) [DecidableRel G.Adj]
    {ν τ σ : ℝ} (hG : IsRobustExpander G ν τ) (hτσ : τ ≤ σ) :
    IsRobustExpander G ν σ := by
  intro S hS hS'
  have hm := mul_le_mul_of_nonneg_right hτσ (Nat.cast_nonneg (Fintype.card V))
  exact hG S (by linarith) (by nlinarith)

namespace OrdinaryRobustStability

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem induced_neighbors_card (W : Finset V) (S : Finset (W : Set V))
    (v : (W : Set V)) :
    ((G.induce (W : Set V)).neighborFinset v ∩ S).card =
      (G.neighborFinset v.val ∩ S.image Subtype.val).card := by
  have heq : (((G.induce (W : Set V)).neighborFinset v ∩ S).image Subtype.val) =
      G.neighborFinset v.val ∩ S.image Subtype.val := by
    ext w
    simp only [Finset.mem_image, Finset.mem_inter, SimpleGraph.mem_neighborFinset,
      SimpleGraph.induce, SimpleGraph.comap_adj]
    constructor
    · rintro ⟨x, ⟨hxG, hxS⟩, rfl⟩
      exact ⟨hxG, ⟨x, hxS, rfl⟩⟩
    · rintro ⟨hxG, ⟨x, hxS, rfl⟩⟩
      exact ⟨x, ⟨hxG, hxS⟩, rfl⟩
  rw [← heq, Finset.card_image_of_injective _ Subtype.val_injective]

theorem induced_degree (W : Finset V) (v : (W : Set V)) :
    (G.induce (W : Set V)).degree v = (G.neighborFinset v.val ∩ W).card := by
  have h := congrArg Finset.card (G.map_neighborFinset_induce (s := (W : Set V)) v)
  simpa only [Finset.card_map, Finset.toFinset_coe, SimpleGraph.card_neighborFinset_eq_degree,
    ← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using h

theorem induced_degree_bounds (W : Finset V) (v : (W : Set V)) :
    (G.induce (W : Set V)).degree v ≤ G.degree v.val ∧
      G.degree v.val + W.card ≤ (G.induce (W : Set V)).degree v + Fintype.card V := by
  rw [induced_degree]
  have hupper := Finset.card_le_card
    (Finset.inter_subset_left : G.neighborFinset v.val ∩ W ⊆ G.neighborFinset v.val)
  have hu := Finset.card_le_univ (G.neighborFinset v.val ∪ W)
  have heq := Finset.card_union_add_card_inter (G.neighborFinset v.val) W
  change _ ≤ (G.neighborFinset v.val).card ∧ _
  constructor
  · exact hupper
  · change (G.neighborFinset v.val).card + W.card ≤ _
    omega

end OrdinaryRobustStability

/-- Keeping at least the original robust surplus minus the deleted vertices
gives the half-parameter conclusion after both kinds of deletion. -/
theorem IsRobustExpander.after_edge_and_vertex_deletion
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    {ν τ μ : ℝ} (hG : IsRobustExpander G ν τ)
    (hHG : H ≤ G) (hν : 0 ≤ ν) (hν1 : ν ≤ 1)
    (hτ : 0 ≤ τ) (hτ1 : τ < 1 / 4) (hμν : μ ≤ ν / 2)
    (hloss : ∀ v, (G.degree v : ℝ) ≤ H.degree v + μ * Fintype.card V)
    (W : Finset V)
    (hdelete : (Fintype.card V : ℝ) - W.card ≤ ν * Fintype.card V / 2) :
    IsRobustExpander (H.induce (W : Set V)) (ν / 2) (2 * τ) := by
  classical
  let n : ℝ := Fintype.card V
  let n' : ℝ := W.card
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hn' : 0 ≤ n' := Nat.cast_nonneg _
  have hle : n' ≤ n := by dsimp [n, n']; exact_mod_cast Finset.card_le_univ W
  have hhalf : n / 2 ≤ n' := by
    have hmul := mul_le_mul_of_nonneg_right hν1 hn
    change n - n' ≤ ν * n / 2 at hdelete
    linarith
  intro S hSlow hShigh
  have hScard : (S.image Subtype.val).card = S.card :=
    Finset.card_image_of_injective _ Subtype.val_injective
  have hdom : Nat.card (W : Set V) = W.card := by
    simpa only [← Nat.card_eq_fintype_card] using Fintype.card_coe W
  simp only [← Nat.card_eq_fintype_card, hdom] at hSlow hShigh ⊢
  change 2 * τ * n' ≤ (S.card : ℝ) at hSlow
  change (S.card : ℝ) ≤ (1 - 2 * τ) * n' at hShigh
  have hSlow' : τ * n ≤ ((S.image Subtype.val).card : ℝ) := by
    rw [hScard]
    have hmul := mul_le_mul_of_nonneg_left hhalf hτ
    linarith
  have hShigh' : ((S.image Subtype.val).card : ℝ) ≤ (1 - τ) * n := by
    rw [hScard]
    have h1 := mul_le_mul_of_nonneg_left hle (show 0 ≤ 1 - 2 * τ by linarith)
    have h2 := mul_nonneg hτ hn
    nlinarith
  have hex := hG (S.image Subtype.val) hSlow' hShigh'
  rw [hScard] at hex
  let R := robustNeighbors G ν (S.image Subtype.val)
  let R' := robustNeighbors (H.induce (W : Set V)) (ν / 2) S
  have hsubset : R ∩ W ⊆ R'.image Subtype.val := by
    intro v hv
    rcases Finset.mem_inter.mp hv with ⟨hvR, hvW⟩
    apply Finset.mem_image.mpr
    refine ⟨⟨v, hvW⟩, ?_, rfl⟩
    rw [mem_robustNeighbors, OrdinaryRobustStability.induced_neighbors_card]
    simp only [← Nat.card_eq_fintype_card, hdom]
    have hvH := robustNeighbors_after_edge_deletion G H hHG ν μ hloss
      (S.image Subtype.val) hvR
    have hvcount : (ν - μ) * n ≤
        ((H.neighborFinset v ∩ S.image Subtype.val).card : ℝ) :=
      (mem_robustNeighbors H (ν - μ) (S.image Subtype.val) v).mp hvH
    have hsmall := mul_le_mul_of_nonneg_right hμν hn
    have hmul := mul_le_mul_of_nonneg_left hle hν
    change ν / 2 * n' ≤ _
    nlinarith
  have hcard : (R ∩ W).card ≤ R'.card := by
    have h := Finset.card_le_card hsubset
    rwa [Finset.card_image_of_injective _ Subtype.val_injective] at h
  have hunion : (R ∪ W).card ≤ Fintype.card V := Finset.card_le_univ _
  have hsum := Finset.card_union_add_card_inter R W
  have hcount : R.card + W.card ≤ R'.card + Fintype.card V := by omega
  have hreal : (R.card : ℝ) + n' ≤ R'.card + n := by
    dsimp [n, n']
    exact_mod_cast hcount
  change (S.card : ℝ) + ν * n ≤ R.card at hex
  change (S.card : ℝ) + ν / 2 * n' ≤ R'.card
  have hmul := mul_le_mul_of_nonneg_left hle hν
  change n - n' ≤ ν * n / 2 at hdelete
  nlinarith

theorem IsRobustExpander.after_vertex_deletion
    (G : SimpleGraph V) [DecidableRel G.Adj] {ν τ : ℝ}
    (hG : IsRobustExpander G ν τ) (hν : 0 ≤ ν) (hν1 : ν ≤ 1)
    (hτ : 0 ≤ τ) (hτ1 : τ < 1 / 4) (W : Finset V)
    (hdelete : (Fintype.card V : ℝ) - W.card ≤ ν * Fintype.card V / 2) :
    IsRobustExpander (G.induce (W : Set V)) (ν / 2) (2 * τ) := by
  exact IsRobustExpander.after_edge_and_vertex_deletion G G hG le_rfl hν hν1 hτ hτ1
    (μ := 0) (by linarith) (by intro v; simp) W hdelete

namespace OrdinaryPackingReserve

open BipartitePackingAccounting

variable {I : Type*} (G R : SimpleGraph V) (M : I → G.Subgraph) (T : Finset I)

theorem unused_reserve_robust (ν τ μ : ℝ) (hR : IsRobustExpander R ν τ)
    (hμ : 0 ≤ μ)
    (hload : ∀ v, (reserveLoad G R M T v : ℝ) ≤ μ * Fintype.card V) :
    IsRobustExpander (R \ edgeUnion (fun i => (M i).spanningCoe) T) (ν - μ) τ := by
  apply IsRobustExpander.after_edge_deletion R
    (R \ edgeUnion (fun i => (M i).spanningCoe) T) hR sdiff_le hμ
  intro v
  have h := unused_reserve_degree G R M T v
  have h' : ((R \ edgeUnion (fun i => (M i).spanningCoe) T).degree v : ℝ) +
      reserveLoad G R M T v = R.degree v := by exact_mod_cast h
  linarith [hload v]

theorem residual_graph_robust (ν τ μ : ℝ) (hRG : R ≤ G)
    (hR : IsRobustExpander R ν τ) (hμ : 0 ≤ μ)
    (hload : ∀ v, (reserveLoad G R M T v : ℝ) ≤ μ * Fintype.card V) :
    IsRobustExpander (G \ edgeUnion (fun i => (M i).spanningCoe) T) (ν - μ) τ := by
  have hsub : R \ edgeUnion (fun i => (M i).spanningCoe) T ≤
      G \ edgeUnion (fun i => (M i).spanningCoe) T := by
    intro v w hvw
    exact ⟨hRG hvw.1, hvw.2⟩
  exact (unused_reserve_robust G R M T ν τ μ hR hμ hload).mono_graph _ _ hsub

theorem unused_reserve_after_vertex_deletion (ν τ μ : ℝ)
    (hR : IsRobustExpander R ν τ) (hν : 0 ≤ ν) (hν1 : ν ≤ 1)
    (hτ : 0 ≤ τ) (hτ1 : τ < 1 / 4) (hμν : μ ≤ ν / 2)
    (hload : ∀ v, (reserveLoad G R M T v : ℝ) ≤ μ * Fintype.card V)
    (W : Finset V)
    (hdelete : (Fintype.card V : ℝ) - W.card ≤ ν * Fintype.card V / 2) :
    IsRobustExpander
      ((R \ edgeUnion (fun i => (M i).spanningCoe) T).induce (W : Set V))
      (ν / 2) (2 * τ) := by
  apply IsRobustExpander.after_edge_and_vertex_deletion R
    (R \ edgeUnion (fun i => (M i).spanningCoe) T) hR sdiff_le hν hν1 hτ hτ1 hμν
      _ W hdelete
  intro v
  have h := unused_reserve_degree G R M T v
  have h' : ((R \ edgeUnion (fun i => (M i).spanningCoe) T).degree v : ℝ) +
      reserveLoad G R M T v = R.degree v := by exact_mod_cast h
  linarith [hload v]

end OrdinaryPackingReserve
end Overfull
