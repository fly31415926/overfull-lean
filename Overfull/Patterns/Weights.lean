import Overfull.ForceMatching.Cuts

/-!
# Weights of finite boundary patterns

The weights are obtained by grouping a finite distribution on actual
perfect matchings. Capacity bounds refer to actual host edges. No
fractional decomposition of a later residual graph is assumed.
-/

namespace Overfull.Patterns

open Finset Classical FractionalMatching MatchingProbability
open scoped BigOperators

variable {S P : Type*} [Fintype S] [Fintype P]

/-- Sum the weights of all samples having one common pattern. -/
noncomputable def aggregateWeight (w : S → ℝ) (code : S → P) (p : P) : ℝ :=
  ∑ s ∈ univ.filter (fun s => code s = p), w s

omit [Fintype P] in
theorem aggregateWeight_nonneg (w : S → ℝ) (hw : ∀ s, 0 ≤ w s)
    (code : S → P) (p : P) : 0 ≤ aggregateWeight w code p := by
  exact sum_nonneg (fun s _ => hw s)

/-- Grouping by the common code preserves every weighted statistic. -/
theorem aggregateWeight_statistic (w : S → ℝ) (code : S → P) (f : P → ℝ) :
    (∑ p, aggregateWeight w code p * f p) = ∑ s, w s * f (code s) := by
  classical
  simp only [aggregateWeight, sum_mul, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro s _
  simp [eq_comm]

theorem aggregateWeight_sum (w : S → ℝ) (code : S → P) :
    ∑ p, aggregateWeight w code p = ∑ s, w s := by
  simpa using aggregateWeight_statistic w code (fun _ => 1)

omit [Fintype P] in
/-- A positive pattern weight has an actual positive-weight sample. -/
theorem aggregateWeight_pos_witness (w : S → ℝ) (code : S → P) (p : P)
    (hp : 0 < aggregateWeight w code p) :
    ∃ s, code s = p ∧ 0 < w s := by
  classical
  by_contra hn
  push_neg at hn
  have hnonpos : aggregateWeight w code p ≤ 0 :=
    sum_nonpos (fun s hs => hn s (mem_filter.mp hs).2)
  linarith

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {k : ℕ} (D : Distribution G k S)

/-- Scale the probability law so each original edge has total weight one. -/
noncomputable def scaledWeight (s : S) : ℝ := k * D.weight s

omit [Fintype V] [DecidableRel G.Adj] in
theorem scaledWeight_nonneg (s : S) : 0 ≤ scaledWeight D s :=
  mul_nonneg (Nat.cast_nonneg _) (D.nonneg s)

omit [Fintype V] [DecidableRel G.Adj] in
theorem scaledWeight_sum : ∑ s, scaledWeight D s = k := by
  simp only [scaledWeight, ← mul_sum, D.sum_one, mul_one]

omit [Fintype V] [DecidableRel G.Adj] in
theorem scaledWeight_marginal (hk : 0 < k) (e : G.edgeSet) :
    (∑ s ∈ univ.filter (fun s => e.val ∈ (D.matching s).edgeSet),
      scaledWeight D s) = 1 := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  simp only [scaledWeight, ← mul_sum, D.marginal]
  exact mul_one_div_cancel hkR

/-- The total weight of compressed copies of one edge is at most one. -/
theorem scaled_selected_edge_le_one (hk : 0 < k) (F : S → Finset G.edgeSet)
    (hF : ∀ s, F s ⊆ matchingEdges (D.matching s)) (e : G.edgeSet) :
    (∑ s ∈ univ.filter (fun s => e ∈ F s), scaledWeight D s) ≤ 1 := by
  rw [← scaledWeight_marginal D hk e]
  apply sum_le_sum_of_subset_of_nonneg
  · intro s hs
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    exact (mem_filter.mp (hF s (mem_filter.mp hs).2)).2
  · intro s _ _
    exact scaledWeight_nonneg D s

/-- Summing edge marginals gives capacity for every actual edge pool. -/
theorem scaled_selected_capacity (hk : 0 < k) (F : S → Finset G.edgeSet)
    (hF : ∀ s, F s ⊆ matchingEdges (D.matching s)) (A : Finset G.edgeSet) :
    (∑ s, scaledWeight D s * ((F s ∩ A).card : ℝ)) ≤ A.card := by
  classical
  calc
    _ = ∑ e ∈ A, ∑ s ∈ univ.filter (fun s => e ∈ F s), scaledWeight D s := by
      simp only [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, mul_sum,
        mul_one, sum_filter]
      rw [sum_comm]
      apply sum_congr rfl
      intro s _
      rw [← sum_filter]
      congr 1
      ext e
      simp [and_comm]
    _ ≤ ∑ _e ∈ A, (1 : ℝ) := by
      exact sum_le_sum (fun e _ => scaled_selected_edge_le_one D hk F hF e)
    _ = A.card := by simp

/-- Any pattern statistic bounded by its actual selected edge pool obeys
the same capacity inequality after aggregation. -/
theorem aggregate_capacity (hk : 0 < k) (code : S → P)
    (F : S → Finset G.edgeSet) (hF : ∀ s, F s ⊆ matchingEdges (D.matching s))
    (A : Finset G.edgeSet) (c : P → ℕ)
    (hc : ∀ s, c (code s) ≤ (F s ∩ A).card) :
    (∑ p, aggregateWeight (scaledWeight D) code p * (c p : ℝ)) ≤ A.card := by
  rw [aggregateWeight_statistic]
  exact (sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left
    (by exact_mod_cast hc s) (scaledWeight_nonneg D s))).trans
      (scaled_selected_capacity D hk F hF A)

omit [Fintype P] [Fintype V] [DecidableRel G.Adj] in
/-- In a simple graph a fixed exceptional pair is one actual edge.
Every pattern requiring it consequently has weight at most one. -/
theorem aggregateWeight_le_one_of_edge (hk : 0 < k) (code : S → P) (p : P)
    (e : G.edgeSet)
    (he : ∀ s, code s = p → e.val ∈ (D.matching s).edgeSet) :
    aggregateWeight (scaledWeight D) code p ≤ 1 := by
  rw [← scaledWeight_marginal D hk e]
  apply sum_le_sum_of_subset_of_nonneg
  · intro s hs
    exact mem_filter.mpr ⟨mem_univ _, he s (mem_filter.mp hs).2⟩
  · intro s _ _
    exact scaledWeight_nonneg D s

/-- Weighted crossing counts of compressed matchings are bounded by the
original cut. The code is shared by every sample. -/
theorem aggregate_cut_capacity (hk : 0 < k) (code : S → P)
    (F : S → Finset G.edgeSet) (hF : ∀ s, F s ⊆ matchingEdges (D.matching s))
    (X : Finset V) (crossing : P → ℕ)
    (hcrossing : ∀ s, crossing (code s) = cutCount (F s) X) :
    (∑ p, aggregateWeight (scaledWeight D) code p * (crossing p : ℝ)) ≤
      cutCount (univ : Finset G.edgeSet) X := by
  apply aggregate_capacity D hk code F hF (cutEdges univ X) crossing
  intro s
  rw [hcrossing]
  apply le_of_eq
  unfold cutCount
  congr 1
  ext e
  simp [cutEdges, Lovasz.BMatch.cut]

end Overfull.Patterns
