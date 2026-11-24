import Overfull.MultigraphMatchingProbability
import Overfull.CircuitPatterns.Weights
import Overfull.CircuitPatterns.Rounding

/-!
# Native multigraph pattern weights and actual-copy capacities

All samples and pools in this file consist of original edge copies. In
particular, parallel copies contribute separately to the pool capacity.
The finite aggregation lemmas have no graph hypothesis; only those
graph-independent lemmas are reused from the simple-host development.
-/

noncomputable section

namespace Overfull.AssignedParts.NativeWeights

open Finset Classical
open Overfull.CircuitPatterns (aggregateWeight aggregateWeight_nonneg
  aggregateWeight_statistic aggregateWeight_sum aggregateWeight_pos_witness)
open scoped BigOperators

variable {V E S : Type*} [Fintype S] {G : Multigraph V E} {k : ℕ}
  (D : MultigraphMatchingProbability.Distribution G k S)

/-- Scale the actual-copy probability law by its regular degree. -/
def scaledWeight (s : S) : ℝ := k * D.weight s

theorem scaledWeight_nonneg (s : S) : 0 ≤ scaledWeight D s :=
  mul_nonneg (Nat.cast_nonneg _) (D.nonneg s)

theorem scaledWeight_sum : ∑ s, scaledWeight D s = k := by
  simp only [scaledWeight, ← mul_sum, D.sum_one, mul_one]

/-- Every actual edge copy, including each parallel copy, has weight one. -/
theorem scaledWeight_marginal (hk : 0 < k) (e : E) :
    (∑ s ∈ univ.filter (fun s => e ∈ D.matching s), scaledWeight D s) = 1 := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  simp only [scaledWeight, ← mul_sum, D.marginal]
  exact mul_one_div_cancel hkR

/-- Double counting applies to every finite actual-copy selection and pool. -/
theorem weighted_pool_sum (F : S → Finset E) (A : Finset E) :
    (∑ s, scaledWeight D s * ((F s ∩ A).card : ℝ)) =
      ∑ e ∈ A, ∑ s ∈ univ.filter (fun s => e ∈ F s), scaledWeight D s := by
  simp only [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, mul_sum,
    mul_one, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro s _
  rw [← sum_filter]
  congr 1
  ext e
  simp [and_comm]

/-- The scaled expected usage of a pool is its exact number of copies. -/
theorem scaled_matching_pool_eq (hk : 0 < k) (A : Finset E) :
    (∑ s, scaledWeight D s * ((D.matching s ∩ A).card : ℝ)) = A.card := by
  rw [weighted_pool_sum]
  simp only [scaledWeight_marginal D hk]
  simp

/-- Taking a submatching can only reduce the weight using one copy. -/
theorem scaled_selected_edge_le_one (hk : 0 < k) (F : S → Finset E)
    (hF : ∀ s, F s ⊆ D.matching s) (e : E) :
    (∑ s ∈ univ.filter (fun s => e ∈ F s), scaledWeight D s) ≤ 1 := by
  rw [← scaledWeight_marginal D hk e]
  apply sum_le_sum_of_subset_of_nonneg
  · intro s hs
    exact mem_filter.mpr ⟨mem_univ _, hF s (mem_filter.mp hs).2⟩
  · intro s _ _
    exact scaledWeight_nonneg D s

/-- Compressed copies obey capacity for an arbitrary pool of actual copies. -/
theorem scaled_selected_capacity (hk : 0 < k) (F : S → Finset E)
    (hF : ∀ s, F s ⊆ D.matching s) (A : Finset E) :
    (∑ s, scaledWeight D s * ((F s ∩ A).card : ℝ)) ≤ A.card := by
  rw [weighted_pool_sum]
  calc
    _ ≤ ∑ _e ∈ A, (1 : ℝ) := by
      exact sum_le_sum (fun e _ => scaled_selected_edge_le_one D hk F hF e)
    _ = A.card := by simp

variable {P : Type*} [Fintype P]

/-- Grouping by any finite code preserves total scaled weight. -/
theorem aggregateWeight_total (code : S → P) :
    ∑ p, aggregateWeight (scaledWeight D) code p = k := by
  rw [aggregateWeight_sum, scaledWeight_sum]

/-- A code statistic bounded by actual selected pool use obeys copy capacity. -/
theorem aggregate_capacity (hk : 0 < k) (code : S → P)
    (F : S → Finset E) (hF : ∀ s, F s ⊆ D.matching s)
    (A : Finset E) (c : P → ℕ)
    (hc : ∀ s, c (code s) ≤ (F s ∩ A).card) :
    (∑ p, aggregateWeight (scaledWeight D) code p * (c p : ℝ)) ≤ A.card := by
  rw [aggregateWeight_statistic]
  exact (sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left
    (by exact_mod_cast hc s) (scaledWeight_nonneg D s))).trans
      (scaled_selected_capacity D hk F hF A)

/-- If every sample of one code uses a pool, its weight is at most the
number of actual copies in that pool. Parallel copies are not collapsed. -/
theorem aggregateWeight_le_pool (hk : 0 < k) (code : S → P) (p : P)
    (A : Finset E)
    (huse : ∀ s, code s = p → (D.matching s ∩ A).Nonempty) :
    aggregateWeight (scaledWeight D) code p ≤ A.card := by
  have hstat : ∀ s, (if code s = p then 1 else 0) ≤
      (D.matching s ∩ A).card := by
    intro s
    split_ifs with hs
    · exact Nat.succ_le_of_lt (card_pos.mpr (huse s hs))
    · exact Nat.zero_le _
  have h := aggregate_capacity D hk code D.matching (fun _ => subset_refl _)
    A (fun q => if q = p then 1 else 0) hstat
  simpa using h

/-- A bounded finite code has a heavy code and an actual positive-weight
representative of that same code. No new matching is substituted for it. -/
theorem exists_heavy_code [Nonempty P] (hk : 0 < k) (code : S → P)
    (B : ℕ) (hB : 0 < B) (hcard : Fintype.card P ≤ B) :
    ∃ p s, code s = p ∧ 0 < scaledWeight D s ∧
      (k : ℝ) / B ≤ aggregateWeight (scaledWeight D) code p := by
  let w := aggregateWeight (scaledWeight D) code
  have hw : ∀ p, 0 ≤ w p :=
    aggregateWeight_nonneg _ (scaledWeight_nonneg D) code
  obtain ⟨p, hp, _⟩ := CircuitPatterns.exists_maximum_weight w
  have hweight : (k : ℝ) / B ≤ w p :=
    CircuitPatterns.maximum_weight_lower_bound w p k B hw hp
      (aggregateWeight_total D code) (by exact_mod_cast hB) (by exact_mod_cast hcard)
  have hratio : 0 < (k : ℝ) / B :=
    div_pos (by exact_mod_cast hk) (by exact_mod_cast hB)
  have hpos : 0 < w p := hratio.trans_le hweight
  obtain ⟨s, hs, hws⟩ := aggregateWeight_pos_witness _ code p hpos
  exact ⟨p, s, hs, hws, hweight⟩

end Overfull.AssignedParts.NativeWeights
