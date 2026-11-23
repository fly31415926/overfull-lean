import Overfull.MultigraphMatchingProbability
import Overfull.CircuitPatterns.Weights

/-!
# Actual-copy capacities for a multigraph matching distribution

This adapts the finite marginal and pool-counting proofs from
CircuitPatterns.Weights without identifying parallel copies. The conditional
bundle bound is its actual multiplicity, not one. It does not construct the
boundary compression, a reserve, or the residual-host factorization.
-/

noncomputable section

namespace Overfull.MultigraphMatchingProbability

open Finset Classical
open scoped BigOperators

variable {V E S : Type*} [Fintype V] [Fintype E] [Fintype S]
    {G : Multigraph V E} {k : ℕ} (D : Distribution G k S)

/-- Probability scaled by the original host degree, on original edge copies. -/
def actualCopyWeight (t : S) : ℝ := (k : ℝ) * D.weight t

theorem actualCopyWeight_nonneg (t : S) : 0 ≤ actualCopyWeight D t :=
  mul_nonneg (Nat.cast_nonneg _) (D.nonneg t)

theorem actualCopyWeight_sum : ∑ t, actualCopyWeight D t = (k : ℝ) := by
  simp only [actualCopyWeight, ← mul_sum, D.sum_one, mul_one]

/-- Each individual parallel copy has scaled marginal exactly one. -/
theorem actualCopyWeight_marginal (hk : 0 < k) (e : E) :
    (∑ t ∈ univ.filter (fun t => e ∈ D.matching t), actualCopyWeight D t) = 1 := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  simp only [actualCopyWeight, ← mul_sum, D.marginal e]
  exact mul_one_div_cancel hkR

/-- Selecting only original matching copies cannot increase a copy marginal. -/
theorem actualCopy_selected_edge_le_one (hk : 0 < k) (F : S → Finset E)
    (hF : ∀ t, F t ⊆ D.matching t) (e : E) :
    (∑ t ∈ univ.filter (fun t => e ∈ F t), actualCopyWeight D t) ≤ 1 := by
  rw [← actualCopyWeight_marginal D hk e]
  apply sum_le_sum_of_subset_of_nonneg
  · intro t ht
    exact mem_filter.mpr ⟨mem_univ _, hF t (mem_filter.mp ht).2⟩
  · intro t _ _
    exact actualCopyWeight_nonneg D t

/-- Pool capacity counts edge copies, including parallel edges separately. -/
theorem actualCopy_selected_capacity (hk : 0 < k) (F : S → Finset E)
    (hF : ∀ t, F t ⊆ D.matching t) (A : Finset E) :
    (∑ t, actualCopyWeight D t * ((F t ∩ A).card : ℝ)) ≤ (A.card : ℝ) := by
  classical
  calc
    _ = ∑ e ∈ A, ∑ t ∈ univ.filter (fun t => e ∈ F t), actualCopyWeight D t := by
      simp only [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, mul_sum,
        mul_one, sum_filter]
      rw [sum_comm]
      apply sum_congr rfl
      intro t _
      rw [← sum_filter]
      congr 1
      ext e
      simp [and_comm]
    _ ≤ ∑ _e ∈ A, (1 : ℝ) := by
      exact sum_le_sum (fun e _ => actualCopy_selected_edge_le_one D hk F hF e)
    _ = (A.card : ℝ) := by simp

/-- Graph-independent pattern aggregation transfers the copy-pool capacity. -/
theorem actualCopy_aggregate_capacity {P : Type*} [Fintype P]
    (hk : 0 < k) (code : S → P) (F : S → Finset E)
    (hF : ∀ t, F t ⊆ D.matching t) (A : Finset E) (c : P → ℕ)
    (hc : ∀ t, c (code t) ≤ (F t ∩ A).card) :
    (∑ p, CircuitPatterns.aggregateWeight (actualCopyWeight D) code p *
      (c p : ℝ)) ≤ (A.card : ℝ) := by
  rw [CircuitPatterns.aggregateWeight_statistic]
  exact (sum_le_sum (fun t _ => mul_le_mul_of_nonneg_left
    (by exact_mod_cast hc t) (actualCopyWeight_nonneg D t))).trans
      (actualCopy_selected_capacity D hk F hF A)

/-- Requiring some selected copy from a pool bounds the entire pattern
weight by the number of original copies in that pool, not by one. -/
theorem actualCopy_pattern_weight_le_pool {P : Type*} [Fintype P]
    (hk : 0 < k) (code : S → P) (p : P)
    (F : S → Finset E) (hF : ∀ t, F t ⊆ D.matching t)
    (A : Finset E)
    (hreq : ∀ t, code t = p → (F t ∩ A).Nonempty) :
    CircuitPatterns.aggregateWeight (actualCopyWeight D) code p ≤ (A.card : ℝ) := by
  calc
    _ = ∑ t : S, if code t = p then actualCopyWeight D t else 0 := by
      simp only [CircuitPatterns.aggregateWeight, sum_filter]
    _ ≤ ∑ t, actualCopyWeight D t * ((F t ∩ A).card : ℝ) := by
      apply sum_le_sum
      intro t _
      by_cases hp : code t = p
      · simp only [if_pos hp]
        have hcount : 1 ≤ (F t ∩ A).card := by
          have hpos := card_pos.mpr (hreq t hp)
          omega
        have hcountR : (1 : ℝ) ≤ ((F t ∩ A).card : ℝ) := by
          exact_mod_cast hcount
        simpa only [mul_one] using
          (mul_le_mul_of_nonneg_left hcountR (actualCopyWeight_nonneg D t))
      · simp only [if_neg hp]
        positivity
    _ ≤ (A.card : ℝ) := actualCopy_selected_capacity D hk F hF A

/-- The finite pool of all distinct original copies with the same endpoints. -/
def parallelCopyPool (v w : V) : Finset E :=
  univ.filter (fun e => G.edge e = s(v,w))

/-- Correct native replacement for the simple-graph internal-pair bound.
A pattern containing some parallel copy of a prescribed pair has scaled
weight at most the multiplicity of that pair. -/
theorem actualCopy_pattern_weight_le_parallel_multiplicity
    {P : Type*} [Fintype P] (hk : 0 < k)
    (code : S → P) (p : P) (v w : V)
    (hpair : ∀ t, code t = p →
      ∃ e ∈ D.matching t, G.edge e = s(v,w)) :
    CircuitPatterns.aggregateWeight (actualCopyWeight D) code p ≤
      ((parallelCopyPool (G := G) v w).card : ℝ) := by
  apply actualCopy_pattern_weight_le_pool D hk code p
    D.matching (fun _ => subset_rfl) (parallelCopyPool (G := G) v w)
  intro t ht
  obtain ⟨e, he, hends⟩ := hpair t ht
  exact ⟨e, mem_inter.mpr ⟨he, mem_filter.mpr ⟨mem_univ _, hends⟩⟩⟩

end Overfull.MultigraphMatchingProbability
