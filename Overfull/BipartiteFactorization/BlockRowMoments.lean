import Overfull.BipartiteFactorization.BlockProductSampling
import Overfull.Probability.ProductMoments
import Overfull.Probability.VarianceShift
import Overfull.Probability.CappedMean

/-!
# Actual exceptional-row moments in independent part samples

The statistic counts original multigraph edge copies from a fixed vertex
into the sampled block. Disjoint parts give an exact sum of weighted samples.
Their actual finite moments yield the variance coefficient one and the capped
row margin used for the correction score.
-/

noncomputable section

namespace Overfull.BipartiteFactorization.BlockRowMoments

open Finset Classical FiniteProbability BlockProductSampling

variable {V E ι : Type*} [Fintype ι]

/-- Sum original-vertex weights over the actual union of disjoint samples. -/
theorem sum_sampledBlock (D : ι → Finset V)
    (hdisj : ∀ i j, i ≠ j → Disjoint (D i) (D j))
    (τ : ∀ i, Finset (D i)) (w : V → ℝ) :
    (∑ v ∈ sampledBlock D τ, w v) = ∑ i, ∑ v ∈ τ i, w v.val := by
  unfold sampledBlock
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro i _
    exact Finset.sum_image (fun _ _ _ _ h => Subtype.ext h)
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro v hi hj
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨y, _, hy⟩ := Finset.mem_image.mp hj
    exact Finset.disjoint_left.mp (hdisj i j hij) x.property (hy ▸ y.property)

/-- An exact common sampling fraction gives this mean even for an empty
part, whose weighted population sum is zero. -/
theorem mean_partWeightedSum (D : Finset V) (s : ℕ) (hs : s ≤ D.card)
    (p₀ : ℝ) (hfraction : (s : ℝ) = p₀ * D.card) (w : D → ℝ) :
    mean (Hypergeometric.weight (E := D) s) (Hypergeometric.weightedSum w) =
      p₀ * ∑ v, w v := by
  rw [Hypergeometric.mean_weightedSum s (by simpa only [Fintype.card_coe] using hs)]
  by_cases hD : D.card = 0
  · haveI : IsEmpty D := Fintype.card_eq_zero_iff.mp (by simpa only [Fintype.card_coe] using hD)
    simp
  · rw [Fintype.card_coe, hfraction,
      mul_div_cancel_right₀ p₀ (Nat.cast_ne_zero.mpr hD)]

variable [Fintype E] (G : Multigraph V E)

/-- The actual row count is exactly the sum of the parallel-copy weights
selected separately in every vertex part. -/
theorem edgesTo_sampledBlock_eq_sum (D : ι → Finset V)
    (hdisj : ∀ i j, i ≠ j → Disjoint (D i) (D j))
    (τ : ∀ i, Finset (D i)) (x : V) :
    ((G.edgesTo x (sampledBlock D τ)).card : ℝ) =
      ∑ i, Hypergeometric.weightedSum
        (fun v : D i => ((G.parallelEdges v.val x).card : ℝ)) (τ i) := by
  have hcount : ((G.edgesTo x (sampledBlock D τ)).card : ℝ) =
      ∑ v ∈ sampledBlock D τ, ((G.parallelEdges v x).card : ℝ) := by
    exact_mod_cast (BlockSampling.sum_parallel_card G x (sampledBlock D τ)).symm
  rw [hcount, sum_sampledBlock D hdisj]
  rfl

/-- Summing the complete part populations counts the actual unsampled row. -/
theorem sum_part_parallel_card (D : ι → Finset V)
    (hdisj : ∀ i j, i ≠ j → Disjoint (D i) (D j))
    (B : Finset V) (hcover : univ.biUnion D = B) (x : V) :
    (∑ i, ∑ v : D i, ((G.parallelEdges v.val x).card : ℝ)) =
      (G.edgesTo x B).card := by
  rw [sum_part_weights D hdisj (fun v => ((G.parallelEdges v x).card : ℝ)), hcover]
  exact_mod_cast BlockSampling.sum_parallel_card G x B

/-- The row expectation is the common fraction times the actual number
of edge copies from the exceptional vertex to the original block. -/
theorem mean_edgesTo (D : ι → Finset V)
    (hdisj : ∀ i j, i ≠ j → Disjoint (D i) (D j))
    (B : Finset V) (hcover : univ.biUnion D = B)
    (s : ι → ℕ) (hs : ∀ i, s i ≤ (D i).card)
    (p₀ : ℝ) (hfraction : ∀ i, (s i : ℝ) = p₀ * (D i).card) (x : V) :
    mean (piWeight (fun i => Hypergeometric.weight (E := D i) (s i)))
      (fun τ => ((G.edgesTo x (sampledBlock D τ)).card : ℝ)) =
        p₀ * (G.edgesTo x B).card := by
  simp_rw [edgesTo_sampledBlock_eq_sum G D hdisj]
  rw [mean_pi_sum]
  · simp_rw [mean_partWeightedSum _ _ (hs _) p₀ (hfraction _)]
    rw [← Finset.mul_sum, sum_part_parallel_card G D hdisj B hcover x]
  · intro i
    exact Hypergeometric.sum_weight _ (by simpa only [Fintype.card_coe] using hs i)

/-- Independent fixed-size part sampling retains the coefficient one in
the row variance bound. Parallel edge copies may occur. -/
theorem variance_edgesTo_le (D : ι → Finset V)
    (hdisj : ∀ i j, i ≠ j → Disjoint (D i) (D j))
    (B : Finset V) (hcover : univ.biUnion D = B)
    (s : ι → ℕ) (hs : ∀ i, s i ≤ (D i).card)
    (p₀ : ℝ) (hfraction : ∀ i, (s i : ℝ) = p₀ * (D i).card)
    (x : V) (a : ℝ)
    (hweight : ∀ v ∈ B, ((G.parallelEdges x v).card : ℝ) ≤ a) :
    variance (piWeight (fun i => Hypergeometric.weight (E := D i) (s i)))
      (fun τ => ((G.edgesTo x (sampledBlock D τ)).card : ℝ)) ≤
        a * (p₀ * (G.edgesTo x B).card) := by
  simp_rw [edgesTo_sampledBlock_eq_sum G D hdisj]
  apply (variance_pi_sum_le
    (fun i => Hypergeometric.weight (E := D i) (s i))
    (fun i => Hypergeometric.weight_nonneg _)
    (fun i => Hypergeometric.sum_weight _ (by simpa only [Fintype.card_coe] using hs i))
    (fun i => Hypergeometric.weightedSum
      (fun v : D i => ((G.parallelEdges v.val x).card : ℝ)))).trans
  calc
    _ ≤ ∑ i, a * mean (Hypergeometric.weight (E := D i) (s i))
        (Hypergeometric.weightedSum (fun v : D i => ((G.parallelEdges v.val x).card : ℝ))) := by
      apply Finset.sum_le_sum
      intro i _
      apply Hypergeometric.variance_weightedSum_le_max_mul_mean
        (s i) (by simpa only [Fintype.card_coe] using hs i) _ a
        (fun _ => Nat.cast_nonneg _)
      intro v
      rw [BlockSampling.parallelEdges_symm G v.val x]
      apply hweight v.val
      rw [← hcover]
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, v.property⟩
    _ = a * (p₀ * (G.edgesTo x B).card) := by
      simp_rw [mean_partWeightedSum _ _ (hs _) p₀ (hfraction _)]
      rw [← Finset.mul_sum, ← Finset.mul_sum,
        sum_part_parallel_card G D hdisj B hcover x]

/-- Original degree control on the sampled side supplies every row's
individual parallel-copy bound. -/
theorem variance_edgesTo_le_of_degree (D : ι → Finset V)
    (hdisj : ∀ i j, i ≠ j → Disjoint (D i) (D j))
    (B : Finset V) (hcover : univ.biUnion D = B)
    (s : ι → ℕ) (hs : ∀ i, s i ≤ (D i).card)
    (p₀ : ℝ) (hfraction : ∀ i, (s i : ℝ) = p₀ * (D i).card)
    (x : V) (a : ℝ) (hdegree : ∀ v ∈ B, (G.degree v : ℝ) ≤ a) :
    variance (piWeight (fun i => Hypergeometric.weight (E := D i) (s i)))
      (fun τ => ((G.edgesTo x (sampledBlock D τ)).card : ℝ)) ≤
        a * (p₀ * (G.edgesTo x B).card) := by
  apply variance_edgesTo_le G D hdisj B hcover s hs p₀ hfraction x a
  intro v hv
  exact (Nat.cast_le.mpr (G.parallelEdges_card_le_degree x v)).trans (hdegree v hv)

/-- The actual capped exceptional row has the manuscript's `7/4` mean
margin. All mean and variance hypotheses are derived from the graph sample. -/
theorem capped_row_mean (D : ι → Finset V)
    (hdisj : ∀ i j, i ≠ j → Disjoint (D i) (D j))
    (B : Finset V) (hcover : univ.biUnion D = B)
    (s : ι → ℕ) (hs : ∀ i, s i ≤ (D i).card)
    (p₀ : ℝ) (hfraction : ∀ i, (s i : ℝ) = p₀ * (D i).card)
    (x : V) (U : Finset V) (lam ell a : ℝ)
    (hp₀ : 0 < p₀) (hlam : 0 < lam) (ha : 0 ≤ a)
    (hdegree : ∀ v ∈ B, (G.degree v : ℝ) ≤ a)
    (hc : 0 < ((G.edgesTo x U).card : ℝ))
    (hdc : ((G.edgesTo x B).card : ℝ) ≤ (G.edgesTo x U).card / 2)
    (hell_lower : (59 / 64 : ℝ) * lam * (G.edgesTo x U).card ≤ ell)
    (hell_upper : ell ≤ (15 / 16 : ℝ) * lam * (G.edgesTo x U).card)
    (ha_upper : a ≤ p₀ * (G.edgesTo x U).card / 4096) :
    (7 / 4 : ℝ) * lam * (G.edgesTo x B).card ≤
      mean (piWeight (fun i => Hypergeometric.weight (E := D i) (s i)))
        (fun τ => min ((64 * lam / p₀) * (G.edgesTo x (sampledBlock D τ)).card) ell) := by
  have hω : 0 < 64 * lam / p₀ := by positivity
  have hell : 0 < ell := lt_of_lt_of_le (by positivity) hell_lower
  have hmean := mean_edgesTo G D hdisj B hcover s hs p₀ hfraction x
  have hvar := variance_edgesTo_le_of_degree G D hdisj B hcover s hs p₀ hfraction x a hdegree
  rw [← hmean] at hvar
  apply correction_capped_mean_lower
    (piWeight (fun i => Hypergeometric.weight (E := D i) (s i)))
    (piWeight_nonneg _ (fun i => Hypergeometric.weight_nonneg _))
    (sum_piWeight _ (fun i => Hypergeometric.sum_weight _
      (by simpa only [Fintype.card_coe] using hs i)))
    (fun τ => ((G.edgesTo x (sampledBlock D τ)).card : ℝ)) (fun _ => Nat.cast_nonneg _)
    p₀ (G.edgesTo x B).card (G.edgesTo x U).card lam (64 * lam / p₀) ell a
    hp₀ (Nat.cast_nonneg _) hc hlam.le hω hell ha hmean hvar hdc hell_lower _ ha_upper
  apply (div_le_iff₀ hω).mpr
  have heq : (15 / 1024 : ℝ) * p₀ * (G.edgesTo x U).card * (64 * lam / p₀) =
      (15 / 16 : ℝ) * lam * (G.edgesTo x U).card := by
    field_simp
    ring
  rw [heq]
  exact hell_upper

end Overfull.BipartiteFactorization.BlockRowMoments
