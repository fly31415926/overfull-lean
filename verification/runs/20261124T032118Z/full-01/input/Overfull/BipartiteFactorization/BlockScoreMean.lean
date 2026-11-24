import Overfull.BipartiteFactorization.BlockProductSampling
import Overfull.BipartiteFactorization.BlockMembership
import Overfull.BipartiteFactorization.BlockRowMoments
import Overfull.Probability.CappedMean

/-!
# Expected correction scores and actual good blocks

The correction score counts original internal edge copies and capped
exceptional rows. Its mean is assembled from their actual sampling laws;
the existing product variance then gives a quantitative lower tail.
-/

noncomputable section

namespace Overfull.BipartiteFactorization.BlockScoreMean

open Finset Classical FiniteProbability BlockProductSampling

variable {V E Ω ι : Type*} [Fintype E] [Fintype Ω] [Fintype ι]

/-- Linearity of the actual capped graph score, with one term per
original exceptional vertex. -/
theorem mean_cappedScore (G : Multigraph V E) (Z : Finset V)
    (ell : V → ℝ) (ω₁ ω₂ : ℝ) (p : Ω → ℝ) (T : Ω → Finset V) :
    mean p (fun τ => BlockSampling.cappedScore G Z ell ω₁ ω₂ (T τ)) =
      ω₂ * mean p (fun τ => (G.internalEdges (T τ)).card) +
        ∑ x ∈ Z, mean p (fun τ => min (ω₁ * (G.edgesTo x (T τ)).card) (ell x)) := by
  simp only [BlockSampling.cappedScore, mean_add, mean_mul_left]
  congr 1
  simp only [mean, Finset.mul_sum]
  exact Finset.sum_comm

/-- Summing the original exceptional rows counts every cross copy once. -/
theorem sum_rows_eq_cross (G : Multigraph V E) (B Z : Finset V)
    (hBZ : Disjoint B Z) :
    (∑ x ∈ Z, ((G.edgesTo x B).card : ℝ)) = (betweenCopies G Z B).card := by
  have h := BlockSampling.cross_degree_sum G Z B hBZ.symm
  rw [BlockSampling.betweenCopies_symm G B Z] at h
  exact_mod_cast h

/-- The finite accounting step that combines internal-copy and row means.
The product-sampling application below proves both moment premises. -/
theorem cappedScore_mean_of_counts (G : Multigraph V E) (B Z : Finset V)
    (hBZ : Disjoint B Z) (ell : V → ℝ) (p : Ω → ℝ) (T : Ω → Finset V)
    (p₀ lam : ℝ) (hp₀ : 0 < p₀) (hlam : 0 ≤ lam)
    (hinternal : p₀ ^ 2 / 2 * (G.internalEdges B).card ≤
      mean p (fun τ => (G.internalEdges (T τ)).card))
    (hrow : ∀ x ∈ Z, (7 / 4 : ℝ) * lam * (G.edgesTo x B).card ≤
      mean p (fun τ => min ((64 * lam / p₀) * (G.edgesTo x (T τ)).card) (ell x))) :
    (7 / 4 : ℝ) * lam * (correctionPool G B Z).card ≤
      mean p (fun τ => BlockSampling.cappedScore G Z ell
        (64 * lam / p₀) (64 * lam / p₀ ^ 2) (T τ)) := by
  rw [mean_cappedScore]
  have hi := mul_le_mul_of_nonneg_left hinternal
    (show 0 ≤ 64 * lam / p₀ ^ 2 by positivity)
  have hfactor : (64 * lam / p₀ ^ 2) * (p₀ ^ 2 / 2) = 32 * lam := by
    field_simp
    ring
  have hi' : 32 * lam * (G.internalEdges B).card ≤
      (64 * lam / p₀ ^ 2) * mean p (fun τ => (G.internalEdges (T τ)).card) := by
    simpa only [← mul_assoc, hfactor] using hi
  have hz := Finset.sum_le_sum (s := Z) hrow
  rw [← Finset.mul_sum, sum_rows_eq_cross G B Z hBZ] at hz
  rw [BlockSampling.correction_pool_card G B Z hBZ, Nat.cast_add]
  have hnonneg : 0 ≤ lam * (G.internalEdges B).card := by positivity
  nlinarith only [hi', hz, hnonneg]

/-- An event of probability below one has a good outcome in the actual
support. This avoids obtaining a zero-weight tuple of wrong sample sizes. -/
theorem exists_support_not_of_probability_lt_one
    (p : Ω → ℝ) (hp : ∀ τ, 0 ≤ p τ) (hpsum : (∑ τ, p τ) = 1)
    (bad : Ω → Prop) (hbad : MatchingProbability.probability p bad < 1) :
    ∃ τ, 0 < p τ ∧ ¬ bad τ := by
  by_contra h
  have hall : ∀ τ, 0 < p τ → bad τ := by
    intro τ hτ
    by_contra hn
    exact h ⟨τ, hτ, hn⟩
  have heq : MatchingProbability.probability p bad = 1 := by
    unfold MatchingProbability.probability
    rw [Finset.sum_filter]
    calc
      (∑ τ, if bad τ then p τ else 0) = ∑ τ, p τ := by
        apply Finset.sum_congr rfl
        intro τ _
        by_cases hb : bad τ
        · simp only [if_pos hb]
        · have hz : p τ = 0 := le_antisymm
            (le_of_not_gt (fun hpos => hb (hall τ hpos))) (hp τ)
          simp only [if_neg hb, hz]
      _ = 1 := hpsum
  exact (ne_of_lt hbad) heq

/-- A nonzero product sample has the prescribed size in every part. -/
theorem sample_card_of_weight_ne_zero (D : ι → Finset V) (s : ι → ℕ)
    (τ : ∀ i, Finset (D i))
    (hτ : piWeight (fun i => Hypergeometric.weight (E := ↥(D i)) (s i)) τ ≠ 0) :
    ∀ i, (τ i).card = s i := by
  intro i
  by_contra hi
  have hz : Hypergeometric.weight (s i) (τ i) = 0 := by
    simp only [Hypergeometric.weight, if_neg hi]
  apply hτ
  unfold piWeight
  exact Finset.prod_eq_zero (Finset.mem_univ i) hz

/-- The full score mean for actual independent part samples. Internal
edge-copy probabilities and exceptional-row moments are proved inputs of
the development, not premises of this graph theorem. -/
theorem cappedScore_product_mean (G : Multigraph V E)
    (D : ι → Finset V) (hdisj : ∀ i j, i ≠ j → Disjoint (D i) (D j))
    (B Z U : Finset V) (hcover : univ.biUnion D = B) (hBZ : Disjoint B Z)
    (s : ι → ℕ) (hs : ∀ i, s i ≤ (D i).card)
    (p₀ lam a : ℝ) (hp₀ : 0 < p₀) (hlam : 0 < lam) (ha : 0 ≤ a)
    (hfraction : ∀ i, (s i : ℝ) = p₀ * (D i).card)
    (hselect : ∀ i, (D i).Nonempty → 2 ≤ s i)
    (hdegree : ∀ v ∈ B, (G.degree v : ℝ) ≤ a) (ell : V → ℝ)
    (hc : ∀ x ∈ Z, 0 < ((G.edgesTo x U).card : ℝ))
    (hdc : ∀ x ∈ Z, ((G.edgesTo x B).card : ℝ) ≤ (G.edgesTo x U).card / 2)
    (hell_lower : ∀ x ∈ Z, (59 / 64 : ℝ) * lam * (G.edgesTo x U).card ≤ ell x)
    (hell_upper : ∀ x ∈ Z, ell x ≤ (15 / 16 : ℝ) * lam * (G.edgesTo x U).card)
    (ha_upper : ∀ x ∈ Z, a ≤ p₀ * (G.edgesTo x U).card / 4096) :
    (7 / 4 : ℝ) * lam * (correctionPool G B Z).card ≤
      mean (piWeight (fun i => Hypergeometric.weight (E := ↥(D i)) (s i)))
        (fun τ => BlockSampling.cappedScore G Z ell
          (64 * lam / p₀) (64 * lam / p₀ ^ 2) (sampledBlock D τ)) := by
  apply cappedScore_mean_of_counts G B Z hBZ ell
    (piWeight (fun i => Hypergeometric.weight (E := ↥(D i)) (s i)))
    (sampledBlock D) p₀ lam hp₀ hlam.le
  · exact mean_internalEdges_ge G D hdisj B hcover s hs p₀ hfraction hselect
  · intro x hx
    exact BlockRowMoments.capped_row_mean G D hdisj B hcover s hs p₀ hfraction
      x U lam (ell x) a hp₀ hlam ha hdegree (hc x hx) (hdc x hx)
      (hell_lower x hx) (hell_upper x hx) (ha_upper x hx)

/-- The graph-specific lower tail, with both the mean and variance
derived from the original multigraph and the actual part sampling. -/
theorem cappedScore_product_lower_tail (G : Multigraph V E)
    (D : ι → Finset V) (hdisj : ∀ i j, i ≠ j → Disjoint (D i) (D j))
    (B Z U : Finset V) (hcover : univ.biUnion D = B) (hBZ : Disjoint B Z)
    (s : ι → ℕ) (hs : ∀ i, s i ≤ (D i).card)
    (p₀ lam a : ℝ) (hp₀ : 0 < p₀) (hp₀1 : p₀ ≤ 1)
    (hlam : 0 < lam) (ha : 0 ≤ a)
    (hfraction : ∀ i, (s i : ℝ) = p₀ * (D i).card)
    (hselect : ∀ i, (D i).Nonempty → 2 ≤ s i)
    (hdegree : ∀ v ∈ B, (G.degree v : ℝ) ≤ a) (ell : V → ℝ)
    (hc : ∀ x ∈ Z, 0 < ((G.edgesTo x U).card : ℝ))
    (hdc : ∀ x ∈ Z, ((G.edgesTo x B).card : ℝ) ≤ (G.edgesTo x U).card / 2)
    (hell_lower : ∀ x ∈ Z, (59 / 64 : ℝ) * lam * (G.edgesTo x U).card ≤ ell x)
    (hell_upper : ∀ x ∈ Z, ell x ≤ (15 / 16 : ℝ) * lam * (G.edgesTo x U).card)
    (ha_upper : ∀ x ∈ Z, a ≤ p₀ * (G.edgesTo x U).card / 4096)
    (hM : 0 < (correctionPool G B Z).card) :
    MatchingProbability.probability
      (piWeight (fun i => Hypergeometric.weight (E := ↥(D i)) (s i)))
      (fun τ => BlockSampling.cappedScore G Z ell
        (64 * lam / p₀) (64 * lam / p₀ ^ 2) (sampledBlock D τ) <
          (13 / 8 : ℝ) * lam * (correctionPool G B Z).card) ≤
        (2 : ℝ) ^ 21 * a / (p₀ ^ 3 * (correctionPool G B Z).card) := by
  have hD : ∀ i, D i ⊆ B := by
    intro i v hv
    rw [← hcover]
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hv⟩
  have hfractions : ∀ i, (s i : ℝ) / (D i).card ≤ p₀ := by
    intro i
    by_cases hi : (D i).card = 0
    · simp only [hi, Nat.cast_zero, div_zero]
      exact hp₀.le
    · rw [hfraction i, mul_div_cancel_right₀ p₀ (Nat.cast_ne_zero.mpr hi)]
  have hω : 64 * lam / p₀ ≤ 64 * lam / p₀ ^ 2 := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    simpa only [pow_two, mul_one] using mul_le_mul_of_nonneg_left hp₀1 hp₀.le
  apply correction_score_lower_tail
    (piWeight (fun i => Hypergeometric.weight (E := ↥(D i)) (s i)))
    (piWeight_nonneg _ (fun i => Hypergeometric.weight_nonneg _))
    (fun τ => BlockSampling.cappedScore G Z ell
      (64 * lam / p₀) (64 * lam / p₀ ^ 2) (sampledBlock D τ))
    p₀ lam a (correctionPool G B Z).card hp₀ hlam (by exact_mod_cast hM)
  · exact cappedScore_product_mean G D hdisj B Z U hcover hBZ s hs p₀ lam a
      hp₀ hlam ha hfraction hselect hdegree ell hc hdc hell_lower hell_upper ha_upper
  · exact cappedScore_product_variance G D hdisj B Z hD hBZ s hs
      p₀ hp₀.le hfractions ell (64 * lam / p₀) (64 * lam / p₀ ^ 2)
      a (by positivity) hω ha hdegree

/-- A sufficient actual pool size yields a block with the prescribed
part sizes and the required correction score. The sample is selected in
the positive support of the product law. -/
theorem exists_block_large_score (G : Multigraph V E)
    (D : ι → Finset V) (hdisj : ∀ i j, i ≠ j → Disjoint (D i) (D j))
    (B Z U : Finset V) (hcover : univ.biUnion D = B) (hBZ : Disjoint B Z)
    (s : ι → ℕ) (hs : ∀ i, s i ≤ (D i).card)
    (p₀ lam a : ℝ) (hp₀ : 0 < p₀) (hp₀1 : p₀ ≤ 1)
    (hlam : 0 < lam) (ha : 0 ≤ a)
    (hfraction : ∀ i, (s i : ℝ) = p₀ * (D i).card)
    (hselect : ∀ i, (D i).Nonempty → 2 ≤ s i)
    (hdegree : ∀ v ∈ B, (G.degree v : ℝ) ≤ a) (ell : V → ℝ)
    (hc : ∀ x ∈ Z, 0 < ((G.edgesTo x U).card : ℝ))
    (hdc : ∀ x ∈ Z, ((G.edgesTo x B).card : ℝ) ≤ (G.edgesTo x U).card / 2)
    (hell_lower : ∀ x ∈ Z, (59 / 64 : ℝ) * lam * (G.edgesTo x U).card ≤ ell x)
    (hell_upper : ∀ x ∈ Z, ell x ≤ (15 / 16 : ℝ) * lam * (G.edgesTo x U).card)
    (ha_upper : ∀ x ∈ Z, a ≤ p₀ * (G.edgesTo x U).card / 4096)
    (hM : 0 < (correctionPool G B Z).card)
    (hbudget : (2 : ℝ) ^ 21 * a < p₀ ^ 3 * (correctionPool G B Z).card) :
    ∃ τ : ∀ i, Finset (D i), (∀ i, (τ i).card = s i) ∧
      (13 / 8 : ℝ) * lam * (correctionPool G B Z).card ≤
        BlockSampling.cappedScore G Z ell
          (64 * lam / p₀) (64 * lam / p₀ ^ 2) (sampledBlock D τ) := by
  have htail := cappedScore_product_lower_tail G D hdisj B Z U hcover hBZ
    s hs p₀ lam a hp₀ hp₀1 hlam ha hfraction hselect hdegree ell hc hdc
    hell_lower hell_upper ha_upper hM
  have hMreal : (0 : ℝ) < (correctionPool G B Z).card := by exact_mod_cast hM
  have hprob := htail.trans_lt ((div_lt_one (by positivity)).mpr hbudget)
  obtain ⟨τ, hτ, hgood⟩ := exists_support_not_of_probability_lt_one
    (piWeight (fun i => Hypergeometric.weight (E := ↥(D i)) (s i)))
    (piWeight_nonneg _ (fun i => Hypergeometric.weight_nonneg _))
    (sum_piWeight _ (fun i => Hypergeometric.sum_weight _
      (by simpa only [Fintype.card_coe] using hs i))) _ hprob
  exact ⟨τ, sample_card_of_weight_ne_zero D s τ (ne_of_gt hτ), le_of_not_gt hgood⟩

end Overfull.BipartiteFactorization.BlockScoreMean
