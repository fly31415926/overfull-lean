import Overfull.Probability.PartitionConcentration
import Overfull.BipartiteFactorization.BlockRowMoments
import Overfull.BipartiteFactorization.Preferred

/-!
# Preferred-edge lower tails in the actual partition sample

Distinct representative endpoints have an exponential lower tail under the
product of uniform fixed-size part laws. The estimate is transported back to
their actual original edge copies. Special vertices instead use the actual
row mean and coefficient-one variance bound, allowing parallel copies.
-/

noncomputable section

namespace Overfull.BipartiteFactorization.PreferredSampling

open Finset Classical FiniteProbability BlockProductSampling

variable {V E ι : Type*} [Fintype ι]

/-- Distinguished endpoints in one part, regarded as members of its actual
finite population subtype. -/
def partRepresentatives (D R : Finset V) : Finset D :=
  univ.filter (fun v => v.val ∈ R)

private theorem part_count (D R : Finset V) (T : Finset D) :
    (Hypergeometric.count (partRepresentatives D R) T : ℝ) =
      ∑ v ∈ T, if v.val ∈ R then 1 else 0 := by
  simpa only [Hypergeometric.count, Finset.inter_comm, partRepresentatives,
    Finset.mem_filter, Finset.mem_univ, true_and] using
      (Hypergeometric.count_eq_sum T (partRepresentatives D R))

/-- The product statistic is exactly the count in the sampled original
vertex union, including outcomes outside the prescribed-size support. -/
theorem representative_count (D : ι → Finset V)
    (hdisj : ∀ i j, i ≠ j → Disjoint (D i) (D j))
    (R : Finset V) (T : ∀ i, Finset (D i)) :
    ((R ∩ sampledBlock D T).card : ℝ) =
      PartitionConcentration.count (fun i => partRepresentatives (D i) R) T := by
  calc
    _ = ∑ v ∈ sampledBlock D T, if v ∈ R then (1 : ℝ) else 0 := by
      simpa only [Hypergeometric.count, Finset.inter_comm] using
        (Hypergeometric.count_eq_sum (sampledBlock D T) R)
    _ = ∑ i, ∑ v ∈ T i, if v.val ∈ R then (1 : ℝ) else 0 :=
      BlockRowMoments.sum_sampledBlock D hdisj T (fun v => if v ∈ R then 1 else 0)
    _ = _ := by
      unfold PartitionConcentration.count
      exact Finset.sum_congr rfl (fun i _ => (part_count (D i) R (T i)).symm)

/-- Each distinguished original endpoint is counted in exactly one part. -/
theorem sum_part_representatives (D : ι → Finset V)
    (hdisj : ∀ i j, i ≠ j → Disjoint (D i) (D j))
    (B : Finset V) (hcover : univ.biUnion D = B)
    (R : Finset V) (hRB : R ⊆ B) :
    (∑ i, ((partRepresentatives (D i) R).card : ℝ)) = R.card := by
  have hpart (i : ι) : ((partRepresentatives (D i) R).card : ℝ) =
      ∑ v : D i, if v.val ∈ R then (1 : ℝ) else 0 := by
    simpa only [Hypergeometric.count, Finset.inter_univ] using
      part_count (D i) R univ
  calc
    _ = ∑ i, ∑ v : D i, if v.val ∈ R then (1 : ℝ) else 0 :=
      Finset.sum_congr rfl (fun i _ => hpart i)
    _ = ∑ v ∈ B, if v ∈ R then (1 : ℝ) else 0 := by
      rw [sum_part_weights D hdisj (fun v => if v ∈ R then (1 : ℝ) else 0), hcover]
    _ = _ := by
      have h := Hypergeometric.count_eq_sum B R
      rw [Hypergeometric.count, Finset.inter_eq_right.mpr hRB] at h
      exact h.symm

/-- Exact equal sampling fractions give the actual representative-count
mean; empty parts are handled without cancelling their cardinalities. -/
theorem expected_representatives (D : ι → Finset V)
    (hdisj : ∀ i j, i ≠ j → Disjoint (D i) (D j))
    (B : Finset V) (hcover : univ.biUnion D = B)
    (s : ι → ℕ) (p₀ : ℝ)
    (hfraction : ∀ i, (s i : ℝ) = p₀ * (D i).card)
    (R : Finset V) (hRB : R ⊆ B) :
    PartitionConcentration.expectedCount s (fun i => partRepresentatives (D i) R) =
      p₀ * R.card := by
  unfold PartitionConcentration.expectedCount
  calc
    _ = ∑ i, p₀ * (partRepresentatives (D i) R).card := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hD : (D i).card = 0
      · have hR : (partRepresentatives (D i) R).card = 0 := by
          have h := Finset.card_le_univ (partRepresentatives (D i) R)
          simpa only [Fintype.card_coe, hD, Nat.le_zero] using h
        simp only [hR, Nat.cast_zero, mul_zero]
      · rw [Fintype.card_coe, hfraction i,
          mul_div_cancel_right₀ p₀ (Nat.cast_ne_zero.mpr hD)]
    _ = p₀ * ∑ i, ((partRepresentatives (D i) R).card : ℝ) := by
      rw [Finset.mul_sum]
    _ = _ := by rw [sum_part_representatives D hdisj B hcover R hRB]

/-- The actual number of selected distinct endpoints has an exponential
half-mean lower tail. This supports a union over linearly many ordinary rows. -/
theorem representative_half_mean_lower_tail (D : ι → Finset V)
    (hdisj : ∀ i j, i ≠ j → Disjoint (D i) (D j))
    (B : Finset V) (hcover : univ.biUnion D = B)
    (s : ι → ℕ) (hs : ∀ i, s i ≤ (D i).card)
    (p₀ : ℝ) (hfraction : ∀ i, (s i : ℝ) = p₀ * (D i).card)
    (R : Finset V) (hRB : R ⊆ B) :
    MatchingProbability.probability
      (piWeight (fun i => Hypergeometric.weight (E := D i) (s i)))
      (fun T => ((R ∩ sampledBlock D T).card : ℝ) < p₀ * R.card / 2) ≤
        Real.exp (-p₀ * R.card / 12) := by
  have h := PartitionConcentration.half_mean_lower_tail s
    (fun i => by simpa only [Fintype.card_coe] using hs i)
    (fun i => partRepresentatives (D i) R)
  rw [expected_representatives D hdisj B hcover s p₀ hfraction R hRB] at h
  simpa only [representative_count D hdisj, neg_mul] using h

/-- A lower bound on the original representative set gives the manuscript's
preferred-endpoint threshold and an explicit exponential failure budget. -/
theorem representative_endpoints_lower_tail (D : ι → Finset V)
    (hdisj : ∀ i j, i ≠ j → Disjoint (D i) (D j))
    (B : Finset V) (hcover : univ.biUnion D = B)
    (s : ι → ℕ) (hs : ∀ i, s i ≤ (D i).card)
    (p₀ : ℝ) (hp₀ : 0 ≤ p₀)
    (hfraction : ∀ i, (s i : ℝ) = p₀ * (D i).card)
    (R : Finset V) (hRB : R ⊆ B) (β c : ℝ)
    (hR : β * c / 4 ≤ R.card) :
    MatchingProbability.probability
      (piWeight (fun i => Hypergeometric.weight (E := D i) (s i)))
      (fun T => ((R ∩ sampledBlock D T).card : ℝ) < β * p₀ * c / 8) ≤
        Real.exp (-β * p₀ * c / 48) := by
  have hscaled := mul_le_mul_of_nonneg_left hR hp₀
  calc
    _ ≤ MatchingProbability.probability
        (piWeight (fun i => Hypergeometric.weight (E := D i) (s i)))
        (fun T => ((R ∩ sampledBlock D T).card : ℝ) < p₀ * R.card / 2) := by
      apply MatchingProbability.probability_mono _
        (piWeight_nonneg _ (fun i => Hypergeometric.weight_nonneg _))
      intro T hT
      nlinarith
    _ ≤ Real.exp (-p₀ * R.card / 12) :=
      representative_half_mean_lower_tail D hdisj B hcover s hs p₀ hfraction R hRB
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

private theorem special_lower_tail_of_moments {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (hw : ∀ T, 0 ≤ w T) (X : Ω → ℝ)
    (p₀ c d a : ℝ) (hp₀ : 0 < p₀) (hc : 0 < c) (ha : 0 ≤ a)
    (hdc : c / 2 ≤ d) (hmean : mean w X = p₀ * d)
    (hvar : variance w X ≤ a * (p₀ * d)) :
    MatchingProbability.probability w (fun T => X T < p₀ * c / 3) ≤
      18 * a / (p₀ * c) := by
  have hd : 0 < d := by linarith
  have hpd : 0 < p₀ * d := mul_pos hp₀ hd
  have hthreshold : p₀ * c / 3 ≤ 2 * (p₀ * d) / 3 := by
    have h := mul_le_mul_of_nonneg_left hdc hp₀.le
    nlinarith
  have htail := lower_tail_of_mean_lower w hw X (p₀ * d) (2 * (p₀ * d) / 3)
    (by nlinarith) hmean.ge
  calc
    _ ≤ MatchingProbability.probability w (fun T => X T < 2 * (p₀ * d) / 3) :=
      MatchingProbability.probability_mono w hw (fun _ h => h.trans_le hthreshold)
    _ ≤ variance w X / (p₀ * d - 2 * (p₀ * d) / 3) ^ 2 := htail
    _ ≤ (a * (p₀ * d)) / (p₀ * d - 2 * (p₀ * d) / 3) ^ 2 :=
      div_le_div_of_nonneg_right hvar (sq_nonneg _)
    _ = 9 * a / (p₀ * d) := by
      rw [show p₀ * d - 2 * (p₀ * d) / 3 = p₀ * d / 3 by ring]
      field_simp [hp₀.ne', hd.ne']
      ring
    _ ≤ _ := by
      apply (div_le_div_iff₀ hpd (mul_pos hp₀ hc)).mpr
      have h := mul_le_mul_of_nonneg_left hdc (mul_nonneg ha hp₀.le)
      nlinarith

variable [Fintype E] (G : Multigraph V E)

/-- The special-vertex lower tail uses the actual multigraph row moments.
Parallel original copies are allowed, with degree control on the sampled side. -/
theorem special_preferred_lower_tail (D : ι → Finset V)
    (hdisj : ∀ i j, i ≠ j → Disjoint (D i) (D j))
    (B : Finset V) (hcover : univ.biUnion D = B)
    (s : ι → ℕ) (hs : ∀ i, s i ≤ (D i).card)
    (p₀ : ℝ) (hp₀ : 0 < p₀)
    (hfraction : ∀ i, (s i : ℝ) = p₀ * (D i).card)
    (x : V) (U : Finset V) (a : ℝ) (ha : 0 ≤ a)
    (hdegree : ∀ v ∈ B, (G.degree v : ℝ) ≤ a)
    (hc : 0 < ((G.edgesTo x U).card : ℝ))
    (hside : ((G.edgesTo x U).card : ℝ) / 2 ≤ (G.edgesTo x B).card) :
    MatchingProbability.probability
      (piWeight (fun i => Hypergeometric.weight (E := D i) (s i)))
      (fun T => ((G.edgesTo x (sampledBlock D T)).card : ℝ) <
        p₀ * (G.edgesTo x U).card / 3) ≤
      18 * a / (p₀ * (G.edgesTo x U).card) := by
  exact special_lower_tail_of_moments _
    (piWeight_nonneg _ (fun i => Hypergeometric.weight_nonneg _)) _
    p₀ (G.edgesTo x U).card (G.edgesTo x B).card a hp₀ hc ha hside
    (BlockRowMoments.mean_edgesTo G D hdisj B hcover s hs p₀ hfraction x)
    (BlockRowMoments.variance_edgesTo_le_of_degree G D hdisj B hcover s hs p₀
      hfraction x a hdegree)

/-- Distinct representative other ends identify sampled original edge copies
exactly with their sampled endpoint set. -/
theorem representative_edges_count (x : V) (B : Finset V) (F : Finset E)
    (hF : F ⊆ G.edgesTo x B) (hinj : Set.InjOn (G.otherEnd x) F) (T : Finset V) :
    (F ∩ G.edgesTo x T).card = (F.image (G.otherEnd x) ∩ T).card := by
  have himage : (F ∩ G.edgesTo x T).image (G.otherEnd x) =
      F.image (G.otherEnd x) ∩ T := by
    ext v
    simp only [Finset.mem_image, Finset.mem_inter]
    constructor
    · rintro ⟨e, ⟨heF, heT⟩, rfl⟩
      exact ⟨⟨e, heF, rfl⟩, ((G.mem_edgesTo x T e).mp heT).2⟩
    · rintro ⟨⟨e, heF, rfl⟩, heT⟩
      exact ⟨e, ⟨heF, (G.mem_edgesTo x T e).mpr
        ⟨((G.mem_edgesTo x B e).mp (hF heF)).1, heT⟩⟩, rfl⟩
  rw [← himage, Finset.card_image_of_injOn (hinj.mono (by
    intro e he
    exact (Finset.mem_inter.mp he).1))]

/-- The ordinary preferred-edge lower tail counts the actual distinguished
copies. Their injective other ends are the representatives in the product
Chernoff argument. -/
theorem representative_edges_lower_tail (D : ι → Finset V)
    (hdisj : ∀ i j, i ≠ j → Disjoint (D i) (D j))
    (B : Finset V) (hcover : univ.biUnion D = B)
    (s : ι → ℕ) (hs : ∀ i, s i ≤ (D i).card)
    (p₀ : ℝ) (hp₀ : 0 ≤ p₀)
    (hfraction : ∀ i, (s i : ℝ) = p₀ * (D i).card)
    (x : V) (F : Finset E) (hF : F ⊆ G.edgesTo x B)
    (hinj : Set.InjOn (G.otherEnd x) F) (β c : ℝ)
    (hFsize : β * c / 4 ≤ F.card) :
    MatchingProbability.probability
      (piWeight (fun i => Hypergeometric.weight (E := D i) (s i)))
      (fun T => ((F ∩ G.edgesTo x (sampledBlock D T)).card : ℝ) <
        β * p₀ * c / 8) ≤
      Real.exp (-β * p₀ * c / 48) := by
  have hRB : F.image (G.otherEnd x) ⊆ B := by
    intro v hv
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hv
    exact ((G.mem_edgesTo x B e).mp (hF he)).2
  have hRsize : β * c / 4 ≤ (F.image (G.otherEnd x)).card := by
    rw [Finset.card_image_of_injOn hinj]
    exact hFsize
  have h := representative_endpoints_lower_tail D hdisj B hcover s hs p₀ hp₀
    hfraction (F.image (G.otherEnd x)) hRB β c hRsize
  simpa only [representative_edges_count G x B F hF hinj] using h

end Overfull.BipartiteFactorization.PreferredSampling
