import Overfull.BipartiteFactorization.PreferredSampling
import Overfull.BipartiteFactorization.BlockScoreMean

/-!
# Actual good blocks from a graph-derived failure budget

Ordinary preferred rows, special preferred rows, and the correction score are
controlled in one product experiment. The three sets of vertices are separate:
only the correction vertices must be disjoint from the sampled side.
Every probability estimate is derived from graph hypotheses before the union
bound is applied. A budget below one gives a positive-support sample, and hence
the prescribed cardinality in every component of the partition.
-/

noncomputable section

namespace Overfull.BipartiteFactorization.BlockSelectionBudget

open Finset Classical FiniteProbability BlockProductSampling

variable {V E : Type*} [Fintype E]

/-- An ordinary row fails when too few of its actual representative copies
meet the selected block. -/
def ordinaryBad (G : Multigraph V E) (U : Finset V) (F : V → Finset E)
    (β p₀ : ℝ) (T : Finset V) (x : V) : Prop :=
  ((F x ∩ G.edgesTo x T).card : ℝ) < β * p₀ * (G.edgesTo x U).card / 8

/-- A special row uses all original copies incident with the selected block. -/
def specialBad (G : Multigraph V E) (U : Finset V)
    (p₀ : ℝ) (T : Finset V) (x : V) : Prop :=
  ((G.edgesTo x T).card : ℝ) < p₀ * (G.edgesTo x U).card / 3

/-- The required lower bound for the capped correction score. -/
def scoreBad (G : Multigraph V E) (B Zcorr : Finset V)
    (p₀ lam : ℝ) (ell : V → ℝ) (T : Finset V) : Prop :=
  BlockSampling.cappedScore G Zcorr ell (64 * lam / p₀) (64 * lam / p₀ ^ 2) T <
    (13 / 8 : ℝ) * lam * (correctionPool G B Zcorr).card

/-- The union of all ordinary, special, and correction-score failures. -/
def bad (G : Multigraph V E) (B U Wo Ws Zcorr : Finset V)
    (F : V → Finset E) (β p₀ lam : ℝ) (ell : V → ℝ) (T : Finset V) : Prop :=
  (∃ x ∈ Wo, ordinaryBad G U F β p₀ T x) ∨
    (∃ x ∈ Ws, specialBad G U p₀ T x) ∨ scoreBad G B Zcorr p₀ lam ell T

/-- The explicit numerical budget for one side. The palette fraction and row
caps affect the score hypotheses, but cancel from this probability bound. -/
def failureBudget (G : Multigraph V E) (B U Wo Ws Zcorr : Finset V)
    (β p₀ a : ℝ) : ℝ :=
  (∑ x ∈ Wo, Real.exp (-β * p₀ * (G.edgesTo x U).card / 48)) +
    ((∑ x ∈ Ws, 18 * a / (p₀ * (G.edgesTo x U).card)) +
      (2 : ℝ) ^ 21 * a / (p₀ ^ 3 * (correctionPool G B Zcorr).card))

/-- All three actual graph inequalities required from a selected block. -/
def GoodBlock (G : Multigraph V E) (B U Wo Ws Zcorr : Finset V)
    (F : V → Finset E) (β p₀ lam : ℝ) (ell : V → ℝ) (T : Finset V) : Prop :=
  (∀ x ∈ Wo, β * p₀ * (G.edgesTo x U).card / 8 ≤
      ((F x ∩ G.edgesTo x T).card : ℝ)) ∧
    (∀ x ∈ Ws, p₀ * (G.edgesTo x U).card / 3 ≤
      ((G.edgesTo x T).card : ℝ)) ∧
    (13 / 8 : ℝ) * lam * (correctionPool G B Zcorr).card ≤
      BlockSampling.cappedScore G Zcorr ell (64 * lam / p₀) (64 * lam / p₀ ^ 2) T

theorem not_bad_iff_goodBlock (G : Multigraph V E) (B U Wo Ws Zcorr : Finset V)
    (F : V → Finset E) (β p₀ lam : ℝ) (ell : V → ℝ) (T : Finset V) :
    ¬ bad G B U Wo Ws Zcorr F β p₀ lam ell T ↔
      GoodBlock G B U Wo Ws Zcorr F β p₀ lam ell T := by
  simp only [bad, GoodBlock, ordinaryBad, specialBad, scoreBad,
    not_or, not_exists, not_and, not_lt]

variable {ι : Type*} [Fintype ι]

/-- Combine the actual graph tails in the independent fixed-size part
experiment. No failure probabilities or moment bounds are assumed. Empty
ordinary and special vertex sets are allowed. -/
theorem probability_bad_le (G : Multigraph V E)
    (D : ι → Finset V) (hdisj : ∀ i j, i ≠ j → Disjoint (D i) (D j))
    (B U Wo Ws Zcorr : Finset V) (hcover : univ.biUnion D = B)
    (hBZ : Disjoint B Zcorr) (s : ι → ℕ) (hs : ∀ i, s i ≤ (D i).card)
    (F : V → Finset E) (β p₀ lam a : ℝ)
    (hp₀ : 0 < p₀) (hp₀1 : p₀ ≤ 1) (hlam : 0 < lam) (ha : 0 ≤ a)
    (hfraction : ∀ i, (s i : ℝ) = p₀ * (D i).card)
    (hselect : ∀ i, (D i).Nonempty → 2 ≤ s i)
    (hdegree : ∀ v ∈ B, (G.degree v : ℝ) ≤ a)
    (hF : ∀ x ∈ Wo, F x ⊆ G.edgesTo x B)
    (hinj : ∀ x ∈ Wo, Set.InjOn (G.otherEnd x) (F x))
    (hFsize : ∀ x ∈ Wo, β * (G.edgesTo x U).card / 4 ≤ (F x).card)
    (hspecial_c : ∀ x ∈ Ws, 0 < ((G.edgesTo x U).card : ℝ))
    (hspecial_side : ∀ x ∈ Ws,
      ((G.edgesTo x U).card : ℝ) / 2 ≤ (G.edgesTo x B).card)
    (ell : V → ℝ)
    (hc : ∀ x ∈ Zcorr, 0 < ((G.edgesTo x U).card : ℝ))
    (hdc : ∀ x ∈ Zcorr,
      ((G.edgesTo x B).card : ℝ) ≤ (G.edgesTo x U).card / 2)
    (hell_lower : ∀ x ∈ Zcorr,
      (59 / 64 : ℝ) * lam * (G.edgesTo x U).card ≤ ell x)
    (hell_upper : ∀ x ∈ Zcorr,
      ell x ≤ (15 / 16 : ℝ) * lam * (G.edgesTo x U).card)
    (ha_upper : ∀ x ∈ Zcorr, a ≤ p₀ * (G.edgesTo x U).card / 4096)
    (hM : 0 < (correctionPool G B Zcorr).card) :
    MatchingProbability.probability
      (piWeight (fun i => Hypergeometric.weight (E := ↥(D i)) (s i)))
      (fun τ => bad G B U Wo Ws Zcorr F β p₀ lam ell (sampledBlock D τ)) ≤
      failureBudget G B U Wo Ws Zcorr β p₀ a := by
  have hw := piWeight_nonneg
    (fun i => Hypergeometric.weight (E := ↥(D i)) (s i))
    (fun i => Hypergeometric.weight_nonneg _)
  have hordinary : MatchingProbability.probability
      (piWeight (fun i => Hypergeometric.weight (E := ↥(D i)) (s i)))
      (fun τ => ∃ x ∈ Wo, ordinaryBad G U F β p₀ (sampledBlock D τ) x) ≤
      ∑ x ∈ Wo, Real.exp (-β * p₀ * (G.edgesTo x U).card / 48) := by
    calc
      _ ≤ ∑ x ∈ Wo, MatchingProbability.probability
          (piWeight (fun i => Hypergeometric.weight (E := ↥(D i)) (s i)))
          (fun τ => ordinaryBad G U F β p₀ (sampledBlock D τ) x) :=
        MatchingProbability.probability_exists_le_sum _ hw Wo
          (fun x τ => ordinaryBad G U F β p₀ (sampledBlock D τ) x)
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro x hx
        simpa only [ordinaryBad] using
          PreferredSampling.representative_edges_lower_tail G D hdisj B hcover
            s hs p₀ hp₀.le hfraction x (F x) (hF x hx) (hinj x hx)
            β (G.edgesTo x U).card (hFsize x hx)
  have hspecial : MatchingProbability.probability
      (piWeight (fun i => Hypergeometric.weight (E := ↥(D i)) (s i)))
      (fun τ => ∃ x ∈ Ws, specialBad G U p₀ (sampledBlock D τ) x) ≤
      ∑ x ∈ Ws, 18 * a / (p₀ * (G.edgesTo x U).card) := by
    calc
      _ ≤ ∑ x ∈ Ws, MatchingProbability.probability
          (piWeight (fun i => Hypergeometric.weight (E := ↥(D i)) (s i)))
          (fun τ => specialBad G U p₀ (sampledBlock D τ) x) :=
        MatchingProbability.probability_exists_le_sum _ hw Ws
          (fun x τ => specialBad G U p₀ (sampledBlock D τ) x)
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro x hx
        simpa only [specialBad] using
          PreferredSampling.special_preferred_lower_tail G D hdisj B hcover
            s hs p₀ hp₀ hfraction x U a ha hdegree
            (hspecial_c x hx) (hspecial_side x hx)
  have hscore : MatchingProbability.probability
      (piWeight (fun i => Hypergeometric.weight (E := ↥(D i)) (s i)))
      (fun τ => scoreBad G B Zcorr p₀ lam ell (sampledBlock D τ)) ≤
      (2 : ℝ) ^ 21 * a / (p₀ ^ 3 * (correctionPool G B Zcorr).card) := by
    exact BlockScoreMean.cappedScore_product_lower_tail G D hdisj B Zcorr U
      hcover hBZ s hs p₀ lam a hp₀ hp₀1 hlam ha hfraction hselect hdegree
      ell hc hdc hell_lower hell_upper ha_upper hM
  unfold bad failureBudget
  apply (MatchingProbability.probability_union_le _ hw
    (fun τ => ∃ x ∈ Wo, ordinaryBad G U F β p₀ (sampledBlock D τ) x)
    (fun τ => (∃ x ∈ Ws, specialBad G U p₀ (sampledBlock D τ) x) ∨
      scoreBad G B Zcorr p₀ lam ell (sampledBlock D τ))).trans
  apply add_le_add hordinary
  exact (MatchingProbability.probability_union_le _ hw
    (fun τ => ∃ x ∈ Ws, specialBad G U p₀ (sampledBlock D τ) x)
    (fun τ => scoreBad G B Zcorr p₀ lam ell (sampledBlock D τ))).trans
      (add_le_add hspecial hscore)

/-- A graph-derived budget below one gives a good block in the positive
support of the experiment, with exactly the prescribed size in each part. -/
theorem exists_good_block (G : Multigraph V E)
    (D : ι → Finset V) (hdisj : ∀ i j, i ≠ j → Disjoint (D i) (D j))
    (B U Wo Ws Zcorr : Finset V) (hcover : univ.biUnion D = B)
    (hBZ : Disjoint B Zcorr) (s : ι → ℕ) (hs : ∀ i, s i ≤ (D i).card)
    (F : V → Finset E) (β p₀ lam a : ℝ)
    (hp₀ : 0 < p₀) (hp₀1 : p₀ ≤ 1) (hlam : 0 < lam) (ha : 0 ≤ a)
    (hfraction : ∀ i, (s i : ℝ) = p₀ * (D i).card)
    (hselect : ∀ i, (D i).Nonempty → 2 ≤ s i)
    (hdegree : ∀ v ∈ B, (G.degree v : ℝ) ≤ a)
    (hF : ∀ x ∈ Wo, F x ⊆ G.edgesTo x B)
    (hinj : ∀ x ∈ Wo, Set.InjOn (G.otherEnd x) (F x))
    (hFsize : ∀ x ∈ Wo, β * (G.edgesTo x U).card / 4 ≤ (F x).card)
    (hspecial_c : ∀ x ∈ Ws, 0 < ((G.edgesTo x U).card : ℝ))
    (hspecial_side : ∀ x ∈ Ws,
      ((G.edgesTo x U).card : ℝ) / 2 ≤ (G.edgesTo x B).card)
    (ell : V → ℝ)
    (hc : ∀ x ∈ Zcorr, 0 < ((G.edgesTo x U).card : ℝ))
    (hdc : ∀ x ∈ Zcorr,
      ((G.edgesTo x B).card : ℝ) ≤ (G.edgesTo x U).card / 2)
    (hell_lower : ∀ x ∈ Zcorr,
      (59 / 64 : ℝ) * lam * (G.edgesTo x U).card ≤ ell x)
    (hell_upper : ∀ x ∈ Zcorr,
      ell x ≤ (15 / 16 : ℝ) * lam * (G.edgesTo x U).card)
    (ha_upper : ∀ x ∈ Zcorr, a ≤ p₀ * (G.edgesTo x U).card / 4096)
    (hM : 0 < (correctionPool G B Zcorr).card)
    (hbudget : failureBudget G B U Wo Ws Zcorr β p₀ a < 1) :
    ∃ τ : ∀ i, Finset (D i),
      0 < piWeight (fun i => Hypergeometric.weight (E := ↥(D i)) (s i)) τ ∧
      (∀ i, (τ i).card = s i) ∧
      GoodBlock G B U Wo Ws Zcorr F β p₀ lam ell (sampledBlock D τ) := by
  have htail := probability_bad_le G D hdisj B U Wo Ws Zcorr hcover hBZ
    s hs F β p₀ lam a hp₀ hp₀1 hlam ha hfraction hselect hdegree
    hF hinj hFsize hspecial_c hspecial_side ell hc hdc
    hell_lower hell_upper ha_upper hM
  obtain ⟨τ, hτ, hgood⟩ := BlockScoreMean.exists_support_not_of_probability_lt_one
    (piWeight (fun i => Hypergeometric.weight (E := ↥(D i)) (s i)))
    (piWeight_nonneg _ (fun i => Hypergeometric.weight_nonneg _))
    (sum_piWeight _ (fun i => Hypergeometric.sum_weight _
      (by simpa only [Fintype.card_coe] using hs i))) _ (htail.trans_lt hbudget)
  exact ⟨τ, hτ, BlockScoreMean.sample_card_of_weight_ne_zero D s τ (ne_of_gt hτ),
    (not_bad_iff_goodBlock G B U Wo Ws Zcorr F β p₀ lam ell (sampledBlock D τ)).mp hgood⟩

end Overfull.BipartiteFactorization.BlockSelectionBudget
