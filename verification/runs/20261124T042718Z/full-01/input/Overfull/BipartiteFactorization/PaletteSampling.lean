import Overfull.BipartiteFactorization.PaletteRows
import Overfull.Probability.WeightedSampling
import Overfull.Probability.PermutationSampling

/-!
# Sampling actual allowed palette labels and their edge-copy demands

The population is the subtype of the actual allowed-color set. The sampling
fraction is therefore the selected size divided by that set's cardinality.
Pool weights count original copies, and their weighted sampled sum is proved
to be the actual palette-pool intersection count.
-/

noncomputable section

namespace Overfull.BipartiteFactorization.PaletteSampling

open Finset Classical FiniteProbability

variable {V E : Type*} [Fintype E] {G : Multigraph V E} {k : ℕ}

/-- Lift a subset of the allowed-color subtype to its original color labels. -/
def liftPalette (C : Finset (Fin k)) (T : Finset C) : Finset (Fin k) :=
  T.map (Function.Embedding.subtype (fun i => i ∈ C))

omit [Fintype E] in
@[simp] theorem mem_liftPalette (C : Finset (Fin k)) (T : Finset C) (i : Fin k) :
    i ∈ liftPalette C T ↔ ∃ hi : i ∈ C, (⟨i, hi⟩ : C) ∈ T := by
  simp only [liftPalette, Finset.mem_map, Function.Embedding.coe_subtype]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j.property, hj⟩
  · rintro ⟨hi, hj⟩
    exact ⟨⟨i, hi⟩, hj, rfl⟩

omit [Fintype E] in
theorem liftPalette_subset (C : Finset (Fin k)) (T : Finset C) :
    liftPalette C T ⊆ C := by
  intro i hi
  exact ((mem_liftPalette C T i).mp hi).choose

omit [Fintype E] in
@[simp] theorem liftPalette_card (C : Finset (Fin k)) (T : Finset C) :
    (liftPalette C T).card = T.card := Finset.card_map _

omit [Fintype E] in
theorem liftPalette_disjoint (C : Finset (Fin k)) (S T : Finset C)
    (hST : Disjoint S T) : Disjoint (liftPalette C S) (liftPalette C T) := by
  apply Finset.disjoint_left.mpr
  intro i hiS hiT
  obtain ⟨hi, hS⟩ := (mem_liftPalette C S i).mp hiS
  obtain ⟨hi', hT⟩ := (mem_liftPalette C T i).mp hiT
  exact Finset.disjoint_left.mp hST hS hT

omit [Fintype E] in
@[simp] theorem liftPalette_univ (C : Finset (Fin k)) :
    liftPalette C univ = C := by
  ext i
  simp only [mem_liftPalette, Finset.mem_univ, exists_prop, and_true]

/-- The real weight of one original label is its number of copies in the pool. -/
def poolColorWeight (c : G.EdgeColoring k) (P : Finset E) (i : Fin k) : ℝ :=
  (P.filter (fun e => c.color e = i)).card

omit [Fintype E] in
theorem poolColorWeight_nonneg (c : G.EdgeColoring k) (P : Finset E) (i : Fin k) :
    0 ≤ poolColorWeight c P i := Nat.cast_nonneg _

/-- Partition actual pool copies by their selected original label. -/
theorem palette_pool_card_eq_sum (c : G.EdgeColoring k)
    (I : Finset (Fin k)) (P : Finset E) :
    (paletteEdges c I ∩ P).card =
      ∑ i ∈ I, (P.filter (fun e => c.color e = i)).card := by
  have hmap : (paletteEdges c I ∩ P).toSet.MapsTo c.color I := by
    intro e he
    exact (mem_paletteEdges c I e).mp (Finset.mem_inter.mp he).1
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  ext e
  simp only [Finset.mem_filter, Finset.mem_inter, mem_paletteEdges]
  constructor
  · rintro ⟨⟨_, heP⟩, hei⟩
    exact ⟨heP, hei⟩
  · rintro ⟨heP, hei⟩
    exact ⟨⟨hei ▸ hi, heP⟩, hei⟩

/-- The actual demand on a pool from one sampled allowed-color subset. -/
def poolDemand (c : G.EdgeColoring k) (C : Finset (Fin k)) (P : Finset E)
    (T : Finset C) : ℝ :=
  (paletteEdges c (liftPalette C T) ∩ P).card

/-- The weighted statistic is exactly the count of the selected original copies. -/
theorem poolDemand_eq_weightedSum (c : G.EdgeColoring k)
    (C : Finset (Fin k)) (P : Finset E) (T : Finset C) :
    poolDemand c C P T =
      Hypergeometric.weightedSum (fun i : C => poolColorWeight c P i.val) T := by
  simp only [poolDemand, palette_pool_card_eq_sum, Nat.cast_sum,
    liftPalette, Finset.sum_map, Function.Embedding.coe_subtype,
    Hypergeometric.weightedSum, poolColorWeight]

/-- The total weight of all allowed labels counts exactly the allowed pool copies. -/
theorem sum_allowed_pool_weights (c : G.EdgeColoring k)
    (C : Finset (Fin k)) (P : Finset E) :
    (∑ i : C, poolColorWeight c P i.val) = (paletteEdges c C ∩ P).card := by
  have h := poolDemand_eq_weightedSum c C P univ
  simpa only [poolDemand, liftPalette_univ, Hypergeometric.weightedSum] using h.symm

/-- Exact mean under uniform sampling from the actual allowed population. -/
theorem mean_poolDemand (c : G.EdgeColoring k) (C : Finset (Fin k))
    (P : Finset E) (s : ℕ) (hs : s ≤ C.card) :
    mean (Hypergeometric.weight s) (poolDemand c C P) =
      ((s : ℝ) / C.card) * (paletteEdges c C ∩ P).card := by
  have hfun : poolDemand c C P =
      Hypergeometric.weightedSum (fun i : C => poolColorWeight c P i.val) :=
    funext (poolDemand_eq_weightedSum c C P)
  rw [hfun, Hypergeometric.mean_weightedSum s (by simpa using hs),
    sum_allowed_pool_weights]
  simp only [Fintype.card_coe]

/-- Discarding the allowed restriction gives the original-pool mean bound. -/
theorem mean_poolDemand_le (c : G.EdgeColoring k) (C : Finset (Fin k))
    (P : Finset E) (s : ℕ) (hs : s ≤ C.card) :
    mean (Hypergeometric.weight s) (poolDemand c C P) ≤
      ((s : ℝ) / C.card) * P.card := by
  rw [mean_poolDemand c C P s hs]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact_mod_cast Finset.card_le_card (Finset.inter_subset_right : paletteEdges c C ∩ P ⊆ P)

/-- Bounded per-color copy weights control variance by maximum weight times
mean, with the actual allowed-color sampling law. -/
theorem variance_poolDemand_le_max_mul_mean (c : G.EdgeColoring k)
    (C : Finset (Fin k)) (P : Finset E) (s : ℕ) (hs : s ≤ C.card)
    (M : ℝ) (hM : ∀ i ∈ C, poolColorWeight c P i ≤ M) :
    variance (Hypergeometric.weight s) (poolDemand c C P) ≤
      M * mean (Hypergeometric.weight s) (poolDemand c C P) := by
  have hfun : poolDemand c C P =
      Hypergeometric.weightedSum (fun i : C => poolColorWeight c P i.val) :=
    funext (poolDemand_eq_weightedSum c C P)
  rw [hfun]
  exact Hypergeometric.variance_weightedSum_le_max_mul_mean s (by simpa using hs)
    (fun i : C => poolColorWeight c P i.val) M
    (fun i => poolColorWeight_nonneg c P i.val) (fun i => hM i.val i.property)

theorem variance_poolDemand_le (c : G.EdgeColoring k)
    (C : Finset (Fin k)) (P : Finset E) (s : ℕ) (hs : s ≤ C.card)
    (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ i ∈ C, poolColorWeight c P i ≤ M) :
    variance (Hypergeometric.weight s) (poolDemand c C P) ≤
      M * (((s : ℝ) / C.card) * P.card) := by
  exact (variance_poolDemand_le_max_mul_mean c C P s hs M hM).trans
    (mul_le_mul_of_nonneg_left (mean_poolDemand_le c C P s hs) hM0)

/-- Every event of the actual pool demand has the same marginal law under
one uniform permutation of the actual allowed-label population. -/
theorem probability_permuted_poolDemand (c : G.EdgeColoring k)
    (C : Finset (Fin k)) (P : Finset E) (S : Finset C) (Q : ℝ → Prop) :
    PermutationSampling.probability
      (fun σ => Q (poolDemand c C P (PermutationSampling.sample S σ))) =
        Hypergeometric.probability S.card (fun T => Q (poolDemand c C P T)) :=
  PermutationSampling.probability_sample S (fun T => Q (poolDemand c C P T))

omit [Fintype E] in
/-- Lift a simultaneous family of good disjoint samples from the actual
allowed-label subtype to disjoint palettes of the original labels. -/
theorem exists_disjoint_allowed_palettes {ι : Type*} [Fintype ι]
    (C : Finset (Fin k)) (n : ι → ℕ) (hn : (∑ i, n i) ≤ C.card)
    (bad : ι → Finset (Fin k) → Prop) (ε : ι → ℝ)
    (hbad : ∀ i, Hypergeometric.probability (n i)
      (fun T : Finset C => bad i (liftPalette C T)) ≤ ε i)
    (hε : (∑ i, ε i) < 1) :
    ∃ I : ι → Finset (Fin k),
      (∀ i, I i ⊆ C) ∧ (∀ i, (I i).card = n i) ∧
      (∀ i j, i ≠ j → Disjoint (I i) (I j)) ∧ ∀ i, ¬ bad i (I i) := by
  obtain ⟨T, hcard, hdisj, hgood⟩ := PermutationSampling.exists_disjoint_samples n
    (by simpa using hn) (fun i T => bad i (liftPalette C T)) ε hbad hε
  refine ⟨fun i => liftPalette C (T i), fun i => liftPalette_subset C (T i),
    fun i => (liftPalette_card C (T i)).trans (hcard i), ?_, hgood⟩
  intro i j hij
  exact liftPalette_disjoint C (T i) (T j) (hdisj i j hij)

end Overfull.BipartiteFactorization.PaletteSampling
