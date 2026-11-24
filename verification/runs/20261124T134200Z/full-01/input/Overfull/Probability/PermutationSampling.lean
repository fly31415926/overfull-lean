import Overfull.Probability.Hypergeometric
import Overfull.ColoringExtension.Permutation
import Mathlib.Data.Fintype.EquivFin

/-!
# Disjoint fixed-size samples from one uniform permutation

Images of disjoint position sets are disjoint for every permutation. Each
individual image nevertheless has the exact uniform fixed-size subset law.
Consequently marginal probability bounds can be combined by a union bound,
without an independence assumption between the selected samples.
-/

noncomputable section

namespace Overfull.PermutationSampling

open Finset Classical

variable {E : Type*} [Fintype E]

/-- Apply a permutation to actual positions in the finite population. -/
def sample (S : Finset E) (σ : Equiv.Perm E) : Finset E :=
  S.map σ.toEmbedding

omit [Fintype E] in
@[simp] theorem sample_card (S : Finset E) (σ : Equiv.Perm E) :
    (sample S σ).card = S.card := Finset.card_map _

omit [Fintype E] in
@[simp] theorem mem_sample (S : Finset E) (σ : Equiv.Perm E) (x : E) :
    x ∈ sample S σ ↔ σ.symm x ∈ S := by
  simp only [sample, Finset.mem_map, Equiv.toEmbedding_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa only [Equiv.symm_apply_apply] using hy
  · intro hx
    exact ⟨σ.symm x, hx, σ.apply_symm_apply x⟩

omit [Fintype E] in
theorem sample_mul (S : Finset E) (τ σ : Equiv.Perm E) :
    sample S (τ * σ) = sample (sample S σ) τ := by
  ext x
  simp only [mem_sample]
  rfl

omit [Fintype E] in
theorem sample_injective (σ : Equiv.Perm E) :
    Function.Injective (fun S : Finset E => sample S σ) := by
  intro S T h
  ext x
  have hx := congrArg (fun F : Finset E => σ x ∈ F) h
  simpa only [mem_sample, Equiv.symm_apply_apply] using (Iff.of_eq hx)

omit [Fintype E] in
theorem sample_disjoint (S T : Finset E) (σ : Equiv.Perm E) (hST : Disjoint S T) :
    Disjoint (sample S σ) (sample T σ) := by
  apply Finset.disjoint_left.mpr
  intro x hxS hxT
  exact Finset.disjoint_left.mp hST ((mem_sample S σ x).mp hxS)
    ((mem_sample T σ x).mp hxT)

/-- Every target of the same size is the actual image of the position set. -/
theorem exists_sample_eq (S T : Finset E) (hcard : S.card = T.card) :
    ∃ σ : Equiv.Perm E, sample S σ = T := by
  let e : S ≃ T := Fintype.equivOfCardEq (by simpa using hcard)
  let source : S ↪ E := Function.Embedding.subtype (fun x => x ∈ S)
  let target : S ↪ E := e.toEmbedding.trans (Function.Embedding.subtype (fun x => x ∈ T))
  have hc := ColoringExtension.restrictionFiber_card source target
  have hpos : 0 < (ColoringExtension.restrictionFiber source target).card := by
    rw [hc]
    exact Nat.factorial_pos _
  obtain ⟨σ, hσ⟩ := Finset.card_pos.mp hpos
  have hσ' := (ColoringExtension.mem_restrictionFiber source target σ).mp hσ
  refine ⟨σ, ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    have hy' : σ y = (e ⟨y, hy⟩).val := hσ' ⟨y, hy⟩
    exact hy' ▸ (e ⟨y, hy⟩).property
  · intro hx
    let y := e.symm ⟨x, hx⟩
    refine Finset.mem_map.mpr ⟨y.val, y.property, ?_⟩
    change σ y.val = x
    have hy : σ y.val = (e y).val := hσ' y
    rw [hy]
    change (e (e.symm ⟨x, hx⟩)).val = x
    rw [Equiv.apply_symm_apply]

/-- The actual permutations realizing one target sample. -/
def fiber (S T : Finset E) : Finset (Equiv.Perm E) :=
  univ.filter (fun σ => sample S σ = T)

@[simp] theorem mem_fiber (S T : Finset E) (σ : Equiv.Perm E) :
    σ ∈ fiber S T ↔ sample S σ = T := by
  simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Equal-size target fibers are translates of the stabilizer fiber. -/
theorem fiber_card_eq (S T : Finset E) (hcard : S.card = T.card) :
    (fiber S T).card = (fiber S S).card := by
  obtain ⟨τ, hτ⟩ := exists_sample_eq S T hcard
  have hfiber : fiber S T = (fiber S S).image (fun σ => τ * σ) := by
    ext σ
    simp only [mem_fiber, Finset.mem_image]
    constructor
    · intro hσ
      refine ⟨τ⁻¹ * σ, ?_, by simp⟩
      apply (sample_injective τ)
      change sample (sample S (τ⁻¹ * σ)) τ = sample S τ
      rw [← sample_mul, mul_inv_cancel_left, hσ, hτ]
    · rintro ⟨ρ, hρ, rfl⟩
      rw [sample_mul, hρ, hτ]
  rw [hfiber, Finset.card_image_of_injective _ (by
    intro σ ρ h
    exact mul_left_cancel h)]

/-- Partition all permutations by their actual image of a fixed position set. -/
theorem card_perm_eq_choose_mul_fiber (S : Finset E) :
    Fintype.card (Equiv.Perm E) =
      Nat.choose (Fintype.card E) S.card * (fiber S S).card := by
  have hmap : (univ : Finset (Equiv.Perm E)).toSet.MapsTo (sample S)
      ((univ : Finset E).powersetCard S.card) := by
    intro σ _
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, sample_card S σ⟩
  have hcount := Finset.card_eq_sum_card_fiberwise hmap
  calc
    Fintype.card (Equiv.Perm E) =
        ∑ T ∈ (univ : Finset E).powersetCard S.card, (fiber S T).card := hcount
    _ = ∑ _T ∈ (univ : Finset E).powersetCard S.card, (fiber S S).card := by
      apply Finset.sum_congr rfl
      intro T hT
      exact fiber_card_eq S T (Finset.mem_powersetCard.mp hT).2.symm
    _ = _ := by simp

/-- The uniform real weight on all actual permutations. -/
def weight (_σ : Equiv.Perm E) : ℝ :=
  1 / (Fintype.card (Equiv.Perm E) : ℝ)

def probability (P : Equiv.Perm E → Prop) : ℝ :=
  MatchingProbability.probability weight P

theorem weight_nonneg (σ : Equiv.Perm E) : 0 ≤ weight σ := by
  unfold weight
  positivity

theorem sum_weight : (∑ σ : Equiv.Perm E, weight σ) = 1 := by
  have hn : (Fintype.card (Equiv.Perm E) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp only [weight, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- The probability of an individual target is exactly the hypergeometric
sample weight, including empty and full position sets. -/
theorem probability_sample_eq (S T : Finset E) :
    probability (fun σ => sample S σ = T) = Hypergeometric.weight S.card T := by
  have hprob : probability (fun σ => sample S σ = T) =
      ((fiber S T).card : ℝ) / Fintype.card (Equiv.Perm E) := by
    simp only [probability, MatchingProbability.probability, fiber, weight,
      Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv, one_mul]
    congr 3
    ext σ
    simp
  rw [hprob]
  by_cases hcard : T.card = S.card
  · rw [Hypergeometric.weight, if_pos hcard, fiber_card_eq S T hcard.symm]
    have hden : (Fintype.card (Equiv.Perm E) : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    have hchoose : (Nat.choose (Fintype.card E) S.card : ℝ) ≠ 0 := by
      exact_mod_cast Nat.choose_ne_zero (Finset.card_le_univ S)
    apply (div_eq_div_iff hden hchoose).mpr
    have hc : (Fintype.card (Equiv.Perm E) : ℝ) =
        (Nat.choose (Fintype.card E) S.card : ℝ) * (fiber S S).card := by
      exact_mod_cast card_perm_eq_choose_mul_fiber S
    rw [hc]
    ring
  · have hf : fiber S T = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro σ hσ
      have h := congrArg Finset.card ((mem_fiber S T σ).mp hσ)
      rw [sample_card] at h
      exact hcard h.symm
    simp only [hf, Finset.card_empty, Nat.cast_zero, zero_div,
      Hypergeometric.weight, if_neg hcard]

/-- Any statistic of one permutation image has the exact fixed-size
sampling expectation. This is a marginal law, not joint independence. -/
theorem expectation_sample (S : Finset E) (f : Finset E → ℝ) :
    (∑ σ : Equiv.Perm E, weight σ * f (sample S σ)) =
      ∑ T : Finset E, Hypergeometric.weight S.card T * f T := by
  calc
    _ = ∑ T : Finset E, ∑ σ ∈ fiber S T, weight σ * f (sample S σ) := by
      exact (Finset.sum_fiberwise univ (sample S)
        (fun σ => weight σ * f (sample S σ))).symm
    _ = ∑ T : Finset E, (∑ σ ∈ fiber S T, weight σ) * f T := by
      apply Finset.sum_congr rfl
      intro T _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [(mem_fiber S T σ).mp hσ]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro T _
      have h := probability_sample_eq S T
      have h' : (∑ σ ∈ fiber S T, weight σ) = Hypergeometric.weight S.card T := by
        calc
          _ = probability (fun σ => sample S σ = T) := by
            unfold probability MatchingProbability.probability
            apply Finset.sum_congr
            · ext σ
              simp only [mem_fiber, Finset.mem_filter, Finset.mem_univ, true_and]
            · intro σ _
              rfl
          _ = _ := h
      rw [h']

/-- Transfer every event of an individual sample to the actual uniform
permutation experiment. -/
theorem probability_sample (S : Finset E) (P : Finset E → Prop) :
    probability (fun σ => P (sample S σ)) = Hypergeometric.probability S.card P := by
  have h := expectation_sample S (fun T => if P T then 1 else 0)
  simpa only [probability, Hypergeometric.probability, MatchingProbability.probability,
    Finset.sum_filter, mul_ite, mul_one, mul_zero] using h

/-- Prescribed total size at most the population gives disjoint actual
position sets, without requiring a chosen ordering of the population. -/
theorem exists_positions {ι : Type*} [Fintype ι] (n : ι → ℕ)
    (hn : (∑ i, n i) ≤ Fintype.card E) :
    ∃ S : ι → Finset E, (∀ i, (S i).card = n i) ∧
      ∀ i j, i ≠ j → Disjoint (S i) (S j) := by
  have hc : Fintype.card (Σ i, Fin (n i)) ≤ Fintype.card E := by simpa using hn
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hc
  let row (i : ι) : Fin (n i) ↪ E :=
    ⟨fun j => e ⟨i, j⟩, fun j l h => by
      have he := e.injective h
      exact eq_of_heq (Sigma.mk.inj_iff.mp he).2⟩
  let S := fun i => univ.map (row i)
  refine ⟨S, ?_, ?_⟩
  · intro i
    simp only [S, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro x hxi hxj
    obtain ⟨u, _, hu⟩ := Finset.mem_map.mp hxi
    obtain ⟨v, _, hv⟩ := Finset.mem_map.mp hxj
    exact hij (congrArg Sigma.fst (e.injective (hu.trans hv.symm)))

/-- A simultaneous disjoint sample exists whenever the sum of the marginal
bad-event bounds is below one. No independence between samples is assumed. -/
theorem exists_disjoint_samples {ι : Type*} [Fintype ι] (n : ι → ℕ)
    (hn : (∑ i, n i) ≤ Fintype.card E)
    (bad : ι → Finset E → Prop) (ε : ι → ℝ)
    (hbad : ∀ i, Hypergeometric.probability (n i) (bad i) ≤ ε i)
    (hε : (∑ i, ε i) < 1) :
    ∃ T : ι → Finset E, (∀ i, (T i).card = n i) ∧
      (∀ i j, i ≠ j → Disjoint (T i) (T j)) ∧ ∀ i, ¬ bad i (T i) := by
  obtain ⟨S, hcard, hdisj⟩ := exists_positions (E := E) n hn
  let P := fun σ : Equiv.Perm E => ∃ i, bad i (sample (S i) σ)
  have hbound : probability P < 1 := by
    have hu := MatchingProbability.probability_exists_le_sum weight weight_nonneg univ
      (fun i σ => bad i (sample (S i) σ))
    have hu' : probability P ≤
        ∑ i, probability (fun σ => bad i (sample (S i) σ)) := by
      simpa only [probability, P, Finset.mem_univ, true_and] using hu
    apply lt_of_le_of_lt hu'
    calc
      _ ≤ ∑ i, ε i := by
        apply Finset.sum_le_sum
        intro i _
        rw [probability_sample, hcard]
        exact hbad i
      _ < 1 := hε
  have hex : ∃ σ : Equiv.Perm E, ¬ P σ := by
    by_contra hnP
    push_neg at hnP
    have heq : probability P = 1 := by
      unfold probability MatchingProbability.probability
      simp only [Finset.sum_filter, hnP, if_true]
      exact sum_weight
    rw [heq] at hbound
    exact lt_irrefl _ hbound
  obtain ⟨σ, hσ⟩ := hex
  refine ⟨fun i => sample (S i) σ, fun i => (sample_card _ _).trans (hcard i),
    fun i j hij => sample_disjoint _ _ σ (hdisj i j hij), ?_⟩
  intro i hi
  exact hσ ⟨i, hi⟩

end Overfull.PermutationSampling
