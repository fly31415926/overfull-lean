import Overfull.BipartiteFactorization.BlockSampling

/-!
# Actual correction-score variance for independent block samples

Each coordinate is an actual fixed-size sample from one vertex part.
Disjoint parts turn coordinate swaps into swaps in the sampled vertex
union, and count each original vertex weight at most once.
-/

noncomputable section

namespace Overfull.BipartiteFactorization.BlockProductSampling

open Finset Classical

variable {V E ι : Type*} [Fintype ι]

/-- The actual block formed by the union of sampled vertices in each part. -/
def sampledBlock (D : ι → Finset V) (τ : ∀ i, Finset (D i)) : Finset V :=
  univ.biUnion (fun i => (τ i).image Subtype.val)

theorem mem_sampledBlock (D : ι → Finset V) (τ : ∀ i, Finset (D i)) (v : V) :
    v ∈ sampledBlock D τ ↔ ∃ i, ∃ x ∈ τ i, x.val = v := by
  simp only [sampledBlock, Finset.mem_biUnion, Finset.mem_univ,
    true_and, Finset.mem_image]

theorem sampledBlock_subset (D : ι → Finset V) (τ : ∀ i, Finset (D i))
    (B : Finset V) (hD : ∀ i, D i ⊆ B) : sampledBlock D τ ⊆ B := by
  intro v hv
  obtain ⟨i, x, _, rfl⟩ := (mem_sampledBlock D τ v).mp hv
  exact hD i x.property

/-- In disjoint parts, membership of a vertex is determined by its own
coordinate, including for samples outside the cardinality support. -/
theorem sampledBlock_mem_part (D : ι → Finset V)
    (hdisj : ∀ i j, i ≠ j → Disjoint (D i) (D j))
    (τ : ∀ i, Finset (D i)) (i : ι) (x : D i) :
    x.val ∈ sampledBlock D τ ↔ x ∈ τ i := by
  constructor
  · intro hx
    obtain ⟨j, y, hy, hyx⟩ := (mem_sampledBlock D τ x.val).mp hx
    by_cases hji : j = i
    · subst j
      have hxy : y = x := Subtype.ext hyx
      exact hxy ▸ hy
    · exact False.elim (Finset.disjoint_left.mp (hdisj j i hji)
        (hyx ▸ y.property) x.property)
  · intro hx
    exact (mem_sampledBlock D τ x.val).mpr ⟨i, x, hx, rfl⟩

theorem sampledBlock_update_outside (D : ι → Finset V)
    (τ : ∀ i, Finset (D i)) (i : ι) (T : Finset (D i)) (v : V)
    (hv : v ∉ D i) :
    v ∈ sampledBlock D (Function.update τ i T) ↔ v ∈ sampledBlock D τ := by
  simp only [mem_sampledBlock]
  constructor
  · rintro ⟨j, x, hx, hxv⟩
    have hji : j ≠ i := by
      intro hji
      subst j
      exact hv (hxv ▸ x.property)
    exact ⟨j, x, by simpa only [Function.update_of_ne hji] using hx, hxv⟩
  · rintro ⟨j, x, hx, hxv⟩
    have hji : j ≠ i := by
      intro hji
      subst j
      exact hv (hxv ▸ x.property)
    exact ⟨j, x, by simpa only [Function.update_of_ne hji] using hx, hxv⟩

/-- Updating one part replaces exactly the block's vertices in that part. -/
theorem sampledBlock_update (D : ι → Finset V)
    (hdisj : ∀ i j, i ≠ j → Disjoint (D i) (D j))
    (τ : ∀ i, Finset (D i)) (i : ι) (T : Finset (D i)) :
    sampledBlock D (Function.update τ i T) =
      (sampledBlock D τ \ D i) ∪ T.image Subtype.val := by
  ext v
  by_cases hv : v ∈ D i
  · have hmem := sampledBlock_mem_part D hdisj (Function.update τ i T) i ⟨v, hv⟩
    simp only [Function.update_self] at hmem
    rw [hmem]
    simp only [Finset.mem_union, Finset.mem_sdiff, hv, not_true_eq_false, and_false,
      false_or, Finset.mem_image]
    constructor
    · exact fun h => ⟨⟨v, hv⟩, h, rfl⟩
    · rintro ⟨x, hx, hxv⟩
      exact (Subtype.ext hxv : x = ⟨v, hv⟩) ▸ hx
  · rw [sampledBlock_update_outside D τ i T v hv]
    have hn : v ∉ T.image Subtype.val := by
      intro he
      obtain ⟨x, _, hxv⟩ := Finset.mem_image.mp he
      exact hv (hxv ▸ x.property)
    simp only [Finset.mem_union, Finset.mem_sdiff, hv, not_false_eq_true, and_true,
      hn, or_false]

/-- A swap in one sampled part is exactly a swap of the original vertices
in the block union. This identity retains the actual vertex representatives. -/
theorem sampledBlock_update_swap (D : ι → Finset V)
    (hdisj : ∀ i j, i ≠ j → Disjoint (D i) (D j))
    (τ : ∀ i, Finset (D i)) (i : ι) (T : Finset (D i)) (x y : D i) :
    sampledBlock D (Function.update τ i (insert y (T.erase x))) =
      insert y.val ((sampledBlock D (Function.update τ i T)).erase x.val) := by
  have hx : x.val ∉ sampledBlock D τ \ D i := by
    intro h
    exact (Finset.mem_sdiff.mp h).2 x.property
  rw [sampledBlock_update D hdisj τ i, sampledBlock_update D hdisj τ i,
    Finset.image_insert, Finset.image_erase Subtype.val_injective]
  ext v
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
  by_cases hv : v = x.val
  · subst v
    simp only [hx, false_or, ne_eq, not_true_eq_false, false_and, or_false]
  · tauto

/-- Disjoint parts count each actual vertex weight once. -/
theorem sum_part_weights (D : ι → Finset V)
    (hdisj : ∀ i j, i ≠ j → Disjoint (D i) (D j)) (w : V → ℝ) :
    (∑ i, ∑ x : D i, w x.val) = ∑ x ∈ univ.biUnion D, w x := by
  rw [Finset.sum_biUnion (fun i _ j _ hij => hdisj i j hij)]
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_coe_sort (D i) w

/-- If the parts lie in the core side, their total nonnegative influence
weight is bounded by the actual total weight on that side. -/
theorem sum_part_weights_le (D : ι → Finset V)
    (hdisj : ∀ i j, i ≠ j → Disjoint (D i) (D j))
    (B : Finset V) (hD : ∀ i, D i ⊆ B) (w : V → ℝ)
    (hw : ∀ x ∈ B, 0 ≤ w x) :
    (∑ i, ∑ x : D i, w x.val) ≤ ∑ x ∈ B, w x := by
  rw [sum_part_weights D hdisj w]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
    exact hD i hi
  · intro x hx _
    exact hw x hx

variable [Fintype E] (G : Multigraph V E)

/-- The actual nonlinear score satisfies the coordinate-swap hypothesis
on the product sample space. No score-influence estimate is assumed. -/
theorem cappedScore_coordinate_swap (D : ι → Finset V)
    (hdisj : ∀ i j, i ≠ j → Disjoint (D i) (D j))
    (B Z : Finset V) (hD : ∀ i, D i ⊆ B)
    (ell : V → ℝ) (ω₁ ω₂ : ℝ) (hω₁ : 0 ≤ ω₁) (hω₂ : 0 ≤ ω₂)
    (τ : ∀ i, Finset (D i)) (i : ι) (T : Finset (D i))
    (x : D i) (hx : x ∈ T) (y : D i) :
    |BlockSampling.cappedScore G Z ell ω₁ ω₂
        (sampledBlock D (Function.update τ i (insert y (T.erase x)))) -
      BlockSampling.cappedScore G Z ell ω₁ ω₂
        (sampledBlock D (Function.update τ i T))| ≤
      BlockSampling.vertexWeight G B Z ω₁ ω₂ x.val +
        BlockSampling.vertexWeight G B Z ω₁ ω₂ y.val := by
  rw [sampledBlock_update_swap D hdisj τ i T x y]
  apply BlockSampling.cappedScore_swap_le G B Z ell ω₁ ω₂ hω₁ hω₂
    (sampledBlock_subset D (Function.update τ i T) B hD) _ (hD i y.property)
  apply (sampledBlock_mem_part D hdisj (Function.update τ i T) i x).mpr
  simpa only [Function.update_self] using hx

/-- The manuscript variance bound for the actual capped correction score
under independent fixed-size samples from disjoint vertex parts. The parts
need only lie in the core side; covering the side is unnecessary. -/
theorem cappedScore_product_variance (D : ι → Finset V)
    (hdisj : ∀ i j, i ≠ j → Disjoint (D i) (D j))
    (B Z : Finset V) (hD : ∀ i, D i ⊆ B) (hBZ : Disjoint B Z)
    (s : ι → ℕ) (hs : ∀ i, s i ≤ (D i).card)
    (p₀ : ℝ) (hp₀ : 0 ≤ p₀) (hfraction : ∀ i, (s i : ℝ) / (D i).card ≤ p₀)
    (ell : V → ℝ) (ω₁ ω₂ a : ℝ) (hω₁ : 0 ≤ ω₁) (hω₁₂ : ω₁ ≤ ω₂)
    (ha : 0 ≤ a) (hdegree : ∀ v ∈ B, (G.degree v : ℝ) ≤ a) :
    FiniteProbability.variance
      (FiniteProbability.piWeight (fun i => Hypergeometric.weight (E := ↥(D i)) (s i)))
      (fun τ => BlockSampling.cappedScore G Z ell ω₁ ω₂ (sampledBlock D τ)) ≤
        8 * p₀ * ω₂ ^ 2 * a * (correctionPool G B Z).card := by
  have hω₂ : 0 ≤ ω₂ := hω₁.trans hω₁₂
  have htotal : (∑ i, ∑ v : D i, BlockSampling.vertexWeight G B Z ω₁ ω₂ v.val) ≤
      2 * ω₂ * (correctionPool G B Z).card := by
    exact (sum_part_weights_le D hdisj B hD
      (BlockSampling.vertexWeight G B Z ω₁ ω₂)
      (fun v _ => BlockSampling.vertexWeight_nonneg G B Z ω₁ ω₂ hω₁ hω₂ v)).trans
      (BlockSampling.sum_vertexWeight_le G B Z hBZ ω₁ ω₂ hω₁ hω₁₂)
  have h := Hypergeometric.variance_product_of_swap_bounded
    (fun i => ↥(D i)) s (fun i => by simpa only [Fintype.card_coe] using hs i)
    (fun i (v : D i) => BlockSampling.vertexWeight G B Z ω₁ ω₂ v.val)
    (fun _ v => BlockSampling.vertexWeight_nonneg G B Z ω₁ ω₂ hω₁ hω₂ v.val)
    (fun τ => BlockSampling.cappedScore G Z ell ω₁ ω₂ (sampledBlock D τ))
    (fun i τ T _ x hx y _ => by
      have hdec : (fun u v : D i => Classical.propDecidable (u = v)) =
          (inferInstance : DecidableEq (D i)) := Subsingleton.elim _ _
      simpa only [hdec] using cappedScore_coordinate_swap G D hdisj B Z hD
        ell ω₁ ω₂ hω₁ hω₂ τ i T x hx y)
    p₀ (ω₂ * a) (2 * ω₂ * (correctionPool G B Z).card) hp₀ (mul_nonneg hω₂ ha)
    (fun i => by simpa only [Fintype.card_coe] using hfraction i)
    (fun i v => BlockSampling.vertexWeight_le G B Z hBZ ω₁ ω₂ a hω₁ hω₁₂
      v.val (hD i v.property) (hdegree v.val (hD i v.property))) htotal
  calc
    _ ≤ 4 * p₀ * (ω₂ * a) * (2 * ω₂ * (correctionPool G B Z).card) := h
    _ = _ := by ring

end Overfull.BipartiteFactorization.BlockProductSampling
