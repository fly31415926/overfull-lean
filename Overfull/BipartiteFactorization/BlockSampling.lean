import Overfull.BipartiteFactorization.Imbalance
import Overfull.Probability.SwapVariance

/-!
# Actual capped correction scores under block swaps

Every incidence and degree counts original multigraph copies. A single
vertex insertion changes the capped score by at most its incident weight.
The derived weight bounds make the uniform-subset variance estimate usable
for the actual correction pool.
-/

noncomputable section

namespace Overfull.BipartiteFactorization.BlockSampling

open Finset Classical

variable {V E : Type*} [Fintype E] (G : Multigraph V E)

/-- The actual correction score in a sampled core block. Real caps include
natural-number caps by coercion. -/
def cappedScore (Z : Finset V) (ell : V → ℝ) (ω₁ ω₂ : ℝ) (T : Finset V) : ℝ :=
  ω₂ * (G.internalEdges T).card +
    ∑ x ∈ Z, min (ω₁ * (G.edgesTo x T).card) (ell x)

/-- The influence weight of one core vertex, counting actual incident copies. -/
def vertexWeight (B Z : Finset V) (ω₁ ω₂ : ℝ) (v : V) : ℝ :=
  ω₂ * (G.restrictEdges (G.internalEdges B)).degree v +
    ω₁ * (G.edgesTo v Z).card

theorem internalEdges_mono {S T : Finset V} (hST : S ⊆ T) :
    G.internalEdges S ⊆ G.internalEdges T := by
  intro e he
  obtain ⟨hx, hy⟩ := (G.mem_internalEdges S e).mp he
  exact (G.mem_internalEdges T e).mpr ⟨hST hx, hST hy⟩

theorem parallelEdges_symm (x y : V) : G.parallelEdges x y = G.parallelEdges y x := by
  have hsub (x y : V) : G.parallelEdges x y ⊆ G.parallelEdges y x := by
    intro e he
    obtain ⟨hxe, hxy⟩ := (G.mem_parallelEdges x y e).mp he
    have heq : G.edge e = s(x, y) := by rw [G.edge_eq_otherEnd x e hxe, hxy]
    apply (G.mem_parallelEdges y x e).mpr
    exact ⟨by simp [heq], G.otherEnd_eq_of_edge e y x (heq.trans Sym2.eq_swap)⟩
  exact Finset.Subset.antisymm (hsub x y) (hsub y x)

/-- Counting a vertex's incident copies by their actual other endpoint. -/
theorem sum_parallel_card (v : V) (Z : Finset V) :
    (∑ x ∈ Z, (G.parallelEdges x v).card) = (G.edgesTo v Z).card := by
  have hmap : (G.edgesTo v Z).toSet.MapsTo (G.otherEnd v) Z := by
    intro e he
    exact ((G.mem_edgesTo v Z e).mp he).2
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  apply Finset.sum_congr rfl
  intro x hx
  rw [parallelEdges_symm G x v]
  congr 1
  ext e
  simp only [Finset.mem_filter, G.mem_edgesTo, G.mem_parallelEdges]
  constructor
  · exact fun h => ⟨⟨h.1, h.2 ▸ hx⟩, h.2⟩
  · exact fun h => ⟨h.1.1, h.2⟩

theorem internal_degree_eq_edgesTo (B : Finset V) (v : V) (hv : v ∈ B) :
    (G.restrictEdges (G.internalEdges B)).degree v = (G.edgesTo v B).card := by
  rw [G.restrictEdges_degree]
  congr 1
  ext e
  simp only [Finset.mem_inter, G.mem_incidenceEdges, G.mem_edgesTo]
  constructor
  · rintro ⟨heB, hve⟩
    exact ⟨hve, ((G.internalEdges_iff_of_edge e v _ (G.edge_eq_otherEnd v e hve) B).mp heB).2⟩
  · rintro ⟨hve, hoB⟩
    exact ⟨(G.internalEdges_iff_of_edge e v _ (G.edge_eq_otherEnd v e hve) B).mpr
      ⟨hv, hoB⟩, hve⟩

/-- Every internal copy contributes twice to its induced-side degree sum. -/
theorem internal_degree_sum (B : Finset V) :
    (∑ v ∈ B, (G.restrictEdges (G.internalEdges B)).degree v) =
      2 * (G.internalEdges B).card := by
  have h := restricted_degree_sum G (G.internalEdges B) B
  have heach (e : E) (he : e ∈ G.internalEdges B) : sideIncidence G B e = 2 := by
    obtain ⟨hx, hy⟩ := (G.mem_internalEdges B e).mp he
    simp only [sideIncidence, if_pos hx, if_pos hy]
    norm_num
  have hs : (∑ v ∈ B, ((G.restrictEdges (G.internalEdges B)).degree v : ℤ)) =
      2 * (G.internalEdges B).card := by
    rw [h, Finset.sum_congr rfl heach]
    simp [mul_comm]
  exact_mod_cast hs

theorem betweenCopies_symm (B Z : Finset V) :
    betweenCopies G B Z = betweenCopies G Z B := by
  ext e
  simp only [mem_betweenCopies]
  tauto

/-- Cross copies are counted once from either side of a disjoint cut. -/
theorem cross_degree_sum (B Z : Finset V) (hBZ : Disjoint B Z) :
    (∑ v ∈ B, (G.edgesTo v Z).card) = (betweenCopies G Z B).card := by
  have h := betweenCopies_inter_card G univ B Z hBZ
  simpa only [Finset.univ_inter, betweenCopies_symm G B Z] using h.symm

theorem correction_pool_card (B Z : Finset V) (hBZ : Disjoint B Z) :
    (correctionPool G B Z).card =
      (G.internalEdges B).card + (betweenCopies G Z B).card := by
  apply Finset.card_union_of_disjoint
  apply Finset.disjoint_left.mpr
  intro e heB heZ
  obtain ⟨x, hxZ, hex⟩ := Finset.mem_biUnion.mp heZ
  have hxe := ((G.mem_edgesTo x B e).mp hex).1
  have hxB := ((G.internalEdges_iff_of_edge e x _ (G.edge_eq_otherEnd x e hxe) B).mp heB).1
  exact Finset.disjoint_left.mp hBZ hxB hxZ

theorem vertexWeight_nonneg (B Z : Finset V) (ω₁ ω₂ : ℝ)
    (hω₁ : 0 ≤ ω₁) (hω₂ : 0 ≤ ω₂) (v : V) :
    0 ≤ vertexWeight G B Z ω₁ ω₂ v := by
  unfold vertexWeight
  positivity

/-- The two weighted incidence sets at a core vertex are disjoint subsets
of its actual original incidences. -/
theorem vertexWeight_le (B Z : Finset V) (hBZ : Disjoint B Z)
    (ω₁ ω₂ a : ℝ) (hω₁ : 0 ≤ ω₁) (hω₁₂ : ω₁ ≤ ω₂)
    (v : V) (hv : v ∈ B) (hdegree : (G.degree v : ℝ) ≤ a) :
    vertexWeight G B Z ω₁ ω₂ v ≤ ω₂ * a := by
  have hω₂ := hω₁.trans hω₁₂
  have hcount : ((G.edgesTo v B).card : ℝ) + (G.edgesTo v Z).card ≤ G.degree v := by
    exact_mod_cast (edgesTo_union_card G v hBZ).symm.trans_le
      (edgesTo_card_le_degree G v (B ∪ Z))
  have hw := mul_le_mul_of_nonneg_right hω₁₂ (Nat.cast_nonneg (G.edgesTo v Z).card)
  have hd := mul_le_mul_of_nonneg_left (hcount.trans hdegree) hω₂
  unfold vertexWeight
  rw [internal_degree_eq_edgesTo G B v hv]
  nlinarith

/-- The sum of the actual vertex weights is charged to at most two copies
of the whole correction pool. -/
theorem sum_vertexWeight_le (B Z : Finset V) (hBZ : Disjoint B Z)
    (ω₁ ω₂ : ℝ) (hω₁ : 0 ≤ ω₁) (hω₁₂ : ω₁ ≤ ω₂) :
    (∑ v ∈ B, vertexWeight G B Z ω₁ ω₂ v) ≤
      2 * ω₂ * (correctionPool G B Z).card := by
  have hω₂ := hω₁.trans hω₁₂
  have hi : (∑ v ∈ B, ((G.restrictEdges (G.internalEdges B)).degree v : ℝ)) =
      2 * (G.internalEdges B).card := by exact_mod_cast internal_degree_sum G B
  have hz : (∑ v ∈ B, ((G.edgesTo v Z).card : ℝ)) =
      (betweenCopies G Z B).card := by exact_mod_cast cross_degree_sum G B Z hBZ
  have hw := mul_le_mul_of_nonneg_right hω₁₂ (Nat.cast_nonneg (betweenCopies G Z B).card)
  have hnonneg := mul_nonneg hω₂ (Nat.cast_nonneg (betweenCopies G Z B).card)
  simp only [vertexWeight, Finset.sum_add_distrib, ← Finset.mul_sum, hi, hz,
    correction_pool_card G B Z hBZ, Nat.cast_add]
  nlinarith

/-- Adding a vertex only adds copies incident with that vertex. -/
theorem internalEdges_insert_card_le (B : Finset V) {T : Finset V}
    (hTB : T ⊆ B) {v : V} (hv : v ∈ B) :
    (G.internalEdges (insert v T)).card ≤ (G.internalEdges T).card +
      (G.restrictEdges (G.internalEdges B)).degree v := by
  have hsub : G.internalEdges (insert v T) ⊆
      G.internalEdges T ∪ (G.internalEdges B ∩ G.incidenceEdges v) := by
    intro e he
    by_cases heT : e ∈ G.internalEdges T
    · exact Finset.mem_union_left _ heT
    apply Finset.mem_union_right
    apply Finset.mem_inter.mpr
    refine ⟨internalEdges_mono G (Finset.insert_subset_iff.mpr ⟨hv, hTB⟩) he, ?_⟩
    rw [G.mem_incidenceEdges, G.incident_iff]
    have hends := (G.mem_internalEdges (insert v T) e).mp he
    simp only [Finset.mem_insert] at hends
    have hnot := mt (G.mem_internalEdges T e).mpr heT
    tauto
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans_eq
    (by rw [G.restrictEdges_degree]))

theorem edgesTo_insert (x v : V) (T : Finset V) :
    G.edgesTo x (insert v T) = G.edgesTo x T ∪ G.parallelEdges x v := by
  ext e
  simp only [G.mem_edgesTo, G.mem_parallelEdges, Finset.mem_insert, Finset.mem_union]
  tauto

theorem cappedScore_mono (Z : Finset V) (ell : V → ℝ) (ω₁ ω₂ : ℝ)
    (hω₁ : 0 ≤ ω₁) (hω₂ : 0 ≤ ω₂) {S T : Finset V} (hST : S ⊆ T) :
    cappedScore G Z ell ω₁ ω₂ S ≤ cappedScore G Z ell ω₁ ω₂ T := by
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left
      (Nat.cast_le.mpr (Finset.card_le_card (internalEdges_mono G hST))) hω₂
  · apply Finset.sum_le_sum
    intro x hx
    exact min_le_min_right _ (mul_le_mul_of_nonneg_left
      (Nat.cast_le.mpr (Finset.card_le_card (edgesTo_mono G x hST))) hω₁)

/-- Capping a row does not increase the cost of inserting one vertex. -/
theorem cappedRow_insert_le (x v : V) (T : Finset V) (cap ω : ℝ) (hω : 0 ≤ ω) :
    min (ω * (G.edgesTo x (insert v T)).card) cap ≤
      min (ω * (G.edgesTo x T).card) cap + ω * (G.parallelEdges x v).card := by
  have hcard : (G.edgesTo x (insert v T)).card ≤
      (G.edgesTo x T).card + (G.parallelEdges x v).card := by
    rw [edgesTo_insert]
    exact Finset.card_union_le _ _
  have hreal : ((G.edgesTo x (insert v T)).card : ℝ) ≤
      (G.edgesTo x T).card + (G.parallelEdges x v).card := by exact_mod_cast hcard
  calc
    _ ≤ min (ω * (G.edgesTo x T).card + ω * (G.parallelEdges x v).card) cap := by
      apply min_le_min_right
      simpa only [mul_add] using mul_le_mul_of_nonneg_left hreal hω
    _ ≤ _ := CorrectionCapacity.min_add_loss _ _ _
      (mul_nonneg hω (Nat.cast_nonneg _))

/-- A one-vertex insertion is controlled by the actual incidence weight. -/
theorem cappedScore_insert_le (B Z : Finset V) (ell : V → ℝ) (ω₁ ω₂ : ℝ)
    (hω₁ : 0 ≤ ω₁) (hω₂ : 0 ≤ ω₂) {T : Finset V} (hTB : T ⊆ B)
    {v : V} (hv : v ∈ B) :
    cappedScore G Z ell ω₁ ω₂ (insert v T) ≤
      cappedScore G Z ell ω₁ ω₂ T + vertexWeight G B Z ω₁ ω₂ v := by
  have hi : ((G.internalEdges (insert v T)).card : ℝ) ≤
      (G.internalEdges T).card + (G.restrictEdges (G.internalEdges B)).degree v := by
    exact_mod_cast internalEdges_insert_card_le G B hTB hv
  have hrows := Finset.sum_le_sum (fun x (_hx : x ∈ Z) =>
    cappedRow_insert_le G x v T (ell x) ω₁ hω₁)
  have hsum : (∑ x ∈ Z, ((G.parallelEdges x v).card : ℝ)) =
      (G.edgesTo v Z).card := by exact_mod_cast sum_parallel_card G v Z
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hsum] at hrows
  have hiw := mul_le_mul_of_nonneg_left hi hω₂
  unfold cappedScore vertexWeight
  linarith

/-- Swapping one selected core vertex for another has bounded change in
the actual capped correction score. This also allows the new vertex to
already belong to the sample. -/
theorem cappedScore_swap_le (B Z : Finset V) (ell : V → ℝ) (ω₁ ω₂ : ℝ)
    (hω₁ : 0 ≤ ω₁) (hω₂ : 0 ≤ ω₂) {T : Finset V} (hTB : T ⊆ B)
    {u : V} (hu : u ∈ T) {v : V} (hv : v ∈ B) :
    |cappedScore G Z ell ω₁ ω₂ (insert v (T.erase u)) -
      cappedScore G Z ell ω₁ ω₂ T| ≤
        vertexWeight G B Z ω₁ ω₂ u + vertexWeight G B Z ω₁ ω₂ v := by
  have hR : T.erase u ⊆ B := (Finset.erase_subset _ _).trans hTB
  have huB := hTB hu
  have hiu := cappedScore_insert_le G B Z ell ω₁ ω₂ hω₁ hω₂ hR huB
  rw [Finset.insert_erase hu] at hiu
  have hiv := cappedScore_insert_le G B Z ell ω₁ ω₂ hω₁ hω₂ hR hv
  have hlu := cappedScore_mono G Z ell ω₁ ω₂ hω₁ hω₂ (Finset.erase_subset u T)
  have hlv := cappedScore_mono G Z ell ω₁ ω₂ hω₁ hω₂
    (Finset.subset_insert v (T.erase u))
  have hwu := vertexWeight_nonneg G B Z ω₁ ω₂ hω₁ hω₂ u
  have hwv := vertexWeight_nonneg G B Z ω₁ ω₂ hω₁ hω₂ v
  rw [abs_le]
  constructor <;> linarith

/-- The actual graph score satisfies the weighted uniform-slice variance
bound, using its proved copy-incidence swap estimate. -/
theorem variance_cappedScore_le_weights (B Z : Finset V) (ell : V → ℝ)
    (ω₁ ω₂ : ℝ) (hω₁ : 0 ≤ ω₁) (hω₂ : 0 ≤ ω₂)
    (s : ℕ) (hs : s ≤ B.card) :
    SwapVariance.sliceVariance B s (cappedScore G Z ell ω₁ ω₂) ≤
      4 * ((s : ℝ) / B.card) * ∑ v ∈ B, vertexWeight G B Z ω₁ ω₂ v ^ 2 := by
  apply SwapVariance.weighted_slice_variance B s hs
    (vertexWeight G B Z ω₁ ω₂)
    (fun v _ => vertexWeight_nonneg G B Z ω₁ ω₂ hω₁ hω₂ v)
  intro T hTB _ u hu v hv _
  exact cappedScore_swap_le G B Z ell ω₁ ω₂ hω₁ hω₂ hTB hu hv

/-- The uniform-block variance is bounded using only original core degrees
and the actual correction pool. The sample size may be zero or full. -/
theorem variance_cappedScore_le (B Z : Finset V) (hBZ : Disjoint B Z)
    (ell : V → ℝ) (ω₁ ω₂ a : ℝ) (hω₁ : 0 ≤ ω₁) (hω₁₂ : ω₁ ≤ ω₂)
    (ha : 0 ≤ a) (hdegree : ∀ v ∈ B, (G.degree v : ℝ) ≤ a)
    (s : ℕ) (hs : s ≤ B.card) :
    SwapVariance.sliceVariance B s (cappedScore G Z ell ω₁ ω₂) ≤
      8 * ((s : ℝ) / B.card) * ω₂ ^ 2 * a * (correctionPool G B Z).card := by
  have hω₂ := hω₁.trans hω₁₂
  have hsq : (∑ v ∈ B, vertexWeight G B Z ω₁ ω₂ v ^ 2) ≤
      (ω₂ * a) * (2 * ω₂ * (correctionPool G B Z).card) := by
    calc
      _ ≤ ∑ v ∈ B, (ω₂ * a) * vertexWeight G B Z ω₁ ω₂ v := by
        apply Finset.sum_le_sum
        intro v hv
        have hmax := vertexWeight_le G B Z hBZ ω₁ ω₂ a hω₁ hω₁₂ v hv (hdegree v hv)
        have hnonneg := vertexWeight_nonneg G B Z ω₁ ω₂ hω₁ hω₂ v
        simpa only [pow_two] using mul_le_mul_of_nonneg_right hmax hnonneg
      _ = (ω₂ * a) * ∑ v ∈ B, vertexWeight G B Z ω₁ ω₂ v := by
        rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (sum_vertexWeight_le G B Z hBZ ω₁ ω₂ hω₁ hω₁₂) (mul_nonneg hω₂ ha)
  calc
    _ ≤ 4 * ((s : ℝ) / B.card) * ∑ v ∈ B, vertexWeight G B Z ω₁ ω₂ v ^ 2 :=
      variance_cappedScore_le_weights G B Z ell ω₁ ω₂ hω₁ hω₂ s hs
    _ ≤ 4 * ((s : ℝ) / B.card) *
        ((ω₂ * a) * (2 * ω₂ * (correctionPool G B Z).card)) :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = _ := by ring

end Overfull.BipartiteFactorization.BlockSampling
