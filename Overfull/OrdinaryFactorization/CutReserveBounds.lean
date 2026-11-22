import Overfull.OrdinaryFactorization.CutReserve

/-!
# Degree, spread, and palette bounds for the actual cut-reserve graphs

Every estimate concerns the reserve and internal graph constructed in
`CutReserveData`. Maximum degrees are bounded through the finite maximum,
and the rounded palette is computed from that actual maximum degree.
-/

noncomputable section

namespace Overfull.OrdinaryFactorization.CutReserveData

open Finset Classical

variable {V I : Type*} [Fintype V] [Fintype I] [DecidableEq V]
variable {H : SimpleGraph V} [DecidableRel H.Adj] {e : I × Bool ≃ V}
variable {α₀ τ ξ p νR σ δ : ℝ}
variable (D : CutReserveData H e α₀ τ ξ p νR σ δ)

/-- The stored internal estimate, expressed using the actual graph accessor. -/
theorem internal_degree_estimate (v : V) :
    |(D.internal.degree v : ℝ) - (1 - p) * H.degree v / 2| ≤
      3 * δ * Fintype.card V := by
  have hdegree : D.internal.degree v =
      (internalLeftover H (OrdinaryRandomReserve.sampledGraph H D.sample) D.left).degree v := by
    calc
      _ = (D.internal.neighborFinset v).card :=
        (D.internal.card_neighborFinset_eq_degree v).symm
      _ = ((internalLeftover H (OrdinaryRandomReserve.sampledGraph H D.sample)
          D.left).neighborFinset v).card := by
        congr 1
      _ = _ := SimpleGraph.card_neighborFinset_eq_degree _ v
  rw [hdegree]
  exact D.internal_degree v

theorem internal_degree_lower (k : ℕ) (a : ℝ) (hp1 : p ≤ 1)
    (hdegree : ∀ v, (k : ℝ) - a ≤ H.degree v) (v : V) :
    (1 - p) * ((k : ℝ) - a) / 2 - 3 * δ * Fintype.card V ≤
      (D.internal.degree v : ℝ) := by
  have h := (abs_le.mp (D.internal_degree_estimate v)).1
  have hmul := mul_le_mul_of_nonneg_left (hdegree v) (show 0 ≤ 1 - p by linarith)
  nlinarith

theorem internal_degree_upper (k : ℕ) (hp1 : p ≤ 1)
    (hdegree : ∀ v, (H.degree v : ℝ) ≤ k) (v : V) :
    (D.internal.degree v : ℝ) ≤ (1 - p) * k / 2 + 3 * δ * Fintype.card V := by
  have h := (abs_le.mp (D.internal_degree_estimate v)).2
  have hmul := mul_le_mul_of_nonneg_left (hdegree v) (show 0 ≤ 1 - p by linarith)
  nlinarith

/-- Comparison with the ambient regular degree, allowing the original
simple core to have error `a`. -/
theorem internal_reference_degree_error (k : ℕ) (a : ℝ) (ha : 0 ≤ a)
    (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hdegree : ∀ v, (k : ℝ) - a ≤ H.degree v ∧ (H.degree v : ℝ) ≤ k) (v : V) :
    |(D.internal.degree v : ℝ) - (1 - p) * k / 2| ≤
      a / 2 + 3 * δ * Fintype.card V := by
  have hlower := D.internal_degree_lower k a hp1 (fun w => (hdegree w).1) v
  have hupper := D.internal_degree_upper k hp1 (fun w => (hdegree w).2) v
  have hpa : (1 - p) * a ≤ a := by nlinarith [mul_nonneg hp ha]
  apply abs_le.mpr
  constructor <;> nlinarith

/-- The upper bound is proved at a vertex attaining the actual finite
maximum; the empty graph is handled separately. -/
theorem internal_maxDegree_upper (k : ℕ) (hδ : 0 ≤ δ) (hp1 : p ≤ 1)
    (hdegree : ∀ v, (H.degree v : ℝ) ≤ k) :
    (D.internal.maxDegree : ℝ) ≤ (1 - p) * k / 2 + 3 * δ * Fintype.card V := by
  rcases isEmpty_or_nonempty V with hV | hV
  · letI := hV
    rw [SimpleGraph.maxDegree_of_isEmpty, Nat.cast_zero]
    have hp' : 0 ≤ 1 - p := by linarith
    positivity
  · letI := hV
    obtain ⟨v, hv⟩ := D.internal.exists_maximal_degree_vertex
    rw [hv]
    exact D.internal_degree_upper k hp1 hdegree v

/-- The spread is derived from the same graph's maximum and the lower
bound at the specified vertex. -/
theorem internal_degree_spread (k : ℕ) (a : ℝ) (ha : 0 ≤ a)
    (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hdegree : ∀ v, (k : ℝ) - a ≤ H.degree v ∧ (H.degree v : ℝ) ≤ k) (v : V) :
    (D.internal.maxDegree : ℝ) - D.internal.degree v ≤
      a / 2 + 6 * δ * Fintype.card V := by
  letI : Nonempty V := ⟨v⟩
  obtain ⟨w, hw⟩ := D.internal.exists_maximal_degree_vertex
  have hupper := D.internal_degree_upper k hp1 (fun u => (hdegree u).2) w
  have hlower := (abs_le.mp (D.internal_reference_degree_error k a ha hp hp1 hdegree v)).1
  rw [hw]
  linarith

/-- The sharper multiplicative lower bound retains a linear internal
minimum degree with the stated tolerance. -/
theorem internal_degree_linear_lower (k : ℕ) (a α : ℝ)
    (hp : p ≤ 1 / 2)
    (hk : α * Fintype.card V ≤ (k : ℝ))
    (ha : a ≤ α * Fintype.card V / 4) (hδ : δ ≤ α / 128)
    (hdegree : ∀ v, (k : ℝ) - a ≤ H.degree v) (v : V) :
    (α / 8) * Fintype.card V ≤ (D.internal.degree v : ℝ) := by
  have hn : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hka : 0 ≤ (k : ℝ) - a := by
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    linarith
  have hhalf : (1 / 2 : ℝ) ≤ 1 - p := by linarith
  have hmul := mul_le_mul_of_nonneg_right hhalf hka
  have herror := mul_le_mul_of_nonneg_right hδ hn
  have hlow := D.internal_degree_lower k a (by linarith) hdegree v
  nlinarith

/-- The two stored side estimates for the actual reserve accessor. -/
theorem reserve_side_degree_estimate (v : V) :
    |((D.reserve.neighborFinset v ∩ D.left).card : ℝ) - p * H.degree v / 2| ≤
      2 * δ * Fintype.card V ∧
    |((D.reserve.neighborFinset v ∩ D.right).card : ℝ) - p * H.degree v / 2| ≤
      2 * δ * Fintype.card V := by
  have hneighbors : D.reserve.neighborFinset v =
      (OrdinaryRandomReserve.sampledGraph H D.sample).neighborFinset v := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset, reserve]
  simpa only [hneighbors] using D.reserve_degrees v

/-- Summing the two actual side degrees gives the reserve's total degree. -/
theorem reserve_degree_error (v : V) :
    |(D.reserve.degree v : ℝ) - p * H.degree v| ≤ 4 * δ * Fintype.card V := by
  have hsum : (D.reserve.degree v : ℝ) =
      (D.reserve.neighborFinset v ∩ D.left).card +
        (D.reserve.neighborFinset v ∩ D.right).card := by
    exact_mod_cast OrdinaryRandomReserve.degree_eq_side_counts
      D.reserve D.left D.right D.disjoint D.cover v
  have hA := abs_le.mp (D.reserve_side_degree_estimate v).1
  have hB := abs_le.mp (D.reserve_side_degree_estimate v).2
  apply abs_le.mpr
  constructor <;> nlinarith

theorem reserve_degree_linear_lower (k : ℕ) (a α : ℝ) (hp : 0 ≤ p)
    (hk : α * Fintype.card V ≤ (k : ℝ))
    (ha : a ≤ α * Fintype.card V / 4) (hδ : δ ≤ p * α / 16)
    (hdegree : ∀ v, (k : ℝ) - a ≤ H.degree v) (v : V) :
    (p * α / 2) * Fintype.card V ≤ (D.reserve.degree v : ℝ) := by
  have hn : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hhost : 3 * α * Fintype.card V / 4 ≤ (H.degree v : ℝ) := by
    linarith [hdegree v]
  have hweighted := mul_le_mul_of_nonneg_left hhost hp
  have herror := mul_le_mul_of_nonneg_right hδ hn
  have hlower := (abs_le.mp (D.reserve_degree_error v)).1
  nlinarith

/-- The actual palette used by the forbidden-color extension. -/
def paletteSize (κ : ℝ) : ℕ :=
  D.internal.maxDegree + 1 + Nat.ceil (κ * Fintype.card V)

theorem paletteSize_pos (κ : ℝ) : 0 < D.paletteSize κ := by
  dsimp only [paletteSize]
  omega

/-- A small linear extra palette still leaves at least two fifths of the
ambient regular degree. The rounded palette is calculated from the actual
internal maximum degree, rather than assumed as a bound. -/
theorem paletteSize_bounds (k : ℕ) (α κ : ℝ) (hα : 0 < α)
    (hκ : 0 ≤ κ) (hκsmall : κ ≤ α / 512)
    (hδ : 0 ≤ δ) (hδsmall : δ ≤ α / 1000) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hk : α * Fintype.card V ≤ (k : ℝ))
    (hlarge : 100 / α ≤ (Fintype.card V : ℝ))
    (hdegree : ∀ v, (H.degree v : ℝ) ≤ k) :
    0 < D.paletteSize κ ∧ (D.paletteSize κ : ℝ) ≤ 3 * k / 5 ∧
      D.paletteSize κ ≤ k ∧ (2 : ℝ) * k / 5 ≤ (k - D.paletteSize κ : ℕ) := by
  have hn : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hmax := D.internal_maxDegree_upper k hδ hp1 hdegree
  have hhalf : (1 - p) * (k : ℝ) / 2 ≤ k / 2 := by
    nlinarith [mul_nonneg hp (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hceil := Nat.ceil_lt_add_one (mul_nonneg hκ hn)
  have hδn := mul_le_mul_of_nonneg_right hδsmall hn
  have hκn := mul_le_mul_of_nonneg_right hκsmall hn
  have h100 : (100 : ℝ) ≤ α * Fintype.card V := by
    have h := (div_le_iff₀ hα).mp hlarge
    nlinarith
  have hupper : (D.paletteSize κ : ℝ) ≤ 3 * k / 5 := by
    dsimp only [paletteSize]
    push_cast
    nlinarith
  have hle : D.paletteSize κ ≤ k := by
    have hleR : (D.paletteSize κ : ℝ) ≤ k := by
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
      linarith
    exact_mod_cast hleR
  refine ⟨D.paletteSize_pos κ, hupper, hle, ?_⟩
  rw [Nat.cast_sub hle]
  linarith

end Overfull.OrdinaryFactorization.CutReserveData
