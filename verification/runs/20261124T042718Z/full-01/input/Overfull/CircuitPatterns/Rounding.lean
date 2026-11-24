import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic

/-!
# Weighted rounding for frequent boundary patterns

All weights and all tests refer to one fixed proposed selection. The
bookkeeping weights after a realized prefix are numerical quantities;
no residual fractional matching decomposition is asserted.
-/

namespace Overfull.CircuitPatterns

open Finset Classical
open scoped BigOperators

variable {P : Type*} [Fintype P]

/-- Keep an integer reserve in one distinguished pattern. -/
noncomputable def remainingWeight (w : P → ℝ) (p₀ : P) (r : ℕ) (p : P) : ℝ :=
  w p - if p = p₀ then (r : ℝ) else 0

/-- The common proposal, before any sparse-pair or small-cut discards. -/
noncomputable def proposedMultiplicity (η : ℝ) (w : P → ℝ) (p₀ : P) (r : ℕ)
    (p : P) : ℕ := ⌊(1-η)*remainingWeight w p₀ r p⌋₊

/-- Discard entire patterns; a retained pattern keeps its proposed count. -/
noncomputable def acceptedMultiplicity (keep : P → Prop) (m : P → ℕ) (p : P) : ℕ :=
  if keep p then m p else 0

omit [Fintype P] in
theorem acceptedMultiplicity_le (keep : P → Prop) (m : P → ℕ) (p : P) :
    acceptedMultiplicity keep m p ≤ m p := by
  unfold acceptedMultiplicity
  split_ifs <;> omega

theorem exists_maximum_weight [Nonempty P] (w : P → ℝ) :
    ∃ p₀ : P, (∀ p, w p ≤ w p₀) ∧
      (∑ p, w p) ≤ (Fintype.card P : ℝ)*w p₀ := by
  obtain ⟨p₀, _, hp₀⟩ := Finset.exists_max_image (univ : Finset P) w
    Finset.univ_nonempty
  refine ⟨p₀, fun p => hp₀ p (mem_univ p), ?_⟩
  calc
    (∑ p, w p) ≤ ∑ _p : P, w p₀ :=
      Finset.sum_le_sum (fun p _ => hp₀ p (mem_univ p))
    _ = _ := by simp

/-- The bound may use an upper bound for the number of patterns. -/
theorem maximum_weight_lower_bound (w : P → ℝ) (p₀ : P) (k B : ℝ)
    (hw : ∀ p, 0 ≤ w p) (hmax : ∀ p, w p ≤ w p₀)
    (hsum : ∑ p, w p = k) (hB : 0 < B) (hcard : (Fintype.card P : ℝ) ≤ B) :
    k/B ≤ w p₀ := by
  apply (div_le_iff₀ hB).mpr
  have hsumle : k ≤ (Fintype.card P : ℝ)*w p₀ := by
    rw [← hsum]
    calc
      (∑ p, w p) ≤ ∑ _p : P, w p₀ := sum_le_sum (fun p _ => hmax p)
      _ = _ := by simp
  nlinarith [mul_le_mul_of_nonneg_right hcard (hw p₀)]

/-- Choosing half the frequent pattern leaves a linear integer reserve. -/
theorem reserve_floor_bounds (w₀ k B : ℝ) (hB : 0 < B)
    (hlarge : 6*B ≤ k) (hweight : k/B ≤ w₀) :
    k/(3*B) ≤ (⌊w₀/2⌋₊ : ℝ) ∧ (⌊w₀/2⌋₊ : ℝ) ≤ w₀/2 ∧
      (⌊w₀/2⌋₊ : ℝ) ≤ w₀ := by
  have hratio : 6 ≤ k/B := (le_div_iff₀ hB).mpr (by nlinarith)
  have hw₀ : 0 ≤ w₀ := by linarith
  have hfloor := Nat.lt_floor_add_one (w₀/2)
  have hfloorle := Nat.floor_le (show 0 ≤ w₀/2 by positivity)
  have heq : k/(3*B) = (k/B)/3 := by field_simp
  rw [heq]
  constructor
  · nlinarith
  exact ⟨hfloorle, by linarith⟩

omit [Fintype P] in
theorem remainingWeight_nonneg (w : P → ℝ) (p₀ : P) (r : ℕ)
    (hw : ∀ p, 0 ≤ w p) (hr : (r : ℝ) ≤ w p₀) (p : P) :
    0 ≤ remainingWeight w p₀ r p := by
  by_cases hp : p = p₀ <;> simp only [remainingWeight, hp, if_true, if_false]
  · subst p
    linarith
  · simpa only [sub_zero] using hw p

omit [Fintype P] in
theorem remainingWeight_le (w : P → ℝ) (p₀ : P) (r : ℕ) (p : P) :
    remainingWeight w p₀ r p ≤ w p := by
  unfold remainingWeight
  split_ifs <;> linarith [show (0 : ℝ) ≤ r from Nat.cast_nonneg _]

theorem remainingWeight_sum (w : P → ℝ) (p₀ : P) (r : ℕ) :
    (∑ p, remainingWeight w p₀ r p) = (∑ p, w p) - r := by
  simp [remainingWeight, sum_sub_distrib]

theorem remainingWeight_weighted_sum (w c : P → ℝ) (p₀ : P) (r : ℕ) :
    (∑ p, remainingWeight w p₀ r p*c p) = (∑ p, w p*c p) - r*c p₀ := by
  simp [remainingWeight, sub_mul, ite_mul, sum_sub_distrib]

omit [Fintype P] in
theorem proposedMultiplicity_le_scaled (η : ℝ) (w : P → ℝ) (p₀ : P) (r : ℕ)
    (hη : η ≤ 1) (hw : ∀ p, 0 ≤ w p) (hr : (r : ℝ) ≤ w p₀) (p : P) :
    (proposedMultiplicity η w p₀ r p : ℝ) ≤ (1-η)*remainingWeight w p₀ r p := by
  exact Nat.floor_le (mul_nonneg (sub_nonneg.mpr hη)
    (remainingWeight_nonneg w p₀ r hw hr p))

omit [Fintype P] in
theorem proposedMultiplicity_le_remaining (η : ℝ) (w : P → ℝ) (p₀ : P) (r : ℕ)
    (hη₀ : 0 ≤ η) (hη₁ : η ≤ 1)
    (hw : ∀ p, 0 ≤ w p) (hr : (r : ℝ) ≤ w p₀) (p : P) :
    (proposedMultiplicity η w p₀ r p : ℝ) ≤ remainingWeight w p₀ r p := by
  have h := proposedMultiplicity_le_scaled η w p₀ r hη₁ hw hr p
  have hn := remainingWeight_nonneg w p₀ r hw hr p
  nlinarith [mul_nonneg hη₀ hn]

omit [Fintype P] in
theorem proposedMultiplicity_le_weight (η : ℝ) (w : P → ℝ) (p₀ : P) (r : ℕ)
    (hη₀ : 0 ≤ η) (hη₁ : η ≤ 1)
    (hw : ∀ p, 0 ≤ w p) (hr : (r : ℝ) ≤ w p₀) (p : P) :
    (proposedMultiplicity η w p₀ r p : ℝ) ≤ w p :=
  (proposedMultiplicity_le_remaining η w p₀ r hη₀ hη₁ hw hr p).trans
    (remainingWeight_le w p₀ r p)

omit [Fintype P] in
/-- In particular no pattern containing a simple exceptional pair is selected. -/
theorem proposedMultiplicity_eq_zero_of_weight_le_one
    (η : ℝ) (w : P → ℝ) (p₀ : P) (r : ℕ)
    (hη₀ : 0 < η) (hη₁ : η ≤ 1)
    (hw : ∀ p, 0 ≤ w p) (hr : (r : ℝ) ≤ w p₀)
    (p : P) (hp : w p ≤ 1) : proposedMultiplicity η w p₀ r p = 0 := by
  have hn := remainingWeight_nonneg w p₀ r hw hr p
  have hu := (remainingWeight_le w p₀ r p).trans hp
  have hprod : (1-η)*remainingWeight w p₀ r p < 1 := by
    have h := mul_le_mul_of_nonneg_left hu (sub_nonneg.mpr hη₁)
    nlinarith
  have hfloor := (Nat.floor_lt_one
    (mul_nonneg (sub_nonneg.mpr hη₁) hn)).mpr hprod
  exact Nat.lt_one_iff.mp hfloor

/-- Weighted pair demands retain the full distinguished-pattern reserve. -/
theorem proposed_demand_le (η : ℝ) (w c : P → ℝ) (p₀ : P) (r : ℕ) (d : ℝ)
    (hη₁ : η ≤ 1) (hw : ∀ p, 0 ≤ w p) (hr : (r : ℝ) ≤ w p₀)
    (hc : ∀ p, 0 ≤ c p) (hcap : (∑ p, w p*c p) ≤ d) :
    (∑ p, (proposedMultiplicity η w p₀ r p : ℝ)*c p) ≤
      (1-η)*(d-r*c p₀) := by
  calc
    _ ≤ ∑ p, ((1-η)*remainingWeight w p₀ r p)*c p := by
      apply sum_le_sum
      intro p _
      exact mul_le_mul_of_nonneg_right
        (proposedMultiplicity_le_scaled η w p₀ r hη₁ hw hr p) (hc p)
    _ = (1-η)*((∑ p, w p*c p)-r*c p₀) := by
      rw [← remainingWeight_weighted_sum w c p₀ r, mul_sum]
      apply sum_congr rfl
      intro p _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (sub_le_sub_right hcap _)
      (sub_nonneg.mpr hη₁)

theorem proposed_cut_reserve (η : ℝ) (w c : P → ℝ) (p₀ : P) (r : ℕ) (d : ℝ)
    (hη₁ : η ≤ 1) (hw : ∀ p, 0 ≤ w p) (hr : (r : ℝ) ≤ w p₀)
    (hc : ∀ p, 0 ≤ c p) (hcap : (∑ p, w p*c p) ≤ d) :
    η*d ≤ d - ∑ p, (proposedMultiplicity η w p₀ r p : ℝ)*c p := by
  have h := proposed_demand_le η w c p₀ r d hη₁ hw hr hc hcap
  have hreserve : 0 ≤ (1-η)*(r : ℝ)*c p₀ := by
    exact mul_nonneg (mul_nonneg (sub_nonneg.mpr hη₁) (Nat.cast_nonneg r)) (hc p₀)
  nlinarith only [h, hreserve]

/-- Flooring loses less than one unit per possible pattern. -/
theorem proposed_total_bounds (η : ℝ) (w : P → ℝ) (p₀ : P) (r : ℕ) (k : ℝ)
    (hη₀ : 0 ≤ η) (hη₁ : η ≤ 1)
    (hw : ∀ p, 0 ≤ w p) (hr : (r : ℝ) ≤ w p₀) (hsum : ∑ p, w p = k) :
    (∑ p, (proposedMultiplicity η w p₀ r p : ℝ)) ≤ k-r ∧
      (1-η)*(k-r) - Fintype.card P ≤
        ∑ p, (proposedMultiplicity η w p₀ r p : ℝ) := by
  have hrem := remainingWeight_sum w p₀ r
  rw [hsum] at hrem
  constructor
  · calc
      _ ≤ ∑ p, remainingWeight w p₀ r p := by
        exact sum_le_sum (fun p _ => proposedMultiplicity_le_remaining η w p₀ r
          hη₀ hη₁ hw hr p)
      _ = _ := hrem
  · have hfloor : ∀ p, (1-η)*remainingWeight w p₀ r p - 1 ≤
        (proposedMultiplicity η w p₀ r p : ℝ) := by
      intro p
      have h := Nat.lt_floor_add_one ((1-η)*remainingWeight w p₀ r p)
      change _ ≤ (⌊(1-η)*remainingWeight w p₀ r p⌋₊ : ℝ)
      linarith
    have h := sum_le_sum (fun p (_ : p ∈ (univ : Finset P)) => hfloor p)
    simpa only [sum_sub_distrib, ← mul_sum, hrem, sum_const, card_univ,
      nsmul_eq_mul, mul_one] using h

/-- A pattern discarded by any test is charged to at least one of those
tests. Every test is evaluated against the same original multiplicities. -/
theorem discard_union_bound {D : Type*} [Fintype D]
    (m : P → ℕ) (keep : P → Prop) (bad : D → P → Prop)
    (hcover : ∀ p, ¬ keep p → ∃ d, bad d p) :
    (∑ p, (m p : ℝ)) ≤
      (∑ p, (acceptedMultiplicity keep m p : ℝ)) +
        ∑ d, ∑ p, if bad d p then (m p : ℝ) else 0 := by
  have hpoint (p : P) : (m p : ℝ) ≤
      acceptedMultiplicity keep m p + ∑ d, if bad d p then (m p : ℝ) else 0 := by
    by_cases hp : keep p
    · simp only [acceptedMultiplicity, if_pos hp]
      exact le_add_of_nonneg_right (sum_nonneg (fun d _ => by split_ifs <;> positivity))
    · obtain ⟨d, hd⟩ := hcover p hp
      have h := Finset.single_le_sum
        (f := fun e : D => if bad e p then (m p : ℝ) else 0)
        (fun e (_ : e ∈ (univ : Finset D)) => by dsimp only; split_ifs <;> positivity)
        (mem_univ d)
      simpa only [acceptedMultiplicity, if_neg hp, Nat.cast_zero, zero_add, if_pos hd]
        using h
  have h := sum_le_sum (fun p (_ : p ∈ (univ : Finset P)) => hpoint p)
  have hs : (∑ p, ∑ d, if bad d p then (m p : ℝ) else 0) =
      ∑ d, ∑ p, if bad d p then (m p : ℝ) else 0 := Finset.sum_comm
  simpa only [sum_add_distrib, hs] using h

/-- Quantitative residual interval after arbitrary whole-pattern discards. -/
theorem accepted_residual_bounds (η : ℝ) (w : P → ℝ) (p₀ : P) (r : ℕ)
    (k E : ℝ) (keep : P → Prop)
    (hη₀ : 0 ≤ η) (hη₁ : η ≤ 1)
    (hw : ∀ p, 0 ≤ w p) (hr : (r : ℝ) ≤ w p₀)
    (hsum : ∑ p, w p = k)
    (hdiscard : (∑ p, (proposedMultiplicity η w p₀ r p : ℝ)) ≤
      (∑ p, (acceptedMultiplicity keep (proposedMultiplicity η w p₀ r) p : ℝ)) + E) :
    (r : ℝ) ≤ k - ∑ p, (acceptedMultiplicity keep (proposedMultiplicity η w p₀ r) p : ℝ) ∧
      k - (∑ p, (acceptedMultiplicity keep (proposedMultiplicity η w p₀ r) p : ℝ)) ≤
        r + η*k + Fintype.card P + E := by
  have hb := proposed_total_bounds η w p₀ r k hη₀ hη₁ hw hr hsum
  have hle : (∑ p, (acceptedMultiplicity keep (proposedMultiplicity η w p₀ r) p : ℝ)) ≤
      ∑ p, (proposedMultiplicity η w p₀ r p : ℝ) := by
    apply sum_le_sum
    intro p _
    exact_mod_cast acceptedMultiplicity_le keep (proposedMultiplicity η w p₀ r) p
  have hηr : 0 ≤ η*(r : ℝ) := mul_nonneg hη₀ (Nat.cast_nonneg r)
  constructor <;> nlinarith

/-- Crossing a test consumes at least one unit of its integer demand. -/
theorem crossing_multiplicity_le_demand (m : P → ℕ) (c : P → ℕ) :
    (∑ p, if 0 < c p then (m p : ℝ) else 0) ≤ ∑ p, (m p : ℝ)*c p := by
  apply sum_le_sum
  intro p _
  by_cases hc : 0 < c p
  · simp only [if_pos hc]
    have hcR : (1 : ℝ) ≤ c p := by exact_mod_cast hc
    nlinarith [show (0 : ℝ) ≤ m p from Nat.cast_nonneg _]
  · simp only [if_neg hc]
    positivity

theorem crossing_multiplicity_le_capacity (m : P → ℕ) (w : P → ℝ) (c : P → ℕ)
    (d : ℝ) (hm : ∀ p, (m p : ℝ) ≤ w p)
    (hcap : (∑ p, w p*c p) ≤ d) :
    (∑ p, if 0 < c p then (m p : ℝ) else 0) ≤ d := by
  apply (crossing_multiplicity_le_demand m c).trans
  apply le_trans _ hcap
  apply sum_le_sum
  intro p _
  exact mul_le_mul_of_nonneg_right (hm p) (Nat.cast_nonneg _)

/-- A protected even cut is small for the single common proposal, so its
entire discard costs at most `2a/η`. -/
theorem small_proposed_cut_discard_bound (η a d : ℝ)
    (w : P → ℝ) (c : P → ℕ) (p₀ : P) (r : ℕ)
    (hη₀ : 0 < η) (hη₁ : η ≤ 1)
    (hw : ∀ p, 0 ≤ w p) (hr : (r : ℝ) ≤ w p₀)
    (hcap : (∑ p, w p*c p) ≤ d)
    (hsmall : d - (∑ p, (proposedMultiplicity η w p₀ r p : ℝ)*c p) < 2*a) :
    (∑ p, if 0 < c p then (proposedMultiplicity η w p₀ r p : ℝ) else 0) ≤ 2*a/η := by
  have hres := proposed_cut_reserve η w (fun p => (c p : ℝ)) p₀ r d hη₁ hw hr
    (fun p => Nat.cast_nonneg _) hcap
  have hd : d ≤ 2*a/η := (le_div_iff₀ hη₀).mpr (by nlinarith)
  exact (crossing_multiplicity_le_capacity _ w c d
    (proposedMultiplicity_le_weight η w p₀ r hη₀.le hη₁ hw hr) hcap).trans hd

/-- Prefix bookkeeping subtracts the actual realized crossing counts. -/
theorem prefix_weighted_capacity (w : P → ℝ) (n c : P → ℕ) (d : ℝ)
    (hcap : (∑ p, w p*c p) ≤ d) :
    (∑ p, (w p-(n p : ℝ))*c p) ≤ d - ∑ p, (n p : ℝ)*c p := by
  simp only [sub_mul, sum_sub_distrib]
  exact sub_le_sub_right hcap _

theorem prefix_weight_sum (w : P → ℝ) (n : P → ℕ) (k : ℝ)
    (hsum : ∑ p, w p = k) :
    (∑ p, (w p-(n p : ℝ))) = k - ∑ p, (n p : ℝ) := by
  rw [sum_sub_distrib, hsum]

/-- Every odd whole union is crossed positively by every pattern. -/
theorem prefix_odd_cut_bound (w : P → ℝ) (n c : P → ℕ) (k d : ℝ)
    (hsum : ∑ p, w p = k) (hn : ∀ p, (n p : ℝ) ≤ w p)
    (hc : ∀ p, 1 ≤ c p) (hcap : (∑ p, w p*c p) ≤ d) :
    k - (∑ p, (n p : ℝ)) ≤ d - ∑ p, (n p : ℝ)*c p := by
  rw [← prefix_weight_sum w n k hsum]
  apply le_trans _ (prefix_weighted_capacity w n c d hcap)
  apply sum_le_sum
  intro p _
  have hcR : (1 : ℝ) ≤ c p := by exact_mod_cast hc p
  nlinarith [sub_nonneg.mpr (hn p)]

/-- Invalid ambient patterns need no odd-cut condition when their original
weight is zero. A processed prefix cannot use such patterns. -/
theorem prefix_odd_cut_bound_on_support (w : P → ℝ) (n c : P → ℕ) (k d : ℝ)
    (hsum : ∑ p, w p = k) (hn : ∀ p, (n p : ℝ) ≤ w p)
    (hc : ∀ p, 0 < w p → 1 ≤ c p) (hcap : (∑ p, w p*c p) ≤ d) :
    k - (∑ p, (n p : ℝ)) ≤ d - ∑ p, (n p : ℝ)*c p := by
  rw [← prefix_weight_sum w n k hsum]
  apply le_trans _ (prefix_weighted_capacity w n c d hcap)
  apply sum_le_sum
  intro p _
  by_cases hp : 0 < w p
  · have hcR : (1 : ℝ) ≤ c p := by exact_mod_cast hc p hp
    nlinarith [sub_nonneg.mpr (hn p)]
  · have hzero : w p-(n p : ℝ) = 0 := by
      have hnonneg : (0 : ℝ) ≤ n p := Nat.cast_nonneg _
      have hupper := not_lt.mp hp
      linarith [hn p]
    rw [hzero, zero_mul]

/-- The stronger pair inequality keeps the distinguished reserve at every
prefix and after every whole-pattern discard. -/
theorem prefix_pair_reserve (η : ℝ) (w : P → ℝ) (p₀ : P) (r : ℕ)
    (n c : P → ℕ) (d : ℝ) (hη₀ : 0 ≤ η) (hη₁ : η ≤ 1)
    (hw : ∀ p, 0 ≤ w p) (hr : (r : ℝ) ≤ w p₀)
    (hn : ∀ p, n p ≤ proposedMultiplicity η w p₀ r p)
    (hcap : (∑ p, w p*c p) ≤ d) :
    (r : ℝ)*c p₀ ≤ d - ∑ p, (n p : ℝ)*c p := by
  have hsum : (∑ p, (n p : ℝ)*c p) ≤
      ∑ p, remainingWeight w p₀ r p*c p := by
    apply sum_le_sum
    intro p _
    have hnp : (n p : ℝ) ≤ proposedMultiplicity η w p₀ r p := by exact_mod_cast hn p
    exact mul_le_mul_of_nonneg_right
      (hnp.trans (proposedMultiplicity_le_remaining η w p₀ r hη₀ hη₁ hw hr p))
      (Nat.cast_nonneg _)
  rw [remainingWeight_weighted_sum] at hsum
  linarith


/-- Exact retained natural degree, with no truncated-subtraction ambiguity. -/
theorem accepted_natural_residual_bounds (η : ℝ) (w : P → ℝ) (p₀ : P) (r k : ℕ)
    (E : ℝ) (keep : P → Prop)
    (hη₀ : 0 ≤ η) (hη₁ : η ≤ 1)
    (hw : ∀ p, 0 ≤ w p) (hr : (r : ℝ) ≤ w p₀)
    (hsum : ∑ p, w p = (k : ℝ))
    (hdiscard : (∑ p, (proposedMultiplicity η w p₀ r p : ℝ)) ≤
      (∑ p, (acceptedMultiplicity keep (proposedMultiplicity η w p₀ r) p : ℝ)) + E) :
    let m := acceptedMultiplicity keep (proposedMultiplicity η w p₀ r)
    let h := k-∑ p, m p
    h+(∑ p, m p) = k ∧ r ≤ h ∧
      (h : ℝ) ≤ r+η*k+Fintype.card P+E := by
  dsimp only
  let m := acceptedMultiplicity keep (proposedMultiplicity η w p₀ r)
  have hb := accepted_residual_bounds η w p₀ r k E keep hη₀ hη₁ hw hr hsum hdiscard
  change (r : ℝ) ≤ k - ∑ p, (m p : ℝ) ∧
    k - (∑ p, (m p : ℝ)) ≤ r+η*k+Fintype.card P+E at hb
  have hsumleR : (∑ p, (m p : ℝ)) ≤ k := by linarith [show (0 : ℝ) ≤ r from Nat.cast_nonneg _]
  have hsumle : (∑ p, m p) ≤ k := by exact_mod_cast hsumleR
  have hcast : ((k-∑ p, m p : ℕ) : ℝ) = k-∑ p, (m p : ℝ) := by
    rw [Nat.cast_sub hsumle, Nat.cast_sum]
  refine ⟨Nat.sub_add_cancel hsumle, ?_, ?_⟩
  · have h := hb.1
    rw [← hcast] at h
    exact_mod_cast h
  · rw [hcast]
    exact hb.2

/-- All exclusions are determined before the first realization. -/
noncomputable def pairCutKeep {J X : Type*} [Fintype X]
    (pairCount : J → P → ℕ) (pairCapacity : J → ℝ)
    (cutCount : X → P → ℕ) (cutCapacity : X → ℝ)
    (m : P → ℕ) (L a : ℝ) (p : P) : Prop :=
  (∀ j, pairCapacity j < L → pairCount j p = 0) ∧
    (∀ x, cutCapacity x - (∑ q, (m q : ℝ)*cutCount x q) < 2*a → cutCount x p = 0)

/-- Combining sparse pairs and small even whole cuts counts overlaps only
once on the left, so overlapping tests cause no difficulty. -/
theorem pair_cut_discard_bound {J X : Type*} [Fintype J] [Fintype X]
    (η a L : ℝ) (w : P → ℝ) (p₀ : P) (r : ℕ)
    (pairCount : J → P → ℕ) (pairCapacity : J → ℝ)
    (cutCount : X → P → ℕ) (cutCapacity : X → ℝ)
    (hη₀ : 0 < η) (hη₁ : η ≤ 1) (ha : 0 ≤ a) (hL : 0 ≤ L)
    (hw : ∀ p, 0 ≤ w p) (hr : (r : ℝ) ≤ w p₀)
    (hpairs : ∀ j, (∑ p, w p*pairCount j p) ≤ pairCapacity j)
    (hcuts : ∀ x, (∑ p, w p*cutCount x p) ≤ cutCapacity x) :
    let m := proposedMultiplicity η w p₀ r
    let keep := pairCutKeep pairCount pairCapacity cutCount cutCapacity m L a
    (∑ p, (m p : ℝ)) ≤ (∑ p, (acceptedMultiplicity keep m p : ℝ)) +
      (Fintype.card J : ℝ)*L + (Fintype.card X : ℝ)*(2*a/η) := by
  dsimp only
  let m := proposedMultiplicity η w p₀ r
  let keep := pairCutKeep pairCount pairCapacity cutCount cutCapacity m L a
  let bad : J ⊕ X → P → Prop := fun d p => match d with
    | Sum.inl j => pairCapacity j < L ∧ 0 < pairCount j p
    | Sum.inr x => cutCapacity x-(∑ q, (m q : ℝ)*cutCount x q) < 2*a ∧ 0 < cutCount x p
  have hcover (p : P) (hp : ¬keep p) : ∃ d, bad d p := by
    change ¬((∀ j, pairCapacity j < L → pairCount j p = 0) ∧
      (∀ x, cutCapacity x-(∑ q, (m q : ℝ)*cutCount x q) < 2*a → cutCount x p = 0)) at hp
    by_contra hn
    apply hp
    constructor
    · intro j hj
      have hnot : ¬0 < pairCount j p := fun hpos => hn ⟨Sum.inl j, hj, hpos⟩
      omega
    · intro x hx
      have hnot : ¬0 < cutCount x p := fun hpos => hn ⟨Sum.inr x, hx, hpos⟩
      omega
  have hbase := discard_union_bound m keep bad hcover
  have hpair (j : J) : (∑ p, if bad (Sum.inl j) p then (m p : ℝ) else 0) ≤ L := by
    by_cases hj : pairCapacity j < L
    · simp only [bad, hj, true_and]
      exact (crossing_multiplicity_le_capacity m w (pairCount j) (pairCapacity j)
        (proposedMultiplicity_le_weight η w p₀ r hη₀.le hη₁ hw hr) (hpairs j)).trans hj.le
    · simp only [bad, hj, false_and, if_false, sum_const_zero]
      exact hL
  have hcut (x : X) : (∑ p, if bad (Sum.inr x) p then (m p : ℝ) else 0) ≤ 2*a/η := by
    by_cases hx : cutCapacity x-(∑ q, (m q : ℝ)*cutCount x q) < 2*a
    · simp only [bad, hx, true_and]
      exact small_proposed_cut_discard_bound η a (cutCapacity x) w (cutCount x) p₀ r
        hη₀ hη₁ hw hr (hcuts x) hx
    · simp only [bad, hx, false_and, if_false, sum_const_zero]
      positivity
  have htests : (∑ d, ∑ p, if bad d p then (m p : ℝ) else 0) ≤
      (Fintype.card J : ℝ)*L + (Fintype.card X : ℝ)*(2*a/η) := by
    rw [Fintype.sum_sum_type]
    have h₁ := sum_le_sum (fun j (_ : j ∈ (univ : Finset J)) => hpair j)
    have h₂ := sum_le_sum (fun x (_ : x ∈ (univ : Finset X)) => hcut x)
    convert (add_le_add h₁ h₂) using 1
    · congr 1 <;> (apply sum_congr rfl; intro d _; apply sum_congr rfl; intro p _; split_ifs <;> rfl)
    · simp
  change (∑ p, (m p : ℝ)) ≤ (∑ p, (acceptedMultiplicity keep m p : ℝ)) +
    (Fintype.card J : ℝ)*L + (Fintype.card X : ℝ)*(2*a/η)
  linarith

/-- The explicit discard coefficient for at most four cores. -/
theorem four_core_discard_coefficient (t j x : ℕ) (a η : ℝ)
    (hj : j ≤ 4*t+6) (hx : x ≤ 2^(t+4)) (ha : 0 ≤ a) (hη : 0 < η) :
    (j : ℝ)*((t+8)*a/η) + (x : ℝ)*(2*a/η) ≤
      (((4*t+6)*(t+8)+2^(t+5) : ℕ) : ℝ)*a/η := by
  have hjR : (j : ℝ) ≤ 4*t+6 := by exact_mod_cast hj
  have hxR : (x : ℝ) ≤ (2 : ℝ)^(t+4) := by exact_mod_cast hx
  have h₁ := mul_le_mul_of_nonneg_right hjR (show 0 ≤ ((t : ℝ)+8)*a/η by positivity)
  have h₂ := mul_le_mul_of_nonneg_right hxR (show 0 ≤ 2*a/η by positivity)
  have hexp : (2 : ℝ)^(t+5) = (2 : ℝ)^(t+4)*2 := by
    rw [show t+5 = t+4+1 by omega, pow_succ]
  push_cast
  rw [hexp]
  calc
    _ ≤ (4*(t : ℝ)+6)*(((t : ℝ)+8)*a/η) + (2 : ℝ)^(t+4)*(2*a/η) := add_le_add h₁ h₂
    _ = _ := by ring

/-- Every accepted pattern has zero demand on every protected cut. -/
theorem accepted_zero_on_protected_cut {J X : Type*} [Fintype X]
    (pairCount : J → P → ℕ) (pairCapacity : J → ℝ)
    (cutCount : X → P → ℕ) (cutCapacity : X → ℝ)
    (m : P → ℕ) (L a : ℝ) (x : X)
    (hx : cutCapacity x-(∑ q, (m q : ℝ)*cutCount x q) < 2*a) :
    ∀ p, acceptedMultiplicity
      (pairCutKeep pairCount pairCapacity cutCount cutCapacity m L a) m p * cutCount x p = 0 := by
  intro p
  unfold acceptedMultiplicity
  split_ifs with hp
  · rw [hp.2 x hx, Nat.mul_zero]
  · exact Nat.zero_mul _

/-- Discarding patterns can only increase a cut relative to its proposal. -/
theorem prefix_cut_mono (m n c : P → ℕ) (d : ℝ) (hn : ∀ p, n p ≤ m p) :
    d - (∑ p, (m p : ℝ)*c p) ≤ d - ∑ p, (n p : ℝ)*c p := by
  apply sub_le_sub_left
  apply sum_le_sum
  intro p _
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hn p) (Nat.cast_nonneg _)

end Overfull.CircuitPatterns
