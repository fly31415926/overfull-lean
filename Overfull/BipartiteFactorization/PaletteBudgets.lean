import Overfull.BipartiteFactorization.PaletteSampling

/-!
# Numerical failure budgets for actual allowed palettes

The actual sampling population is the allowed-color set. Its cardinality
bound converts the exact fraction `s / C.card` to a bound in terms of
`s / k`. The pool-demand tail below derives both moments from the actual
edge-copy statistic before applying finite Chebyshev.
-/

noncomputable section

namespace Overfull.FiniteProbability

open Finset Classical

variable {Ω : Type*} [Fintype Ω]

/-- An upper-tail estimate from an upper bound for the actual mean. -/
theorem upper_tail_of_mean_upper (p : Ω → ℝ) (hp : ∀ i, 0 ≤ p i)
    (X : Ω → ℝ) (b t : ℝ) (hbt : b < t) (hb : mean p X ≤ b) :
    MatchingProbability.probability p (fun i => t < X i) ≤
      variance p X / (t - b) ^ 2 := by
  apply le_trans (MatchingProbability.probability_mono p hp (fun i hi =>
    show t - b ≤ |X i - mean p X| from by
      have h := le_abs_self (X i - mean p X)
      linarith))
  exact chebyshev p hp X (t - b) (sub_pos.mpr hbt)

/-- Numerical pool-demand tail for the manuscript's `5/4` threshold.
The graph-specific application below proves these moment hypotheses. -/
theorem palette_pool_upper_tail (p : Ω → ℝ) (hp : ∀ i, 0 ≤ p i)
    (X : Ω → ℝ) (lam B M : ℝ) (hlam : 0 < lam) (hB : 0 ≤ B)
    (hM : 0 < M)
    (hmean : mean p X ≤ (33 / 32 : ℝ) * lam * M)
    (hvar : variance p X ≤ (33 / 32 : ℝ) * lam * B * M) :
    MatchingProbability.probability p (fun i => (5 / 4 : ℝ) * lam * M < X i) ≤
      32 * B / (lam * M) := by
  have hgap : (33 / 32 : ℝ) * lam * M < (5 / 4 : ℝ) * lam * M := by
    nlinarith [mul_pos hlam hM]
  have htail := upper_tail_of_mean_upper p hp X
    ((33 / 32 : ℝ) * lam * M) ((5 / 4 : ℝ) * lam * M) hgap hmean
  apply htail.trans
  calc
    variance p X / ((5 / 4 : ℝ) * lam * M - (33 / 32 : ℝ) * lam * M) ^ 2 ≤
        ((33 / 32 : ℝ) * lam * B * M) /
          ((5 / 4 : ℝ) * lam * M - (33 / 32 : ℝ) * lam * M) ^ 2 :=
      div_le_div_of_nonneg_right hvar (sq_nonneg _)
    _ = (1056 / 49 : ℝ) * B / (lam * M) := by
      field_simp [ne_of_gt hlam, ne_of_gt hM]
      ring
    _ ≤ 32 * B / (lam * M) := by
      apply div_le_div_of_nonneg_right _ (mul_nonneg hlam.le hM.le)
      nlinarith

end Overfull.FiniteProbability

namespace Overfull.BipartiteFactorization.PaletteBudgets

open Finset Classical FiniteProbability PaletteSampling

variable {V E : Type*} [Fintype E] {G : Multigraph V E} {k : ℕ}

omit [Fintype E] in
/-- The allowed population is positive under the quantitative size bound. -/
theorem allowed_card_pos (C : Finset (Fin k)) (hk : 0 < k)
    (hC : (32 / 33 : ℝ) * k ≤ C.card) : 0 < (C.card : ℝ) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  nlinarith

omit [Fintype E] in
/-- Passing to the allowed population can only increase the sampling fraction. -/
theorem allowed_fraction_lower (C : Finset (Fin k)) (s : ℕ) (hk : 0 < k)
    (hC : (32 / 33 : ℝ) * k ≤ C.card) :
    (s : ℝ) / k ≤ (s : ℝ) / C.card := by
  have hcard : (C.card : ℝ) ≤ k := by
    exact_mod_cast (show C.card ≤ k by simpa using Finset.card_le_univ C)
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg s) (allowed_card_pos C hk hC) hcard

omit [Fintype E] in
/-- The actual allowed fraction has a uniform upper bound in terms of `s/k`. -/
theorem allowed_fraction_le (C : Finset (Fin k)) (s : ℕ) (hk : 0 < k)
    (hC : (32 / 33 : ℝ) * k ≤ C.card) :
    (s : ℝ) / C.card ≤ (33 / 32 : ℝ) * ((s : ℝ) / k) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hcard := allowed_card_pos C hk hC
  have hratio : (k : ℝ) ≤ (33 / 32 : ℝ) * C.card := by linarith
  have hnonneg : 0 ≤ (s : ℝ) / k := by positivity
  apply (div_le_iff₀ hcard).mpr
  calc
    (s : ℝ) = ((s : ℝ) / k) * k := by
      exact (div_mul_cancel₀ _ (ne_of_gt hk')).symm
    _ ≤ ((s : ℝ) / k) * ((33 / 32 : ℝ) * C.card) :=
      mul_le_mul_of_nonneg_left hratio hnonneg
    _ = (33 / 32 : ℝ) * ((s : ℝ) / k) * C.card := by ring

omit [Fintype E] in
/-- The stronger `511/512` retention estimate supplies the numerical hypothesis. -/
theorem allowed_card_bound_of_retention (C : Finset (Fin k))
    (hC : (511 / 512 : ℝ) * k ≤ C.card) :
    (32 / 33 : ℝ) * k ≤ C.card := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  nlinarith

/-- Pool demand mean, derived from the actual allowed-color sample. -/
theorem mean_poolDemand_le_scaled (c : G.EdgeColoring k) (C : Finset (Fin k))
    (P : Finset E) (s : ℕ) (hs : s ≤ C.card) (hk : 0 < k)
    (hC : (32 / 33 : ℝ) * k ≤ C.card) :
    mean (Hypergeometric.weight s) (poolDemand c C P) ≤
      (33 / 32 : ℝ) * ((s : ℝ) / k) * P.card := by
  exact (mean_poolDemand_le c C P s hs).trans
    (mul_le_mul_of_nonneg_right (allowed_fraction_le C s hk hC) (Nat.cast_nonneg _))

/-- Pool demand variance, retaining actual original-copy per-color bounds. -/
theorem variance_poolDemand_le_scaled (c : G.EdgeColoring k)
    (C : Finset (Fin k)) (P : Finset E) (s : ℕ) (hs : s ≤ C.card) (hk : 0 < k)
    (hC : (32 / 33 : ℝ) * k ≤ C.card) (B : ℝ) (hB : 0 ≤ B)
    (hcolor : ∀ i ∈ C, poolColorWeight c P i ≤ B) :
    variance (Hypergeometric.weight s) (poolDemand c C P) ≤
      (33 / 32 : ℝ) * ((s : ℝ) / k) * B * P.card := by
  calc
    _ ≤ B * mean (Hypergeometric.weight s) (poolDemand c C P) :=
      variance_poolDemand_le_max_mul_mean c C P s hs B hcolor
    _ ≤ B * ((33 / 32 : ℝ) * ((s : ℝ) / k) * P.card) :=
      mul_le_mul_of_nonneg_left (mean_poolDemand_le_scaled c C P s hs hk hC) hB
    _ = _ := by ring

/-- Actual original-pool demand exceeds its target only with the stated
explicit failure probability. Both moments are derived inside this theorem. -/
theorem poolDemand_upper_tail (c : G.EdgeColoring k) (C : Finset (Fin k))
    (P : Finset E) (s : ℕ) (hs : s ≤ C.card) (hk : 0 < k)
    (hC : (32 / 33 : ℝ) * k ≤ C.card) (hspos : 0 < s) (hP : 0 < P.card)
    (B : ℝ) (hB : 0 ≤ B) (hcolor : ∀ i ∈ C, poolColorWeight c P i ≤ B) :
    Hypergeometric.probability s
      (fun T : Finset C => (5 / 4 : ℝ) * ((s : ℝ) / k) * P.card < poolDemand c C P T) ≤
        32 * B / (((s : ℝ) / k) * P.card) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hs' : (0 : ℝ) < s := by exact_mod_cast hspos
  have hP' : (0 : ℝ) < P.card := by exact_mod_cast hP
  exact palette_pool_upper_tail (Hypergeometric.weight s) (Hypergeometric.weight_nonneg s)
    (poolDemand c C P) ((s : ℝ) / k) B P.card (div_pos hs' hk') hB hP'
    (mean_poolDemand_le_scaled c C P s hs hk hC)
    (variance_poolDemand_le_scaled c C P s hs hk hC B hB hcolor)

/-- The pool-demand failure bound includes an empty pool. Its failure
event is empty, and the displayed right-hand side is zero in that case. -/
theorem poolDemand_upper_tail_all (c : G.EdgeColoring k) (C : Finset (Fin k))
    (P : Finset E) (s : ℕ) (hs : s ≤ C.card) (hk : 0 < k)
    (hC : (32 / 33 : ℝ) * k ≤ C.card) (hspos : 0 < s)
    (B : ℝ) (hB : 0 ≤ B) (hcolor : ∀ i ∈ C, poolColorWeight c P i ≤ B) :
    Hypergeometric.probability s
      (fun T : Finset C => (5 / 4 : ℝ) * ((s : ℝ) / k) * P.card < poolDemand c C P T) ≤
        32 * B / (((s : ℝ) / k) * P.card) := by
  by_cases hP : P = ∅
  · subst P
    simp [poolDemand, Hypergeometric.probability, MatchingProbability.probability]
  · exact poolDemand_upper_tail c C P s hs hk hC hspos
      (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hP)) B hB hcolor

end Overfull.BipartiteFactorization.PaletteBudgets
