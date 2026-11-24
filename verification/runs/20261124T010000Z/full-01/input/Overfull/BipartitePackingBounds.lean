import Overfull.BipartitePackingStep
import Overfull.Probability.Concentration
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Bounds on the use of a bipartite reserve

The recurrence is solved for every initial segment. Its bound depends only
on the fixed parameters, and not on future forbidden vertex sets.
-/

namespace Overfull.BipartitePackingBounds

open Finset
open scoped BigOperators

/-- A finite affine recurrence, including the zero-step case. -/
theorem affine_recurrence (t : ℕ → ℝ) (a b : ℝ) (ha : 0 ≤ 1 + a)
    (n : ℕ) (hzero : t 0 ≤ 0)
    (hstep : ∀ s < n, t (s + 1) ≤ (1 + a) * t s + a * b) :
    t n ≤ b * ((1 + a) ^ n - 1) := by
  induction n with
  | zero => simpa using hzero
  | succ n ih =>
    have hind := ih (fun s hs => hstep s (by omega))
    calc
      t (n + 1) ≤ (1 + a) * t n + a * b := hstep n (by omega)
      _ ≤ (1 + a) * (b * ((1 + a) ^ n - 1)) + a * b :=
        add_le_add_right (mul_le_mul_of_nonneg_left hind ha) _
      _ = b * ((1 + a) ^ (n + 1) - 1) := by rw [pow_succ]; ring

/-- The exact geometric estimate used for the total reserve degree. -/
theorem reserve_recurrence_geometric (t : ℕ → ℝ) (m n : ℕ) (ℓ γ ε : ℝ)
    (hm : 0 < m) (hℓ : 0 ≤ ℓ) (hγ : 0 < γ)
    (hzero : t 0 ≤ 0)
    (hstep : ∀ s < n, t (s + 1) ≤
      (1 + 4 * ℓ / (γ * m)) * t s + 32 * ℓ * ε * m / γ) :
    t n ≤ 8 * ε * (m : ℝ) ^ 2 * ((1 + 4 * ℓ / (γ * m)) ^ n - 1) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hconstant : (4 * ℓ / (γ * m)) * (8 * ε * (m : ℝ) ^ 2) =
      32 * ℓ * ε * m / γ := by field_simp; ring
  apply affine_recurrence t (4 * ℓ / (γ * m)) (8 * ε * (m : ℝ) ^ 2)
    (by positivity) n hzero
  intro s hs
  simpa only [hconstant] using hstep s hs

/-- For at most twice the side order, the geometric factor has a fixed
exponential upper bound. -/
theorem geometric_factor_bound (m n : ℕ) (ℓ γ : ℝ)
    (hm : 0 < m) (hℓ : 0 ≤ ℓ) (hγ : 0 < γ) (hn : n ≤ 2 * m) :
    (1 + 4 * ℓ / (γ * m)) ^ n ≤ Real.exp (8 * ℓ / γ) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have ha : 0 ≤ 4 * ℓ / (γ * m) := by positivity
  have hnR : (n : ℝ) ≤ 2 * m := by exact_mod_cast hn
  have hbase : 1 + 4 * ℓ / (γ * m) ≤ Real.exp (4 * ℓ / (γ * m)) := by
    simpa only [add_comm] using Real.add_one_le_exp (4 * ℓ / (γ * m))
  calc
    _ ≤ Real.exp (4 * ℓ / (γ * m)) ^ n :=
      pow_le_pow_left₀ (by positivity) hbase n
    _ = Real.exp ((n : ℝ) * (4 * ℓ / (γ * m))) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (8 * ℓ / γ) := by
      apply Real.exp_le_exp.mpr
      calc
        (n : ℝ) * (4 * ℓ / (γ * m)) ≤ (2 * m) * (4 * ℓ / (γ * m)) :=
          mul_le_mul_of_nonneg_right hnR ha
        _ = 8 * ℓ / γ := by field_simp; ring

/-- Uniform total load bound for every initial segment of the construction. -/
theorem reserve_recurrence_bound (t : ℕ → ℝ) (m n : ℕ) (ℓ γ ε : ℝ)
    (hm : 0 < m) (hℓ : 0 ≤ ℓ) (hγ : 0 < γ) (hε : 0 ≤ ε)
    (hn : n ≤ 2 * m) (hzero : t 0 ≤ 0)
    (hstep : ∀ s < n, t (s + 1) ≤
      (1 + 4 * ℓ / (γ * m)) * t s + 32 * ℓ * ε * m / γ) :
    t n ≤ 8 * (Real.exp (8 * ℓ / γ) - 1) * ε * (m : ℝ) ^ 2 := by
  calc
    t n ≤ 8 * ε * (m : ℝ) ^ 2 * ((1 + 4 * ℓ / (γ * m)) ^ n - 1) :=
      reserve_recurrence_geometric t m n ℓ γ ε hm hℓ hγ hzero hstep
    _ ≤ 8 * ε * (m : ℝ) ^ 2 * (Real.exp (8 * ℓ / γ) - 1) :=
      mul_le_mul_of_nonneg_left
        (sub_le_sub_right (geometric_factor_bound m n ℓ γ hm hℓ hγ hn) 1)
        (by positivity)
    _ = _ := by ring

/-- The matching deficiency estimate gives precisely the affine recurrence
above when each augmentation uses at most `ℓ` reserve edges. -/
theorem reserve_step_bound (m h : ℕ) (ℓ γ ε d t t' : ℝ)
    (hm : 0 < m) (hℓ : 0 ≤ ℓ) (hγ : 0 < γ)
    (hd : γ * m / 2 ≤ d)
    (hdef : (h : ℝ) ≤ (8 * ε * (m : ℝ) ^ 2 + t) / d)
    (huse : t' ≤ t + 2 * ℓ * h) :
    t' ≤ (1 + 4 * ℓ / (γ * m)) * t + 32 * ℓ * ε * m / γ := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hdpos : 0 < d := (by positivity : 0 < γ * (m : ℝ) / 2).trans_le hd
  have hmul := (le_div_iff₀ hdpos).mp hdef
  have hlower := mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg h)
  have hh : (h : ℝ) ≤ 2 * (8 * ε * (m : ℝ) ^ 2 + t) / (γ * m) := by
    apply (le_div_iff₀ (by positivity : 0 < γ * (m : ℝ))).mpr
    nlinarith
  calc
    t' ≤ t + 2 * ℓ * h := huse
    _ ≤ t + 2 * ℓ * (2 * (8 * ε * (m : ℝ) ^ 2 + t) / (γ * m)) :=
      add_le_add_left (mul_le_mul_of_nonneg_left hh (by positivity)) t
    _ = _ := by field_simp; ring

/-- A positive linear capacity has the claimed lower bound after rounding. -/
theorem half_le_floor (x : ℝ) (hx : 2 ≤ x) : x / 2 ≤ (Nat.floor x : ℝ) := by
  have hfloor := Nat.lt_floor_add_one x
  linarith

/-- The actual vertices at the integer capacity form a small set. -/
theorem saturated_vertices_bound {V : Type*} [Fintype V]
    (u : V → ℕ) (Z : Finset V) (m : ℕ) (μ c₀ ε : ℝ)
    (hm : 0 < m) (hμ : 0 < μ) (hlarge : 2 ≤ μ * m)
    (hZ : ∀ v ∈ Z, u v = Nat.floor (μ * m))
    (htotal : (∑ v, (u v : ℝ)) ≤ c₀ * ε * (m : ℝ) ^ 2) :
    (Z.card : ℝ) ≤ 2 * c₀ * ε * m / μ := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hcapacity := half_le_floor (μ * m) hlarge
  have hsum : (Z.card : ℝ) * (Nat.floor (μ * m) : ℝ) ≤
      c₀ * ε * (m : ℝ) ^ 2 := by
    calc
      _ = ∑ v ∈ Z, (u v : ℝ) := by
        simp_rw [Finset.sum_congr rfl (fun v hv => congrArg (Nat.cast : ℕ → ℝ) (hZ v hv))]
        simp
      _ ≤ ∑ v, (u v : ℝ) := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ Z) (fun v _ _ => Nat.cast_nonneg (u v))
      _ ≤ _ := htotal
  apply (le_div_iff₀ hμ).mpr
  have hcap := mul_le_mul_of_nonneg_left hcapacity (Nat.cast_nonneg Z.card)
  have hres : (Z.card : ℝ) * (μ * m / 2) ≤ c₀ * ε * (m : ℝ) ^ 2 := hcap.trans hsum
  apply (mul_le_mul_iff_right₀ hmR).mp
  nlinarith

/-- The small constants can be fixed before the graph and its order. -/
theorem exists_load_parameters (θ δ₀ γ p α c₀ : ℝ) (ℓ : ℕ)
    (hθ : 0 < θ) (hδ₀ : 0 < δ₀) (hγ : 0 < γ) (hp : 0 < p)
    (hα : 0 < α) (hc₀ : 0 ≤ c₀) :
    ∃ μ ε : ℝ, 0 < μ ∧ μ < min θ δ₀ / 100 ∧ 0 < ε ∧
      ε < min (p * α / 8) (γ / 16) ∧ 4 * c₀ * ε / μ < γ / 8 ∧
      (1 + 4 * c₀ / μ + 2 * (ℓ + 1) * (16 + 2 * c₀) / γ) * ε <
        min θ δ₀ / 8 := by
  have hmin : 0 < min θ δ₀ := lt_min hθ hδ₀
  let μ := min θ δ₀ / 200
  have hμ : 0 < μ := by dsimp [μ]; positivity
  have hμsmall : μ < min θ δ₀ / 100 := by dsimp [μ]; linarith
  let K := 1 + 4 * c₀ / μ + 2 * ((ℓ : ℝ) + 1) * (16 + 2 * c₀) / γ
  have hK : 0 < K := by dsimp [K]; positivity
  have ha : 0 < min (p * α / 8) (γ / 16) := by positivity
  have hb : 0 < γ * μ / (32 * (c₀ + 1)) := by positivity
  have hc : 0 < min θ δ₀ / (8 * K) := by positivity
  obtain ⟨ε, hε, hsmall⟩ := exists_between
    (lt_min ha (lt_min hb hc))
  have hεa := (lt_min_iff.mp hsmall).1
  have hεb := (lt_min_iff.mp (lt_min_iff.mp hsmall).2).1
  have hεc := (lt_min_iff.mp (lt_min_iff.mp hsmall).2).2
  refine ⟨μ, ε, hμ, hμsmall, hε, hεa, ?_, ?_⟩
  · have hb' := (lt_div_iff₀ (by positivity : 0 < 32 * (c₀ + 1))).mp hεb
    apply (div_lt_iff₀ hμ).mpr
    nlinarith
  · have hc' := (lt_div_iff₀ (by positivity : 0 < 8 * K)).mp hεc
    change K * ε < min θ δ₀ / 8
    nlinarith

/-- One threshold handles both rounding and the additive slack needed by
the short-path lemma. No graph enters its choice. -/
theorem exists_order_threshold (μ θ δ₀ : ℝ)
    (hμ : 0 < μ) (hθ : 0 < θ) (hδ₀ : 0 < δ₀) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      0 < m ∧ 2 ≤ μ * m ∧ 1 ≤ min θ δ₀ * m / 8 := by
  obtain ⟨m₀, hm₀⟩ := exists_nat_gt (max (2 / μ) (8 / min θ δ₀))
  refine ⟨m₀, ?_⟩
  intro m hm
  have hmm : (m₀ : ℝ) ≤ m := by exact_mod_cast hm
  have htwo : 2 / μ < (m : ℝ) := (le_max_left _ _).trans_lt (hm₀.trans_le hmm)
  have height : 8 / min θ δ₀ < (m : ℝ) :=
    (le_max_right _ _).trans_lt (hm₀.trans_le hmm)
  have hmR : (0 : ℝ) < m := (by positivity : 0 < 2 / μ).trans htwo
  refine ⟨by exact_mod_cast hmR, ?_, ?_⟩
  · have h := (div_lt_iff₀ hμ).mp htwo
    nlinarith
  · have h := (div_lt_iff₀ (lt_min hθ hδ₀)).mp height
    nlinarith

/-- The path budget in the manuscript implies the exact bound, including
the minus one, required by the augmenting-path theorem. -/
theorem augmenting_path_budget (m : ℕ) (θ δ₀ μ w : ℝ)
    (hμ : μ ≤ δ₀ / 2) (hlarge : 1 ≤ min θ δ₀ * m / 8)
    (hw : w ≤ min θ δ₀ * m / 8) :
    w ≤ min (θ / 2) (δ₀ - μ) * m / 2 - 1 := by
  have hmin : min θ δ₀ / 2 ≤ min (θ / 2) (δ₀ - μ) := by
    apply le_min
    · exact div_le_div_of_nonneg_right (min_le_left θ δ₀) (by norm_num)
    · linarith [min_le_right θ δ₀]
  have hmul := mul_le_mul_of_nonneg_right hmin (Nat.cast_nonneg m)
  nlinarith

/-- At every permitted round the nominal degree is still linear in the
ambient side order. -/
theorem nominal_degree_lower (m s : ℕ) (Δ p γ : ℝ)
    (hp : 0 ≤ p) (hpγ : p ≤ γ / 8) (hγ : 0 ≤ γ)
    (hΔ : Δ ≤ 2 * m) (hs : (s : ℝ) ≤ Δ - γ * m) :
    γ * m / 2 ≤ (1 - p) * Δ - s := by
  have h₁ := mul_le_mul_of_nonneg_left hΔ hp
  have h₂ := mul_le_mul_of_nonneg_right hpγ (Nat.cast_nonneg m)
  have h₃ := mul_nonneg hγ (Nat.cast_nonneg m)
  nlinarith

end Overfull.BipartitePackingBounds
