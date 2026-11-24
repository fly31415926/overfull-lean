import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-!
# Coupled integer parameters for the bipartite absorber

The palettes used by the absorber cannot be rounded independently.  This
file constructs their common integer parameters, proves every division and
subtraction exact, and chooses all positive ratios and order thresholds
before the actual cluster size and ambient degree.  It constructs numerical
parameters only; the spanning setup and robust absorber remain separate
geometric obligations.
-/

noncomputable section

namespace Overfull.BipartiteFactorization.AbsorberParameters

open Classical

/-- The eight integer parameters appearing in the absorber and its palettes. -/
structure Data where
  r1 : ℕ
  r : ℕ
  r2 : ℕ
  r3 : ℕ
  rdiamond : ℕ
  s : ℕ
  k1 : ℕ
  k2 : ℕ

/-- The coefficient of the small-parameter budget. -/
def budgetCoefficient (l g t f : ℕ) : ℕ := 96 * l * g ^ 2 * t + 1 + f * t

/-- Choosing `r` divisible by `q` ensures all required quotient integrality.
This is a permissible stronger divisibility than `q / gcd(q,f*t) ∣ r`. -/
def make (l g t f q r1 n : ℕ) : Data :=
  let r := q * n
  let r2 := 96 * l * g ^ 2 * t * r
  let r3 := f * t * n
  let rd := r1 + r2 + r - (q - 1) * r3
  let s := q * r3 + 7 * rd
  ⟨r1, r, r2, r3, rd, s, 2 * r3, 2 * rd⟩

/-- Every integer condition needed for the later degree accounting. -/
structure Valid (l g t f q m : ℕ) (P : Data) : Prop where
  r1_pos : 0 < P.r1
  r_pos : 0 < P.r
  r3_pos : 0 < P.r3
  rdiamond_pos : 0 < P.rdiamond
  q_dvd_r : q ∣ P.r
  r2_eq : P.r2 = 96 * l * g ^ 2 * t * P.r
  fine_exact : q * P.r3 = P.r * f * t
  diamond_exact : P.rdiamond + (q - 1) * P.r3 = P.r1 + P.r2 + P.r
  systems_eq : P.s = q * P.r3 + 7 * P.rdiamond
  fine_palette_eq : P.k1 = 2 * P.r3
  coarse_palette_eq : P.k2 = 2 * P.rdiamond
  small_budget : 100 * (P.r2 + P.r + q * P.r3) ≤ P.r1
  cluster_capacity : P.r * t ^ 2 ≤ m
  diamond_lower : 99 * P.r1 ≤ 100 * P.rdiamond
  diamond_upper : 100 * P.rdiamond ≤ 101 * P.r1
  systems_upper : P.s ≤ 8 * P.r1
  reserved_exact : P.r1 + P.r2 + P.r3 + 6 * P.rdiamond + P.r = P.s
  reserved_sub : P.r1 + P.r2 + P.r3 + 6 * P.rdiamond = P.s - P.r
  selected_exact : q * P.k1 + 7 * P.k2 = 2 * P.s

/-- The budget is exactly a fixed coefficient times the chosen small degree. -/
theorem make_budget (l g t f q r1 n : ℕ) :
    (make l g t f q r1 n).r2 + (make l g t f q r1 n).r +
        q * (make l g t f q r1 n).r3 = budgetCoefficient l g t f * (q * n) := by
  simp only [make, budgetCoefficient]
  ring

/-- All coupled natural-number identities follow from the one small budget.
In particular the definition of `rdiamond` never truncates. -/
theorem make_valid (l g t f q m r1 n : ℕ)
    (ht : 0 < t) (hf : 0 < f) (hq : 0 < q) (hn : 0 < n)
    (hbudget : 100 * (budgetCoefficient l g t f * (q * n)) ≤ r1)
    (hcapacity : q * n * t ^ 2 ≤ m) :
    Valid l g t f q m (make l g t f q r1 n) := by
  let P := make l g t f q r1 n
  have hr : 0 < P.r := Nat.mul_pos hq hn
  have hr3 : 0 < P.r3 := Nat.mul_pos (Nat.mul_pos hf ht) hn
  have hsmall : 100 * (P.r2 + P.r + q * P.r3) ≤ P.r1 := by
    change 100 * ((make l g t f q r1 n).r2 + (make l g t f q r1 n).r +
      q * (make l g t f q r1 n).r3) ≤ r1
    rw [make_budget]
    exact hbudget
  have hr1 : 0 < P.r1 := by omega
  have hqm : (q - 1) * P.r3 + P.r3 = q * P.r3 := by
    have hq' : q - 1 + 1 = q := by omega
    nlinarith
  have hcut : (q - 1) * P.r3 ≤ P.r1 + P.r2 + P.r := by omega
  have hdiamond : P.rdiamond + (q - 1) * P.r3 = P.r1 + P.r2 + P.r :=
    Nat.sub_add_cancel hcut
  have hrdpos : 0 < P.rdiamond := by omega
  have hrdlo : 99 * P.r1 ≤ 100 * P.rdiamond := by omega
  have hrdup : 100 * P.rdiamond ≤ 101 * P.r1 := by omega
  have hsys : P.s = q * P.r3 + 7 * P.rdiamond := rfl
  have hreserve : P.r1 + P.r2 + P.r3 + 6 * P.rdiamond + P.r = P.s := by omega
  refine ⟨hr1, hr, hr3, hrdpos, ?_, rfl, ?_, hdiamond, hsys, rfl, rfl,
    hsmall, hcapacity, hrdlo, hrdup, ?_, hreserve, ?_, ?_⟩
  · exact dvd_mul_right q n
  · dsimp [P, make]
    ring
  · change P.s ≤ 8 * P.r1
    omega
  · change P.r1 + P.r2 + P.r3 + 6 * P.rdiamond = P.s - P.r
    omega
  · change q * (2 * P.r3) + 7 * (2 * P.rdiamond) = 2 * P.s
    rw [hsys]
    ring

/-- Both palettes are positive even integers. -/
theorem Valid.palettes (l g t f q m : ℕ) (P : Data) (h : Valid l g t f q m P) :
    0 < P.k1 ∧ Even P.k1 ∧ 0 < P.k2 ∧ Even P.k2 := by
  rw [h.fine_palette_eq, h.coarse_palette_eq]
  have := h.r3_pos
  have := h.rdiamond_pos
  exact ⟨by omega, ⟨P.r3, by omega⟩, by omega, ⟨P.rdiamond, by omega⟩⟩

/-- The apparent quotient in `r3 = r*f*t/q` is an exact integer quotient. -/
theorem Valid.fine_quotient (l g t f q m : ℕ) (P : Data)
    (h : Valid l g t f q m P) (hq : 0 < q) :
    P.r3 = P.r * f * t / q := by
  rw [← h.fine_exact, Nat.mul_div_cancel_left _ hq]

/-- The required, possibly smaller, period also divides the constructed `r`. -/
theorem Valid.required_period (l g t f q m : ℕ) (P : Data)
    (h : Valid l g t f q m P) :
    q / Nat.gcd q (f * t) ∣ P.r := by
  exact dvd_trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left q (f * t))) h.q_dvd_r

/-- Downward integer rounding retains at least half a target of size two. -/
theorem floor_half (x : ℝ) (hx : 2 ≤ x) :
    0 < ⌊x⌋₊ ∧ x / 2 ≤ (⌊x⌋₊ : ℝ) ∧ (⌊x⌋₊ : ℝ) ≤ x := by
  have hlow := Nat.lt_floor_add_one x
  have hupp := Nat.floor_le (show 0 ≤ x by linarith)
  have hpos : (0 : ℝ) < ⌊x⌋₊ := by linarith
  exact ⟨by exact_mod_cast hpos, by linarith, hupp⟩

/-- A threshold before the cluster order simultaneously controls both
roundings.  The small degree is a multiple of the fixed palette count. -/
theorem exists_rounding_threshold (rho xi : ℝ) (q : ℕ)
    (hrho : 0 < rho) (hxi : 0 < xi) (hq : 0 < q) :
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m →
      let r1 := ⌊rho * m⌋₊
      let n := ⌊xi * m / q⌋₊
      0 < n ∧ rho * m / 2 ≤ (r1 : ℝ) ∧ (r1 : ℝ) ≤ rho * m ∧
        xi * m / 2 ≤ (q * n : ℕ) ∧ (q * n : ℕ) ≤ xi * m := by
  let m₀ := max ⌈4 / rho⌉₊ ⌈4 * q / xi⌉₊ + 1
  refine ⟨m₀, by omega, ?_⟩
  intro m hm
  have hmr : ⌈4 / rho⌉₊ ≤ m := by dsimp [m₀] at hm; omega
  have hmx : ⌈4 * q / xi⌉₊ ≤ m := by dsimp [m₀] at hm; omega
  have hrr : 4 / rho ≤ (m : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hmr)
  have hxx : 4 * q / xi ≤ (m : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hmx)
  have hr4 : 4 ≤ rho * m := by
    have := (div_le_iff₀ hrho).mp hrr
    nlinarith
  have hx4 : 4 * q ≤ xi * m := by
    have := (div_le_iff₀ hxi).mp hxx
    nlinarith
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hx2 : 2 ≤ xi * m / q := (le_div_iff₀ hqR).mpr (by linarith)
  obtain ⟨_, hrl, hru⟩ := floor_half (rho * m) (by linarith)
  obtain ⟨hn, hnl, hnu⟩ := floor_half (xi * m / q) hx2
  refine ⟨hn, hrl, hru, ?_, ?_⟩
  · have h := mul_le_mul_of_nonneg_left hnl hqR.le
    push_cast
    calc
      xi * m / 2 = q * ((xi * m / q) / 2) := by field_simp
      _ ≤ _ := h
  · have h := mul_le_mul_of_nonneg_left hnu hqR.le
    push_cast
    calc
      _ ≤ q * (xi * m / q) := h
      _ = xi * m := by field_simp

/-- Explicit cluster-scaled bounds accompanying the constructed parameters. -/
structure Scaled (rho xi : ℝ) (m : ℕ) (P : Data) : Prop where
  r1_lower : rho * m / 2 ≤ (P.r1 : ℝ)
  r1_upper : (P.r1 : ℝ) ≤ rho * m
  r_lower : xi * m / 2 ≤ (P.r : ℝ)
  r_upper : (P.r : ℝ) ≤ xi * m

/-- Construct the complete integer data at every sufficiently large cluster
order.  The caller supplies fixed positive ratios, not integer parameters
or a rounding/divisibility oracle. -/
theorem exists_uniform_data (l g t f q : ℕ) (rho xi : ℝ)
    (ht : 0 < t) (hf : 0 < f) (hq : 0 < q)
    (hrho : 0 < rho) (hxi : 0 < xi)
    (hbudget : 400 * (budgetCoefficient l g t f : ℝ) * xi ≤ rho)
    (hcapacity : xi * (t : ℝ) ^ 2 ≤ 1) :
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m →
      ∃ P : Data, Valid l g t f q m P ∧ Scaled rho xi m P := by
  obtain ⟨m₀, hm₀, hround⟩ := exists_rounding_threshold rho xi q hrho hxi hq
  refine ⟨m₀, hm₀, ?_⟩
  intro m hm
  obtain ⟨hn, hr1l, hr1u, hrl, hru⟩ := hround m hm
  let n := ⌊xi * m / q⌋₊
  let r1 := ⌊rho * m⌋₊
  have hbudget' : 100 * (budgetCoefficient l g t f * (q * n)) ≤ r1 := by
    have hC : (0 : ℝ) ≤ budgetCoefficient l g t f := Nat.cast_nonneg _
    have h1 := mul_le_mul_of_nonneg_left hru (show 0 ≤ 100 *
      (budgetCoefficient l g t f : ℝ) by positivity)
    have h2 := mul_le_mul_of_nonneg_right hbudget (Nat.cast_nonneg m)
    have h3 : (100 * (budgetCoefficient l g t f : ℝ) * (q * n : ℕ) : ℝ) ≤ r1 := by
      dsimp [n, r1]
      nlinarith only [h1, h2, hr1l]
    have h4 : 100 * budgetCoefficient l g t f * (q * n) ≤ r1 := by
      exact_mod_cast h3
    simpa only [Nat.mul_assoc] using h4
  have hcapacity' : q * n * t ^ 2 ≤ m := by
    have h1 := mul_le_mul_of_nonneg_right hru (sq_nonneg (t : ℝ))
    have h2 := mul_le_mul_of_nonneg_right hcapacity (Nat.cast_nonneg m)
    have h3 : ((q * n : ℕ) : ℝ) * (t : ℝ) ^ 2 ≤ m := by
      dsimp [n]
      nlinarith only [h1, h2]
    exact_mod_cast h3
  refine ⟨make l g t f q r1 n,
    make_valid l g t f q m r1 n ht hf hq hn hbudget' hcapacity', ?_⟩
  exact ⟨hr1l, hr1u, hrl, hru⟩

/-- Actual palette fractions have fixed positive lower bounds and the
manuscript upper bounds.  Here `m` is the cluster order, so the side order
is `t*m/2`. The upper degree bound is the one obtained from simplicity. -/
theorem palette_fraction_bounds (l g t f q m k : ℕ) (P : Data)
    (rho xi alpha : ℝ) (ht : 0 < t) (hf : 0 < f) (hq : 0 < q) (hm : 0 < m)
    (hrho : 0 < rho) (hxi : 0 < xi) (halpha : 0 < alpha)
    (h : Valid l g t f q m P) (hscale : Scaled rho xi m P)
    (hkl : alpha * t * m / 2 ≤ (k : ℝ)) (hku : (k : ℝ) ≤ t * m) :
    0 < k ∧
      xi * f / q ≤ (P.k1 : ℝ) / k ∧
      (P.k1 : ℝ) / k ≤ 4 * xi * f / (alpha * q) ∧
      rho / (2 * t) ≤ (P.k2 : ℝ) / k ∧
      (P.k2 : ℝ) / k ≤ 8 * rho / (alpha * t) ∧
      (P.s : ℝ) ≤ 8 * rho * m := by
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hfR : (0 : ℝ) < f := by exact_mod_cast hf
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hkR : (0 : ℝ) < k := (by positivity : 0 < alpha * t * m / 2).trans_le hkl
  have hkNat : 0 < k := by exact_mod_cast hkR
  have hfineq : (q : ℝ) * P.k1 = 2 * P.r * f * t := by
    rw [h.fine_palette_eq]
    have heq : (q : ℝ) * P.r3 = (P.r : ℝ) * f * t := by exact_mod_cast h.fine_exact
    push_cast
    nlinarith only [heq]
  have hrlo := hscale.r_lower
  have hrup := hscale.r_upper
  have hr1lo := hscale.r1_lower
  have hr1up := hscale.r1_upper
  have hk2loNat : P.r1 ≤ P.k2 := by
    rw [h.coarse_palette_eq]
    have := h.diamond_lower
    omega
  have hk2upNat : P.k2 ≤ 4 * P.r1 := by
    rw [h.coarse_palette_eq]
    have := h.diamond_upper
    omega
  have hk2lo : rho * m / 2 ≤ (P.k2 : ℝ) := hr1lo.trans (by exact_mod_cast hk2loNat)
  have hk2up : (P.k2 : ℝ) ≤ 4 * rho * m := by
    have hbound : (P.k2 : ℝ) ≤ 4 * P.r1 := by exact_mod_cast hk2upNat
    linarith
  refine ⟨hkNat, ?_, ?_, ?_, ?_, ?_⟩
  · apply (le_div_iff₀ hkR).mpr
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hqR).mpr
    have h1 := mul_le_mul_of_nonneg_left hku (mul_nonneg hxi.le hfR.le)
    have h2 := mul_le_mul_of_nonneg_right hrlo (show 0 ≤ 2 * (f : ℝ) * t by positivity)
    nlinarith only [h1, h2, hfineq]
  · apply (div_le_div_iff₀ hkR (mul_pos halpha hqR)).mpr
    have h1 := mul_le_mul_of_nonneg_right hrup
      (show 0 ≤ 2 * alpha * (f : ℝ) * t by positivity)
    have h2 := mul_le_mul_of_nonneg_left hkl (show 0 ≤ 4 * xi * f by positivity)
    have heq := congrArg (fun x : ℝ => alpha * x) hfineq
    nlinarith only [h1, h2, heq]
  · apply (le_div_iff₀ hkR).mpr
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (show 0 < 2 * (t : ℝ) by positivity)).mpr
    have h1 := mul_le_mul_of_nonneg_left hku hrho.le
    have h2 := mul_le_mul_of_nonneg_right hk2lo (show 0 ≤ 2 * (t : ℝ) by positivity)
    nlinarith only [h1, h2]
  · apply (div_le_div_iff₀ hkR (mul_pos halpha htR)).mpr
    have h1 := mul_le_mul_of_nonneg_right hk2up (mul_nonneg halpha.le htR.le)
    have h2 := mul_le_mul_of_nonneg_left hkl (show 0 ≤ 8 * rho by positivity)
    nlinarith only [h1, h2]
  · have hs : (P.s : ℝ) ≤ 8 * P.r1 := by exact_mod_cast h.systems_upper
    linarith

/-- Fixed real inequalities sufficient for every later integer choice. -/
structure Rates (l g t f q : ℕ)
    (alpha fineMax coarseMax reserveMax rhoMax xiMax rho xi : ℝ) : Prop where
  rho_pos : 0 < rho
  xi_pos : 0 < xi
  rho_le : rho ≤ rhoMax
  xi_le : xi ≤ xiMax
  budget : 400 * (budgetCoefficient l g t f : ℝ) * xi ≤ rho
  cluster : xi * (t : ℝ) ^ 2 ≤ 1
  fine : 4 * xi * f / (alpha * q) ≤ fineMax
  coarse : 8 * rho / (alpha * t) ≤ coarseMax
  reserved : 16 * rho / t ≤ reserveMax
  total : 128 * rho ≤ alpha * t

/-- Arbitrarily small requested bounds can be met simultaneously by fixed
positive ratios.  No actual cluster order, degree, or integer palette is
an input to this choice. -/
theorem exists_rates (l g t f q : ℕ)
    (alpha fineMax coarseMax reserveMax rhoMax xiMax : ℝ)
    (ht : 0 < t) (hf : 0 < f) (hq : 0 < q)
    (halpha : 0 < alpha) (hfine : 0 < fineMax) (hcoarse : 0 < coarseMax)
    (hreserve : 0 < reserveMax) (hrhomax : 0 < rhoMax) (hximax : 0 < xiMax) :
    ∃ rho xi : ℝ, Rates l g t f q
      alpha fineMax coarseMax reserveMax rhoMax xiMax rho xi := by
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hfR : (0 : ℝ) < f := by exact_mod_cast hf
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  let C : ℝ := budgetCoefficient l g t f
  have hC : 0 < C := by
    dsimp [C]
    exact_mod_cast (show 0 < budgetCoefficient l g t f by unfold budgetCoefficient; omega)
  let rho := min rhoMax (min (coarseMax * alpha * t / 8)
    (min (reserveMax * t / 16) (alpha * t / 128)))
  have hrho : 0 < rho := by dsimp [rho]; positivity
  have hrhoMax : rho ≤ rhoMax := min_le_left _ _
  have hrhoCoarse : rho ≤ coarseMax * alpha * t / 8 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hrhoReserve : rho ≤ reserveMax * t / 16 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrhoTotal : rho ≤ alpha * t / 128 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  let xi := min xiMax (min (rho / (400 * C))
    (min (1 / (t : ℝ)^2) (fineMax * alpha * q / (4 * f))))
  have hxi : 0 < xi := by dsimp [xi]; positivity
  have hxiMax : xi ≤ xiMax := min_le_left _ _
  have hxiBudget : xi ≤ rho / (400 * C) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hxiCluster : xi ≤ 1 / (t : ℝ)^2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hxiFine : xi ≤ fineMax * alpha * q / (4 * f) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨rho, xi, hrho, hxi, hrhoMax, hxiMax, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := (le_div_iff₀ (show 0 < 400 * C by positivity)).mp hxiBudget
    change 400 * C * xi ≤ rho
    nlinarith
  · exact (le_div_iff₀ (sq_pos_of_pos htR)).mp hxiCluster
  · apply (div_le_iff₀ (mul_pos halpha hqR)).mpr
    have h := (le_div_iff₀ (show 0 < 4 * (f : ℝ) by positivity)).mp hxiFine
    nlinarith
  · apply (div_le_iff₀ (mul_pos halpha htR)).mpr
    nlinarith
  · apply (div_le_iff₀ htR).mpr
    linarith
  · linarith

/-- With the main ratio already fixed, a sufficiently large reduced order
meets every coarse and total bound. This is the source quantifier order:
`rho` precedes the reduced graph and its cluster count. -/
theorem exists_cluster_count_threshold (rho alpha coarseMax reserveMax : ℝ)
    (halpha : 0 < alpha)
    (hcoarse : 0 < coarseMax) (hreserve : 0 < reserveMax) :
    ∃ t₀ : ℕ, 1 ≤ t₀ ∧ ∀ t : ℕ, t₀ ≤ t →
      8 * rho / (alpha * t) ≤ coarseMax ∧
      16 * rho / t ≤ reserveMax ∧ 128 * rho ≤ alpha * t := by
  let t₀ := max ⌈8 * rho / (alpha * coarseMax)⌉₊
    (max ⌈16 * rho / reserveMax⌉₊ ⌈128 * rho / alpha⌉₊) + 1
  refine ⟨t₀, by omega, ?_⟩
  intro t ht
  have htNat : 0 < t := by dsimp [t₀] at ht; omega
  have htR : (0 : ℝ) < t := by exact_mod_cast htNat
  have h1n : ⌈8 * rho / (alpha * coarseMax)⌉₊ ≤ t := by dsimp [t₀] at ht; omega
  have h2n : ⌈16 * rho / reserveMax⌉₊ ≤ t := by dsimp [t₀] at ht; omega
  have h3n : ⌈128 * rho / alpha⌉₊ ≤ t := by dsimp [t₀] at ht; omega
  have h1 : 8 * rho / (alpha * coarseMax) ≤ (t : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast h1n)
  have h2 : 16 * rho / reserveMax ≤ (t : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast h2n)
  have h3 : 128 * rho / alpha ≤ (t : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast h3n)
  refine ⟨?_, ?_, ?_⟩
  · apply (div_le_iff₀ (mul_pos halpha htR)).mpr
    have he := (div_le_iff₀ (mul_pos halpha hcoarse)).mp h1
    nlinarith only [he]
  · apply (div_le_iff₀ htR).mpr
    have he := (div_le_iff₀ hreserve).mp h2
    nlinarith only [he]
  · have he := (div_le_iff₀ halpha).mp h3
    nlinarith only [he]

/-- Choose only the smaller ratio after the reduced order is known; the
main absorber ratio stays fixed. -/
theorem exists_rates_fixed_rho (l g t f q : ℕ)
    (alpha fineMax coarseMax reserveMax rho xiMax : ℝ)
    (ht : 0 < t) (hf : 0 < f) (hq : 0 < q)
    (halpha : 0 < alpha) (hfine : 0 < fineMax)
    (hrho : 0 < rho) (hximax : 0 < xiMax)
    (hcoarse : 8 * rho / (alpha * t) ≤ coarseMax)
    (hreserve : 16 * rho / t ≤ reserveMax)
    (htotal : 128 * rho ≤ alpha * t) :
    ∃ xi : ℝ, Rates l g t f q
      alpha fineMax coarseMax reserveMax rho xiMax rho xi := by
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hfR : (0 : ℝ) < f := by exact_mod_cast hf
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  let C : ℝ := budgetCoefficient l g t f
  have hC : 0 < C := by
    dsimp [C]
    exact_mod_cast (show 0 < budgetCoefficient l g t f by unfold budgetCoefficient; omega)
  let xi := min xiMax (min (rho / (400 * C))
    (min (1 / (t : ℝ)^2) (fineMax * alpha * q / (4 * f))))
  have hxi : 0 < xi := by dsimp [xi]; positivity
  have hxiMax : xi ≤ xiMax := min_le_left _ _
  have hxiBudget : xi ≤ rho / (400 * C) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hxiCluster : xi ≤ 1 / (t : ℝ)^2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hxiFine : xi ≤ fineMax * alpha * q / (4 * f) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨xi, hrho, hxi, le_rfl, hxiMax, ?_, ?_, ?_, hcoarse, hreserve, htotal⟩
  · have he := (le_div_iff₀ (show 0 < 400 * C by positivity)).mp hxiBudget
    change 400 * C * xi ≤ rho
    nlinarith only [he]
  · exact (le_div_iff₀ (sq_pos_of_pos htR)).mp hxiCluster
  · apply (div_le_iff₀ (mul_pos halpha hqR)).mpr
    have he := (le_div_iff₀ (show 0 < 4 * (f : ℝ) by positivity)).mp hxiFine
    nlinarith only [he]

/-- The final numerical conclusions for an admissible ambient degree. -/
structure PaletteBounds (t m k : ℕ) (P : Data)
    (lam0 fineMax coarseMax reserveMax : ℝ) : Prop where
  fine_lower : lam0 ≤ (P.k1 : ℝ) / k
  fine_upper : (P.k1 : ℝ) / k ≤ fineMax
  coarse_lower : lam0 ≤ (P.k2 : ℝ) / k
  coarse_upper : (P.k2 : ℝ) / k ≤ coarseMax
  selected_half : 4 * P.s ≤ k
  reserve_upper : (2 * P.s : ℕ) ≤ reserveMax * t * m

/-- Assemble the scaled integer bounds and fixed rates into actual palette
bounds, including a positive fraction of unused colors. -/
theorem palette_bounds_of_rates (l g t f q m k : ℕ) (P : Data)
    (alpha fineMax coarseMax reserveMax rhoMax xiMax rho xi : ℝ)
    (ht : 0 < t) (hf : 0 < f) (hq : 0 < q) (hm : 0 < m)
    (halpha : 0 < alpha)
    (hrates : Rates l g t f q alpha fineMax coarseMax reserveMax rhoMax xiMax rho xi)
    (h : Valid l g t f q m P) (hscale : Scaled rho xi m P)
    (hkl : alpha * t * m / 2 ≤ (k : ℝ)) (hku : (k : ℝ) ≤ t * m) :
    PaletteBounds t m k P (min (xi * f / q) (rho / (2 * t)))
      fineMax coarseMax reserveMax := by
  obtain ⟨_, hfl, hfu, hcl, hcu, hsu⟩ := palette_fraction_bounds l g t f q m k P
    rho xi alpha ht hf hq hm hrates.rho_pos hrates.xi_pos halpha h hscale hkl hku
  refine ⟨(min_le_left _ _).trans hfl, hfu.trans hrates.fine,
    (min_le_right _ _).trans hcl, hcu.trans hrates.coarse, ?_, ?_⟩
  · have hb := mul_le_mul_of_nonneg_right hrates.total (Nat.cast_nonneg m)
    have hx : (4 * P.s : ℕ) ≤ (k : ℝ) := by
      push_cast
      nlinarith only [hsu, hb, hkl]
    exact_mod_cast hx
  · have htR : (0 : ℝ) < t := by exact_mod_cast ht
    have hb := (div_le_iff₀ htR).mp hrates.reserved
    have hb' := mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg m)
    push_cast
    nlinarith only [hsu, hb']

/-- Complete parameter construction with the manuscript quantifier order.
The positive main ratio is fixed first. A lower reduced-order threshold
comes next. Once a permitted reduced order is known, the small ratio,
common lower palette fraction and cluster-order threshold are fixed before
every actual cluster size and every admissible ambient degree. -/
theorem exists_uniform_parameters (l g f q : ℕ)
    (alpha fineMax coarseMax reserveMax rho xiMax : ℝ)
    (hf : 0 < f) (hq : 0 < q) (halpha : 0 < alpha)
    (hfine : 0 < fineMax) (hcoarse : 0 < coarseMax) (hreserve : 0 < reserveMax)
    (hrho : 0 < rho) (hximax : 0 < xiMax) :
    ∃ t₀ : ℕ, 1 ≤ t₀ ∧ ∀ t : ℕ, t₀ ≤ t →
      ∃ xi lam0 : ℝ, 0 < xi ∧ xi ≤ xiMax ∧ 0 < lam0 ∧
        ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m →
          ∃ P : Data, Valid l g t f q m P ∧ Scaled rho xi m P ∧
            ∀ k : ℕ, alpha * t * m / 2 ≤ (k : ℝ) → (k : ℝ) ≤ t * m →
              PaletteBounds t m k P lam0 fineMax coarseMax reserveMax := by
  obtain ⟨t₀, ht₀, hthreshold⟩ := exists_cluster_count_threshold rho alpha coarseMax reserveMax
    halpha hcoarse hreserve
  refine ⟨t₀, ht₀, ?_⟩
  intro t ht
  have htpos : 0 < t := by omega
  have htR : (0 : ℝ) < t := by exact_mod_cast htpos
  have hfR : (0 : ℝ) < f := by exact_mod_cast hf
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  obtain ⟨hcoarse', hreserve', htotal⟩ := hthreshold t ht
  obtain ⟨xi, hxi⟩ := exists_rates_fixed_rho l g t f q alpha fineMax coarseMax reserveMax
    rho xiMax htpos hf hq halpha hfine hrho hximax hcoarse' hreserve' htotal
  obtain ⟨m₀, hm₀, hdata⟩ := exists_uniform_data l g t f q rho xi htpos hf hq
    hrho hxi.xi_pos hxi.budget hxi.cluster
  refine ⟨xi, min (xi * f / q) (rho / (2 * t)), hxi.xi_pos, hxi.xi_le,
    ?_, m₀, hm₀, ?_⟩
  · apply lt_min
    · exact div_pos (mul_pos hxi.xi_pos hfR) hqR
    · exact div_pos hrho (by positivity)
  · intro m hm
    have hmpos : 0 < m := by omega
    obtain ⟨P, hP, hscale⟩ := hdata m hm
    refine ⟨P, hP, hscale, ?_⟩
    intro k hkl hku
    exact palette_bounds_of_rates l g t f q m k P alpha fineMax coarseMax reserveMax
      rho xiMax rho xi htpos hf hq hmpos halpha hxi hP hscale hkl hku

/-- The prescribed side-order divisibility produces an actual equal
cluster order with the full refinement divisibility. -/
theorem exists_cluster_order (l f q h side : ℕ) (hf : 0 < f)
    (hfq : f ∣ q) (hside : 12 * h * q * l ∣ side) :
    ∃ m : ℕ, 2 * side = (6 * f * h) * m ∧ 4 * l * (q / f) ∣ m := by
  obtain ⟨c, rfl⟩ := hfq
  obtain ⟨n, rfl⟩ := hside
  refine ⟨4 * l * c * n, ?_, ?_⟩
  · ring
  · rw [Nat.mul_div_cancel_left c hf]
    exact ⟨n, rfl⟩

/-- The fixed refinements in the manuscript imply all six structural
integrality conditions of the absorber. This proves integer divisibility,
so there is no appeal to asymptotic notation or informal rounding. -/
theorem spanning_divisibilities (l g f q h m : ℕ) (hf : 0 < f)
    (hfg : 7 * g * (g - 1) ∣ f) (hfq : f ∣ q)
    (hm : 4 * l * (q / f) ∣ m) :
    14 ∣ 6 * f * h ∧ f ∣ 6 * f * h ∧ g ∣ 6 * f * h ∧
      4 * l ∣ m ∧ q ∣ f * m ∧
      3 * g * (g - 1) ∣ 2 * f * (6 * f * h) := by
  obtain ⟨b, hb⟩ := hfg
  obtain ⟨c, rfl⟩ := hfq
  rw [Nat.mul_div_cancel_left c hf] at hm
  obtain ⟨n, rfl⟩ := hm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨3 * g * (g - 1) * b * h, ?_⟩
    rw [hb]
    ring
  · exact ⟨6 * h, by ring⟩
  · refine ⟨6 * 7 * (g - 1) * b * h, ?_⟩
    rw [hb]
    ring
  · exact ⟨c * n, by ring⟩
  · exact ⟨4 * l * n, by ring⟩
  · refine ⟨28 * f * b * h, ?_⟩
    rw [hb]
    ring

/-- A common lower palette fraction can be decreased without changing the
actual integer parameters. -/
theorem PaletteBounds.mono_lower {t m k : ℕ} {P : Data}
    {lam0 lam1 fineMax coarseMax reserveMax : ℝ}
    (h : PaletteBounds t m k P lam0 fineMax coarseMax reserveMax)
    (hlam : lam1 ≤ lam0) :
    PaletteBounds t m k P lam1 fineMax coarseMax reserveMax :=
  ⟨hlam.trans h.fine_lower, h.fine_upper, hlam.trans h.coarse_lower,
    h.coarse_upper, h.selected_half, h.reserve_upper⟩

/-- For any fixed finite list of possible cluster counts, one positive
palette lower bound and one cluster-order threshold work for the whole
list. The small ratio is allowed to depend on the cluster count, exactly
as in the source parameter choice. -/
theorem exists_uniform_parameter_family (l g f q : ℕ)
    (alpha fineMax coarseMax reserveMax rho xiMax : ℝ)
    (hf : 0 < f) (hq : 0 < q) (halpha : 0 < alpha)
    (hfine : 0 < fineMax) (hcoarse : 0 < coarseMax) (hreserve : 0 < reserveMax)
    (hrho : 0 < rho) (hximax : 0 < xiMax) :
    ∃ t₀ : ℕ, 1 ≤ t₀ ∧
      ∀ (I : Type*) [Fintype I] [Nonempty I] (t : I → ℕ),
        (∀ i, t₀ ≤ t i) →
        ∃ (xi : I → ℝ) (lam0 : ℝ),
          (∀ i, 0 < xi i ∧ xi i ≤ xiMax) ∧ 0 < lam0 ∧
          ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ i, ∀ m : ℕ, m₀ ≤ m →
            ∃ P : Data, Valid l g (t i) f q m P ∧ Scaled rho (xi i) m P ∧
              ∀ k : ℕ, alpha * t i * m / 2 ≤ (k : ℝ) → (k : ℝ) ≤ t i * m →
                PaletteBounds (t i) m k P lam0 fineMax coarseMax reserveMax := by
  obtain ⟨t₀, ht₀, hparameters⟩ := exists_uniform_parameters l g f q
    alpha fineMax coarseMax reserveMax rho xiMax
    hf hq halpha hfine hcoarse hreserve hrho hximax
  refine ⟨t₀, ht₀, ?_⟩
  intro I _ _ t ht
  have hc := fun i => hparameters (t i) (ht i)
  choose xi lam hx hxu hlam mi hmi hdata using hc
  let lam0 := Finset.univ.inf' Finset.univ_nonempty lam
  have hlam0 : 0 < lam0 := by
    apply (Finset.lt_inf'_iff _).mpr
    intro i _
    exact hlam i
  have hlamle (i : I) : lam0 ≤ lam i :=
    Finset.inf'_le _ (Finset.mem_univ i)
  let m₀ := max 1 (Finset.univ.sup mi)
  refine ⟨xi, lam0, (fun i => ⟨hx i, hxu i⟩), hlam0, m₀, le_max_left _ _, ?_⟩
  intro i m hm
  have him : mi i ≤ m := by
    exact (Finset.le_sup (Finset.mem_univ i)).trans ((le_max_right _ _).trans hm)
  obtain ⟨P, hP, hscale, hbound⟩ := hdata i m him
  refine ⟨P, hP, hscale, ?_⟩
  intro k hkl hku
  exact (hbound k hkl hku).mono_lower (hlamle i)

/-- A positive fine target incorporating every scalar localization bound. -/
def fineTarget (beta theta : ℝ) (q : ℕ) : ℝ :=
  min (beta * theta / (262144 * (q : ℝ)^2))
    (min (beta * theta / (5600 * q)) (1 / (100000 * q)))

/-- A positive coarse target incorporating the localization and total budgets. -/
def coarseTarget (beta theta : ℝ) : ℝ :=
  min (beta * theta / 12845056) (beta * theta / 5600)

theorem source_targets_pos (beta theta : ℝ) (q : ℕ)
    (hbeta : 0 < beta) (htheta : 0 < theta) (hq : 0 < q) :
    0 < fineTarget beta theta q ∧ 0 < coarseTarget beta theta := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  constructor
  · unfold fineTarget
    positivity
  · unfold coarseTarget
    positivity

/-- The four displayed localization requirements, including actual color
counts, for `p1=1/q` and `p2=1/7`. -/
structure SourcePaletteBounds (q k : ℕ) (P : Data) (beta theta : ℝ) : Prop where
  fine : (P.k1 : ℝ) / k ≤ beta * (1 / (q : ℝ))^2 * theta / 262144
  coarse : (P.k2 : ℝ) / k ≤ beta * (1 / 7 : ℝ)^2 * theta / 262144
  selected : ((q * P.k1 + 7 * P.k2 : ℕ) : ℝ) ≤ beta * theta * k / 400
  fine_total : ((q * P.k1 : ℕ) : ℝ) ≤ beta * (1 / 7 : ℝ) * theta * k / 400
  overlap : (5 / 4 : ℝ) * q * ((P.k1 : ℝ) / k) ≤ (1 / 7 : ℝ)^2 / 1024

/-- The chosen targets imply every source palette-size inequality; the
source constants `2^18`, `400`, and `1024` are retained. -/
theorem source_palette_bounds (q k : ℕ) (P : Data) (beta theta : ℝ)
    (hq : 0 < q) (hk : 0 < k) (hbeta : 0 < beta) (htheta : 0 < theta)
    (hf : (P.k1 : ℝ) / k ≤ fineTarget beta theta q)
    (hc : (P.k2 : ℝ) / k ≤ coarseTarget beta theta) :
    SourcePaletteBounds q k P beta theta := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hb : 0 < beta * theta := mul_pos hbeta htheta
  have hf1 : (P.k1 : ℝ) / k ≤ beta * theta / (262144 * (q : ℝ)^2) :=
    hf.trans (min_le_left _ _)
  have hf2 : (P.k1 : ℝ) / k ≤ beta * theta / (5600 * q) :=
    hf.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hf3 : (P.k1 : ℝ) / k ≤ 1 / (100000 * q) :=
    hf.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hc1 : (P.k2 : ℝ) / k ≤ beta * theta / 12845056 :=
    hc.trans (min_le_left _ _)
  have hc2 : (P.k2 : ℝ) / k ≤ beta * theta / 5600 :=
    hc.trans (min_le_right _ _)
  have hfcount : 5600 * (q : ℝ) * P.k1 ≤ beta * theta * k := by
    have hh := (div_le_div_iff₀ hkR (show 0 < 5600 * (q : ℝ) by positivity)).mp hf2
    nlinarith only [hh]
  have hccount : 5600 * (P.k2 : ℝ) ≤ beta * theta * k := by
    have hh := (div_le_div_iff₀ hkR (by norm_num : (0 : ℝ) < 5600)).mp hc2
    nlinarith only [hh]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · calc
      (P.k1 : ℝ) / k ≤ beta * theta / (262144 * (q : ℝ)^2) := hf1
      _ = beta * (1 / (q : ℝ))^2 * theta / 262144 := by field_simp
  · calc
      (P.k2 : ℝ) / k ≤ beta * theta / 12845056 := hc1
      _ = beta * (1 / 7 : ℝ)^2 * theta / 262144 := by ring
  · push_cast
    have hb' : 0 ≤ beta * theta * k := mul_nonneg hb.le hkR.le
    nlinarith only [hfcount, hccount, hb']
  · push_cast
    have hb' : 0 ≤ beta * theta * k := mul_nonneg hb.le hkR.le
    nlinarith only [hfcount, hb']
  · have hh := (le_div_iff₀ (show 0 < 100000 * (q : ℝ) by positivity)).mp hf3
    norm_num
    nlinarith only [hh]

/-- The coupled construction specialized to all four manuscript palette
inequalities, with positive lower fractions and the reserve bound retained.
All size, positivity and integrality claims concern the same actual data. -/
theorem exists_uniform_source_parameters (l g f q : ℕ)
    (alpha beta theta reserveMax rho xiMax : ℝ)
    (hf : 0 < f) (hq : 0 < q) (halpha : 0 < alpha)
    (hbeta : 0 < beta) (htheta : 0 < theta) (hreserve : 0 < reserveMax)
    (hrho : 0 < rho) (hximax : 0 < xiMax) :
    ∃ t₀ : ℕ, 1 ≤ t₀ ∧ ∀ t : ℕ, t₀ ≤ t →
      ∃ xi lam0 : ℝ, 0 < xi ∧ xi ≤ xiMax ∧ 0 < lam0 ∧
        ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m →
          ∃ P : Data, Valid l g t f q m P ∧ Scaled rho xi m P ∧
            ∀ k : ℕ, alpha * t * m / 2 ≤ (k : ℝ) → (k : ℝ) ≤ t * m →
              SourcePaletteBounds q k P beta theta ∧
                PaletteBounds t m k P lam0 (fineTarget beta theta q)
                  (coarseTarget beta theta) reserveMax := by
  obtain ⟨hft, hct⟩ := source_targets_pos beta theta q hbeta htheta hq
  obtain ⟨t₀, ht₀, hparameters⟩ := exists_uniform_parameters l g f q
    alpha (fineTarget beta theta q) (coarseTarget beta theta) reserveMax rho xiMax
    hf hq halpha hft hct hreserve hrho hximax
  refine ⟨t₀, ht₀, ?_⟩
  intro t ht
  have htpos : 0 < t := by omega
  have htR : (0 : ℝ) < t := by exact_mod_cast htpos
  obtain ⟨xi, lam0, hx, hxu, hlam, m₀, hm₀, hdata⟩ := hparameters t ht
  refine ⟨xi, lam0, hx, hxu, hlam, m₀, hm₀, ?_⟩
  intro m hm
  have hmpos : 0 < m := by omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  obtain ⟨P, hP, hscale, hb⟩ := hdata m hm
  refine ⟨P, hP, hscale, ?_⟩
  intro k hkl hku
  have hkR : (0 : ℝ) < k := (by positivity : 0 < alpha * t * m / 2).trans_le hkl
  have hkpos : 0 < k := by exact_mod_cast hkR
  have hbound := hb k hkl hku
  exact ⟨source_palette_bounds q k P beta theta hq hkpos hbeta htheta
    hbound.fine_upper hbound.coarse_upper, hbound⟩

end Overfull.BipartiteFactorization.AbsorberParameters
