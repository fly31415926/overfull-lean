import Overfull.Absorption.Thresholds

/-!
# Uniform threshold schedules with an arbitrary positive error function

The next threshold is chosen only after the current exceptional-set bound
has been determined. The finite minimum retains the correct quantifier
order without assuming that the requested error function is monotone.
-/

namespace Overfull.AbsorptionThresholds

open Classical

/-- The positive finite lower envelope needed when the argument of the
requested function is the actual final exceptional cardinality. -/
noncomputable def lowerEnvelope (f : ℕ → ℝ) : ℕ → ℝ
  | 0 => f 0
  | n+1 => min (lowerEnvelope f n) (f (n+1))

theorem lowerEnvelope_pos (f : ℕ → ℝ) (hf : ∀ n, 0 < f n) (n : ℕ) :
    0 < lowerEnvelope f n := by
  induction n with
  | zero => exact hf 0
  | succ n ih => exact lt_min ih (hf (n+1))

theorem lowerEnvelope_le (f : ℕ → ℝ) {s t : ℕ} (hst : s ≤ t) :
    lowerEnvelope f t ≤ f s := by
  induction t generalizing s with
  | zero =>
    have hs : s = 0 := by omega
    subst s
    exact le_rfl
  | succ t ih =>
    by_cases hs : s ≤ t
    · exact (min_le_left _ _).trans (ih hs)
    · have heq : s = t+1 := by omega
      subst s
      exact min_le_right _ _

theorem lowerEnvelope_antitone (f : ℕ → ℝ) : Antitone (lowerEnvelope f) :=
  antitone_nat_of_succ_le (fun _ => min_le_left _ _)

/-- A finite uniform upper bound for graph-dependent natural parameters. -/
def upperEnvelope (g : ℕ → ℕ) : ℕ → ℕ
  | 0 => g 0
  | n+1 => max (upperEnvelope g n) (g (n+1))

theorem le_upperEnvelope (g : ℕ → ℕ) {s t : ℕ} (hst : s ≤ t) :
    g s ≤ upperEnvelope g t := by
  induction t generalizing s with
  | zero =>
    have hs : s = 0 := by omega
    subst s
    exact le_rfl
  | succ t ih =>
    by_cases hs : s ≤ t
    · exact (ih hs).trans (le_max_left _ _)
    · have heq : s = t+1 := by omega
      subst s
      exact le_max_right _ _

/-- One error and one order bound work for every member of a fixed finite
schedule. They are chosen before the graph selects a band. -/
theorem finite_uniform_parameters (ε : ℕ → ℝ) (N : ℕ → ℕ) (L : ℕ)
    (hε : ∀ i, 0 < ε i) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ n₀ : ℕ,
      ∀ i ≤ L, δ ≤ ε i ∧ N i ≤ n₀ := by
  exact ⟨lowerEnvelope ε L, lowerEnvelope_pos ε hε L, upperEnvelope N L,
    fun i hi => ⟨lowerEnvelope_le ε hi, le_upperEnvelope N hi⟩⟩

/-- The natural exceptional bound at one positive threshold. -/
noncomputable def thresholdBound (c ρ : ℝ) : ℕ := Nat.ceil (c/ρ)

/-- The available next threshold depends on the already fixed current
exceptional bound. The second control function can encode packing or
absorption tolerances. -/
noncomputable def nextThreshold (c : ℝ) (f control : ℕ → ℝ) (ρ : ℝ) : ℝ :=
  min (ρ/2) (min (f (thresholdBound c ρ)/16)
    (control (thresholdBound c ρ)/16))

noncomputable def thresholdSequence (c : ℝ) (f control : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1/2
  | i+1 => nextThreshold c f control (thresholdSequence c f control i)

theorem nextThreshold_pos (c ρ : ℝ) (f control : ℕ → ℝ)
    (hρ : 0 < ρ) (hf : ∀ t, 0 < f t) (hcontrol : ∀ t, 0 < control t) :
    0 < nextThreshold c f control ρ := by
  unfold nextThreshold
  exact lt_min (by positivity)
    (lt_min (by exact div_pos (hf _) (by norm_num))
      (by exact div_pos (hcontrol _) (by norm_num)))

theorem thresholdSequence_pos (c : ℝ) (f control : ℕ → ℝ)
    (hf : ∀ t, 0 < f t) (hcontrol : ∀ t, 0 < control t) (i : ℕ) :
    0 < thresholdSequence c f control i := by
  induction i with
  | zero => norm_num [thresholdSequence]
  | succ i ih => exact nextThreshold_pos c _ f control ih hf hcontrol

theorem thresholdSequence_half (c : ℝ) (f control : ℕ → ℝ) (i : ℕ) :
    thresholdSequence c f control (i+1) ≤ thresholdSequence c f control i/2 :=
  min_le_left _ _

theorem thresholdSequence_strictAnti (c : ℝ) (f control : ℕ → ℝ)
    (hf : ∀ t, 0 < f t) (hcontrol : ∀ t, 0 < control t) :
    StrictAnti (thresholdSequence c f control) := by
  apply strictAnti_nat_of_succ_lt
  intro i
  have hpos := thresholdSequence_pos c f control hf hcontrol i
  have hhalf := thresholdSequence_half c f control i
  linarith only [hpos, hhalf]

theorem thresholdSequence_lt_one (c : ℝ) (f control : ℕ → ℝ)
    (hf : ∀ t, 0 < f t) (hcontrol : ∀ t, 0 < control t) (i : ℕ) :
    thresholdSequence c f control i < 1 := by
  have h := (thresholdSequence_strictAnti c f control hf hcontrol).antitone
    (Nat.zero_le i)
  norm_num only [thresholdSequence] at h
  linarith only [h]

theorem thresholdSequence_error (c : ℝ) (f control : ℕ → ℝ) (i : ℕ) :
    16*thresholdSequence c f control (i+1) ≤
      f (thresholdBound c (thresholdSequence c f control i)) := by
  have h : thresholdSequence c f control (i+1) ≤
      f (thresholdBound c (thresholdSequence c f control i))/16 :=
    (min_le_right _ _).trans (min_le_left _ _)
  linarith only [h]

theorem thresholdSequence_control (c : ℝ) (f control : ℕ → ℝ) (i : ℕ) :
    16*thresholdSequence c f control (i+1) ≤
      control (thresholdBound c (thresholdSequence c f control i)) := by
  have h : thresholdSequence c f control (i+1) ≤
      control (thresholdBound c (thresholdSequence c f control i))/16 :=
    (min_le_right _ _).trans (min_le_right _ _)
  linarith only [h]

/-- A schedule exists for any requested finite length and any positive
function; no monotonicity of either control function is used. -/
theorem exists_threshold_schedule (c : ℝ) (f control : ℕ → ℝ) (L : ℕ)
    (hf : ∀ t, 0 < f t) (hcontrol : ∀ t, 0 < control t) :
    ∃ (ρ : ℕ → ℝ) (t : ℕ → ℕ) (T : ℕ),
      ρ 0 = 1/2 ∧ (∀ i, 0 < ρ i) ∧ StrictAnti ρ ∧
      (∀ i, t i = Nat.ceil (c/ρ i)) ∧
      (∀ i, 16*ρ (i+1) ≤ f (t i) ∧ 16*ρ (i+1) ≤ control (t i)) ∧
      ∀ i ≤ L, t i ≤ T := by
  let ρ := thresholdSequence c f control
  let t := fun i => thresholdBound c (ρ i)
  refine ⟨ρ, t, upperEnvelope t L, rfl,
    thresholdSequence_pos c f control hf hcontrol,
    thresholdSequence_strictAnti c f control hf hcontrol, fun _ => rfl, ?_, ?_⟩
  · intro i
    exact ⟨thresholdSequence_error c f control i,
      thresholdSequence_control c f control i⟩
  · intro i hi
    exact le_upperEnvelope t hi

/-- In particular, the band-count condition can be fixed before the graph. -/
theorem exists_long_threshold_schedule (c : ℝ) (f control : ℕ → ℝ)
    (hf : ∀ t, 0 < f t) (hcontrol : ∀ t, 0 < control t) :
    ∃ (L : ℕ) (ρ : ℕ → ℝ) (t : ℕ → ℕ) (T : ℕ),
      8*c < (L : ℝ) ∧ ρ 0 = 1/2 ∧ (∀ i, 0 < ρ i) ∧ StrictAnti ρ ∧
      (∀ i, t i = Nat.ceil (c/ρ i)) ∧
      (∀ i, 16*ρ (i+1) ≤ f (t i) ∧ 16*ρ (i+1) ≤ control (t i)) ∧
      ∀ i ≤ L, t i ≤ T := by
  obtain ⟨L, hL⟩ := exists_nat_gt (8*c)
  obtain ⟨ρ, t, T, hρ0, hρpos, hρanti, ht, herr, hT⟩ :=
    exists_threshold_schedule c f control L hf hcontrol
  exact ⟨L, ρ, t, T, hL, hρ0, hρpos, hρanti, ht, herr, hT⟩

/-- A schedule constructed with the finite lower envelope controls the
requested function at every possible actual final exceptional cardinality. -/
theorem thresholdSequence_actual_card_error (c : ℝ) (f control : ℕ → ℝ)
    (i s : ℕ)
    (hs : s ≤ thresholdBound c (thresholdSequence c (lowerEnvelope f) control i)) :
    16*thresholdSequence c (lowerEnvelope f) control (i+1) ≤ f s := by
  exact (thresholdSequence_error c (lowerEnvelope f) control i).trans
    (lowerEnvelope_le f hs)

/-- A finite schedule that directly supports the literal final cardinality
as the argument of the arbitrary positive function. -/
theorem exists_actual_card_threshold_schedule (c : ℝ) (f control : ℕ → ℝ)
    (L : ℕ) (hf : ∀ t, 0 < f t) (hcontrol : ∀ t, 0 < control t) :
    ∃ (ρ : ℕ → ℝ) (t : ℕ → ℕ) (T : ℕ),
      ρ 0 = 1/2 ∧ (∀ i, 0 < ρ i) ∧ StrictAnti ρ ∧
      (∀ i, t i = Nat.ceil (c/ρ i)) ∧
      (∀ i, (∀ s ≤ t i, 16*ρ (i+1) ≤ f s) ∧
        16*ρ (i+1) ≤ control (t i)) ∧
      ∀ i ≤ L, t i ≤ T := by
  obtain ⟨ρ, t, T, hzero, hpos, hanti, ht, herr, hT⟩ :=
    exists_threshold_schedule c (lowerEnvelope f) control L
      (lowerEnvelope_pos f hf) hcontrol
  refine ⟨ρ, t, T, hzero, hpos, hanti, ht, ?_, hT⟩
  intro i
  exact ⟨fun s hs => (herr i).1.trans (lowerEnvelope_le f hs), (herr i).2⟩

/-- Once a finite schedule is fixed, a single original error and order
threshold absorb every constant star bound. The selected index and the
retained degree may depend on the graph. -/
theorem uniform_final_error (L : ℕ) (β : ℝ) (f : ℕ → ℝ)
    (t : ℕ → ℕ) (r D : ℕ → ℝ) (hβ : 0 < β) (hf : ∀ s, 0 < f s)
    (hr : ∀ i ≤ L, 16*r i ≤ f (t i)) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, 0 < n₀ ∧
      ∀ (i n : ℕ) (h hfinal a z : ℝ), i ≤ L → n₀ ≤ n →
        β*n ≤ h → 3*h/4 ≤ hfinal → a+z ≤ ε*n →
        a+r i*h+z+D i ≤ f (t i)*hfinal := by
  let μ := lowerEnvelope (fun i => f (t i)) L
  have hμ : 0 < μ := lowerEnvelope_pos _ (fun i => hf (t i)) L
  have hμi (i : ℕ) (hi : i ≤ L) : μ ≤ f (t i) := lowerEnvelope_le _ hi
  let ε := β*μ/16
  have hε : 0 < ε := by dsimp [ε]; positivity
  let N := fun i => Nat.ceil (16*D i/(β*μ))
  let n₀ := max 1 (upperEnvelope N L)
  refine ⟨ε, hε, n₀, by dsimp [n₀]; omega, ?_⟩
  intro i n h hfinal a z hi hn hlinear hfinal_bound hsmall
  have hN : N i ≤ n := (le_upperEnvelope N hi).trans
    ((le_max_right 1 (upperEnvelope N L)).trans hn)
  have hNreal : (N i : ℝ) ≤ n := by exact_mod_cast hN
  have hden : 0 < β*μ := mul_pos hβ hμ
  have hDscaled : 16*D i ≤ (n : ℝ)*(β*μ) :=
    (div_le_iff₀ hden).mp ((Nat.le_ceil (16*D i/(β*μ))).trans hNreal)
  have hmul := mul_le_mul_of_nonneg_left hlinear hμ.le
  have hD : D i ≤ μ*h/16 := by nlinarith only [hDscaled, hmul]
  have herror : a+z ≤ μ*h/16 := by
    dsimp [ε] at hsmall
    nlinarith only [hsmall, hmul]
  have hh : 0 ≤ h := (mul_nonneg hβ.le (Nat.cast_nonneg n)).trans hlinear
  have hμh := mul_le_mul_of_nonneg_right (hμi i hi) hh
  have hrh := mul_le_mul_of_nonneg_right (hr i hi) hh
  have hlast := mul_le_mul_of_nonneg_left hfinal_bound (hf (t i)).le
  have hfh : 0 ≤ f (t i)*h := mul_nonneg (hf (t i)).le hh
  nlinarith only [hD, herror, hμh, hrh, hlast, hfh]

/-- The final-cardinality form retains full uniformity while making no
monotonicity assumption on `f`. -/
theorem uniform_final_error_actual_card (L : ℕ) (β : ℝ) (f : ℕ → ℝ)
    (t : ℕ → ℕ) (r D : ℕ → ℝ) (hβ : 0 < β) (hf : ∀ s, 0 < f s)
    (hr : ∀ i ≤ L, 16*r i ≤ lowerEnvelope f (t i)) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, 0 < n₀ ∧
      ∀ (i n s : ℕ) (h hfinal a z : ℝ), i ≤ L → n₀ ≤ n → s ≤ t i →
        β*n ≤ h → 3*h/4 ≤ hfinal → a+z ≤ ε*n →
        a+r i*h+z+D i ≤ f s*hfinal := by
  obtain ⟨ε, hε, n₀, hn₀, hbound⟩ :=
    uniform_final_error L β (lowerEnvelope f) t r D hβ
      (lowerEnvelope_pos f hf) hr
  refine ⟨ε, hε, n₀, hn₀, ?_⟩
  intro i n s h hfinal a z hi hn hs hlinear hfinal_bound hsmall
  have hh : 0 ≤ h := (mul_nonneg hβ.le (Nat.cast_nonneg n)).trans hlinear
  have hfinal_nonneg : 0 ≤ hfinal := (by positivity : 0 ≤ 3*h/4).trans hfinal_bound
  exact (hbound i n h hfinal a z hi hn hlinear hfinal_bound hsmall).trans
    (mul_le_mul_of_nonneg_right (lowerEnvelope_le f hs) hfinal_nonneg)

end Overfull.AbsorptionThresholds
