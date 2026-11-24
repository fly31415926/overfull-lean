import Overfull.NativeTerminal.TerminalParameters

/-! Uniform numerical room for the three-core terminal prefix. -/

noncomputable section

namespace Overfull.Terminal

def prefixRounds (h : ℕ) : ℕ := h/100+1

def prefixCapacity (α εp : ℝ) (n : ℕ) : ℕ := ⌊εp*α*n/12⌋₊

structure PrefixBounds (α εp η : ℝ) (n m h m₀ : ℕ) (a : ℝ) : Prop where
  order : m₀ ≤ m
  rounds_le : prefixRounds h ≤ h
  density : α*n/2 ≤ ((h-prefixRounds h : ℕ) : ℝ)
  horizon : prefixRounds h ≤ ⌊(h : ℝ)-(α/2)*m⌋₊
  error : a ≤ εp*m
  final_error : a ≤ η*((h-prefixRounds h : ℕ) : ℝ)
  capacity_pos : 0 < prefixCapacity α εp n
  footprint : ((6*prefixCapacity α εp n : ℕ) : ℝ) ≤ εp*m
  margin : 6*⌊a⌋₊ < prefixRounds h
  budget : n*⌊a⌋₊ ≤ 2*prefixCapacity α εp n*(prefixRounds h-6*⌊a⌋₊)

set_option maxHeartbeats 800000 in
/-- One tolerance and order threshold give all grouping, footprint and packing
inequalities. The requested final error is chosen before any host data. -/
theorem exists_prefix_parameters (α εp η : ℝ) (hα : 0 < α)
    (hεp : 0 < εp) (hη : 0 < η) (m₀ nBase : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, 0 < n₀ ∧ nBase ≤ n₀ ∧
      ∀ (n m h : ℕ) (a : ℝ), n₀ ≤ n → α*n ≤ m → m ≤ n →
        α*n ≤ h → 0 ≤ a → a ≤ ε*n → PrefixBounds α εp η n m h m₀ a := by
  let ε := min (α/2400) (min (εp*α^2/10000) (min (εp*α) (η*α/2)))
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨N, hN⟩ := exists_nat_ge
    (max (200/α) (max (48/(εp*α)) ((m₀ : ℝ)/α)))
  refine ⟨ε, hε, max 1 (max nBase N), by omega, by omega, ?_⟩
  intro n m h a hn hsize hmn hd ha hae
  have hNn : N ≤ n := by omega
  have hNnR : (N : ℝ) ≤ n := by exact_mod_cast hNn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hnlarge : 200 ≤ α*n := by
    have ht : 200/α ≤ (n : ℝ) := (le_max_left _ _).trans (hN.trans hNnR)
    exact (div_le_iff₀ hα).mp ht |>.trans_eq (mul_comm _ _)
  have hfootlarge : 48 ≤ εp*α*n := by
    have ht : 48/(εp*α) ≤ (n : ℝ) :=
      (le_max_left _ _).trans ((le_max_right _ _).trans (hN.trans hNnR))
    have hp : 0 < εp*α := mul_pos hεp hα
    exact (div_le_iff₀ hp).mp ht |>.trans_eq (mul_comm _ _)
  have hmorder : m₀ ≤ m := by
    have ht : (m₀ : ℝ)/α ≤ (n : ℝ) :=
      (le_max_right _ _).trans ((le_max_right _ _).trans (hN.trans hNnR))
    have hmR : (m₀ : ℝ) ≤ m := by
      have hh := (div_le_iff₀ hα).mp ht
      nlinarith
    exact_mod_cast hmR
  have hha : 200 ≤ h := by exact_mod_cast hnlarge.trans hd
  have hround : 2*prefixRounds h ≤ h := by unfold prefixRounds; omega
  have hrh : prefixRounds h ≤ h := by omega
  have hroundR : 2*(prefixRounds h : ℝ) ≤ h := by exact_mod_cast hround
  have hdensity : α*n/2 ≤ ((h-prefixRounds h : ℕ) : ℝ) := by
    rw [Nat.cast_sub hrh]
    linarith
  have hhorizon : prefixRounds h ≤ ⌊(h : ℝ)-(α/2)*m⌋₊ := by
    apply Nat.le_floor
    have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
    have hh := mul_le_mul_of_nonneg_left hmnR hα.le
    linarith
  have hεa : ε ≤ α/2400 := min_le_left _ _
  have hεb : ε ≤ εp*α^2/10000 := (min_le_right _ _).trans (min_le_left _ _)
  have hεc : ε ≤ εp*α :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεd : ε ≤ η*α/2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have haα : a ≤ α*n/2400 := by
    have hh := hae.trans (mul_le_mul_of_nonneg_right hεa hn0)
    nlinarith
  have haB : a ≤ (εp*α^2/10000)*n :=
    hae.trans (mul_le_mul_of_nonneg_right hεb hn0)
  have haC : a ≤ εp*m := by
    have hh := hae.trans (mul_le_mul_of_nonneg_right hεc hn0)
    have hh' := mul_le_mul_of_nonneg_left hsize hεp.le
    nlinarith
  have haD : a ≤ η*((h-prefixRounds h : ℕ) : ℝ) := by
    have hh := hae.trans (mul_le_mul_of_nonneg_right hεd hn0)
    have hh' := mul_le_mul_of_nonneg_left hdensity hη.le
    nlinarith
  have hLupper : (prefixCapacity α εp n : ℝ) ≤ εp*α*n/12 :=
    Nat.floor_le (by positivity)
  have hLlower : εp*α*n/24 ≤ (prefixCapacity α εp n : ℝ) := by
    have hh := Nat.lt_floor_add_one (εp*α*(n : ℝ)/12)
    change εp*α*(n : ℝ)/12 < (prefixCapacity α εp n : ℝ)+1 at hh
    linarith
  have hLpos : 0 < prefixCapacity α εp n := by
    have hh : (0 : ℝ) < prefixCapacity α εp n := by linarith
    exact_mod_cast hh
  have hfoot : ((6*prefixCapacity α εp n : ℕ) : ℝ) ≤ εp*m := by
    push_cast
    have hh := mul_le_mul_of_nonneg_left hsize hεp.le
    nlinarith
  have hDa : (⌊a⌋₊ : ℝ) ≤ a := Nat.floor_le ha
  have hrbound : α*n/100 < (prefixRounds h : ℝ) := by
    have hh : h < 100*prefixRounds h := by unfold prefixRounds; omega
    have hhR : (h : ℝ) < 100*(prefixRounds h : ℝ) := by exact_mod_cast hh
    linarith
  have hmargin : 6*⌊a⌋₊ < prefixRounds h := by
    have hh : (6 : ℝ)*(⌊a⌋₊ : ℝ) < prefixRounds h := by linarith
    exact_mod_cast hh
  have hremain : α*n/200 ≤ ((prefixRounds h-6*⌊a⌋₊ : ℕ) : ℝ) := by
    rw [Nat.cast_sub hmargin.le]
    push_cast
    linarith
  have hbudget : n*⌊a⌋₊ ≤ 2*prefixCapacity α εp n*(prefixRounds h-6*⌊a⌋₊) := by
    have hproduct := mul_le_mul hLlower hremain
      (by positivity : (0 : ℝ) ≤ α*n/200)
      (Nat.cast_nonneg (prefixCapacity α εp n))
    have hupper := mul_le_mul_of_nonneg_left (hDa.trans haB) hn0
    have hcoef : (0 : ℝ) ≤ εp*α^2*n^2 := by positivity
    have hh : (n : ℝ)*(⌊a⌋₊ : ℝ) ≤
        2*(prefixCapacity α εp n : ℝ)*((prefixRounds h-6*⌊a⌋₊ : ℕ) : ℝ) := by
      nlinarith only [hproduct, hupper, hcoef]
    exact_mod_cast hh
  exact ⟨hmorder, hrh, hdensity, hhorizon, haC, haD, hLpos, hfoot, hmargin, hbudget⟩

end Overfull.Terminal
