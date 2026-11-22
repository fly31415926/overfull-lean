import Overfull.Patterns.Encoding
import Overfull.ForeignEdges.PackingSchedule
import Overfull.SmallCuts

/-!
# Parameters for frequent boundary patterns

The packing error, surviving robust parameter, and packing order are fixed
before the requested final error. The discard coefficient is any fixed
nonnegative real number, so either a sharp pair count or a larger finite
ambient test family can be used without changing the argument.
-/

namespace Overfull.Patterns

open Finset Classical ForeignPackingSchedule

/-- All scalar obligations after the requested final error is chosen. -/
structure PatternScalarBounds (t B m₀ : ℕ) (α εp θ η δ C : ℝ)
    (n k m : ℕ) (a : ℝ) : Prop where
  order_pos : 0 < n
  degree_large : 6*B ≤ k
  packing_order : m₀ ≤ m
  footprint : ((2*t+6 : ℕ) : ℝ) ≤ εp*m
  packing_error : a ≤ εp*m
  absorption : (t : ℝ) ≤ θ*m/4
  small_cut_error : a ≤ (α/(4*B))*n/10
  robust_cut : 3 < θ^2*α^2*n
  final_error : a+η*k+B+C*a/η ≤ δ*k/(3*B)

/-- For fixed packing parameters and any finite discard coefficient, one
positive error and one order threshold control every eligible graph and core. -/
theorem exists_pattern_scalar_parameters (α εp θ C : ℝ)
    (hα : 0 < α) (hεp : 0 < εp) (hθ : 0 < θ) (hC : 0 ≤ C)
    (t B m₀ : ℕ) (hB : 0 < B) (δ : ℝ) (hδ : 0 < δ) :
    ∃ η ε : ℝ, 0 < η ∧ η < 1 ∧ η ≤ δ/(12*B) ∧ 0 < ε ∧ ∃ N : ℕ,
      ∀ (n k m z : ℕ) (a : ℝ), N ≤ n → α*n ≤ k → α*n ≤ m →
        0 ≤ a → a+(z : ℝ)+1 ≤ ε*n →
        PatternScalarBounds t B m₀ α εp θ η δ C n k m a := by
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  let η := min (1/2) (δ/(12*B))
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hη1 : η < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hηδ : η ≤ δ/(12*B) := min_le_right _ _
  let K := 1+C/η
  have hK : 0 < K := by dsimp only [K]; positivity
  let ε := min (εp*α) (min (α/(40*B)) (δ*α/(12*B*K)))
  have hε : 0 < ε := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hεpack : ε ≤ εp*α := min_le_left _ _
  have hεsafe : ε ≤ α/(40*B) := (min_le_right _ _).trans (min_le_left _ _)
  have hεerror : ε ≤ δ*α/(12*B*K) := (min_le_right _ _).trans (min_le_right _ _)
  have hεK : ε*K ≤ δ*α/(12*B) := by
    apply (le_div_iff₀ (by positivity : 0 < 12*(B : ℝ))).mpr
    have hh := (le_div_iff₀ (by positivity : 0 < 12*(B : ℝ)*K)).mp hεerror
    nlinarith only [hh]
  obtain ⟨N₁,hN₁⟩ := exists_nat_gt (6*(B : ℝ)/α)
  obtain ⟨N₂,hN₂⟩ := exists_nat_gt ((m₀ : ℝ)/α)
  obtain ⟨N₃,hN₃⟩ := exists_nat_gt (((2*t+6 : ℕ) : ℝ)/(εp*α))
  obtain ⟨N₄,hN₄⟩ := exists_nat_gt (4*(t : ℝ)/(θ*α))
  obtain ⟨N₅,hN₅⟩ := exists_nat_gt (3/(θ^2*α^2))
  obtain ⟨N₆,hN₆⟩ := exists_nat_gt (12*(B : ℝ)^2/(δ*α))
  let N := 1+N₁+N₂+N₃+N₄+N₅+N₆
  refine ⟨η,ε,hη,hη1,hηδ,hε,N,?_⟩
  intro n k m z a hn hdegree hcore ha hbudget
  have hn₁ : N₁ ≤ n := by dsimp only [N] at hn; omega
  have hn₂ : N₂ ≤ n := by dsimp only [N] at hn; omega
  have hn₃ : N₃ ≤ n := by dsimp only [N] at hn; omega
  have hn₄ : N₄ ≤ n := by dsimp only [N] at hn; omega
  have hn₅ : N₅ ≤ n := by dsimp only [N] at hn; omega
  have hn₆ : N₆ ≤ n := by dsimp only [N] at hn; omega
  have hnpos : 0 < n := by dsimp only [N] at hn; omega
  have han : a ≤ ε*n := by linarith [show (0 : ℝ) ≤ z from Nat.cast_nonneg _]
  have hklarge : 6*B ≤ k := by
    have hh := (div_lt_iff₀ hα).mp (hN₁.trans_le (show (N₁ : ℝ) ≤ n by exact_mod_cast hn₁))
    have hh' : (6*(B : ℝ)) ≤ k := by nlinarith only [hh,hdegree]
    exact_mod_cast hh'
  have hmorder : m₀ ≤ m := by
    have hh := (div_lt_iff₀ hα).mp (hN₂.trans_le (show (N₂ : ℝ) ≤ n by exact_mod_cast hn₂))
    have hh' : (m₀ : ℝ) ≤ m := by nlinarith only [hh,hcore]
    exact_mod_cast hh'
  have hfoot : ((2*t+6 : ℕ) : ℝ) ≤ εp*m := by
    have hh := (div_lt_iff₀ (mul_pos hεp hα)).mp
      (hN₃.trans_le (show (N₃ : ℝ) ≤ n by exact_mod_cast hn₃))
    have hh' := mul_le_mul_of_nonneg_left hcore hεp.le
    nlinarith only [hh,hh']
  have hpack : a ≤ εp*m := by
    have hh := mul_le_mul_of_nonneg_right hεpack (Nat.cast_nonneg n)
    have hh' := mul_le_mul_of_nonneg_left hcore hεp.le
    nlinarith only [han,hh,hh']
  have habsorb : (t : ℝ) ≤ θ*m/4 := by
    have hh := (div_lt_iff₀ (mul_pos hθ hα)).mp
      (hN₄.trans_le (show (N₄ : ℝ) ≤ n by exact_mod_cast hn₄))
    have hh' := mul_le_mul_of_nonneg_left hcore hθ.le
    nlinarith only [hh,hh']
  have hsafe : a ≤ (α/(4*B))*n/10 := by
    have hh := mul_le_mul_of_nonneg_right hεsafe (Nat.cast_nonneg n)
    calc
      a ≤ ε*n := han
      _ ≤ (α/(40*B))*n := hh
      _ = _ := by field_simp; ring
  have hrobust : 3 < θ^2*α^2*n := by
    have hh := (div_lt_iff₀ (by positivity : 0 < θ^2*α^2)).mp
      (hN₅.trans_le (show (N₅ : ℝ) ≤ n by exact_mod_cast hn₅))
    nlinarith only [hh]
  have hBerror : (B : ℝ) ≤ δ*k/(12*B) := by
    apply (le_div_iff₀ (by positivity : 0 < 12*(B : ℝ))).mpr
    have hh := (div_lt_iff₀ (mul_pos hδ hα)).mp
      (hN₆.trans_le (show (N₆ : ℝ) ≤ n by exact_mod_cast hn₆))
    have hh' := mul_le_mul_of_nonneg_left hdegree hδ.le
    nlinarith only [hh,hh']
  have hηerror : η*k ≤ δ*k/(12*B) := by
    calc
      _ ≤ (δ/(12*B))*k := mul_le_mul_of_nonneg_right hηδ (Nat.cast_nonneg k)
      _ = _ := by ring
  have haerror : a+C*a/η ≤ δ*k/(12*B) := by
    calc
      _ = a*K := by dsimp only [K]; ring
      _ ≤ (ε*n)*K := mul_le_mul_of_nonneg_right han hK.le
      _ = (ε*K)*n := by ring
      _ ≤ (δ*α/(12*B))*n := mul_le_mul_of_nonneg_right hεK (Nat.cast_nonneg n)
      _ = (δ/(12*B))*(α*n) := by ring
      _ ≤ (δ/(12*B))*k := mul_le_mul_of_nonneg_left hdegree (by positivity)
      _ = _ := by ring
  have herror : a+η*k+B+C*a/η ≤ δ*k/(3*B) := by
    have hid : δ*k/(3*B) = 4*(δ*k/(12*B)) := by field_simp; ring
    have hnonneg : 0 ≤ δ*k/(12*B) := by positivity
    rw [hid]
    linarith only [haerror,hηerror,hBerror,hnonneg]
  exact ⟨hnpos,hklarge,hmorder,hfoot,hpack,habsorb,hsafe,hrobust,herror⟩

/-- The frequent-pattern reserve is larger than the reserve required by
each original core's fixed packing rule. -/
theorem pattern_packing_horizon (α : ℝ) (B n k m q r : ℕ)
    (hα : 0 < α) (hB : 0 < B) (hm : m ≤ n) (hk : α*n ≤ k)
    (hr : (k : ℝ)/(3*B) ≤ r) (hq : q+r ≤ k) :
    q ≤ Nat.floor ((k : ℝ)-(α/(4*B))*m) := by
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hmr : (m : ℝ) ≤ n := by exact_mod_cast hm
  have hqr : (q : ℝ)+r ≤ k := by exact_mod_cast hq
  have hrs := (div_le_iff₀ (by positivity : 0 < 3*(B : ℝ))).mp hr
  have hmdegree : α*(m : ℝ) ≤ k := (mul_le_mul_of_nonneg_left hmr hα.le).trans hk
  have hBr : 0 ≤ (B : ℝ)*r := mul_nonneg hBR.le (Nat.cast_nonneg r)
  have hγ : (α/(4*B))*m ≤ (r : ℝ) := by
    have hdiv : α*m/(4*B) ≤ (r : ℝ) :=
      (div_le_iff₀ (by positivity : 0 < 4*(B : ℝ))).mpr (by nlinarith only [hrs,hmdegree,hBr])
    convert hdiv using 1; ring
  apply Nat.le_floor
  linarith only [hγ,hqr]

/-- The manuscript's robust range is small enough both for packing and
for classifying small cuts at the retained density. -/
theorem pattern_range_bounds (α ν τ : ℝ) (B : ℕ)
    (hα : 0 < α) (hν : 0 < ν) (hντ : ν ≤ τ) (hB : 0 < B)
    (hτ : τ ≤ α/(1000*B)) : τ ≤ α/8 ∧ τ/2 ≤ (α/(4*B))/10 := by
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hτpos : 0 < τ := hν.trans_le hντ
  have hh := (le_div_iff₀ (by positivity : 0 < 1000*(B : ℝ))).mp hτ
  constructor
  · have hmul := mul_nonneg hτpos.le (sub_nonneg.mpr hB1)
    nlinarith only [hh,hmul,hτpos]
  · have hid : (α/(4*B))/10 = α/(40*B) := by field_simp; ring
    rw [hid]
    apply (le_div_iff₀ (by positivity : 0 < 40*(B : ℝ))).mpr
    have hnonneg : 0 ≤ τ*(B : ℝ) := mul_nonneg hτpos.le hBR.le
    nlinarith only [hh,hnonneg]

/-- Packing and surviving robustness are fixed before `δ`. The later
small error and order threshold depend only on the displayed scalar data. -/
theorem exists_frequent_pattern_parameters (t : ℕ) (C α ν τ : ℝ)
    (hC : 0 ≤ C) (hα : 0 < α) (hα1 : α ≤ 1)
    (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτ : τ ≤ α/(1000*patternBound t)) :
    ∃ P : EpochParameters α (α/(4*patternBound t)) τ ν,
      0 < P.output/4 ∧ P.output/4 ≤ τ ∧
      τ/2 ≤ (α/(4*patternBound t))/10 ∧
      ∀ δ : ℝ, 0 < δ → ∃ η ε : ℝ,
        0 < η ∧ η < 1 ∧ η ≤ δ/(12*patternBound t) ∧ 0 < ε ∧ ∃ N : ℕ,
          ∀ (n k m z : ℕ) (a : ℝ), N ≤ n → α*n ≤ k → α*n ≤ m →
            0 ≤ a → a+(z : ℝ)+1 ≤ ε*n →
            PatternScalarBounds t (patternBound t) P.order α P.error P.output η δ C n k m a := by
  have hB : 0 < patternBound t := by unfold patternBound; positivity
  have hBR : (0 : ℝ) < patternBound t := by exact_mod_cast hB
  obtain ⟨hτpacking,hτcuts⟩ := pattern_range_bounds α ν τ (patternBound t) hα hν hντ hB hτ
  obtain ⟨P⟩ := exists_epoch_parameters α (α/(4*patternBound t)) τ ν hα hα1
    (by positivity) hν hντ hτpacking
  refine ⟨P,div_pos P.output_pos (by norm_num),?_,hτcuts,?_⟩
  · have hh := P.output_le
    have hp := P.output_pos
    linarith
  · intro δ hδ
    exact exists_pattern_scalar_parameters α P.error P.output C hα P.error_pos P.output_pos hC
      t (patternBound t) P.order hB δ hδ

end Overfull.Patterns
