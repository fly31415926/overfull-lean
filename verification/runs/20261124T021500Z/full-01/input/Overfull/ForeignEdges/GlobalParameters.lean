import Overfull.ForeignEdges.PreparationRule
import Overfull.ForeignEdges.PackingSchedule
import Overfull.ForeignEdges.EpochParameters

/-!
# Uniform parameters for the four actual foreign-edge epochs

The fixed marking threshold gives an absolute marked-set bound. All packing
rules, safe-preparation rules, and robust restart parameters are then chosen
before the graph, its exceptional order, or its core error. One final error
and order choice supplies the scalar hypotheses at every possible restart.
-/

namespace Overfull.ForeignEpochParameters

open Finset Classical ForeignPackingSchedule

noncomputable def markingThreshold : ℝ := 1/1024000
def markedLimit : ℕ := 3*(1+12*1024000)
def boundaryLimit : ℕ := 4096*(markedLimit+6)
def classLoss : ℕ := 2*boundaryLimit+4*135720

theorem markingThreshold_pos : 0 < markingThreshold := by
  norm_num [markingThreshold]

theorem markedLimit_eq : (markedLimit : ℝ) = 3*(1+12/markingThreshold) := by
  norm_num [markedLimit, markingThreshold]

/-- All local construction certificates for the four epochs. -/
structure RestartParameters (α τ ν₀ : ℝ) where
  input : Fin 4 → ℝ
  output : Fin 4 → ℝ
  packingError : Fin 4 → ℝ
  safeError : Fin 4 → ℝ
  packingOrder : Fin 4 → ℕ
  safeOrder : Fin 4 → ℕ
  initial : input 0 = ν₀
  input_pos : ∀ j, 0 < input j
  input_le : ∀ j, input j ≤ τ
  output_pos : ∀ j, 0 < output j
  output_le : ∀ j, output j ≤ τ/2
  packingError_pos : ∀ j, 0 < packingError j
  safeError_pos : ∀ j, 0 < safeError j
  next : ∀ j : Fin 3,
    input ⟨j.val+1, by omega⟩ = output ⟨j.val, by omega⟩/2
  packing : ∀ j, PackingRule (α/256) (α/1024) (input j) τ
    (packingError j) (output j) (packingOrder j)
  preparation : ∀ j, PreparationRule (α/256) (min (input j) (output j)) τ
    (packingError j) markedLimit (safeError j) (safeOrder j)

/-- Neither the safe rule nor the packing rule is assumed: both are supplied
by the previously proved actual-graph construction theorems. -/
theorem exists_restart_parameters (α τ ν₀ : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hν₀ : 0 < ν₀)
    (hν₀τ : ν₀ ≤ τ) (hτ : τ ≤ (α/256)/1000) :
    Nonempty (RestartParameters α τ ν₀) := by
  have hβ : 0 < α/256 := by positivity
  have hβ1 : α/256 ≤ 1 := by linarith
  have hγ : 0 < α/1024 := by positivity
  have hτpack : τ ≤ (α/256)/8 := by linarith
  obtain ⟨ν, ε, θ, N, hstart, hν, hεθ, hnext, hpack⟩ :=
    exists_packing_schedule (α/256) (α/1024) τ ν₀
      hβ hβ1 hγ hν₀ hν₀τ hτpack
  let safe : (j : Fin 4) → SafeParameters (α/256)
      (min (ν j.val) (θ j.val)) τ (ε j.val) markedLimit :=
    fun j => Classical.choice (exists_safe_parameters (α/256)
      (min (ν j.val) (θ j.val)) τ (ε j.val) markedLimit hβ hβ1
      (lt_min (hν j.val).1 (hεθ j.val).2.1)
      ((min_le_left _ _).trans (hν j.val).2) hτ (hεθ j.val).1)
  exact ⟨{
    input := fun j => ν j.val
    output := fun j => θ j.val
    packingError := fun j => ε j.val
    safeError := fun j => (safe j).error
    packingOrder := fun j => N j.val
    safeOrder := fun j => (safe j).order
    initial := hstart
    input_pos := fun j => (hν j.val).1
    input_le := fun j => (hν j.val).2
    output_pos := fun j => (hεθ j.val).2.1
    output_le := fun j => (hεθ j.val).2.2
    packingError_pos := fun j => (hεθ j.val).1
    safeError_pos := fun j => (safe j).error_pos
    next := fun j => hnext j.val
    packing := fun j => hpack j.val
    preparation := fun j => (safe j).rule
  }⟩

/-- The output and input parameters both dominate the one fixed parameter
used for safety throughout an epoch. The output range can be enlarged back
to the safe range without changing the robust-neighborhood parameter. -/
theorem RestartParameters.safe_parameter_bounds {α τ ν₀ : ℝ}
    (P : RestartParameters α τ ν₀) (j : Fin 4) :
    0 < min (P.input j) (P.output j) ∧
    min (P.input j) (P.output j) ≤ P.input j ∧
    min (P.input j) (P.output j) ≤ P.output j ∧
    min (P.input j) (P.output j) ≤ τ := by
  exact ⟨lt_min (P.input_pos j) (P.output_pos j), min_le_left _ _,
    min_le_right _ _, (min_le_left _ _).trans (P.input_le j)⟩

/-- One original error and graph-order threshold meet all four packing and
safe-preparation budgets, the actual cut allowance, and the robust small-cut
order inequality after any of the at most three vertex moves. -/
theorem RestartParameters.uniform_initial_parameters {α τ ν₀ : ℝ}
    (P : RestartParameters α τ ν₀) (hα : 0 < α) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ,
      ∀ (n m t t' r : ℕ) (a a' : ℝ),
        n₀ ≤ n → m ≤ n → α*n ≤ m → r ≤ 3 →
        0 ≤ a → a' ≤ a+3 → t' ≤ t+3 → a+(t : ℝ)+1 ≤ ε*n →
        0 < n ∧ (α/2)*n ≤ ((m-r : ℕ) : ℝ) ∧ m-r ≤ n ∧
        ∀ j : Fin 4,
          P.packingOrder j ≤ m-r ∧ P.safeOrder j ≤ n ∧
          a'+(t' : ℝ)+1 ≤ P.packingError j*(m-r : ℕ) ∧
          ((2*(boundaryLimit+t'+3) : ℕ) : ℝ) ≤ P.packingError j*(m-r : ℕ) ∧
          a'+(t' : ℝ)+1 ≤ P.safeError j*n ∧
          a'+(t' : ℝ)+1 ≤ (α/256)*n/10 ∧
          ((2*(t'+markedLimit+boundaryLimit+30) : ℕ) : ℝ) ≤ (α/256)*n/10 ∧
          3 < (P.output j)^2*(α/256)^2*n := by
  let β : ℝ := α/256
  have hβ : 0 < β := by dsimp [β]; positivity
  let δ : Fin 4 → ℝ := fun j => min (P.packingError j) (min (P.safeError j) (β/10))
  have hδ (j : Fin 4) : 0 < δ j :=
    lt_min (P.packingError_pos j) (lt_min (P.safeError_pos j) (by positivity))
  have hlarge (j : Fin 4) : ∃ L : ℕ, 3 < (P.output j)^2*β^2*L := by
    have hθ := P.output_pos j
    have hd : 0 < (P.output j)^2*β^2 := by positivity
    obtain ⟨L,hL⟩ := exists_nat_gt (3/((P.output j)^2*β^2))
    refine ⟨L,?_⟩
    have hh := (div_lt_iff₀ hd).mp hL
    nlinarith only [hh]
  choose L hL using hlarge
  let N : Fin 4 → ℕ := fun j => max (P.packingOrder j) (max (P.safeOrder j) (L j))
  let q : ℕ := boundaryLimit+markedLimit+30
  obtain ⟨ε,hε,n₀,huniform⟩ := exists_uniform_epoch_parameters α hα δ hδ N q
  refine ⟨ε,hε,n₀,?_⟩
  intro n m t t' r a a' hn hmn hm hr ha haa htt hbudget
  obtain ⟨hnpos,hretained,hmn',hstage⟩ :=
    huniform n m t t' r a a' hn hmn hm hr ha haa htt hbudget
  refine ⟨hnpos,hretained,hmn',?_⟩
  intro j
  obtain ⟨hNj,hbudgetj,hfootprintj⟩ := hstage j
  have hδpack : δ j ≤ P.packingError j := min_le_left _ _
  have hδsafe : δ j ≤ P.safeError j := (min_le_right _ _).trans (min_le_left _ _)
  have hδβ : δ j ≤ β/10 := (min_le_right _ _).trans (min_le_right _ _)
  have hpack : δ j*((m-r : ℕ) : ℝ) ≤ P.packingError j*(m-r : ℕ) :=
    mul_le_mul_of_nonneg_right hδpack (Nat.cast_nonneg _)
  have hsafe : δ j*((m-r : ℕ) : ℝ) ≤ P.safeError j*n := by
    calc
      _ ≤ P.safeError j*(m-r : ℕ) := mul_le_mul_of_nonneg_right hδsafe (Nat.cast_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast hmn') (P.safeError_pos j).le
  have hsmall : δ j*((m-r : ℕ) : ℝ) ≤ β*n/10 := by
    calc
      _ ≤ (β/10)*(m-r : ℕ) := mul_le_mul_of_nonneg_right hδβ (Nat.cast_nonneg _)
      _ ≤ (β/10)*n := mul_le_mul_of_nonneg_left (by exact_mod_cast hmn') (by positivity)
      _ = _ := by ring
  have hpackOrder : P.packingOrder j ≤ m-r := (le_max_left _ _).trans hNj
  have hsafeOrder : P.safeOrder j ≤ n :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans hNj)).trans hmn'
  have hLOrder : L j ≤ n :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans hNj)).trans hmn'
  have hfootprint : 2*(boundaryLimit+t'+3) ≤ 2*(q+t'+3) := by dsimp [q]; omega
  have hcut : 2*(t'+markedLimit+boundaryLimit+30) ≤ 2*(q+t'+3) := by dsimp [q]; omega
  refine ⟨hpackOrder,hsafeOrder,hbudgetj.trans hpack,
    (show ((2*(boundaryLimit+t'+3) : ℕ) : ℝ) ≤ ((2*(q+t'+3) : ℕ) : ℝ) by
      exact_mod_cast hfootprint).trans (hfootprintj.trans hpack),
    hbudgetj.trans hsafe,hbudgetj.trans hsmall,
    (show ((2*(t'+markedLimit+boundaryLimit+30) : ℕ) : ℝ) ≤ ((2*(q+t'+3) : ℕ) : ℝ) by
      exact_mod_cast hcut).trans (hfootprintj.trans hsmall),?_⟩
  have hmultiply := mul_le_mul_of_nonneg_left (show (L j : ℝ) ≤ n by exact_mod_cast hLOrder)
    (show 0 ≤ (P.output j)^2*β^2 by positivity)
  exact (hL j).trans_le hmultiply

end Overfull.ForeignEpochParameters
