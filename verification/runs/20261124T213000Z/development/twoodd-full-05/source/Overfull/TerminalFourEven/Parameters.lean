import Overfull.Terminal.Parameters

/-! Uniform room for four-copy joining pieces, before any host is supplied. -/

noncomputable section

namespace Overfull.TerminalFourEven

open Terminal

structure FourPrefixBounds (α εp η : ℝ) (n m h m₀ : ℕ) (a : ℝ) : Prop where
  order : m₀ ≤ m
  rounds_le : prefixRounds h ≤ h
  density : α*n/2 ≤ ((h-prefixRounds h : ℕ) : ℝ)
  horizon : prefixRounds h ≤ ⌊(h : ℝ)-(α/2)*m⌋₊
  error : a ≤ εp*m
  final_error : a ≤ η*((h-prefixRounds h : ℕ) : ℝ)
  capacity_pos : 0 < prefixCapacity α (εp/2) n
  footprint : ((6*(2*prefixCapacity α (εp/2) n) : ℕ) : ℝ) ≤ εp*m
  margin : 8*⌊a⌋₊ < prefixRounds h
  budget : n*⌊a⌋₊ ≤ 2*prefixCapacity α (εp/2) n*(prefixRounds h-8*⌊a⌋₊)

/-- The three-copy numerical lemma with doubled error yields the stronger
conflict allowance needed for four-copy pieces. All constants remain uniform. -/
theorem exists_four_prefix_parameters (α εp η : ℝ) (hα : 0 < α)
    (hεp : 0 < εp) (hη : 0 < η) (m₀ nBase : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, 0 < n₀ ∧ nBase ≤ n₀ ∧
      ∀ (n m h : ℕ) (a : ℝ), n₀ ≤ n → α*n ≤ m → m ≤ n →
        α*n ≤ h → 0 ≤ a → a ≤ ε*n → FourPrefixBounds α εp η n m h m₀ a := by
  obtain ⟨ε, hε, n₀, hn₀, hbase, hb⟩ :=
    exists_prefix_parameters α (εp/2) η hα (by positivity) hη m₀ nBase
  refine ⟨ε/2, by positivity, n₀, hn₀, hbase, ?_⟩
  intro n m h a hn hm hmn hh ha hae
  have htwo : 2*a ≤ ε*n := by linarith
  have B := hb n m h (2*a) hn hm hmn hh (by positivity) htwo
  have hf : 2*⌊a⌋₊ ≤ ⌊2*a⌋₊ := by
    apply Nat.le_floor
    push_cast
    exact mul_le_mul_of_nonneg_left (Nat.floor_le ha) (by norm_num)
  have hmargin : 8*⌊a⌋₊ < prefixRounds h := by
    have hbmargin := B.margin
    omega
  have hbudget : n*⌊a⌋₊ ≤
      2*prefixCapacity α (εp/2) n*(prefixRounds h-8*⌊a⌋₊) := by
    calc
      n*⌊a⌋₊ ≤ n*⌊2*a⌋₊ := Nat.mul_le_mul_left n (by omega)
      _ ≤ 2*prefixCapacity α (εp/2) n*(prefixRounds h-6*⌊2*a⌋₊) := B.budget
      _ ≤ 2*prefixCapacity α (εp/2) n*(prefixRounds h-8*⌊a⌋₊) :=
        Nat.mul_le_mul_left _ (by omega)
  refine ⟨B.order, B.rounds_le, B.density, B.horizon, ?_, ?_, B.capacity_pos, ?_,
    hmargin, hbudget⟩
  · have he := B.error
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    nlinarith
  · have he := B.final_error
    linarith
  · have he := B.footprint
    push_cast at he ⊢
    linarith

end Overfull.TerminalFourEven
