import Mathlib.Data.Nat.Basic

/-!
# Termination of a bounded finite refinement

A failed stage strictly increases a positive integer rank. If every state
has rank at most the fixed bound, some stage succeeds before that many
refinements. The state type need not be finite and no maximality oracle is
assumed.
-/

namespace Overfull.RobustPartition

/-- A bounded positive rank forces one of the finitely many tested stages
to be terminal. Stage `K` is used only for the final rank contradiction. -/
theorem exists_terminal_of_bounded_rank {State : Type*} (K : ℕ)
    (valid terminal : ℕ → State → Prop) (rank : State → ℕ)
    (hstart : ∃ s, valid 0 s ∧ 0 < rank s)
    (hbound : ∀ i ≤ K, ∀ s, valid i s → rank s ≤ K)
    (hstep : ∀ i < K, ∀ s, valid i s → ¬ terminal i s →
      ∃ s', valid (i + 1) s' ∧ rank s < rank s') :
    ∃ i < K, ∃ s, valid i s ∧ terminal i s := by
  apply Classical.byContradiction
  intro hnone
  have hfail (i : ℕ) (hi : i < K) (s : State) (hs : valid i s) :
      ¬ terminal i s := fun ht => hnone ⟨i, hi, s, hs, ht⟩
  have hreach : ∀ i ≤ K, ∃ s, valid i s ∧ i < rank s := by
    intro i
    induction i with
    | zero =>
        intro _
        exact hstart
    | succ i ih =>
        intro hi
        have hiK : i < K := Nat.lt_of_lt_of_le (Nat.lt_succ_self i) hi
        obtain ⟨s, hs, hr⟩ := ih (Nat.le_of_lt hiK)
        obtain ⟨s', hs', hr'⟩ := hstep i hiK s hs (hfail i hiK s hs)
        exact ⟨s', hs', lt_of_le_of_lt (Nat.succ_le_of_lt hr) hr'⟩
  obtain ⟨s, hs, hr⟩ := hreach K le_rfl
  exact (not_lt_of_ge (hbound K le_rfl s hs)) hr

end Overfull.RobustPartition
