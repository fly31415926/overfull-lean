import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic

/-!
# Choices depending only on the previous rounds

The history of `s` rounds is indexed by `Fin s`. A rule receives that history
and the current input; an adversary receives only the history. The definitions
therefore allow the current forbidden set to depend on the previous matchings,
while the matching rule has no access to future forbidden sets.

The invariant lemmas below are general finite recursion facts. Their local
feasibility hypotheses must be supplied by the graph-theoretic packing step.
-/

namespace Overfull.BipartitePackingOnline

variable {Input Output : Type*}

/-- Appending a round appends its input to the input history. -/
theorem snoc_inputs {s : ℕ} (H : Fin s → Input × Output) (x : Input) (y : Output) :
    (fun i : Fin (s + 1) => ((Fin.snoc H (x, y) : Fin (s + 1) → Input × Output) i).1) =
      Fin.snoc (fun i => (H i).1) x := by
  funext i
  induction i using Fin.lastCases with
  | last => simp
  | cast i => simp

/-- Appending a round appends its output to the output history. -/
theorem snoc_outputs {s : ℕ} (H : Fin s → Input × Output) (x : Input) (y : Output) :
    (fun i : Fin (s + 1) => ((Fin.snoc H (x, y) : Fin (s + 1) → Input × Output) i).2) =
      Fin.snoc (fun i => (H i).2) y := by
  funext i
  induction i using Fin.lastCases with
  | last => simp
  | cast i => simp

/-- A rule is evaluated only on the previous rounds and the current input. -/
def history
    (rule : (s : ℕ) → (Fin s → Input × Output) → Input → Output)
    (adversary : (s : ℕ) → (Fin s → Input × Output) → Input) :
    (s : ℕ) → Fin s → Input × Output
  | 0 => Fin.elim0
  | s + 1 =>
      let H := history rule adversary s
      let x := adversary s H
      Fin.snoc H (x, rule s H x)

theorem history_zero
    (rule : (s : ℕ) → (Fin s → Input × Output) → Input → Output)
    (adversary : (s : ℕ) → (Fin s → Input × Output) → Input) :
    history rule adversary 0 = Fin.elim0 := rfl

theorem history_succ
    (rule : (s : ℕ) → (Fin s → Input × Output) → Input → Output)
    (adversary : (s : ℕ) → (Fin s → Input × Output) → Input) (s : ℕ) :
    history rule adversary (s + 1) =
      Fin.snoc (history rule adversary s)
        (adversary s (history rule adversary s),
          rule s (history rule adversary s) (adversary s (history rule adversary s))) := rfl

@[simp] theorem history_castSucc
    (rule : (s : ℕ) → (Fin s → Input × Output) → Input → Output)
    (adversary : (s : ℕ) → (Fin s → Input × Output) → Input) (s : ℕ) (i : Fin s) :
    history rule adversary (s + 1) i.castSucc = history rule adversary s i := by
  rw [history_succ, Fin.snoc_castSucc]

@[simp] theorem history_last
    (rule : (s : ℕ) → (Fin s → Input × Output) → Input → Output)
    (adversary : (s : ℕ) → (Fin s → Input × Output) → Input) (s : ℕ) :
    history rule adversary (s + 1) (Fin.last s) =
      (adversary s (history rule adversary s),
        rule s (history rule adversary s) (adversary s (history rule adversary s))) := by
  rw [history_succ, Fin.snoc_last]

@[simp] theorem init_history
    (rule : (s : ℕ) → (Fin s → Input × Output) → Input → Output)
    (adversary : (s : ℕ) → (Fin s → Input × Output) → Input) (s : ℕ) :
    Fin.init (history rule adversary (s + 1)) = history rule adversary s := by
  rw [history_succ, Fin.init_snoc]

/-- Later rounds preserve every earlier input and output. -/
theorem history_castAdd
    (rule : (s : ℕ) → (Fin s → Input × Output) → Input → Output)
    (adversary : (s : ℕ) → (Fin s → Input × Output) → Input) (s k : ℕ) (i : Fin s) :
    history rule adversary (s + k) (Fin.castAdd k i) = history rule adversary s i := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← Fin.castSucc_castAdd]
    exact (history_castSucc rule adversary (s + k) (Fin.castAdd k i)).trans ih

/-- Restriction to any earlier number of rounds gives exactly that history. -/
theorem history_prefix
    (rule : (s : ℕ) → (Fin s → Input × Output) → Input → Output)
    (adversary : (s : ℕ) → (Fin s → Input × Output) → Input)
    {s t : ℕ} (hst : s ≤ t) (i : Fin s) :
    history rule adversary t (Fin.castLE hst i) = history rule adversary s i := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hst
  exact history_castAdd rule adversary s k i

/-- A prescribed sequence is a special case of an adversary. -/
def run
    (rule : (s : ℕ) → (Fin s → Input × Output) → Input → Output)
    (input : ℕ → Input) (s : ℕ) : Fin s → Input × Output :=
  history rule (fun j _ => input j) s

/-- The input at each completed round is the input that was supplied there. -/
theorem run_input
    (rule : (s : ℕ) → (Fin s → Input × Output) → Input → Output)
    (input : ℕ → Input) (s : ℕ) (i : Fin s) :
    (run rule input s i).1 = input i.val := by
  induction s with
  | zero => exact Fin.elim0 i
  | succ s ih =>
    induction i using Fin.lastCases with
    | last => simp [run]
    | cast i => simpa only [run, history_castSucc] using ih i

/-- Agreement of the supplied inputs up to a round forces agreement of the
entire history up to that round, regardless of future supplied inputs. -/
theorem run_congr_prefix
    (rule : (s : ℕ) → (Fin s → Input × Output) → Input → Output)
    (input₁ input₂ : ℕ → Input) (s : ℕ)
    (hinput : ∀ i < s, input₁ i = input₂ i) :
    run rule input₁ s = run rule input₂ s := by
  revert hinput
  induction s with
  | zero => intro _; rfl
  | succ s ih =>
    intro hinput
    have hprev := ih (fun i hi => hinput i (by omega))
    have hlast := hinput s (by omega)
    change (Fin.snoc (run rule input₁ s) (input₁ s, rule s (run rule input₁ s) (input₁ s)) :
      Fin (s + 1) → Input × Output) =
      Fin.snoc (run rule input₂ s) (input₂ s, rule s (run rule input₂ s) (input₂ s))
    rw [hprev, hlast]

/-- A total choice rule. Its fallback is used only when no permitted output
exists at that history and current input. -/
noncomputable def choose
    (fallback : Output)
    (good : (s : ℕ) → (Fin s → Input × Output) → Input → Output → Prop)
    (s : ℕ) (H : Fin s → Input × Output) (x : Input) : Output := by
  classical
  exact if h : ∃ y, good s H x y then Classical.choose h else fallback

theorem choose_spec
    (fallback : Output)
    (good : (s : ℕ) → (Fin s → Input × Output) → Input → Output → Prop)
    (s : ℕ) (H : Fin s → Input × Output) (x : Input)
    (h : ∃ y, good s H x y) :
    good s H x (choose fallback good s H x) := by
  classical
  unfold choose
  simp only [dif_pos h]
  exact Classical.choose_spec h

/-- Induction for an invariant along a bounded sequence of adaptive rounds. -/
theorem history_invariant
    (rule : (s : ℕ) → (Fin s → Input × Output) → Input → Output)
    (adversary : (s : ℕ) → (Fin s → Input × Output) → Input)
    (invariant : (s : ℕ) → (Fin s → Input × Output) → Prop)
    (allowed : (s : ℕ) → (Fin s → Input × Output) → Input → Prop)
    (q : ℕ) (hzero : invariant 0 Fin.elim0)
    (hallowed : ∀ s < q, ∀ H, invariant s H → allowed s H (adversary s H))
    (hstep : ∀ s < q, ∀ H x, invariant s H → allowed s H x →
      invariant (s + 1) (Fin.snoc H (x, rule s H x)))
    (s : ℕ) (hs : s ≤ q) : invariant s (history rule adversary s) := by
  induction s with
  | zero => exact hzero
  | succ s ih =>
    have hslt : s < q := by omega
    have hInv := ih (by omega)
    rw [history_succ]
    exact hstep s hslt _ _ hInv (hallowed s hslt _ hInv)

/-- An execution only needs its own current inputs to be allowed; the
adversary need not satisfy a condition on histories that never arise. -/
theorem history_invariant_along
    (rule : (s : ℕ) → (Fin s → Input × Output) → Input → Output)
    (adversary : (s : ℕ) → (Fin s → Input × Output) → Input)
    (invariant : (s : ℕ) → (Fin s → Input × Output) → Prop)
    (allowed : (s : ℕ) → (Fin s → Input × Output) → Input → Prop)
    (q : ℕ) (hzero : invariant 0 Fin.elim0)
    (halong : ∀ s < q, allowed s (history rule adversary s)
      (adversary s (history rule adversary s)))
    (hstep : ∀ s < q, ∀ H x, invariant s H → allowed s H x →
      invariant (s + 1) (Fin.snoc H (x, rule s H x)))
    (s : ℕ) (hs : s ≤ q) : invariant s (history rule adversary s) := by
  induction s with
  | zero => exact hzero
  | succ s ih =>
    have hslt : s < q := by omega
    have hInv := ih (by omega)
    rw [history_succ]
    exact hstep s hslt _ _ hInv (halong s hslt)

/-- Local feasible choices produce one fixed rule which preserves the
invariant against every adversary whose current input is allowed. -/
theorem choose_history_invariant
    (fallback : Output)
    (good : (s : ℕ) → (Fin s → Input × Output) → Input → Output → Prop)
    (invariant : (s : ℕ) → (Fin s → Input × Output) → Prop)
    (allowed : (s : ℕ) → (Fin s → Input × Output) → Input → Prop)
    (q : ℕ) (hzero : invariant 0 Fin.elim0)
    (hfeasible : ∀ s < q, ∀ H x, invariant s H → allowed s H x →
      ∃ y, good s H x y)
    (hpreserve : ∀ s < q, ∀ H x y, invariant s H → allowed s H x →
      good s H x y → invariant (s + 1) (Fin.snoc H (x, y)))
    (adversary : (s : ℕ) → (Fin s → Input × Output) → Input)
    (hallowed : ∀ s < q, ∀ H, invariant s H → allowed s H (adversary s H))
    (s : ℕ) (hs : s ≤ q) :
    invariant s (history (choose fallback good) adversary s) := by
  refine history_invariant (choose fallback good) adversary invariant allowed q hzero hallowed
    ?_ s hs
  intro j hj H x hInv hx
  exact hpreserve j hj H x _ hInv hx
    (choose_spec fallback good j H x (hfeasible j hj H x hInv hx))

/-- Each output of the chosen rule satisfies its local specification, with
the history and current input from that actual adaptive execution. -/
theorem chosen_output_spec
    (fallback : Output)
    (good : (s : ℕ) → (Fin s → Input × Output) → Input → Output → Prop)
    (adversary : (s : ℕ) → (Fin s → Input × Output) → Input) (s : ℕ)
    (h : ∃ y, good s (history (choose fallback good) adversary s)
      (adversary s (history (choose fallback good) adversary s)) y) :
    good s (history (choose fallback good) adversary s)
      ((history (choose fallback good) adversary (s + 1) (Fin.last s)).1)
      ((history (choose fallback good) adversary (s + 1) (Fin.last s)).2) := by
  rw [history_last]
  exact choose_spec fallback good s _ _ h

end Overfull.BipartitePackingOnline
