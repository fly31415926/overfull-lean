import Overfull.OrdinaryPackingPrefix

/-!
# Applying a fixed adaptive rule to an actual finite transcript

An ambient matching construction produces its forbidden sets and core
matchings together. Agreement with the fixed rule suffices to identify this
transcript with the online execution. Only rounds already presented are
required to be admissible; future entries can be arbitrary.
-/

namespace Overfull.ForeignTranscript

open Finset Classical SimpleGraph BipartitePackingOnline

variable {Input Output : Type*}

/-- The first `s` entries of a transcript on the natural numbers. -/
def transcriptPrefix (T : ℕ → Input × Output) (s : ℕ) : Fin s → Input × Output :=
  fun i => T i.val

@[simp] theorem prefix_zero (T : ℕ → Input × Output) : transcriptPrefix T 0 = Fin.elim0 := by
  funext i
  exact Fin.elim0 i

theorem prefix_succ (T : ℕ → Input × Output) (s : ℕ) :
    transcriptPrefix T (s+1) = Fin.snoc (transcriptPrefix T s) (T s) := by
  funext i
  induction i using Fin.lastCases with
  | last => simp [transcriptPrefix]
  | cast i => simp [transcriptPrefix]

/-- Following the rule on the actual earlier entries identifies the full
finite transcript with the run on its own input sequence. -/
theorem run_eq_prefix
    (rule : (s : ℕ) → (Fin s → Input × Output) → Input → Output)
    (T : ℕ → Input × Output) (s : ℕ)
    (hconsistent : ∀ j < s, (T j).2 = rule j (transcriptPrefix T j) (T j).1) :
    run rule (fun j => (T j).1) s = transcriptPrefix T s := by
  induction s with
  | zero => simpa only [run, history_zero] using (prefix_zero T).symm
  | succ s ih =>
    have hprev := ih (fun j hj => hconsistent j (by omega))
    have hlast := hconsistent s (by omega)
    change (Fin.snoc (run rule (fun j => (T j).1) s)
      ((T s).1, rule s (run rule (fun j => (T j).1) s) (T s).1) :
        Fin (s+1) → Input × Output) = _
    rw [hprev, ← hlast, ← Prod.eta (T s), ← prefix_succ]

end Overfull.ForeignTranscript

namespace Overfull

open Finset Classical SimpleGraph
open ForeignTranscript BipartitePackingOnline

/-- The proved finite-transcriptPrefix packing theorem applies to any actual
transcript that follows its fixed rule. The constants precede the graph,
the rule precedes the transcript, and no future admissibility is assumed. -/
theorem adaptive_ordinary_packing_transcript (α γ ν τ σ₀ : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hγ : 0 < γ)
    (hν : 0 < ν) (hντ : ν ≤ τ) (hτ : τ ≤ α/8)
    (hσ₀ : 0 < σ₀) (hσ₀1 : σ₀ < 1/2) :
    ∃ ε θ₀ : ℝ, 0 < ε ∧ 0 < θ₀ ∧ ∃ m₀ : ℕ,
      ∀ (V : Type*) [Fintype V] (G : SimpleGraph V) (Δ : ℝ),
        m₀ ≤ Fintype.card V → IsRobustExpander G ν τ → α*Fintype.card V ≤ Δ →
        (∀ v, |(G.degree v : ℝ)-Δ| ≤ ε*Fintype.card V) →
        ∃ rule : (s : ℕ) → (Fin s → Finset V × G.Subgraph) → Finset V → G.Subgraph,
          ∀ T : ℕ → Finset V × G.Subgraph,
            ∀ s ≤ Nat.floor (Δ-γ*Fintype.card V),
              (∀ j < s, (T j).2 = rule j (transcriptPrefix T j) (T j).1) →
              (∀ j < s, OrdinaryPackingStrategy.Allowed G (Fintype.card V) ε j
                (transcriptPrefix T j) (T j).1) →
              IsPackingHistory G s (transcriptPrefix T s) ∧
              IsRobustExpander
                (G \ BipartitePackingAccounting.edgeUnion
                  (fun i => (transcriptPrefix T s i).2.spanningCoe) univ) θ₀ σ₀ := by
  obtain ⟨ε, θ₀, hε, hθ₀, m₀, hpack⟩ := adaptive_ordinary_packing_prefix
    α γ ν τ σ₀ hα hα1 hγ hν hντ hτ hσ₀ hσ₀1
  refine ⟨ε, θ₀, hε, hθ₀, m₀, ?_⟩
  intro V _ G Δ hm hrobust hΔ hdegree
  obtain ⟨rule, hrule⟩ := hpack V G Δ hm hrobust hΔ hdegree
  refine ⟨rule, ?_⟩
  intro T s hs hconsistent hallowed
  have heq : ∀ j ≤ s,
      history rule (fun j _ => (T j).1) j = transcriptPrefix T j := by
    intro j hj
    exact run_eq_prefix rule T j (fun k hk => hconsistent k (hk.trans_le hj))
  have hresult := hrule (fun j _ => (T j).1) s hs (by
    intro j hj
    rw [heq j hj.le]
    exact hallowed j hj)
  simpa only [heq s le_rfl] using hresult

end Overfull
