import Overfull.ForeignEdges.Transcript

/-!
# Packing parameters fixed before every refinement restart

Each application has output range `τ/2`. Its output robust parameter is
reduced to at most `τ/2`, and half of that parameter is the next input.
Thus one minority-vertex deletion returns to range `τ`. The entire schedule
is chosen before any graph or matching transcript; only its first four
entries are needed in the foreign-edge argument.
-/

namespace Overfull.ForeignPackingSchedule

open Finset Classical SimpleGraph ForeignTranscript

/-- The complete, proved adaptive rule property at one stage. -/
def PackingRule (α γ ν τ ε θ : ℝ) (m₀ : ℕ) : Prop :=
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
              (fun i => (transcriptPrefix T s i).2.spanningCoe) univ) θ (τ/2)

/-- Parameters and a checked rule for a single epoch. -/
structure EpochParameters (α γ τ ν : ℝ) where
  error : ℝ
  output : ℝ
  order : ℕ
  error_pos : 0 < error
  output_pos : 0 < output
  output_le : output ≤ τ/2
  rule : PackingRule α γ ν τ error output order

theorem exists_epoch_parameters (α γ τ ν : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hγ : 0 < γ)
    (hν : 0 < ν) (hντ : ν ≤ τ) (hτ : τ ≤ α/8) :
    Nonempty (EpochParameters α γ τ ν) := by
  have hτpos : 0 < τ := hν.trans_le hντ
  have hσ : 0 < τ/2 := by positivity
  have hσ1 : τ/2 < (1 : ℝ)/2 := by linarith
  obtain ⟨ε, θ, hε, hθ, m₀, hpack⟩ := adaptive_ordinary_packing_transcript
    α γ ν τ (τ/2) hα hα1 hγ hν hντ hτ hσ hσ1
  refine ⟨⟨ε, min θ (τ/2), m₀, hε, lt_min hθ hσ, min_le_right _ _, ?_⟩⟩
  intro V _ G Δ hm hrobust hΔ hdegree
  obtain ⟨rule, hrule⟩ := hpack V G Δ hm hrobust hΔ hdegree
  refine ⟨rule, ?_⟩
  intro T s hs hconsistent hallowed
  obtain ⟨hhistory, hremaining⟩ := hrule T s hs hconsistent hallowed
  refine ⟨hhistory, ?_⟩
  exact hremaining.mono_parameter _ (min_le_left _ _)

/-- The positive tolerances, robust parameters, and order thresholds for
all restarts depend only on the original scalar parameters. In particular,
the first four entries can be fixed before choosing the original error. -/
theorem exists_packing_schedule (α γ τ ν₀ : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hγ : 0 < γ)
    (hν₀ : 0 < ν₀) (hν₀τ : ν₀ ≤ τ) (hτ : τ ≤ α/8) :
    ∃ ν ε θ : ℕ → ℝ, ∃ m₀ : ℕ → ℕ,
      ν 0 = ν₀ ∧
      (∀ j, 0 < ν j ∧ ν j ≤ τ) ∧
      (∀ j, 0 < ε j ∧ 0 < θ j ∧ θ j ≤ τ/2) ∧
      (∀ j, ν (j+1) = θ j/2) ∧
      (∀ j, PackingRule α γ (ν j) τ (ε j) (θ j) (m₀ j)) := by
  let P := {ν : ℝ // 0 < ν ∧ ν ≤ τ}
  let chooseEpoch : (x : P) → EpochParameters α γ τ x.val :=
    fun x => Classical.choice
      (exists_epoch_parameters α γ τ x.val hα hα1 hγ x.property.1 x.property.2 hτ)
  have hτpos : 0 < τ := hν₀.trans_le hν₀τ
  let next : P → P := fun x =>
    ⟨(chooseEpoch x).output/2, by
      constructor
      · exact half_pos (chooseEpoch x).output_pos
      · have hh := (chooseEpoch x).output_le
        linarith⟩
  let start : P := ⟨ν₀, hν₀, hν₀τ⟩
  let seq : ℕ → P := Nat.rec start (fun _ x => next x)
  refine ⟨(fun j => (seq j).val), (fun j => (chooseEpoch (seq j)).error),
    (fun j => (chooseEpoch (seq j)).output), (fun j => (chooseEpoch (seq j)).order),
    rfl, ?_, ?_, ?_, ?_⟩
  · intro j
    exact (seq j).property
  · intro j
    exact ⟨(chooseEpoch (seq j)).error_pos,
      (chooseEpoch (seq j)).output_pos, (chooseEpoch (seq j)).output_le⟩
  · intro j
    rfl
  · intro j
    exact (chooseEpoch (seq j)).rule

end Overfull.ForeignPackingSchedule
