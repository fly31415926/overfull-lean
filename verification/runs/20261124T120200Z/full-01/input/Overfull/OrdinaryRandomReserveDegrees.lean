import Overfull.OrdinaryRandomReserve
import Overfull.RandomReserveDegrees

/-!
# Degree control and an ordinary robust reserve

Expansion and all vertex-degree estimates hold in one actual edge sample.
The order threshold is chosen before the graph and its vertex type.
-/

namespace Overfull.OrdinaryRandomReserve

open Finset Classical
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def incidentEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) : Finset (Sym2 V) :=
  (G.neighborFinset v).image (fun w => s(v, w))

theorem incidentEdges_card (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    (incidentEdges G v).card = G.degree v := by
  classical
  unfold incidentEdges
  rw [Finset.card_image_of_injective]
  · rfl
  · intro w u h
    rcases Sym2.eq_iff.mp h with ⟨_, hwu⟩ | ⟨hvu, hwv⟩
    · exact hwu
    · exact hwv.trans hvu

omit [DecidableEq V] in
theorem sampled_neighbors (G : SimpleGraph V) [DecidableRel G.Adj]
    (ω : Sym2 V → Bool) (v : V) :
    (sampledGraph G ω).neighborFinset v =
      (G.neighborFinset v).filter (fun w => ω s(v, w) = true) := by
  ext w
  simp [sampledGraph]

theorem incidentEdges_sampled (G : SimpleGraph V) [DecidableRel G.Adj]
    (ω : Sym2 V → Bool) (v : V) :
    incidentEdges (sampledGraph G ω) v =
      (incidentEdges G v).filter (fun e => ω e = true) := by
  unfold incidentEdges
  rw [sampled_neighbors, Finset.filter_image]

theorem sampled_degree (G : SimpleGraph V) [DecidableRel G.Adj]
    (ω : Sym2 V → Bool) (v : V) :
    (sampledGraph G ω).degree v = Bernoulli.retainedCount (incidentEdges G v) ω := by
  rw [← incidentEdges_card, incidentEdges_sampled]
  rfl

theorem degree_failure_probability (G : SimpleGraph V) [DecidableRel G.Adj]
    (p ε : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hε : 0 ≤ ε) (hεp : ε ≤ p) (v : V) :
    Bernoulli.probability p (fun ω => ε * Fintype.card V ≤
      |((sampledGraph G ω).degree v : ℝ) - p * G.degree v|) ≤
      2 * Real.exp (-ε ^ 2 * Fintype.card V / (3 * p)) := by
  have hcard : ((incidentEdges G v).card : ℝ) ≤ Fintype.card V := by
    rw [incidentEdges_card]
    exact_mod_cast (Finset.card_le_univ (G.neighborFinset v))
  have h := Bernoulli.additive_chernoff p ε (Fintype.card V : ℝ)
    hp hp1 hε hεp (incidentEdges G v) hcard
  simpa only [incidentEdges_card, ← sampled_degree] using h

theorem some_degree_failure_probability (G : SimpleGraph V) [DecidableRel G.Adj]
    (p ε : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hε : 0 ≤ ε) (hεp : ε ≤ p) :
    Bernoulli.probability p (fun ω => ∃ v : V, ε * Fintype.card V ≤
      |((sampledGraph G ω).degree v : ℝ) - p * G.degree v|) ≤
      2 * Fintype.card V * Real.exp (-ε ^ 2 * Fintype.card V / (3 * p)) := by
  classical
  let P := fun (v : V) (ω : Sym2 V → Bool) => ε * Fintype.card V ≤
    |((sampledGraph G ω).degree v : ℝ) - p * G.degree v|
  calc
    _ = Bernoulli.probability p (fun ω => ∃ v ∈ (univ : Finset V), P v ω) := by
      simp [P]
    _ ≤ ∑ v : V, Bernoulli.probability p (P v) :=
      Bernoulli.probability_exists_le_sum p hp.le hp1 univ P
    _ ≤ ∑ _v : V, 2 * Real.exp (-ε ^ 2 * Fintype.card V / (3 * p)) :=
      Finset.sum_le_sum (fun v _ => degree_failure_probability G p ε hp hp1 hε hεp v)
    _ = _ := by simp; ring

/-- A single actual sample has robust expansion and all degree bounds. -/
theorem exists_reserve_with_degree_control (p ν ε : ℝ)
    (hp : 0 < p) (hp1 : p ≤ 1) (hν : 0 < ν) (hε : 0 < ε) (hεp : ε ≤ p) :
    ∃ n₀ : ℕ, ∀ (V : Type*) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (τ : ℝ),
      n₀ ≤ Fintype.card V → IsRobustExpander G ν τ →
      ∃ ω : Sym2 V → Bool,
        IsRobustExpander (sampledGraph G ω) (p * ν / 4) τ ∧
        ∀ v : V, |((sampledGraph G ω).degree v : ℝ) - p * G.degree v| <
          ε * Fintype.card V := by
  classical
  let c := p * ν ^ 2 / 48
  let d := ε ^ 2 / (3 * p)
  have hc : 0 < c := by dsimp [c]; positivity
  have hd : 0 < d := by dsimp [d]; positivity
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (max (1 : ℝ) (max (6 / c) (64 / d ^ 2)))
  refine ⟨n₀, ?_⟩
  intro V _ _ G _ τ hn hG
  have hnR : max (1 : ℝ) (max (6 / c) (64 / d ^ 2)) < Fintype.card V :=
    hn₀.trans_le (by exact_mod_cast hn)
  have hn1 : 1 ≤ Fintype.card V := by
    have hh : (1 : ℝ) < Fintype.card V := (le_max_left _ _).trans_lt hnR
    exact_mod_cast hh.le
  have hcn : 6 ≤ c * Fintype.card V := by
    have hh : 6 / c < Fintype.card V :=
      (le_trans (le_max_left _ _) (le_max_right _ _)).trans_lt hnR
    have h := (div_lt_iff₀ hc).mp hh
    nlinarith
  have hdn : 64 ≤ d ^ 2 * Fintype.card V := by
    have hh : 64 / d ^ 2 < Fintype.card V :=
      (le_trans (le_max_right _ _) (le_max_right _ _)).trans_lt hnR
    have h := (div_lt_iff₀ (sq_pos_of_pos hd)).mp hh
    nlinarith
  have herr := RandomReserve.sampling_error_lt_one c d hd (Fintype.card V) hn1 hcn hdn
  let P₁ := fun (ω : Sym2 V → Bool) =>
    ¬ IsRobustExpander (sampledGraph G ω) (p * ν / 4) τ
  let P₂ := fun (ω : Sym2 V → Bool) => ∃ v : V, ε * Fintype.card V ≤
    |((sampledGraph G ω).degree v : ℝ) - p * G.degree v|
  let P := fun ω => P₁ ω ∨ P₂ ω
  have hbad : Bernoulli.probability p P < 1 := by
    have hu : Bernoulli.probability p P ≤
        Bernoulli.probability p P₁ + Bernoulli.probability p P₂ :=
      Bernoulli.probability_union_le p hp.le hp1 P₁ P₂
    have hrob : Bernoulli.probability p P₁ ≤ (4 : ℝ) ^ Fintype.card V *
        Real.exp (-p * ν ^ 2 * (Fintype.card V : ℝ) ^ 2 / 48) :=
      failure_probability G p ν τ hp.le hp1 hν hG
    have hdeg : Bernoulli.probability p P₂ ≤ 2 * Fintype.card V *
        Real.exp (-ε ^ 2 * Fintype.card V / (3 * p)) :=
      some_degree_failure_probability G p ε hp hp1 hε.le hεp
    have harg₁ : -p * ν ^ 2 * (Fintype.card V : ℝ) ^ 2 / 48 =
        -c * (Fintype.card V : ℝ) ^ 2 := by dsimp [c]; ring
    have harg₂ : -ε ^ 2 * (Fintype.card V : ℝ) / (3 * p) =
        -d * Fintype.card V := by dsimp [d]; ring
    rw [harg₁] at hrob
    rw [harg₂] at hdeg
    have hnexp : 0 ≤ (Fintype.card V : ℝ) * Real.exp (-d * Fintype.card V) := by
      positivity
    linarith
  obtain ⟨ω, hω⟩ := Bernoulli.exists_not_of_probability_lt_one p P hbad
  refine ⟨ω, (not_or.mp hω).1 |> not_not.mp, ?_⟩
  intro v
  exact lt_of_not_ge (fun hv => (not_or.mp hω).2 ⟨v, hv⟩)

/-- The reserve-selection step of ordinary adaptive packing, with actual
graph degrees, containment, and constants uniform over all graphs. -/
theorem exists_almost_regular_reserve (p ν ε : ℝ)
    (hp : 0 < p) (hp1 : p ≤ 1) (hν : 0 < ν) (hε : 0 < ε) (hεp : ε ≤ p) :
    ∃ n₀ : ℕ, ∀ (V : Type*) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (τ Δ : ℝ),
      n₀ ≤ Fintype.card V → IsRobustExpander G ν τ →
      (∀ v, |(G.degree v : ℝ) - Δ| ≤ ε * Fintype.card V) →
      ∃ ω : Sym2 V → Bool,
        sampledGraph G ω ≤ G ∧
        IsRobustExpander (sampledGraph G ω) (p * ν / 4) τ ∧
        ∀ v, |((sampledGraph G ω).degree v : ℝ) - p * Δ| <
          2 * ε * Fintype.card V := by
  classical
  obtain ⟨n₀, hn₀⟩ := exists_reserve_with_degree_control p ν ε hp hp1 hν hε hεp
  refine ⟨n₀, ?_⟩
  intro V _ _ G _ τ Δ hn hG hdegrees
  obtain ⟨ω, hrob, hdeg⟩ := hn₀ V G τ hn hG
  refine ⟨ω, sampledGraph_le G ω, hrob, ?_⟩
  intro v
  have hsample := hdeg v
  have hnominal : |p * (G.degree v : ℝ) - p * Δ| ≤ ε * Fintype.card V := by
    rw [← mul_sub, abs_mul, abs_of_pos hp]
    exact (mul_le_mul_of_nonneg_left (hdegrees v) hp.le).trans
      (by nlinarith [mul_nonneg hε.le (Nat.cast_nonneg (Fintype.card V))])
  have htriangle := abs_sub_le ((sampledGraph G ω).degree v : ℝ) (p * G.degree v) (p * Δ)
  linarith

end Overfull.OrdinaryRandomReserve
