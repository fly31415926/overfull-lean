import Overfull.Dense.LinkPacking.Load
import Overfull.Dense.LinkPacking.Feasible
import Overfull.BipartiteFactorization.BlockScoreMean

/-!
# Simultaneous packing of the actual link matchings

The one-link conditional estimates are summed over all links and vertices.
A positive-probability complete history has bounded actual used-edge load.
Dense bipartite matching feasibility then makes every stage of that history
cover its link. All probability and candidate-existence premises are proved
from the graph, overlap, incidence, and numerical hypotheses.
-/

noncomputable section

namespace Overfull.Dense.LinkPacking

open Finset Classical

variable {V : Type*} [Fintype V]

/-- Sum the actual load tails over every monitored link and every vertex. -/
theorem probability_badLoad_le (G : SimpleGraph V) (Y : ℕ → Finset V)
    (b lam : ℝ) (n q : ℕ) (hb : 1 ≤ b) (hlam : 0 < lam)
    (hL : 8 ≤ Parameters.load lam n)
    (hoverlap : ∀ i < q, ∀ j < q, i ≠ j →
      ((Y i ∩ Y j).card : ℝ) ≤ 6 * lam ^ 2 * n)
    (hincidence : ∀ v,
      (((range q).filter (fun s => v ∈ Y s)).card : ℝ) ≤ 2 * b * lam * n) :
    MatchingProbability.probability
        (PredictableBernoulli.weight (Parameters.choices b lam n) q)
        (fun ω => ∃ i ∈ range q, ∃ v : V,
          Parameters.load lam n <
            (localLoad (used G (history G (Parameters.choices b lam n) Y q ω))
              (Y i) v : ℝ)) ≤
      (q : ℝ) * (Fintype.card V : ℝ) * Real.exp (-Parameters.load lam n / 24) := by
  let t := Parameters.choices b lam n
  let w := PredictableBernoulli.weight t q
  let bad := fun (i : ℕ) (v : V) (ω : Fin q → Fin t) =>
    Parameters.load lam n <
      (localLoad (used G (history G t Y q ω)) (Y i) v : ℝ)
  have htail (i : ℕ) (hi : i < q) (v : V) :
      MatchingProbability.probability w (bad i v) ≤
        Real.exp (-Parameters.load lam n / 24) := by
    have h := hits_upper_tail G Y b lam n q i v hb hlam hL
      (fun s hs hsi => hoverlap i hi s hs (Ne.symm hsi)) (hincidence v)
    simpa only [hits_count_eq_localLoad] using h
  have hvertex (i : ℕ) (hi : i < q) :
      MatchingProbability.probability w (fun ω => ∃ v, bad i v ω) ≤
        (Fintype.card V : ℝ) * Real.exp (-Parameters.load lam n / 24) := by
    have hu := MatchingProbability.probability_exists_le_sum w
      (PredictableBernoulli.weight_nonneg t q) (univ : Finset V) (bad i)
    have hu' : MatchingProbability.probability w (fun ω => ∃ v, bad i v ω) ≤
        ∑ v : V, MatchingProbability.probability w (bad i v) := by
      simpa only [mem_univ, true_and] using hu
    calc
      _ ≤ ∑ v : V, MatchingProbability.probability w (bad i v) := hu'
      _ ≤ ∑ _v : V, Real.exp (-Parameters.load lam n / 24) :=
        Finset.sum_le_sum (fun v _ => htail i hi v)
      _ = _ := by simp
  calc
    _ ≤ ∑ i ∈ range q,
        MatchingProbability.probability w (fun ω => ∃ v, bad i v ω) :=
      MatchingProbability.probability_exists_le_sum w
        (PredictableBernoulli.weight_nonneg t q) (range q) (fun i ω => ∃ v, bad i v ω)
    _ ≤ ∑ _i ∈ range q,
        (Fintype.card V : ℝ) * Real.exp (-Parameters.load lam n / 24) := by
      exact Finset.sum_le_sum (fun i hi => hvertex i (mem_range.mp hi))
    _ = _ := by simp [mul_assoc]

/-- A finite complete history whose actual final used-edge loads all obey
the prescribed bound. The numerical union budget is explicit here. -/
theorem exists_bounded_history (G : SimpleGraph V) (Y : ℕ → Finset V)
    (b lam : ℝ) (n q : ℕ) (hb : 1 ≤ b) (hlam : 0 < lam)
    (hL : 8 ≤ Parameters.load lam n)
    (hV : (Fintype.card V : ℝ) ≤ 3 * n) (hq : (q : ℝ) ≤ 3 * b * n)
    (hoverlap : ∀ i < q, ∀ j < q, i ≠ j →
      ((Y i ∩ Y j).card : ℝ) ≤ 6 * lam ^ 2 * n)
    (hincidence : ∀ v,
      (((range q).filter (fun s => v ∈ Y s)).card : ℝ) ≤ 2 * b * lam * n)
    (hbudget : (3 * b * n) * (3 * n) *
      Real.exp (-Parameters.load lam n / 24) < 1) :
    ∃ ω : Fin q → Fin (Parameters.choices b lam n), ∀ i < q, ∀ v,
      (localLoad (used G (history G (Parameters.choices b lam n) Y q ω))
        (Y i) v : ℝ) ≤ Parameters.load lam n := by
  let t := Parameters.choices b lam n
  let w := PredictableBernoulli.weight t q
  let bad := fun ω : Fin q → Fin t => ∃ i ∈ range q, ∃ v : V,
    Parameters.load lam n <
      (localLoad (used G (history G t Y q ω)) (Y i) v : ℝ)
  have hb0 : 0 ≤ b := (show (0 : ℝ) ≤ 1 by norm_num).trans hb
  have hprob : MatchingProbability.probability w bad < 1 := by
    calc
      _ ≤ (q : ℝ) * (Fintype.card V : ℝ) *
          Real.exp (-Parameters.load lam n / 24) :=
        probability_badLoad_le G Y b lam n q hb hlam hL hoverlap hincidence
      _ ≤ (3 * b * n) * (3 * n) * Real.exp (-Parameters.load lam n / 24) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact mul_le_mul hq hV (Nat.cast_nonneg _) (by positivity)
      _ < 1 := hbudget
  obtain ⟨ω, _, hgood⟩ :=
    BipartiteFactorization.BlockScoreMean.exists_support_not_of_probability_lt_one
      w (PredictableBernoulli.weight_nonneg t q)
      (PredictableBernoulli.sum_weight t q (Parameters.choices_pos b lam n hb hL))
      bad hprob
  refine ⟨ω, ?_⟩
  intro i hi v
  exact le_of_not_gt (fun h => hgood ⟨i, mem_range.mpr hi, v, h⟩)

/-- Actual pairwise edge-disjoint perfect matchings on balanced local sides.
Every candidate and probability bound is constructed from the displayed
graph hypotheses. A uniform order threshold later discharges the numerical
load and failure-budget conditions. -/
theorem exists_packing_of_budget (G : SimpleGraph V) (A B : ℕ → Finset V)
    (b lam : ℝ) (n q : ℕ) (hb : 1 ≤ b) (hlam : 0 < lam)
    (hL : 8 ≤ Parameters.load lam n)
    (hV : (Fintype.card V : ℝ) ≤ 3 * n) (hq : (q : ℝ) ≤ 3 * b * n)
    (hAB : ∀ i < q, Disjoint (A i) (B i))
    (hbalance : ∀ i < q, (A i).card = (B i).card)
    (hleft : ∀ i < q, ∀ v ∈ A i,
      ((A i).card : ℝ) / 2 + 81 * b * Parameters.load lam n ≤
        (G.neighborFinset v ∩ B i).card)
    (hright : ∀ i < q, ∀ v ∈ B i,
      ((A i).card : ℝ) / 2 + 81 * b * Parameters.load lam n ≤
        (G.neighborFinset v ∩ A i).card)
    (hoverlap : ∀ i < q, ∀ j < q, i ≠ j →
      (((A i ∪ B i) ∩ (A j ∪ B j)).card : ℝ) ≤ 6 * lam ^ 2 * n)
    (hincidence : ∀ v,
      (((range q).filter (fun s => v ∈ A s ∪ B s)).card : ℝ) ≤ 2 * b * lam * n)
    (hbudget : (3 * b * n) * (3 * n) *
      Real.exp (-Parameters.load lam n / 24) < 1) :
    ∃ M : Fin q → G.Subgraph,
      (∀ i, (M i).IsMatching) ∧
      (∀ i, (M i).verts = (↑(A i.val ∪ B i.val) : Set V)) ∧
      Pairwise (fun i j => Disjoint (M i).spanningCoe (M j).spanningCoe) := by
  let Y := fun i => A i ∪ B i
  let t := Parameters.choices b lam n
  obtain ⟨ω, hload⟩ := exists_bounded_history G Y b lam n q hb hlam hL hV hq
    hoverlap hincidence hbudget
  refine ⟨history G t Y q ω, history_matching G t Y q ω, ?_,
    history_disjoint G t Y q ω⟩
  apply history_covers_of_localLoad G t Y (Parameters.load lam n) q ω _ hload
  intro i hi U hU
  exact exists_candidateOK_of_degree_81 G U (A i) (B i)
    (hAB i hi) (hbalance i hi) b lam n hb hL
    (hleft i hi) (hright i hi) (fun v _ => hU v)

end Overfull.Dense.LinkPacking
