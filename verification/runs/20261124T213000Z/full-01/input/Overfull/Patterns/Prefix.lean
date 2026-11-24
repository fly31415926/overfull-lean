import Overfull.Patterns.Cuts
import Overfull.Patterns.Rounding

/-!
# Pattern multiplicities and exact prefix cut accounting
-/

namespace Overfull.Patterns

open Finset Classical MatchingProbability ForeignPhase
open scoped BigOperators

variable {P : Type*} [Fintype P]

/-- Number of appearances of one pattern in the first `s` rounds. -/
noncomputable def prefixCount (pattern : ℕ → P) (s : ℕ) (p : P) : ℕ :=
  ((range s).filter (fun j => pattern j = p)).card

theorem prefixCount_statistic (pattern : ℕ → P) (s : ℕ) (c : P → ℝ) :
    (∑ p, (prefixCount pattern s p : ℝ) * c p) =
      ∑ j ∈ range s, c (pattern j) := by
  have hc (p : P) : (prefixCount pattern s p : ℝ) =
      ∑ j ∈ range s, if pattern j = p then (1 : ℝ) else 0 := by
    simp [prefixCount, Finset.sum_boole]
  simp_rw [hc, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  simp [ite_mul, eq_comm]

theorem prefixCount_sum (pattern : ℕ → P) (s : ℕ) : ∑ p, prefixCount pattern s p = s := by
  have h := prefixCount_statistic pattern s (fun _ => 1)
  simp only [mul_one, sum_const, card_range, nsmul_eq_mul, mul_one] at h
  exact_mod_cast h

omit [Fintype P] in
theorem prefixCount_mono (pattern : ℕ → P) {s t : ℕ} (hst : s ≤ t) (p : P) :
    prefixCount pattern s p ≤ prefixCount pattern t p := by
  exact card_le_card (filter_subset_filter _ (range_mono hst))

variable {V : Type*} [Fintype V]

/-- Reindexing actual deleted cut edges by their patterns is exact. -/
theorem prefix_cut_accounting (G : SimpleGraph V) [DecidableRel G.Adj]
    (N : ℕ → G.Subgraph) (pattern : ℕ → P) (s : ℕ) (X : Finset V)
    (c : P → ℕ)
    (hpresent : ∀ j < s, (N j).spanningCoe ≤ afterDeletions G N j)
    (hcross : ∀ j < s, cutCount (matchingEdges (N j)) X = c (pattern j)) :
    (graphCutCount (afterDeletions G N s) X : ℝ) +
      (∑ p, (prefixCount pattern s p : ℝ) * c p) = graphCutCount G X := by
  rw [prefixCount_statistic]
  have h := afterDeletions_cut_accounting G N s hpresent X
  have hc : (∑ j ∈ range s, cutCount (matchingEdges (N j)) X) =
      ∑ j ∈ range s, c (pattern j) :=
    sum_congr rfl (fun j hj => hcross j (mem_range.mp hj))
  rw [hc] at h
  exact_mod_cast h

/-- The actual current cut is bounded by numerical remaining weights;
these weights are not asserted to decompose the residual graph. -/
theorem prefix_cut_weighted_lower (G : SimpleGraph V) [DecidableRel G.Adj]
    (N : ℕ → G.Subgraph) (pattern : ℕ → P) (s : ℕ) (X : Finset V)
    (c : P → ℕ) (w : P → ℝ)
    (hpresent : ∀ j < s, (N j).spanningCoe ≤ afterDeletions G N j)
    (hcross : ∀ j < s, cutCount (matchingEdges (N j)) X = c (pattern j))
    (hcap : (∑ p, w p * c p) ≤ graphCutCount G X) :
    (∑ p, (w p - (prefixCount pattern s p : ℝ)) * c p) ≤
      graphCutCount (afterDeletions G N s) X := by
  have h := prefix_weighted_capacity w (prefixCount pattern s) c
    (graphCutCount G X) hcap
  have hactual := prefix_cut_accounting G N pattern s X c hpresent hcross
  linarith

/-- Odd whole unions keep at least the current degree at every prefix. -/
theorem prefix_odd_cut_safe (G : SimpleGraph V) [DecidableRel G.Adj]
    (N : ℕ → G.Subgraph) (pattern : ℕ → P) (s k : ℕ) (X : Finset V)
    (c : P → ℕ) (w : P → ℝ) (hsk : s ≤ k)
    (hpresent : ∀ j < s, (N j).spanningCoe ≤ afterDeletions G N j)
    (hcross : ∀ j < s, cutCount (matchingEdges (N j)) X = c (pattern j))
    (hsum : ∑ p, w p = k)
    (hn : ∀ p, (prefixCount pattern s p : ℝ) ≤ w p)
    (hc : ∀ p, 0 < w p → 1 ≤ c p)
    (hcap : (∑ p, w p * c p) ≤ graphCutCount G X) :
    k - s ≤ graphCutCount (afterDeletions G N s) X := by
  have hh := prefix_odd_cut_bound_on_support w (prefixCount pattern s) c
    (k : ℝ) (graphCutCount G X) hsum hn hc hcap
  have hactual := prefix_cut_accounting G N pattern s X c hpresent hcross
  have hnum : (∑ p, (prefixCount pattern s p : ℝ)) = s := by
    exact_mod_cast prefixCount_sum pattern s
  rw [hnum] at hh
  have hR : (k : ℝ) - s ≤ graphCutCount (afterDeletions G N s) X := by linarith
  exact_mod_cast (show ((k - s : ℕ) : ℝ) ≤ graphCutCount (afterDeletions G N s) X by
    simpa only [Nat.cast_sub hsk] using hR)

end Overfull.Patterns
