import Overfull.Dense.LinkPacking.Candidates
import Overfull.Dense.LinkPacking.History
import Overfull.Dense.LinkPacking.Parameters
import Overfull.Probability.PredictableBernoulli

/-!
# Actual conditional load probabilities for link packing

The process counts whether the chosen candidate uses an edge from a fixed
vertex into a monitored link.  Its conditional probability is computed from
the actual candidate family at every history, including the empty fallback.
Edge-disjoint candidates, actual link overlaps, and actual vertex incidences
discharge all hypotheses of the predictable-indicator concentration theorem.
-/

noncomputable section

namespace Overfull.Dense.LinkPacking

open Finset Classical SimpleGraph FiniteProbability

variable {V : Type*}

/-- Whether a round's chosen candidate uses an edge from `v` into `Y i`.
The candidate family depends on the complete preceding history. -/
def hitsProcess (G : SimpleGraph V) (t : ℕ) (Y : ℕ → Finset V)
    (i : ℕ) (v : V) : PredictableBernoulli.Process t :=
  fun s h z => decide (∃ w ∈ Y i,
    (candidates G t (Y s) (used G (history G t Y s h)) z).Adj v w)

/-- The own round costs at most one; any other incident round costs the
explicit overlap-to-candidate ratio. -/
def hitsBound (b lam : ℝ) (Y : ℕ → Finset V) (i : ℕ) (v : V) (s : ℕ) : ℝ :=
  if s = i then 1 else if v ∈ Y s then Parameters.rate b lam else 0

/-- Exact conditional probability under the next uniform choice. -/
theorem hits_localMean_eq (G : SimpleGraph V) (t : ℕ) (Y : ℕ → Finset V)
    (i s : ℕ) (v : V) (h : Fin s → Fin t) :
    PredictableBernoulli.localMean (hitsProcess G t Y i v) s h =
      (DenseLinkPacking.harmfulCandidates G
        (candidates G t (Y s) (used G (history G t Y s h))) v (Y i)).card / (t : ℝ) := by
  have heq : PredictableBernoulli.localMean (hitsProcess G t Y i v) s h =
      mean (PredictableBernoulli.choiceWeight t) (fun z =>
        if ∃ w ∈ Y i,
          (candidates G t (Y s) (used G (history G t Y s h)) z).Adj v w
        then 1 else 0) := by
    simp only [PredictableBernoulli.localMean, hitsProcess, decide_eq_true_eq]
  rw [heq, mean_indicator]
  simp only [MatchingProbability.probability, PredictableBernoulli.choiceWeight,
    DenseLinkPacking.harmfulCandidates, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
  congr 2
  apply congrArg Finset.card
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem hits_localMean_le_one (G : SimpleGraph V) (t : ℕ) (ht : 0 < t)
    (Y : ℕ → Finset V) (i s : ℕ) (v : V) (h : Fin s → Fin t) :
    PredictableBernoulli.localMean (hitsProcess G t Y i v) s h ≤ 1 := by
  calc
    _ ≤ mean (PredictableBernoulli.choiceWeight t) (fun _ => 1) := by
      apply mean_mono _ (PredictableBernoulli.choiceWeight_nonneg t)
      intro z
      split_ifs <;> norm_num
    _ = 1 := mean_const _ (PredictableBernoulli.sum_choiceWeight t ht) 1

/-- A candidate has no edge at a vertex outside the current link. -/
theorem hits_localMean_eq_zero_of_not_mem (G : SimpleGraph V) (t : ℕ)
    (Y : ℕ → Finset V) (i s : ℕ) (v : V) (h : Fin s → Fin t)
    (hv : v ∉ Y s) :
    PredictableBernoulli.localMean (hitsProcess G t Y i v) s h = 0 := by
  have hnone (z : Fin t) : ¬ ∃ w ∈ Y i,
      (candidates G t (Y s) (used G (history G t Y s h)) z).Adj v w := by
    rintro ⟨w, _hw, hadj⟩
    exact hv (candidates_verts_subset G t (Y s) (used G (history G t Y s h)) z
      ((candidates G t (Y s) (used G (history G t Y s h)) z).edge_vert hadj))
  simp only [PredictableBernoulli.localMean, hitsProcess, hnone, decide_false,
    Bool.false_eq_true, if_false, mean, mul_zero, Finset.sum_const_zero]

/-- Actual edge-disjoint candidate families give the actual link-overlap
bound, without assuming the candidates are complete at this history. -/
theorem hits_harmful_card_le (G : SimpleGraph V) (t : ℕ) (Y : ℕ → Finset V)
    (i s : ℕ) (v : V) (h : Fin s → Fin t) :
    (DenseLinkPacking.harmfulCandidates G
      (candidates G t (Y s) (used G (history G t Y s h))) v (Y i)).card ≤
      (Y i ∩ Y s).card :=
  DenseLinkPacking.harmfulCandidates_card_le G
    (candidates G t (Y s) (used G (history G t Y s h))) (Y s)
    (candidates_verts_subset G t (Y s) (used G (history G t Y s h)))
    (candidates_disjoint G t (Y s) (used G (history G t Y s h))) v (Y i)

/-- The local bound used in predictable concentration is derived from the
actual candidate count and overlap at this particular round and history. -/
theorem hits_localMean_le (G : SimpleGraph V) (Y : ℕ → Finset V)
    (b lam : ℝ) (n : ℕ) (hb : 1 ≤ b) (hlam : 0 ≤ lam)
    (hL : 8 ≤ Parameters.load lam n) (i s : ℕ) (v : V)
    (h : Fin s → Fin (Parameters.choices b lam n))
    (hinter : s ≠ i → ((Y i ∩ Y s).card : ℝ) ≤ 6 * lam ^ 2 * n) :
    PredictableBernoulli.localMean
        (hitsProcess G (Parameters.choices b lam n) Y i v) s h ≤
      hitsBound b lam Y i v s := by
  by_cases hsi : s = i
  · simp only [hitsBound, if_pos hsi]
    exact hits_localMean_le_one G _ (Parameters.choices_pos b lam n hb hL) Y i s v h
  · simp only [hitsBound, if_neg hsi]
    by_cases hv : v ∈ Y s
    · simp only [if_pos hv]
      rw [hits_localMean_eq]
      calc
        _ ≤ ((Y i ∩ Y s).card : ℝ) / Parameters.choices b lam n :=
          div_le_div_of_nonneg_right
            (by exact_mod_cast hits_harmful_card_le G _ Y i s v h) (Nat.cast_nonneg _)
        _ ≤ (6 * lam ^ 2 * n) / Parameters.choices b lam n :=
          div_le_div_of_nonneg_right (hinter hsi) (Nat.cast_nonneg _)
        _ ≤ Parameters.rate b lam := Parameters.local_ratio_le b lam n hb hlam hL
    · simp only [if_neg hv]
      exact le_of_eq (hits_localMean_eq_zero_of_not_mem G _ Y i s v h hv)

/-- The sum of local bounds is controlled by the actual number of rounds
incident to this vertex, plus the possible own round. -/
theorem sum_hitsBound_le (Y : ℕ → Finset V) (b lam : ℝ) (n q i : ℕ) (v : V)
    (hb : 0 < b)
    (hincidence : ((Finset.range q).filter (fun s => v ∈ Y s)).card ≤
      (2 * b * lam * n : ℝ)) :
    (∑ s ∈ Finset.range q, hitsBound b lam Y i v s) ≤ Parameters.load lam n / 2 + 1 := by
  have hr := Parameters.rate_nonneg b lam hb.le
  have hpoint (s : ℕ) : hitsBound b lam Y i v s ≤
      (if s = i then (1 : ℝ) else 0) +
        (if v ∈ Y s then Parameters.rate b lam else 0) := by
    unfold hitsBound
    split_ifs <;> linarith
  have hsum := Finset.sum_le_sum (s := Finset.range q) (fun s _ => hpoint s)
  rw [Finset.sum_add_distrib] at hsum
  have hfirst : (∑ s ∈ Finset.range q, if s = i then (1 : ℝ) else 0) ≤ 1 := by
    rw [Finset.sum_ite_eq']
    split_ifs <;> norm_num
  have hsecond : (∑ s ∈ Finset.range q, if v ∈ Y s then Parameters.rate b lam else 0) =
      Parameters.rate b lam * ((Finset.range q).filter (fun s => v ∈ Y s)).card := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_comm]
  rw [hsecond] at hsum
  have hinc := mul_le_mul_of_nonneg_left hincidence hr
  rw [Parameters.rate_incidence b lam n (ne_of_gt hb)] at hinc
  linarith

/-- Every monitored link and every vertex satisfy the actual load tail.
All local probability premises are discharged inside this graph-specific
theorem from overlaps, candidate disjointness, and vertex incidences. -/
theorem hits_upper_tail (G : SimpleGraph V) (Y : ℕ → Finset V)
    (b lam : ℝ) (n q i : ℕ) (v : V) (hb : 1 ≤ b) (hlam : 0 < lam)
    (hL : 8 ≤ Parameters.load lam n)
    (hinter : ∀ s < q, s ≠ i → ((Y i ∩ Y s).card : ℝ) ≤ 6 * lam ^ 2 * n)
    (hincidence : ((Finset.range q).filter (fun s => v ∈ Y s)).card ≤
      (2 * b * lam * n : ℝ)) :
    MatchingProbability.probability (PredictableBernoulli.weight (Parameters.choices b lam n) q)
        (fun ω => Parameters.load lam n <
          (PredictableBernoulli.count
            (hitsProcess G (Parameters.choices b lam n) Y i v) q ω : ℝ)) ≤
      Real.exp (-Parameters.load lam n / 24) := by
  apply PredictableBernoulli.upper_tail_of_budget_half_add_one
    (Parameters.choices_pos b lam n hb hL)
    (hitsProcess G (Parameters.choices b lam n) Y i v)
    (hitsBound b lam Y i v) q (Parameters.load lam n) hL
  · intro s hs h
    exact hits_localMean_le G Y b lam n hb hlam.le hL i s v h (hinter s hs)
  · exact sum_hitsBound_le Y b lam n q i v (by linarith) hincidence

end Overfull.Dense.LinkPacking
