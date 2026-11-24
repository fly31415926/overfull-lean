import Overfull.BipartiteRange
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Reversing a bipartite robust expander

The reversed graph is the actual pullback along `Sum.swap`.  The proof
counts the original crossing edges between two finite shores.  No degree
hypothesis and no reverse-expansion certificate are supplied as inputs.
-/

namespace Overfull

open Finset

variable {A B : Type*} [Fintype A] [Fintype B]
  [DecidableEq A] [DecidableEq B]
variable (G : SimpleGraph (A ⊕ B)) [DecidableRel G.Adj]

omit [Fintype A] [DecidableEq A] [DecidableEq B] in
/-- Reversing the two summands exchanges the actual left and right
crossing-neighbor sets. -/
theorem leftNeighbors_swap (a : A) :
    leftNeighbors (G.comap Sum.swap) a = rightNeighbors G a := by
  ext b
  simp [leftNeighbors, rightNeighbors, G.adj_comm]

/-- Double-count the actual crossing edges between two finite shores. -/
theorem sum_crossing_neighbors_between (S : Finset A) (T : Finset B) :
    (∑ b ∈ T, (S ∩ leftNeighbors G b).card) =
      ∑ a ∈ S, (T ∩ rightNeighbors G a).card := by
  classical
  have hL (b : B) : S ∩ leftNeighbors G b =
      S.filter (fun a => G.Adj (.inl a) (.inr b)) := by
    ext a
    simp [leftNeighbors]
  have hR (a : A) : T ∩ rightNeighbors G a =
      T.filter (fun b => G.Adj (.inl a) (.inr b)) := by
    ext b
    simp [rightNeighbors]
  simp_rw [hL, hR, Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm

/-- A shore avoiding the actual reverse robust neighborhood has few
incidences with the test set.  Its forward robust neighbors give the
opposite lower bound on precisely the same original edge copies. -/
theorem bipartite_reverse_incidence_bound (ν μ : ℝ)
    (hbalance : Fintype.card A = Fintype.card B)
    (T : Finset B) (S : Finset A)
    (hS : S ⊆ Finset.univ \ bipartiteRobustNeighbors (G.comap Sum.swap) μ T) :
    ν * Fintype.card A * (bipartiteRobustNeighbors G ν S ∩ T).card ≤
      μ * Fintype.card A * S.card := by
  classical
  have hsum : (∑ b ∈ T, ((S ∩ leftNeighbors G b).card : ℝ)) =
      ∑ a ∈ S, ((T ∩ rightNeighbors G a).card : ℝ) := by
    exact_mod_cast sum_crossing_neighbors_between G S T
  calc
    _ = ∑ _b ∈ bipartiteRobustNeighbors G ν S ∩ T,
        ν * (Fintype.card A : ℝ) := by simp [mul_comm]
    _ ≤ ∑ b ∈ bipartiteRobustNeighbors G ν S ∩ T,
        ((S ∩ leftNeighbors G b).card : ℝ) := by
      apply Finset.sum_le_sum
      intro b hb
      exact (mem_bipartiteRobustNeighbors G ν S b).mp (Finset.mem_inter.mp hb).1
    _ ≤ ∑ b ∈ T, ((S ∩ leftNeighbors G b).card : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
        (fun _ _ _ => Nat.cast_nonneg _)
    _ = ∑ a ∈ S, ((T ∩ rightNeighbors G a).card : ℝ) := hsum
    _ ≤ ∑ _a ∈ S, μ * (Fintype.card A : ℝ) := by
      apply Finset.sum_le_sum
      intro a ha
      have hnot := (Finset.mem_sdiff.mp (hS ha)).2
      have hlt := lt_of_not_ge
        ((mem_bipartiteRobustNeighbors (G.comap Sum.swap) μ T a).not.mp hnot)
      rw [leftNeighbors_swap, ← hbalance] at hlt
      exact hlt.le
    _ = _ := by simp [mul_comm]

/-- One-directional robust expansion of a balanced bipartite graph
implies robust expansion in the reverse direction, with explicit loss.
The bound `2 ≤ τ*m` absorbs the rounding used to select the largest
allowed forward shore. -/
theorem IsBipartiteRobustExpander.reverse (ν τ : ℝ)
    (hν : 0 < ν) (hντ : ν ≤ τ) (hτ : τ ≤ 1 / 4)
    (hbalance : Fintype.card A = Fintype.card B)
    (horder : 2 ≤ τ * (Fintype.card A : ℝ))
    (hG : IsBipartiteRobustExpander G ν τ) :
    IsBipartiteRobustExpander (G.comap Sum.swap)
      (min (ν ^ 2) (ν * τ) / 4) (2 * τ) := by
  classical
  let μ : ℝ := min (ν ^ 2) (ν * τ) / 4
  let m : ℝ := Fintype.card A
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  have hτ0 : 0 < τ := hν.trans_le hντ
  have hm : 0 < m := by
    change 2 ≤ τ * m at horder
    by_contra hn
    have hz : m = 0 := le_antisymm (le_of_not_gt hn) hm0
    rw [hz, mul_zero] at horder
    norm_num at horder
  change 2 ≤ τ * m at horder
  have hν1 : ν ≤ 1 := by linarith only [hντ, hτ]
  have hμ0 : 0 ≤ μ := by
    dsimp [μ]
    positivity
  have hμν2 : μ ≤ ν ^ 2 / 4 := by
    exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hμντ : μ ≤ ν * τ / 4 := by
    exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have hμν : μ ≤ ν / 4 := by
    have hn := mul_nonneg hν.le (sub_nonneg.mpr hν1)
    nlinarith only [hμν2, hn]
  have hμτ : μ ≤ τ := by linarith only [hμν, hντ, hν]
  have hμcoef : μ < ν * (ν - μ) := by
    have hn := mul_le_mul_of_nonneg_left hμν hν.le
    nlinarith only [hμν2, hn, sq_pos_of_pos hν]
  have hμτcoef : μ < ν * τ / 2 := by
    nlinarith only [hμντ, mul_pos hν hτ0]
  intro T hTlow hThigh
  rw [← hbalance] at hTlow hThigh ⊢
  change 2 * τ * m ≤ (T.card : ℝ) at hTlow
  change (T.card : ℝ) ≤ (1 - 2 * τ) * m at hThigh
  change (T.card : ℝ) + μ * m ≤
    (bipartiteRobustNeighbors (G.comap Sum.swap) μ T).card
  let Q := bipartiteRobustNeighbors (G.comap Sum.swap) μ T
  let S := Finset.univ \ Q
  have hSQ : (S.card : ℝ) + Q.card = m := by
    have hn : S.card + Q.card = Fintype.card A := by
      simpa [S] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ Q)
    dsimp [m]
    exact_mod_cast hn
  by_contra hfail
  have hbad : (Q.card : ℝ) < (T.card : ℝ) + μ * m := lt_of_not_ge hfail
  have hSlow : τ * m ≤ (S.card : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hμτ hm0
    nlinarith only [hSQ, hbad, hThigh, h]
  have hcount (U : Finset A) (hUS : U ⊆ S) :
      ν * ((bipartiteRobustNeighbors G ν U ∩ T).card : ℝ) ≤ μ * m := by
    have hi := bipartite_reverse_incidence_bound G ν μ hbalance T U hUS
    have hU : (U.card : ℝ) ≤ m := by
      dsimp [m]
      exact_mod_cast Finset.card_le_univ U
    have hu := mul_le_mul_of_nonneg_left hU (mul_nonneg hμ0 hm0)
    apply (mul_le_mul_iff_right₀ hm).mp
    change ν * m * (bipartiteRobustNeighbors G ν U ∩ T).card ≤
      μ * m * U.card at hi
    nlinarith only [hi, hu]
  have hforward (U : Finset A) (hUS : U ⊆ S)
      (hUlow : τ * m ≤ (U.card : ℝ))
      (hUhigh : (U.card : ℝ) ≤ (1 - τ) * m) :
      ν * ((U.card : ℝ) + ν * m + T.card - m) ≤ μ * m := by
    have hx := hG U hUlow hUhigh
    change (U.card : ℝ) + ν * m ≤ (bipartiteRobustNeighbors G ν U).card at hx
    have hi := Finset.card_inter_add_card_union (bipartiteRobustNeighbors G ν U) T
    have hu := Finset.card_le_univ (bipartiteRobustNeighbors G ν U ∪ T)
    rw [← hbalance] at hu
    have hcard : ((bipartiteRobustNeighbors G ν U).card : ℝ) + T.card ≤
        (bipartiteRobustNeighbors G ν U ∩ T).card + m := by
      dsimp [m]
      exact_mod_cast (show (bipartiteRobustNeighbors G ν U).card + T.card ≤
        (bipartiteRobustNeighbors G ν U ∩ T).card + Fintype.card A by omega)
    have hl : (U.card : ℝ) + ν * m + T.card - m ≤
        (bipartiteRobustNeighbors G ν U ∩ T).card := by linarith only [hx, hcard]
    exact (mul_le_mul_of_nonneg_left hl hν.le).trans (hcount U hUS)
  by_cases hShigh : (S.card : ℝ) ≤ (1 - τ) * m
  · have hc := hforward S (Finset.Subset.refl S) hSlow hShigh
    have hl : (ν - μ) * m < (S.card : ℝ) + ν * m + T.card - m := by
      nlinarith only [hSQ, hbad]
    have hb := mul_lt_mul_of_pos_left hl hν
    have hp := mul_lt_mul_of_pos_right hμcoef hm
    nlinarith only [hc, hb, hp]
  · let q : ℕ := ⌊(1 - τ) * m⌋₊
    have hfloor : (q : ℝ) ≤ (1 - τ) * m := by
      apply Nat.floor_le
      exact mul_nonneg (by linarith) hm0
    have hround : (1 - τ) * m < (q : ℝ) + 1 := Nat.lt_floor_add_one _
    have hqS : q ≤ S.card := by
      exact_mod_cast hfloor.trans (lt_of_not_ge hShigh).le
    obtain ⟨U, hUS, hUcard⟩ := Finset.exists_subset_card_eq hqS
    have hUlow : τ * m ≤ (U.card : ℝ) := by
      rw [hUcard]
      have ht := mul_le_mul_of_nonneg_right hτ hm0
      nlinarith only [hround, ht, horder]
    have hUhigh : (U.card : ℝ) ≤ (1 - τ) * m := by simpa [hUcard] using hfloor
    have hc := hforward U hUS hUlow hUhigh
    have hl : τ * m / 2 ≤ (U.card : ℝ) + ν * m + T.card - m := by
      rw [hUcard]
      nlinarith only [hround, hTlow, horder, mul_nonneg hν.le hm0]
    have hb := mul_le_mul_of_nonneg_left hl hν.le
    have hp := mul_lt_mul_of_pos_right hμτcoef hm
    nlinarith only [hc, hb, hp]

/-- Under the usual hierarchy `ν ≤ τ`, the reverse neighborhood
parameter simplifies to `ν²/4`. -/
theorem IsBipartiteRobustExpander.reverse_sq (ν τ : ℝ)
    (hν : 0 < ν) (hντ : ν ≤ τ) (hτ : τ ≤ 1 / 4)
    (hbalance : Fintype.card A = Fintype.card B)
    (horder : 2 ≤ τ * (Fintype.card A : ℝ))
    (hG : IsBipartiteRobustExpander G ν τ) :
    IsBipartiteRobustExpander (G.comap Sum.swap) (ν ^ 2 / 4) (2 * τ) := by
  have hsq : ν ^ 2 ≤ ν * τ := by
    nlinarith only [mul_le_mul_of_nonneg_left hντ hν.le]
  simpa only [min_eq_left hsq] using
    IsBipartiteRobustExpander.reverse G ν τ hν hντ hτ hbalance horder hG

end Overfull
