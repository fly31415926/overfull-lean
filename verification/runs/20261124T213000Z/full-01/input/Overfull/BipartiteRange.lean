import Overfull.BipartiteMatching

/-!
# Reducing the range of bipartite robust expansion

All neighborhood counts refer to actual crossing edges of a finite simple
graph. The balanced side size is the normalization, as in the manuscript.
-/

namespace Overfull

open Finset

variable {A B : Type*} [Fintype A] [Fintype B]
  [DecidableEq A]
variable (G : SimpleGraph (A ⊕ B)) [DecidableRel G.Adj]

theorem mem_bipartiteRobustNeighbors (ν : ℝ) (S : Finset A) (b : B) :
    b ∈ bipartiteRobustNeighbors G ν S ↔
      ν * Fintype.card A ≤ ((S ∩ leftNeighbors G b).card : ℝ) := by
  classical
  simp [bipartiteRobustNeighbors]

theorem bipartiteRobustNeighbors_mono_parameter (ν μ : ℝ)
    (h : μ ≤ ν) (S : Finset A) :
    bipartiteRobustNeighbors G ν S ⊆ bipartiteRobustNeighbors G μ S := by
  intro b hb
  rw [mem_bipartiteRobustNeighbors] at hb ⊢
  exact (mul_le_mul_of_nonneg_right h (Nat.cast_nonneg _)).trans hb

/-- Count the actual crossing edges incident with the chosen left-side set. -/
theorem sum_left_neighbors_in_set (S : Finset A) :
    (∑ b : B, (S ∩ leftNeighbors G b).card) =
      ∑ a ∈ S, (rightNeighbors G a).card := by
  classical
  have hN (b : B) : S ∩ leftNeighbors G b =
      S.filter (fun a => G.Adj (.inl a) (.inr b)) := by
    ext a
    simp [leftNeighbors]
  simp_rw [hN, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp [rightNeighbors]

/-- The incidence bound for a bipartite robust neighborhood. -/
theorem bipartiteRobustNeighbors_incidence_bound (α ν : ℝ) (hν : 0 ≤ ν)
    (hbalance : Fintype.card A = Fintype.card B)
    (hdegree : ∀ a, α * Fintype.card A ≤ ((rightNeighbors G a).card : ℝ))
    (S : Finset A) :
    α * Fintype.card A * S.card ≤
      (bipartiteRobustNeighbors G ν S).card * (S.card : ℝ) +
        ν * (Fintype.card A : ℝ)^2 := by
  classical
  let R := bipartiteRobustNeighbors G ν S
  let m : ℝ := Fintype.card A
  have hm : 0 ≤ m := Nat.cast_nonneg _
  have hsum := sum_left_neighbors_in_set G S
  have hsumR : (∑ b : B, ((S ∩ leftNeighbors G b).card : ℝ)) =
      ∑ a ∈ S, ((rightNeighbors G a).card : ℝ) := by exact_mod_cast hsum
  have hlower : α * m * S.card ≤ ∑ a ∈ S, ((rightNeighbors G a).card : ℝ) := by
    calc
      _ = ∑ _a ∈ S, α * m := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun a _ => hdegree a)
  have hupper : (∑ b : B, ((S ∩ leftNeighbors G b).card : ℝ)) ≤
      (R.card : ℝ) * S.card + ν * m^2 := by
    calc
      _ ≤ ∑ b : B, ((if b ∈ R then (S.card : ℝ) else 0) + ν * m) := by
        apply Finset.sum_le_sum
        intro b _
        by_cases hb : b ∈ R
        · have hcard : ((S ∩ leftNeighbors G b).card : ℝ) ≤ S.card := by
            exact_mod_cast Finset.card_le_card
              (Finset.inter_subset_left : S ∩ leftNeighbors G b ⊆ S)
          rw [if_pos hb]
          nlinarith
        · have hb' : ((S ∩ leftNeighbors G b).card : ℝ) < ν * m := by
            exact lt_of_not_ge ((mem_bipartiteRobustNeighbors G ν S b).not.mp hb)
          rw [if_neg hb, zero_add]
          exact hb'.le
      _ = _ := by simp [Finset.sum_add_distrib, m, ← hbalance]; ring
  exact hlower.trans (hsumR ▸ hupper)

omit [Fintype B] in
/-- Only vertices outside the selected left-side set can be lost from a
right vertex's neighborhood. -/
theorem left_degree_add_card_le_neighbors_add_order (S : Finset A) (b : B) :
    (leftNeighbors G b).card + S.card ≤
      (S ∩ leftNeighbors G b).card + Fintype.card A := by
  have hpart := Finset.card_inter_add_card_sdiff (leftNeighbors G b) S
  have hbound : (leftNeighbors G b \ S).card ≤ (Finset.univ \ S).card := by
    apply Finset.card_le_card
    intro a ha
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, (Finset.mem_sdiff.mp ha).2⟩
  have htotal : (Finset.univ \ S).card + S.card = Fintype.card A := by
    simpa using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
  rw [Finset.inter_comm] at hpart
  omega

/-- Lemma 6.4 of the manuscript (`old:fac:range`). A linear minimum
degree permits the bipartite robust-expansion range to be reduced.
The empty balanced graph is included; for positive order, `α ≤ 1`
is derived from the actual degree bound. -/
theorem bipartite_robust_range_reduction (α ν τ σ : ℝ)
    (hν : 0 < ν) (hντ : ν ≤ τ) (_hτhalf : τ < 1 / 2)
    (hτ : τ < α / 8) (hσ : 0 < σ) (hστ : σ ≤ τ)
    (hbalance : Fintype.card A = Fintype.card B)
    (hleft : ∀ a, α * Fintype.card A ≤ ((rightNeighbors G a).card : ℝ))
    (hright : ∀ b, α * Fintype.card A ≤ ((leftNeighbors G b).card : ℝ))
    (hexpand : IsBipartiteRobustExpander G ν τ) :
    IsBipartiteRobustExpander G (min ν (α * σ / 4)) σ := by
  classical
  let μ := min ν (α * σ / 4)
  let m : ℝ := Fintype.card A
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  have hα : 0 < α := by linarith only [hσ, hστ, hτ]
  have hμ0 : 0 ≤ μ := le_min hν.le (by positivity)
  have hμν : μ ≤ ν := min_le_left _ _
  have hμb : μ ≤ α * σ / 4 := min_le_right _ _
  have hτμ : τ + μ ≤ 3 * α / 4 := by linarith
  intro S hSlow hShigh
  change σ * m ≤ (S.card : ℝ) at hSlow
  change (S.card : ℝ) ≤ (1 - σ) * m at hShigh
  change (S.card : ℝ) + μ * m ≤ (bipartiteRobustNeighbors G μ S).card
  have hSm : (S.card : ℝ) ≤ m := by
    dsimp [m]
    exact_mod_cast Finset.card_le_univ S
  by_cases hm : m = 0
  · have hR0 : (0 : ℝ) ≤ (bipartiteRobustNeighbors G μ S).card := Nat.cast_nonneg _
    nlinarith
  have hmpos : 0 < m := lt_of_le_of_ne hm0 (Ne.symm hm)
  have hα1 : α ≤ 1 := by
    have hcardA : 0 < Fintype.card A := by
      exact_mod_cast (show (0 : ℝ) < Fintype.card A from hmpos)
    obtain ⟨a⟩ := Fintype.card_pos_iff.mp hcardA
    have hdeg := hleft a
    have hbound : ((rightNeighbors G a).card : ℝ) ≤ m := by
      dsimp [m]
      rw [hbalance]
      exact_mod_cast Finset.card_le_univ (rightNeighbors G a)
    change α * m ≤ ((rightNeighbors G a).card : ℝ) at hdeg
    nlinarith
  have hμσ : μ ≤ σ := by
    have hmul := mul_le_mul_of_nonneg_right hα1 hσ.le
    nlinarith
  by_cases hsmall : (S.card : ℝ) < τ * m
  · have hspos : (0 : ℝ) < S.card := lt_of_lt_of_le (mul_pos hσ hmpos) hSlow
    have hinc := bipartiteRobustNeighbors_incidence_bound G α μ hμ0 hbalance hleft S
    change α * m * S.card ≤
      (bipartiteRobustNeighbors G μ S).card * (S.card : ℝ) + μ * m^2 at hinc
    have hμms : μ * m ≤ α * (S.card : ℝ) / 4 := by
      have h1 := mul_le_mul_of_nonneg_right hμb hm0
      have h2 := mul_le_mul_of_nonneg_left hSlow hα.le
      nlinarith
    have hR : 3 * α * m / 4 ≤ (bipartiteRobustNeighbors G μ S).card := by
      have h := mul_le_mul_of_nonneg_right hμms hm0
      nlinarith
    have hbound := mul_le_mul_of_nonneg_right hτμ hm0
    nlinarith
  · by_cases hmiddle : (S.card : ℝ) ≤ (1 - τ) * m
    · have hold := hexpand S (le_of_not_gt hsmall) hmiddle
      have hcard : ((bipartiteRobustNeighbors G ν S).card : ℝ) ≤
          (bipartiteRobustNeighbors G μ S).card := by
        exact_mod_cast Finset.card_le_card
          (bipartiteRobustNeighbors_mono_parameter G ν μ hμν S)
      have hmul := mul_le_mul_of_nonneg_right hμν hm0
      change (S.card : ℝ) + ν * m ≤ (bipartiteRobustNeighbors G ν S).card at hold
      linarith
    · have hlarge : (1 - τ) * m < (S.card : ℝ) := lt_of_not_ge hmiddle
      have hfull : bipartiteRobustNeighbors G μ S = Finset.univ := by
        apply Finset.eq_univ_iff_forall.mpr
        intro b
        rw [mem_bipartiteRobustNeighbors]
        have hdeg := hright b
        have hn : ((leftNeighbors G b).card : ℝ) + S.card ≤
            (S ∩ leftNeighbors G b).card + m := by
          dsimp [m]
          exact_mod_cast left_degree_add_card_le_neighbors_add_order G S b
        have hmul := mul_le_mul_of_nonneg_right hτμ hm0
        change α * m ≤ ((leftNeighbors G b).card : ℝ) at hdeg
        nlinarith
      rw [hfull, Finset.card_univ, ← hbalance]
      change (S.card : ℝ) + μ * m ≤ m
      have hmul := mul_le_mul_of_nonneg_right hμσ hm0
      nlinarith

end Overfull

