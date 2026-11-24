import Overfull.Basic
import Mathlib.Data.Real.Basic

/-!
# Robust neighborhoods and changing the tested range

The definitions use actual neighbor counts in a finite simple graph. The
normalization is by the order of that graph, as in the manuscript.
-/

namespace Overfull

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def robustNeighbors (ν : ℝ) (S : Finset V) : Finset V := by
  classical
  exact univ.filter (fun v => ν * Fintype.card V ≤
    ((G.neighborFinset v ∩ S).card : ℝ))

noncomputable def IsRobustExpander (ν τ : ℝ) : Prop :=
  ∀ S : Finset V,
    τ * Fintype.card V ≤ (S.card : ℝ) →
    (S.card : ℝ) ≤ (1 - τ) * Fintype.card V →
    (S.card : ℝ) + ν * Fintype.card V ≤ (robustNeighbors G ν S).card

theorem mem_robustNeighbors (ν : ℝ) (S : Finset V) (v : V) :
    v ∈ robustNeighbors G ν S ↔
      ν * Fintype.card V ≤ ((G.neighborFinset v ∩ S).card : ℝ) := by
  classical
  simp [robustNeighbors]

theorem robustNeighbors_mono_parameter (ν μ : ℝ) (h : μ ≤ ν) (S : Finset V) :
    robustNeighbors G ν S ⊆ robustNeighbors G μ S := by
  intro v hv
  rw [mem_robustNeighbors] at hv ⊢
  exact (mul_le_mul_of_nonneg_right h (Nat.cast_nonneg _)).trans hv

/-- Double-count incidences between an arbitrary set and the whole graph. -/
theorem sum_neighbors_in_set (S : Finset V) :
    (∑ v : V, (G.neighborFinset v ∩ S).card) =
      ∑ v ∈ S, G.degree v := by
  classical
  have hN (v : V) : G.neighborFinset v ∩ S = S.filter (G.Adj v) := by
    ext w
    simp [and_comm]
  simp_rw [hN, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  simp_rw [G.adj_comm]
  rw [Finset.sum_boole]
  have hset : (Finset.univ.filter (G.Adj v)) = G.neighborFinset v := by
    ext w
    simp
  exact congrArg Finset.card hset

/-- The usual incidence bound for the robust neighborhood of a set. -/
theorem robustNeighbors_incidence_bound (η ν : ℝ) (hν : 0 ≤ ν)
    (hdegree : ∀ v, η * Fintype.card V ≤ (G.degree v : ℝ))
    (S : Finset V) :
    η * Fintype.card V * S.card ≤
      (robustNeighbors G ν S).card * (S.card : ℝ) +
        ν * (Fintype.card V : ℝ)^2 := by
  classical
  let R := robustNeighbors G ν S
  let m : ℝ := Fintype.card V
  have hm : 0 ≤ m := Nat.cast_nonneg _
  have hsum := sum_neighbors_in_set G S
  have hsumR : (∑ v : V, ((G.neighborFinset v ∩ S).card : ℝ)) =
      ∑ v ∈ S, (G.degree v : ℝ) := by exact_mod_cast hsum
  have hlower : η * m * S.card ≤ ∑ v ∈ S, (G.degree v : ℝ) := by
    calc
      _ = ∑ _v ∈ S, η * m := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun v _ => hdegree v)
  have hupper : (∑ v : V, ((G.neighborFinset v ∩ S).card : ℝ)) ≤
      (R.card : ℝ) * S.card + ν * m^2 := by
    calc
      _ ≤ ∑ v : V, ((if v ∈ R then (S.card : ℝ) else 0) + ν * m) := by
        apply Finset.sum_le_sum
        intro v _
        by_cases hv : v ∈ R
        · have hcard : ((G.neighborFinset v ∩ S).card : ℝ) ≤ S.card := by
            exact_mod_cast Finset.card_le_card (Finset.inter_subset_right :
              G.neighborFinset v ∩ S ⊆ S)
          rw [if_pos hv]
          nlinarith
        · have hv' : ((G.neighborFinset v ∩ S).card : ℝ) < ν * m := by
            exact lt_of_not_ge ((mem_robustNeighbors G ν S v).not.mp hv)
          rw [if_neg hv, zero_add]
          exact hv'.le
      _ = _ := by simp [Finset.sum_add_distrib, m]; ring
  exact hlower.trans (hsumR ▸ hupper)

/-- At most the complement of `S` can be lost when counting a vertex's
neighbors in `S`. The additive form avoids truncated subtraction. -/
theorem degree_add_card_le_neighbors_add_order (S : Finset V) (v : V) :
    G.degree v + S.card ≤ (G.neighborFinset v ∩ S).card + Fintype.card V := by
  have hpart := Finset.card_inter_add_card_sdiff (G.neighborFinset v) S
  have hbound : (G.neighborFinset v \ S).card ≤ (Finset.univ \ S).card := by
    apply Finset.card_le_card
    intro w hw
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, (Finset.mem_sdiff.mp hw).2⟩
  have htotal : (Finset.univ \ S).card + S.card = Fintype.card V := by
    simpa using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hpart
  omega

/-- Lemma `pre:range-reduction` in the manuscript: a linear minimum
degree permits the tested robust range to be made arbitrarily smaller. -/
theorem robust_range_reduction (η ν τ τ' : ℝ)
    (hη : 0 < η) (hη1 : η ≤ 1) (hν : 0 < ν)
    (hτ : τ ≤ η / 4) (hτ' : 0 < τ') (hτ'τ : τ' ≤ τ)
    (hdegree : ∀ v, η * Fintype.card V ≤ (G.degree v : ℝ))
    (hexpand : IsRobustExpander G ν τ) :
    IsRobustExpander G (min ν (η * τ' / 2)) τ' := by
  classical
  let μ := min ν (η * τ' / 2)
  let m : ℝ := Fintype.card V
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  have hμ0 : 0 ≤ μ := le_min hν.le (by positivity)
  have hμν : μ ≤ ν := min_le_left _ _
  have hμb : μ ≤ η * τ' / 2 := min_le_right _ _
  have hμτ' : μ ≤ τ' := by
    have hmul := mul_le_mul_of_nonneg_right hη1 hτ'.le
    nlinarith
  have hτμ : τ + μ ≤ η / 2 := by linarith
  intro S hSlow hShigh
  change τ' * m ≤ (S.card : ℝ) at hSlow
  change (S.card : ℝ) ≤ (1 - τ') * m at hShigh
  change (S.card : ℝ) + μ * m ≤ (robustNeighbors G μ S).card
  have hSm : (S.card : ℝ) ≤ m := by
    dsimp [m]
    exact_mod_cast Finset.card_le_univ S
  by_cases hm : m = 0
  · have hR0 : (0 : ℝ) ≤ (robustNeighbors G μ S).card := Nat.cast_nonneg _
    nlinarith
  have hmpos : 0 < m := lt_of_le_of_ne hm0 (Ne.symm hm)
  by_cases hsmall : (S.card : ℝ) < τ * m
  · have hspos : (0 : ℝ) < S.card := lt_of_lt_of_le (mul_pos hτ' hmpos) hSlow
    have hinc := robustNeighbors_incidence_bound G η μ hμ0 hdegree S
    change η * m * S.card ≤
      (robustNeighbors G μ S).card * (S.card : ℝ) + μ * m^2 at hinc
    have hμms : μ * m ≤ η * (S.card : ℝ) / 2 := by
      have h1 := mul_le_mul_of_nonneg_right hμb hm0
      have h2 := mul_le_mul_of_nonneg_left hSlow hη.le
      nlinarith
    have hR : η * m / 2 ≤ (robustNeighbors G μ S).card := by
      have h := mul_le_mul_of_nonneg_right hμms hm0
      nlinarith
    have hbound := mul_le_mul_of_nonneg_right hτμ hm0
    nlinarith
  · by_cases hmiddle : (S.card : ℝ) ≤ (1 - τ) * m
    · have hold := hexpand S (le_of_not_gt hsmall) hmiddle
      have hcard : ((robustNeighbors G ν S).card : ℝ) ≤
          (robustNeighbors G μ S).card := by
        exact_mod_cast Finset.card_le_card (robustNeighbors_mono_parameter G ν μ hμν S)
      have hmul := mul_le_mul_of_nonneg_right hμν hm0
      change (S.card : ℝ) + ν * m ≤ (robustNeighbors G ν S).card at hold
      linarith
    · have hlarge : (1 - τ) * m < (S.card : ℝ) := lt_of_not_ge hmiddle
      have hfull : robustNeighbors G μ S = Finset.univ := by
        apply Finset.eq_univ_iff_forall.mpr
        intro v
        rw [mem_robustNeighbors]
        have hdeg := hdegree v
        have hn : (G.degree v : ℝ) + S.card ≤
            (G.neighborFinset v ∩ S).card + m := by
          dsimp [m]
          exact_mod_cast degree_add_card_le_neighbors_add_order G S v
        have hmul := mul_le_mul_of_nonneg_right hτμ hm0
        change η * m ≤ (G.degree v : ℝ) at hdeg
        nlinarith
      rw [hfull, Finset.card_univ]
      change (S.card : ℝ) + μ * m ≤ m
      have hmul := mul_le_mul_of_nonneg_right hμτ' hm0
      nlinarith

end Overfull
