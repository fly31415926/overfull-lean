import Overfull.RobustRealization.Construction
import Overfull.RobustRealization.Uniform
import Overfull.RobustRealization.Relabeling

/-!
# Balanced robust realization

Lemma 2.21: every sufficiently large integer degree sequence with spread at
most one, linear minimum degree, and even sum has a simple robust-expander
realization on the prescribed labels. Both constants precede the sequence.
-/

namespace Overfull

open Finset Classical SimpleGraph
open scoped BigOperators

set_option maxHeartbeats 800000 in
/-- An almost constant degree sequence of even sum has an actual robust
simple-graph realization. The pairwise degree inequality is equivalent to
the manuscript's maximum-minus-minimum bound of one. -/
theorem balanced_robust_realization (δ τ : ℝ)
    (hδ : 0 < δ) (_hδ1 : δ < 1) (hτ : 0 < τ) (_hτ1 : τ < 1/2) :
    ∃ ν : ℝ, 0 < ν ∧ ∃ n₀ : ℕ,
      ∀ n : ℕ, n₀ ≤ n → ∀ d : Fin n → ℕ,
        (∀ v, δ*n ≤ (d v : ℝ)) → (∀ v, d v ≤ n-1) →
        (∀ u v, d u ≤ d v+1) → Even (∑ v, d v) →
        ∃ G : SimpleGraph (Fin n), (∀ v, G.degree v = d v) ∧
          IsRobustExpander G ν τ := by
  obtain ⟨ν, hν, n₁, hn₁, hrobust⟩ :=
    RobustRealization.exists_cyclePower_robust_parameters δ τ hδ hτ
  obtain ⟨n₂, hn₂⟩ := exists_nat_gt (6/δ)
  refine ⟨ν, hν, max n₁ n₂, ?_⟩
  intro n hn d hlower hupper hspread heven
  have hn₁' : n₁ ≤ n := (le_max_left _ _).trans hn
  have hn₂' : n₂ ≤ n := (le_max_right _ _).trans hn
  have hnpos : 0 < n := hn₁.trans_le hn₁'
  letI : NeZero n := ⟨Nat.ne_of_gt hnpos⟩
  have hnlarge : 6 < δ*n := by
    have hmm : (n₂ : ℝ) ≤ n := by exact_mod_cast hn₂'
    have hh := (div_lt_iff₀ hδ).mp (hn₂.trans_le hmm)
    nlinarith
  obtain ⟨v₀, _, hmin⟩ :=
    Finset.exists_min_image (univ : Finset (Fin n)) d Finset.univ_nonempty
  let a := d v₀
  have ha : 2 ≤ a := by
    have h := hlower v₀
    change δ*n ≤ (a : ℝ) at h
    have hh : (2 : ℝ) ≤ a := by linarith
    exact_mod_cast hh
  have han : a < n := by have := hupper v₀; dsimp [a]; omega
  have hvalues (v : Fin n) : d v = a ∨ d v = a+1 := by
    have h₁ := hmin v (Finset.mem_univ _)
    have h₂ := hspread v v₀
    change a ≤ d v at h₁
    change d v ≤ a+1 at h₂
    omega
  let T : Finset (Fin n) := univ.filter (fun v => d v = a+1)
  have hT (v : Fin n) : v ∈ T ↔ d v = a+1 := by simp [T]
  have hd (v : Fin n) : d v = if v ∈ T then a+1 else a := by
    by_cases hv : v ∈ T
    · rw [if_pos hv]
      exact (hT v).mp hv
    · rw [if_neg hv]
      have hv' := (hT v).not.mp hv
      rcases hvalues v with h | h
      · exact h
      · exact (hv' h).elim
  have hsum : (∑ v, d v) = n*a+T.card := by
    calc
      _ = ∑ v : Fin n, (a + if v ∈ T then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro v _
        rw [hd v]
        split <;> omega
      _ = _ := by simp [Finset.sum_add_distrib]
  have hmax : 0 < T.card → a+1 < n := by
    intro hpos
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
    have hv' := (hT v).mp hv
    have hu := hupper v
    omega
  have hcard : T.card ≤ n := by simpa using Finset.card_le_univ T
  have heven' : Even (n*a+T.card) := hsum ▸ heven
  obtain ⟨G, M, r, Z, hZ, hdegree, hr, hcover, hM⟩ :=
    RobustRealization.exists_degree_multiset n a T.card ha han hcard hmax heven'
  have hr' : δ*n/3 ≤ r := by
    have h := hlower v₀
    change δ*n ≤ (a : ℝ) at h
    linarith
  have hG : IsRobustExpander G ν τ := hrobust n hn₁' r hr' G M hcover hM
  obtain ⟨e, he⟩ := RobustRealization.exists_perm_mem_iff Z T hZ
  refine ⟨G.comap e, ?_, ?_⟩
  · intro v
    have hc := RobustRealization.comap_equiv_degree G e v
    have hv := hdegree (e v)
    have ht : (if e v ∈ Z then a+1 else a) = d v := by
      simpa only [he v] using (hd v).symm
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using hc.trans (hv.trans ht)
  · convert RobustRealization.robust_comap_equiv G e ν τ hG using 1

end Overfull
