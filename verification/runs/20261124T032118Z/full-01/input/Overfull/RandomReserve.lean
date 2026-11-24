import Overfull.BipartiteMatching
import Overfull.Probability.Bernoulli

/-!
# Random reserves in bipartite robust expanders

The random graph is obtained by independent Boolean choices for crossing
edges. Nonedges remain absent. The probability is the actual finite product
probability of those choices.
-/

namespace Overfull.RandomReserve

open Finset Classical
open scoped BigOperators

variable {A B : Type*} [Fintype A] [Fintype B]

def sampledGraph (G : SimpleGraph (A ⊕ B)) (ω : A × B → Bool) :
    SimpleGraph (A ⊕ B) where
  Adj x y := match x, y with
    | .inl a, .inr b => G.Adj (.inl a) (.inr b) ∧ ω (a, b) = true
    | .inr b, .inl a => G.Adj (.inl a) (.inr b) ∧ ω (a, b) = true
    | _, _ => False
  symm := by rintro (a | b) (a' | b') h <;> exact h
  loopless := by rintro (a | b) <;> simp

instance sampledGraph_decidable (G : SimpleGraph (A ⊕ B))
    [DecidableRel G.Adj] (ω : A × B → Bool) :
    DecidableRel (sampledGraph G ω).Adj := by
  intro x y
  cases x <;> cases y <;> simp only [sampledGraph] <;> infer_instance

omit [Fintype A] [Fintype B] in
theorem sampledGraph_le (G : SimpleGraph (A ⊕ B)) (ω : A × B → Bool) :
    sampledGraph G ω ≤ G := by
  rintro (a | b) (a' | b') h
  · exact h.elim
  · exact h.1
  · exact h.1.symm
  · exact h.elim

noncomputable def crossingEdges (G : SimpleGraph (A ⊕ B))
    (X : Finset A) (Z : Finset B) : Finset (A × B) :=
  univ.filter (fun e => e.1 ∈ X ∧ e.2 ∈ Z ∧ G.Adj (.inl e.1) (.inr e.2))

theorem crossingEdges_card (G : SimpleGraph (A ⊕ B)) [DecidableRel G.Adj]
    (X : Finset A) (Z : Finset B) :
    (crossingEdges G X Z).card = ∑ b ∈ Z, (X ∩ leftNeighbors G b).card := by
  classical
  calc
    _ = ∑ b : B, ∑ a : A,
        if a ∈ X ∧ b ∈ Z ∧ G.Adj (.inl a) (.inr b) then 1 else 0 := by
      simp only [crossingEdges, Finset.card_eq_sum_ones, Finset.sum_filter]
      rw [Fintype.sum_prod_type_right]
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro a _
      by_cases h : a ∈ X ∧ b ∈ Z ∧ G.Adj (.inl a) (.inr b) <;> simp [h]
    _ = ∑ b : B, if b ∈ Z then (X ∩ leftNeighbors G b).card else 0 := by
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : b ∈ Z
      · simp only [hb, true_and, if_true]
        rw [Finset.sum_boole]
        simp only [Nat.cast_id]
        apply congrArg Finset.card
        ext a
        simp [leftNeighbors]
      · simp [hb]
    _ = _ := by rw [← Finset.sum_filter]; simp

theorem crossingEdges_sampled (G : SimpleGraph (A ⊕ B))
    (X : Finset A) (Z : Finset B) (ω : A × B → Bool) :
    crossingEdges (sampledGraph G ω) X Z =
      (crossingEdges G X Z).filter (fun e => ω e = true) := by
  ext e
  simp [crossingEdges, sampledGraph, and_assoc]

theorem sampled_count (G : SimpleGraph (A ⊕ B))
    (X : Finset A) (Z : Finset B) (ω : A × B → Bool) :
    (crossingEdges (sampledGraph G ω) X Z).card =
      Bernoulli.retainedCount (crossingEdges G X Z) ω := by
  rw [crossingEdges_sampled]
  rfl

theorem crossingEdges_card_real (G : SimpleGraph (A ⊕ B)) [DecidableRel G.Adj]
    (X : Finset A) (Z : Finset B) :
    ((crossingEdges G X Z).card : ℝ) =
      ∑ b ∈ Z, ((X ∩ leftNeighbors G b).card : ℝ) := by
  exact_mod_cast crossingEdges_card G X Z

theorem crossingEdges_of_robust_neighbors (G : SimpleGraph (A ⊕ B))
    [DecidableRel G.Adj] (ν : ℝ) (X : Finset A) (Z : Finset B)
    (hZ : Z ⊆ bipartiteRobustNeighbors G ν X) :
    ν * Fintype.card A * Z.card ≤ ((crossingEdges G X Z).card : ℝ) := by
  classical
  rw [crossingEdges_card_real]
  calc
    _ = ∑ _b ∈ Z, ν * Fintype.card A := by simp; ring
    _ ≤ _ := Finset.sum_le_sum (fun b hb => by
      have h := hZ hb
      simpa only [bipartiteRobustNeighbors, Finset.mem_filter, Finset.mem_univ,
        true_and] using h)

/-- The deterministic implication used after the simultaneous sampling bounds. -/
theorem robust_of_pair_counts (G H : SimpleGraph (A ⊕ B))
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (p ν τ : ℝ) (hp1 : p ≤ 1) (hν : 0 < ν)
    (hG : IsBipartiteRobustExpander G ν τ)
    (hpairs : ∀ X : Finset A,
      τ * Fintype.card A ≤ (X.card : ℝ) →
      (X.card : ℝ) ≤ (1 - τ) * Fintype.card A →
      ∀ Z : Finset B, Z ⊆ bipartiteRobustNeighbors G ν X →
      Z.card = ⌈ν * Fintype.card A / 2⌉₊ →
      p * ν * Fintype.card A * Z.card / 2 ≤ ((crossingEdges H X Z).card : ℝ)) :
    IsBipartiteRobustExpander H (p * ν / 2) τ := by
  classical
  intro X hXlo hXhi
  by_cases hm : Fintype.card A = 0
  · have hX : X.card = 0 := by have := Finset.card_le_univ X; omega
    simp [hm, hX]
  have hmpos : (0 : ℝ) < Fintype.card A := by exact_mod_cast Nat.pos_of_ne_zero hm
  let R := bipartiteRobustNeighbors G ν X
  let R' := bipartiteRobustNeighbors H (p * ν / 2) X
  let Zbad := R \ R'
  have hbad : Zbad.card < ⌈ν * Fintype.card A / 2⌉₊ := by
    by_contra hnot
    obtain ⟨Z, hZ, hcard⟩ := Finset.exists_subset_card_eq (Nat.le_of_not_gt hnot)
    have hZR : Z ⊆ bipartiteRobustNeighbors G ν X := by
      intro b hb
      exact (Finset.mem_sdiff.mp (hZ hb)).1
    have hnonempty : Z.Nonempty := Finset.card_pos.mp (by
      rw [hcard]
      exact Nat.ceil_pos.mpr (by positivity))
    have hsmall : ((crossingEdges H X Z).card : ℝ) <
        p * ν * Fintype.card A * Z.card / 2 := by
      rw [crossingEdges_card_real]
      calc
        _ < ∑ _b ∈ Z, (p * ν / 2) * Fintype.card A := by
          apply Finset.sum_lt_sum_of_nonempty hnonempty
          intro b hb
          have hbnot := (Finset.mem_sdiff.mp (hZ hb)).2
          have hnr : ¬ (p * ν / 2) * Fintype.card A ≤
              ((X ∩ leftNeighbors H b).card : ℝ) := by
            simpa only [R', bipartiteRobustNeighbors, Finset.mem_filter,
              Finset.mem_univ, true_and] using hbnot
          exact lt_of_not_ge hnr
        _ = _ := by simp; ring
    exact (not_lt_of_ge (hpairs X hXlo hXhi Z hZR hcard)) hsmall
  have hbadR : (Zbad.card : ℝ) < ν * Fintype.card A / 2 := Nat.lt_ceil.mp hbad
  have hpart := Finset.card_sdiff_add_card_inter R R'
  have hinter := Finset.card_le_card (Finset.inter_subset_right : R ∩ R' ⊆ R')
  have hcardR : (R.card : ℝ) ≤ Zbad.card + R'.card := by
    have hh : R.card ≤ Zbad.card + R'.card := by dsimp [Zbad]; omega
    exact_mod_cast hh
  have hex := hG X hXlo hXhi
  change (X.card : ℝ) + ν * Fintype.card A ≤ (R.card : ℝ) at hex
  change (X.card : ℝ) + (p * ν / 2) * Fintype.card A ≤ (R'.card : ℝ)
  have hpm := mul_le_mul_of_nonneg_right hp1 (mul_pos hν hmpos).le
  nlinarith

noncomputable def Relevant (G : SimpleGraph (A ⊕ B)) [DecidableRel G.Adj]
    (ν τ : ℝ) (X : Finset A) (Z : Finset B) : Prop :=
  τ * Fintype.card A ≤ (X.card : ℝ) ∧
  (X.card : ℝ) ≤ (1 - τ) * Fintype.card A ∧
  Z ⊆ bipartiteRobustNeighbors G ν X ∧ Z.card = ⌈ν * Fintype.card A / 2⌉₊

/-- A relevant pair has a quadratically large set of actual crossing edges. -/
theorem relevant_edges_lower (G : SimpleGraph (A ⊕ B)) [DecidableRel G.Adj]
    (ν τ : ℝ) (hν : 0 ≤ ν) (X : Finset A) (Z : Finset B)
    (hrel : Relevant G ν τ X Z) :
    ν ^ 2 * (Fintype.card A : ℝ) ^ 2 / 2 ≤ (crossingEdges G X Z).card := by
  have hc := crossingEdges_of_robust_neighbors G ν X Z hrel.2.2.1
  have hz : ν * Fintype.card A / 2 ≤ (Z.card : ℝ) := by
    rw [hrel.2.2.2]
    exact Nat.le_ceil _
  have hmul := mul_le_mul_of_nonneg_left hz
    (mul_nonneg hν (Nat.cast_nonneg (Fintype.card A)))
  nlinarith

theorem relevant_pair_failure_probability (G : SimpleGraph (A ⊕ B))
    [DecidableRel G.Adj] (p ν τ : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hν : 0 ≤ ν) (X : Finset A) (Z : Finset B)
    (hrel : Relevant G ν τ X Z) :
    Bernoulli.probability p (fun ω =>
      ((crossingEdges (sampledGraph G ω) X Z).card : ℝ) <
        p * ν * Fintype.card A * Z.card / 2) ≤
      Real.exp (-p * ν ^ 2 * (Fintype.card A : ℝ) ^ 2 / 24) := by
  classical
  have hedge := crossingEdges_of_robust_neighbors G ν X Z hrel.2.2.1
  have hlarge := relevant_edges_lower G ν τ hν X Z hrel
  calc
    _ ≤ Bernoulli.probability p (fun ω =>
        (Bernoulli.retainedCount (crossingEdges G X Z) ω : ℝ) <
          p * (crossingEdges G X Z).card / 2) := by
      apply Bernoulli.probability_mono p hp hp1
      intro ω hω
      rw [sampled_count] at hω
      have hmul := mul_le_mul_of_nonneg_left hedge hp
      nlinarith
    _ ≤ Real.exp (-p * (crossingEdges G X Z).card / 12) :=
      Bernoulli.half_mean_lower_tail p hp hp1 _
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hmul := mul_le_mul_of_nonneg_left hlarge hp
      nlinarith

/-- Failure is witnessed by a relevant pair of actual vertex sets. -/
theorem failure_witness (G : SimpleGraph (A ⊕ B)) [DecidableRel G.Adj]
    (p ν τ : ℝ) (hp1 : p ≤ 1) (hν : 0 < ν)
    (hG : IsBipartiteRobustExpander G ν τ) (ω : A × B → Bool)
    (hfail : ¬ IsBipartiteRobustExpander (sampledGraph G ω) (p * ν / 2) τ) :
    ∃ pair : Finset A × Finset B, Relevant G ν τ pair.1 pair.2 ∧
      ((crossingEdges (sampledGraph G ω) pair.1 pair.2).card : ℝ) <
        p * ν * Fintype.card A * pair.2.card / 2 := by
  classical
  by_contra hnot
  apply hfail
  apply robust_of_pair_counts G (sampledGraph G ω) p ν τ hp1 hν hG
  intro X hXlo hXhi Z hZR hcard
  apply le_of_not_gt
  intro hsmall
  exact hnot ⟨(X, Z), ⟨hXlo, hXhi, hZR, hcard⟩, hsmall⟩

/-- The one-sided exponential estimate gives a slightly stronger failure
bound than the factor-two bound stated in the manuscript. -/
theorem failure_probability (G : SimpleGraph (A ⊕ B)) [DecidableRel G.Adj]
    (p ν τ : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hν : 0 < ν)
    (hbalance : Fintype.card A = Fintype.card B)
    (hG : IsBipartiteRobustExpander G ν τ) :
    Bernoulli.probability p (fun ω =>
      ¬ IsBipartiteRobustExpander (sampledGraph G ω) (p * ν / 2) τ) ≤
      (4 : ℝ) ^ Fintype.card A *
        Real.exp (-p * ν ^ 2 * (Fintype.card A : ℝ) ^ 2 / 24) := by
  classical
  let P := fun (pair : Finset A × Finset B) (ω : A × B → Bool) =>
    Relevant G ν τ pair.1 pair.2 ∧
      ((crossingEdges (sampledGraph G ω) pair.1 pair.2).card : ℝ) <
        p * ν * Fintype.card A * pair.2.card / 2
  have hpair (pair : Finset A × Finset B) : Bernoulli.probability p (P pair) ≤
      Real.exp (-p * ν ^ 2 * (Fintype.card A : ℝ) ^ 2 / 24) := by
    by_cases hrel : Relevant G ν τ pair.1 pair.2
    · calc
        _ ≤ Bernoulli.probability p (fun ω =>
            ((crossingEdges (sampledGraph G ω) pair.1 pair.2).card : ℝ) <
              p * ν * Fintype.card A * pair.2.card / 2) :=
          Bernoulli.probability_mono p hp hp1 (fun _ h => h.2)
        _ ≤ _ := relevant_pair_failure_probability G p ν τ hp hp1 hν.le _ _ hrel
    · simp [P, hrel, Bernoulli.probability, MatchingProbability.probability,
        (Real.exp_pos _).le]
  calc
    _ ≤ Bernoulli.probability p (fun ω =>
        ∃ pair ∈ (univ : Finset (Finset A × Finset B)), P pair ω) := by
      apply Bernoulli.probability_mono p hp hp1
      intro ω hfail
      obtain ⟨pair, hpair⟩ := failure_witness G p ν τ hp1 hν hG ω hfail
      exact ⟨pair, Finset.mem_univ _, hpair⟩
    _ ≤ ∑ pair : Finset A × Finset B, Bernoulli.probability p (P pair) :=
      Bernoulli.probability_exists_le_sum p hp hp1 univ P
    _ ≤ ∑ _pair : Finset A × Finset B,
        Real.exp (-p * ν ^ 2 * (Fintype.card A : ℝ) ^ 2 / 24) :=
      Finset.sum_le_sum (fun pair _ => hpair pair)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
        Fintype.card_finset, ← hbalance, nsmul_eq_mul, Nat.cast_mul, Nat.cast_pow,
        Nat.cast_ofNat]
      rw [← mul_pow]
      norm_num

/-- **Lemma 2.14.** Independent retention with probability `p` preserves
bipartite robust expansion with the stated probability bound. -/
theorem bipartite_random_reserve (G : SimpleGraph (A ⊕ B)) [DecidableRel G.Adj]
    (p ν τ : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hν : 0 < ν)
    (hbalance : Fintype.card A = Fintype.card B)
    (hG : IsBipartiteRobustExpander G ν τ) :
    1 - 2 * (4 : ℝ) ^ Fintype.card A *
        Real.exp (-p * ν ^ 2 * (Fintype.card A : ℝ) ^ 2 / 24) ≤
      Bernoulli.probability p (fun ω =>
        IsBipartiteRobustExpander (sampledGraph G ω) (p * ν / 2) τ) := by
  have hf := failure_probability G p ν τ hp.le hp1 hν hbalance hG
  rw [Bernoulli.probability_compl] at hf
  have hn : 0 ≤ (4 : ℝ) ^ Fintype.card A *
      Real.exp (-p * ν ^ 2 * (Fintype.card A : ℝ) ^ 2 / 24) := by positivity
  nlinarith

end Overfull.RandomReserve
