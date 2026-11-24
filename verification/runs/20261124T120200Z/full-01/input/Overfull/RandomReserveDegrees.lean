import Overfull.RandomReserve
import Overfull.Probability.Concentration
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-!
# Simultaneous degree control for a bipartite reserve

These bounds use the same actual edge sample as the robust-expansion result.
-/

namespace Overfull.RandomReserve

open Finset Classical
open scoped BigOperators

variable {A B : Type*} [Fintype A] [Fintype B]

theorem crossingEdges_singleton_left_card (G : SimpleGraph (A ⊕ B))
    [DecidableRel G.Adj] (a : A) :
    (crossingEdges G {a} univ).card = (rightNeighbors G a).card := by
  classical
  let f : B ↪ A × B := ⟨fun b => (a, b), by intro b b' h; exact congrArg Prod.snd h⟩
  have heq : crossingEdges G {a} univ = (rightNeighbors G a).map f := by
    ext e
    rcases e with ⟨a', b⟩
    simp only [crossingEdges, Finset.mem_filter, Finset.mem_univ, Finset.mem_singleton,
      true_and, Finset.mem_map, rightNeighbors]
    constructor
    · rintro ⟨rfl, hadj⟩
      exact ⟨b, by simpa using hadj, rfl⟩
    · rintro ⟨b', hb', h⟩
      have hfst : a = a' := congrArg Prod.fst h
      have hsnd : b' = b := congrArg Prod.snd h
      subst a'
      subst b'
      exact ⟨rfl, by simpa using hb'⟩
  rw [heq, Finset.card_map]

theorem crossingEdges_singleton_right_card (G : SimpleGraph (A ⊕ B))
    [DecidableRel G.Adj] (b : B) :
    (crossingEdges G univ {b}).card = (leftNeighbors G b).card := by
  classical
  simp [crossingEdges_card]

noncomputable def crossingDegree (G : SimpleGraph (A ⊕ B)) [DecidableRel G.Adj] :
    A ⊕ B → ℕ
  | .inl a => (rightNeighbors G a).card
  | .inr b => (leftNeighbors G b).card

noncomputable def incidentCrossingEdges (G : SimpleGraph (A ⊕ B)) :
    A ⊕ B → Finset (A × B)
  | .inl a => crossingEdges G {a} univ
  | .inr b => crossingEdges G univ {b}

theorem incidentCrossingEdges_card (G : SimpleGraph (A ⊕ B)) [DecidableRel G.Adj]
    (v : A ⊕ B) : (incidentCrossingEdges G v).card = crossingDegree G v := by
  cases v with
  | inl a => exact crossingEdges_singleton_left_card G a
  | inr b => exact crossingEdges_singleton_right_card G b

theorem crossingDegree_le (G : SimpleGraph (A ⊕ B)) [DecidableRel G.Adj]
    (hbalance : Fintype.card A = Fintype.card B) (v : A ⊕ B) :
    crossingDegree G v ≤ Fintype.card A := by
  cases v with
  | inl a => rw [crossingDegree, hbalance]; exact Finset.card_le_univ _
  | inr b => exact Finset.card_le_univ _

theorem sampled_crossingDegree (G : SimpleGraph (A ⊕ B)) [DecidableRel G.Adj]
    (ω : A × B → Bool) (v : A ⊕ B) :
    crossingDegree (sampledGraph G ω) v =
      Bernoulli.retainedCount (incidentCrossingEdges G v) ω := by
  cases v with
  | inl a =>
    rw [crossingDegree, ← crossingEdges_singleton_left_card, sampled_count]
    rfl
  | inr b =>
    rw [crossingDegree, ← crossingEdges_singleton_right_card, sampled_count]
    rfl

theorem degree_failure_probability (G : SimpleGraph (A ⊕ B)) [DecidableRel G.Adj]
    (p ε : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hε : 0 ≤ ε) (hεp : ε ≤ p)
    (hbalance : Fintype.card A = Fintype.card B) (v : A ⊕ B) :
    Bernoulli.probability p (fun ω => ε * Fintype.card A ≤
      |(crossingDegree (sampledGraph G ω) v : ℝ) - p * crossingDegree G v|) ≤
      2 * Real.exp (-ε ^ 2 * Fintype.card A / (3 * p)) := by
  have hcard : ((incidentCrossingEdges G v).card : ℝ) ≤ Fintype.card A := by
    rw [incidentCrossingEdges_card]
    exact_mod_cast crossingDegree_le G hbalance v
  have h := Bernoulli.additive_chernoff p ε (Fintype.card A : ℝ)
    hp hp1 hε hεp (incidentCrossingEdges G v) hcard
  simpa only [incidentCrossingEdges_card, ← sampled_crossingDegree] using h

/-- All vertex degrees are controlled in the same sample, with no
independence assumption between the vertex failure events. -/
theorem some_degree_failure_probability (G : SimpleGraph (A ⊕ B))
    [DecidableRel G.Adj] (p ε : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hε : 0 ≤ ε) (hεp : ε ≤ p)
    (hbalance : Fintype.card A = Fintype.card B) :
    Bernoulli.probability p (fun ω => ∃ v : A ⊕ B, ε * Fintype.card A ≤
      |(crossingDegree (sampledGraph G ω) v : ℝ) - p * crossingDegree G v|) ≤
      4 * Fintype.card A * Real.exp (-ε ^ 2 * Fintype.card A / (3 * p)) := by
  classical
  let P := fun (v : A ⊕ B) (ω : A × B → Bool) => ε * Fintype.card A ≤
    |(crossingDegree (sampledGraph G ω) v : ℝ) - p * crossingDegree G v|
  calc
    _ = Bernoulli.probability p (fun ω => ∃ v ∈ (univ : Finset (A ⊕ B)), P v ω) := by
      simp [P]
    _ ≤ ∑ v : A ⊕ B, Bernoulli.probability p (P v) :=
      Bernoulli.probability_exists_le_sum p hp.le hp1 univ P
    _ ≤ ∑ _v : A ⊕ B, 2 * Real.exp (-ε ^ 2 * Fintype.card A / (3 * p)) :=
      Finset.sum_le_sum (fun v _ => degree_failure_probability G p ε hp hp1 hε hεp hbalance v)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_sum, ← hbalance,
        nsmul_eq_mul, Nat.cast_add]
      ring

omit [Fintype A] [Fintype B] in
theorem sampledGraph_bipartite (G : SimpleGraph (A ⊕ B)) (ω : A × B → Bool) :
    (sampledGraph G ω).IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr) := by
  constructor
  · rw [Set.disjoint_left]
    rintro _ ⟨a, rfl⟩ ⟨b, h⟩
    cases h
  · rintro (a | b) (a' | b') h <;> simp [sampledGraph] at h ⊢

/-- In the specified bipartition, crossing degrees are ordinary graph degrees. -/
theorem crossingDegree_eq_degree (G : SimpleGraph (A ⊕ B)) [DecidableRel G.Adj]
    (hbip : G.IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr))
    (v : A ⊕ B) : crossingDegree G v = G.degree v := by
  classical
  have hleft : ∀ a a' : A, ¬ G.Adj (.inl a) (.inl a') := by
    intro a a' h
    simpa using hbip.mem_of_adj h
  have hright : ∀ b b' : B, ¬ G.Adj (.inr b) (.inr b') := by
    intro b b' h
    simpa using hbip.mem_of_adj h
  cases v with
  | inl a =>
    have himage : (rightNeighbors G a).image Sum.inr = G.neighborFinset (.inl a) := by
      ext v
      cases v with
      | inl a' => simp [rightNeighbors, hleft a a']
      | inr b => simp [rightNeighbors]
    rw [crossingDegree, ← SimpleGraph.card_neighborFinset_eq_degree, ← himage,
      Finset.card_image_of_injective _ Sum.inr_injective]
  | inr b =>
    have himage : (leftNeighbors G b).image Sum.inl = G.neighborFinset (.inr b) := by
      ext v
      cases v with
      | inl a => simp [leftNeighbors, G.adj_comm]
      | inr b' => simp [leftNeighbors, hright b b']
    rw [crossingDegree, ← SimpleGraph.card_neighborFinset_eq_degree, ← himage,
      Finset.card_image_of_injective _ Sum.inl_injective]

/-- A uniform elementary estimate used for simultaneous sampling errors. -/
theorem sampling_error_lt_one (c d : ℝ) (hd : 0 < d)
    (m : ℕ) (hm : 1 ≤ m) (hcm : 6 ≤ c * m) (hdm : 64 ≤ d ^ 2 * m) :
    (4 : ℝ) ^ m * Real.exp (-c * (m : ℝ) ^ 2) +
      4 * m * Real.exp (-d * m) < 1 := by
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hfour : (4 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
  have hpower : (4 : ℝ) ^ m ≤ Real.exp (3 * m) := by
    calc
      _ ≤ Real.exp 3 ^ m := pow_le_pow_left₀ (by norm_num) hfour m
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hfirst : (4 : ℝ) ^ m * Real.exp (-c * (m : ℝ) ^ 2) ≤ 1 / 4 := by
    have harg : 3 * (m : ℝ) + -c * (m : ℝ) ^ 2 ≤ -3 * m := by
      have hh := mul_le_mul_of_nonneg_right hcm hm0
      nlinarith
    have hlow : (4 : ℝ) ≤ Real.exp (3 * m) := by
      linarith [Real.add_one_le_exp (3 * (m : ℝ))]
    have hlow' := mul_le_mul_of_nonneg_right hlow (Real.exp_pos (-3 * (m : ℝ))).le
    have hex : Real.exp (3 * (m : ℝ)) * Real.exp (-3 * m) = 1 := by
      rw [← Real.exp_add, show 3 * (m : ℝ) + -3 * m = 0 by ring, Real.exp_zero]
    rw [hex] at hlow'
    calc
      _ ≤ Real.exp (3 * m) * Real.exp (-c * (m : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right hpower (Real.exp_pos _).le
      _ = Real.exp (3 * m + -c * (m : ℝ) ^ 2) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (-3 * m) := Real.exp_le_exp.mpr harg
      _ ≤ 1 / 4 := by linarith
  have hsecond : 4 * (m : ℝ) * Real.exp (-d * m) ≤ 1 / 4 := by
    have hhalf : d * (m : ℝ) / 2 ≤ Real.exp (d * m / 2) := by
      linarith [Real.add_one_le_exp (d * (m : ℝ) / 2)]
    have hsq := pow_le_pow_left₀ (show 0 ≤ d * (m : ℝ) / 2 by positivity) hhalf 2
    have heq : Real.exp (d * (m : ℝ) / 2) ^ 2 = Real.exp (d * m) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [heq] at hsq
    have hdm' := mul_le_mul_of_nonneg_right hdm hm0
    have hlow : 16 * (m : ℝ) ≤ Real.exp (d * m) := by nlinarith
    have hlow' := mul_le_mul_of_nonneg_right hlow (Real.exp_pos (-d * (m : ℝ))).le
    have hex : Real.exp (d * (m : ℝ)) * Real.exp (-d * m) = 1 := by
      rw [← Real.exp_add, show d * (m : ℝ) + -d * m = 0 by ring, Real.exp_zero]
    rw [hex] at hlow'
    nlinarith
  linarith

/-- A uniform order threshold gives one actual sample with robust expansion
and all degree estimates simultaneously. The threshold is chosen before
the vertex types or graph. -/
theorem exists_reserve_with_degree_control (p ν ε : ℝ)
    (hp : 0 < p) (hp1 : p ≤ 1) (hν : 0 < ν) (hε : 0 < ε) (hεp : ε ≤ p) :
    ∃ m₀ : ℕ, ∀ (A B : Type*) [Fintype A] [Fintype B]
      (G : SimpleGraph (A ⊕ B)) [DecidableRel G.Adj] (τ : ℝ),
      Fintype.card A = Fintype.card B → m₀ ≤ Fintype.card A →
      IsBipartiteRobustExpander G ν τ →
      ∃ ω : A × B → Bool,
        IsBipartiteRobustExpander (sampledGraph G ω) (p * ν / 2) τ ∧
        ∀ v : A ⊕ B, |(crossingDegree (sampledGraph G ω) v : ℝ) -
          p * crossingDegree G v| < ε * Fintype.card A := by
  classical
  let c := p * ν ^ 2 / 24
  let d := ε ^ 2 / (3 * p)
  have hc : 0 < c := by dsimp [c]; positivity
  have hd : 0 < d := by dsimp [d]; positivity
  obtain ⟨m₀, hm₀⟩ := exists_nat_gt (max (1 : ℝ) (max (6 / c) (64 / d ^ 2)))
  refine ⟨m₀, ?_⟩
  intro A B _ _ G _ τ hbalance hm hG
  have hmR : max (1 : ℝ) (max (6 / c) (64 / d ^ 2)) < Fintype.card A :=
    hm₀.trans_le (by exact_mod_cast hm)
  have hm1 : 1 ≤ Fintype.card A := by
    have hh : (1 : ℝ) < Fintype.card A := (le_max_left _ _).trans_lt hmR
    exact_mod_cast hh.le
  have hcm : 6 ≤ c * Fintype.card A := by
    have hh : 6 / c < Fintype.card A :=
      (le_trans (le_max_left _ _) (le_max_right _ _)).trans_lt hmR
    have h := (div_lt_iff₀ hc).mp hh
    nlinarith
  have hdm : 64 ≤ d ^ 2 * Fintype.card A := by
    have hh : 64 / d ^ 2 < Fintype.card A :=
      (le_trans (le_max_right _ _) (le_max_right _ _)).trans_lt hmR
    have h := (div_lt_iff₀ (sq_pos_of_pos hd)).mp hh
    nlinarith
  have herr := sampling_error_lt_one c d hd (Fintype.card A) hm1 hcm hdm
  let P₁ := fun (ω : A × B → Bool) =>
    ¬ IsBipartiteRobustExpander (sampledGraph G ω) (p * ν / 2) τ
  let P₂ := fun (ω : A × B → Bool) => ∃ v : A ⊕ B, ε * Fintype.card A ≤
    |(crossingDegree (sampledGraph G ω) v : ℝ) - p * crossingDegree G v|
  let P := fun ω => P₁ ω ∨ P₂ ω
  have hbad : Bernoulli.probability p P < 1 := by
    have hu : Bernoulli.probability p P ≤
        Bernoulli.probability p P₁ + Bernoulli.probability p P₂ :=
      Bernoulli.probability_union_le p hp.le hp1 P₁ P₂
    have hrob : Bernoulli.probability p P₁ ≤ (4 : ℝ) ^ Fintype.card A *
        Real.exp (-p * ν ^ 2 * (Fintype.card A : ℝ) ^ 2 / 24) :=
      failure_probability G p ν τ hp.le hp1 hν hbalance hG
    have hdeg : Bernoulli.probability p P₂ ≤ 4 * Fintype.card A *
        Real.exp (-ε ^ 2 * Fintype.card A / (3 * p)) :=
      some_degree_failure_probability G p ε hp hp1 hε.le hεp hbalance
    have harg₁ : -p * ν ^ 2 * (Fintype.card A : ℝ) ^ 2 / 24 =
        -c * (Fintype.card A : ℝ) ^ 2 := by dsimp [c]; ring
    have harg₂ : -ε ^ 2 * (Fintype.card A : ℝ) / (3 * p) =
        -d * Fintype.card A := by dsimp [d]; ring
    rw [harg₁] at hrob
    rw [harg₂] at hdeg
    linarith
  obtain ⟨ω, hω⟩ := Bernoulli.exists_not_of_probability_lt_one p P hbad
  refine ⟨ω, (not_or.mp hω).1 |> not_not.mp, ?_⟩
  intro v
  exact lt_of_not_ge (fun hv => (not_or.mp hω).2 ⟨v, hv⟩)

/-- The reserve required in Step 1 of adaptive bipartite packing, with
actual graph degrees, containment and a uniform order threshold. -/
theorem exists_almost_regular_reserve (p ν ε : ℝ)
    (hp : 0 < p) (hp1 : p ≤ 1) (hν : 0 < ν) (hε : 0 < ε) (hεp : ε ≤ p) :
    ∃ m₀ : ℕ, ∀ (A B : Type*) [Fintype A] [Fintype B]
      (G : SimpleGraph (A ⊕ B)) [DecidableRel G.Adj] (τ Δ : ℝ),
      G.IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr) →
      Fintype.card A = Fintype.card B → m₀ ≤ Fintype.card A →
      IsBipartiteRobustExpander G ν τ →
      (∀ v, |(G.degree v : ℝ) - Δ| ≤ ε * Fintype.card A) →
      ∃ ω : A × B → Bool,
        sampledGraph G ω ≤ G ∧
        (sampledGraph G ω).IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr) ∧
        IsBipartiteRobustExpander (sampledGraph G ω) (p * ν / 2) τ ∧
        ∀ v, |((sampledGraph G ω).degree v : ℝ) - p * Δ| <
          2 * ε * Fintype.card A := by
  classical
  obtain ⟨m₀, hm₀⟩ := exists_reserve_with_degree_control p ν ε hp hp1 hν hε hεp
  refine ⟨m₀, ?_⟩
  intro A B _ _ G _ τ Δ hbip hbalance hm hG hdegrees
  obtain ⟨ω, hrob, hdeg⟩ := hm₀ A B G τ hbalance hm hG
  have hbipR := sampledGraph_bipartite G ω
  refine ⟨ω, sampledGraph_le G ω, hbipR, hrob, ?_⟩
  intro v
  have hsample := hdeg v
  rw [crossingDegree_eq_degree _ hbipR, crossingDegree_eq_degree _ hbip] at hsample
  have hnominal : |p * (G.degree v : ℝ) - p * Δ| ≤ ε * Fintype.card A := by
    rw [← mul_sub, abs_mul, abs_of_pos hp]
    exact (mul_le_mul_of_nonneg_left (hdegrees v) hp.le).trans
      (by nlinarith [mul_nonneg hε.le (Nat.cast_nonneg (Fintype.card A))])
  have htriangle := abs_sub_le ((sampledGraph G ω).degree v : ℝ) (p * G.degree v) (p * Δ)
  linarith

end Overfull.RandomReserve
