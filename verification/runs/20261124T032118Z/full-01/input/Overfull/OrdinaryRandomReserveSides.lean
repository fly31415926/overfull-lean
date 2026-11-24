import Overfull.OrdinaryRandomReserveDegrees

/-!
# One ordinary robust reserve with two-sided degree control

Each side count is the number of retained actual unordered edges in a fixed
incident-edge set. A union bound over both sets and all vertices is combined
with the existing ordinary robust-expansion failure estimate. The order
threshold precedes the graph and the two sets; they need not form a partition.
-/

namespace Overfull.OrdinaryRandomReserve

open Finset Classical
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Actual unordered edges from a vertex to a specified vertex set. -/
noncomputable def incidentEdgesTo (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (S : Finset V) : Finset (Sym2 V) :=
  (G.neighborFinset v ∩ S).image (fun w => s(v, w))

theorem incidentEdgesTo_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (S : Finset V) :
    (incidentEdgesTo G v S).card = (G.neighborFinset v ∩ S).card := by
  unfold incidentEdgesTo
  apply Finset.card_image_of_injective
  intro w u h
  rcases Sym2.eq_iff.mp h with ⟨_, hwu⟩ | ⟨hvu, hwv⟩
  · exact hwu
  · exact hwv.trans hvu

theorem sampled_neighbors_inter (G : SimpleGraph V) [DecidableRel G.Adj]
    (ω : Sym2 V → Bool) (v : V) (S : Finset V) :
    (sampledGraph G ω).neighborFinset v ∩ S =
      (G.neighborFinset v ∩ S).filter (fun w => ω s(v, w) = true) := by
  rw [sampled_neighbors]
  ext w
  simp only [Finset.mem_inter, Finset.mem_filter]
  tauto

theorem incidentEdgesTo_sampled (G : SimpleGraph V) [DecidableRel G.Adj]
    (ω : Sym2 V → Bool) (v : V) (S : Finset V) :
    incidentEdgesTo (sampledGraph G ω) v S =
      (incidentEdgesTo G v S).filter (fun e => ω e = true) := by
  unfold incidentEdgesTo
  rw [sampled_neighbors_inter, Finset.filter_image]

theorem sampled_side_count (G : SimpleGraph V) [DecidableRel G.Adj]
    (ω : Sym2 V → Bool) (v : V) (S : Finset V) :
    ((sampledGraph G ω).neighborFinset v ∩ S).card =
      Bernoulli.retainedCount (incidentEdgesTo G v S) ω := by
  rw [← incidentEdgesTo_card, incidentEdgesTo_sampled]
  rfl

/-- A single side count has the existing additive Chernoff bound. -/
theorem side_degree_failure_probability (G : SimpleGraph V) [DecidableRel G.Adj]
    (p ε : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hε : 0 ≤ ε) (hεp : ε ≤ p)
    (S : Finset V) (v : V) :
    Bernoulli.probability p (fun ω => ε * Fintype.card V ≤
      |(((sampledGraph G ω).neighborFinset v ∩ S).card : ℝ) -
        p * (G.neighborFinset v ∩ S).card|) ≤
      2 * Real.exp (-ε ^ 2 * Fintype.card V / (3 * p)) := by
  have hcard : ((incidentEdgesTo G v S).card : ℝ) ≤ Fintype.card V := by
    rw [incidentEdgesTo_card]
    exact_mod_cast Finset.card_le_univ (G.neighborFinset v ∩ S)
  have h := Bernoulli.additive_chernoff p ε (Fintype.card V : ℝ)
    hp hp1 hε hεp (incidentEdgesTo G v S) hcard
  simpa only [incidentEdgesTo_card, ← sampled_side_count] using h

theorem some_side_degree_failure_probability (G : SimpleGraph V) [DecidableRel G.Adj]
    (p ε : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hε : 0 ≤ ε) (hεp : ε ≤ p)
    (S : Finset V) :
    Bernoulli.probability p (fun ω => ∃ v : V, ε * Fintype.card V ≤
      |(((sampledGraph G ω).neighborFinset v ∩ S).card : ℝ) -
        p * (G.neighborFinset v ∩ S).card|) ≤
      2 * Fintype.card V * Real.exp (-ε ^ 2 * Fintype.card V / (3 * p)) := by
  let P := fun (v : V) (ω : Sym2 V → Bool) => ε * Fintype.card V ≤
    |(((sampledGraph G ω).neighborFinset v ∩ S).card : ℝ) -
      p * (G.neighborFinset v ∩ S).card|
  calc
    _ = Bernoulli.probability p (fun ω => ∃ v ∈ (univ : Finset V), P v ω) := by
      simp [P]
    _ ≤ ∑ v : V, Bernoulli.probability p (P v) :=
      Bernoulli.probability_exists_le_sum p hp.le hp1 univ P
    _ ≤ ∑ _v : V, 2 * Real.exp (-ε ^ 2 * Fintype.card V / (3 * p)) :=
      Finset.sum_le_sum (fun v _ => side_degree_failure_probability G p ε hp hp1 hε hεp S v)
    _ = _ := by simp; ring

/-- The two families of failure events need not be independent. -/
theorem two_side_degree_failure_probability (G : SimpleGraph V) [DecidableRel G.Adj]
    (p ε : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hε : 0 ≤ ε) (hεp : ε ≤ p)
    (A B : Finset V) :
    Bernoulli.probability p (fun ω =>
      (∃ v : V, ε * Fintype.card V ≤
        |(((sampledGraph G ω).neighborFinset v ∩ A).card : ℝ) -
          p * (G.neighborFinset v ∩ A).card|) ∨
      (∃ v : V, ε * Fintype.card V ≤
        |(((sampledGraph G ω).neighborFinset v ∩ B).card : ℝ) -
          p * (G.neighborFinset v ∩ B).card|)) ≤
      4 * Fintype.card V * Real.exp (-ε ^ 2 * Fintype.card V / (3 * p)) := by
  have hu := Bernoulli.probability_union_le p hp.le hp1
    (fun ω => ∃ v : V, ε * Fintype.card V ≤
      |(((sampledGraph G ω).neighborFinset v ∩ A).card : ℝ) -
        p * (G.neighborFinset v ∩ A).card|)
    (fun ω => ∃ v : V, ε * Fintype.card V ≤
      |(((sampledGraph G ω).neighborFinset v ∩ B).card : ℝ) -
        p * (G.neighborFinset v ∩ B).card|)
  have hA := some_side_degree_failure_probability G p ε hp hp1 hε hεp A
  have hB := some_side_degree_failure_probability G p ε hp hp1 hε hεp B
  linarith

/-- One actual ordinary robust sample controls all degrees into both prescribed
sets. The threshold precedes the graph, its vertex type, and the two sets. -/
theorem exists_reserve_with_side_degree_control (p ν ε : ℝ)
    (hp : 0 < p) (hp1 : p ≤ 1) (hν : 0 < ν) (hε : 0 < ε) (hεp : ε ≤ p) :
    ∃ n₀ : ℕ, ∀ (V : Type*) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (τ : ℝ) (A B : Finset V),
      n₀ ≤ Fintype.card V → IsRobustExpander G ν τ →
      ∃ ω : Sym2 V → Bool,
        sampledGraph G ω ≤ G ∧
        IsRobustExpander (sampledGraph G ω) (p * ν / 4) τ ∧
        ∀ v : V,
          |(((sampledGraph G ω).neighborFinset v ∩ A).card : ℝ) -
            p * (G.neighborFinset v ∩ A).card| < ε * Fintype.card V ∧
          |(((sampledGraph G ω).neighborFinset v ∩ B).card : ℝ) -
            p * (G.neighborFinset v ∩ B).card| < ε * Fintype.card V := by
  let c := p * ν ^ 2 / 48
  let d := ε ^ 2 / (3 * p)
  have hc : 0 < c := by dsimp [c]; positivity
  have hd : 0 < d := by dsimp [d]; positivity
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (max (1 : ℝ) (max (6 / c) (64 / d ^ 2)))
  refine ⟨n₀, ?_⟩
  intro V _ _ G _ τ A B hn hG
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
  let P₂ := fun (ω : Sym2 V → Bool) =>
    (∃ v : V, ε * Fintype.card V ≤
      |(((sampledGraph G ω).neighborFinset v ∩ A).card : ℝ) -
        p * (G.neighborFinset v ∩ A).card|) ∨
    (∃ v : V, ε * Fintype.card V ≤
      |(((sampledGraph G ω).neighborFinset v ∩ B).card : ℝ) -
        p * (G.neighborFinset v ∩ B).card|)
  let P := fun ω => P₁ ω ∨ P₂ ω
  have hbad : Bernoulli.probability p P < 1 := by
    have hu : Bernoulli.probability p P ≤
        Bernoulli.probability p P₁ + Bernoulli.probability p P₂ :=
      Bernoulli.probability_union_le p hp.le hp1 P₁ P₂
    have hrob : Bernoulli.probability p P₁ ≤ (4 : ℝ) ^ Fintype.card V *
        Real.exp (-p * ν ^ 2 * (Fintype.card V : ℝ) ^ 2 / 48) :=
      failure_probability G p ν τ hp.le hp1 hν hG
    have hside : Bernoulli.probability p P₂ ≤ 4 * Fintype.card V *
        Real.exp (-ε ^ 2 * Fintype.card V / (3 * p)) :=
      two_side_degree_failure_probability G p ε hp hp1 hε.le hεp A B
    have harg₁ : -p * ν ^ 2 * (Fintype.card V : ℝ) ^ 2 / 48 =
        -c * (Fintype.card V : ℝ) ^ 2 := by dsimp [c]; ring
    have harg₂ : -ε ^ 2 * (Fintype.card V : ℝ) / (3 * p) =
        -d * Fintype.card V := by dsimp [d]; ring
    rw [harg₁] at hrob
    rw [harg₂] at hside
    linarith
  obtain ⟨ω, hω⟩ := Bernoulli.exists_not_of_probability_lt_one p P hbad
  refine ⟨ω, sampledGraph_le G ω, (not_or.mp hω).1 |> not_not.mp, ?_⟩
  intro v
  constructor
  · exact lt_of_not_ge (fun hv => (not_or.mp hω).2 (Or.inl ⟨v, hv⟩))
  · exact lt_of_not_ge (fun hv => (not_or.mp hω).2 (Or.inr ⟨v, hv⟩))

/-- Transfer the sampling error to any prescribed original side-degree target. -/
theorem side_degree_deviation_from_target (G : SimpleGraph V) [DecidableRel G.Adj]
    (ω : Sym2 V → Bool) (v : V) (S : Finset V) (p ε δ x : ℝ) (hp : 0 ≤ p)
    (hsample : |(((sampledGraph G ω).neighborFinset v ∩ S).card : ℝ) -
      p * (G.neighborFinset v ∩ S).card| < ε * Fintype.card V)
    (horiginal : |((G.neighborFinset v ∩ S).card : ℝ) - x| ≤
      δ * Fintype.card V) :
    |(((sampledGraph G ω).neighborFinset v ∩ S).card : ℝ) - p * x| <
      (ε + p * δ) * Fintype.card V := by
  have hscaled : |p * ((G.neighborFinset v ∩ S).card : ℝ) - p * x| ≤
      p * (δ * Fintype.card V) := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hp]
    exact mul_le_mul_of_nonneg_left horiginal hp
  calc
    _ ≤ |(((sampledGraph G ω).neighborFinset v ∩ S).card : ℝ) -
          p * (G.neighborFinset v ∩ S).card| +
        |p * ((G.neighborFinset v ∩ S).card : ℝ) - p * x| :=
      abs_sub_le _ _ _
    _ < ε * Fintype.card V + p * (δ * Fintype.card V) :=
      add_lt_add_of_lt_of_le hsample hscaled
    _ = _ := by ring

/-- A balanced original pair of side degrees gives one robust reserve with
both side degrees close to the target `p * k / 2`. -/
theorem exists_reserve_with_balanced_side_degrees (p ν ε : ℝ)
    (hp : 0 < p) (hp1 : p ≤ 1) (hν : 0 < ν) (hε : 0 < ε) (hεp : ε ≤ p) :
    ∃ n₀ : ℕ, ∀ (V : Type*) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (τ : ℝ) (A B : Finset V) (δ k : ℝ),
      n₀ ≤ Fintype.card V → IsRobustExpander G ν τ →
      (∀ v : V,
        |((G.neighborFinset v ∩ A).card : ℝ) - k / 2| ≤ δ * Fintype.card V ∧
        |((G.neighborFinset v ∩ B).card : ℝ) - k / 2| ≤ δ * Fintype.card V) →
      ∃ ω : Sym2 V → Bool,
        sampledGraph G ω ≤ G ∧
        IsRobustExpander (sampledGraph G ω) (p * ν / 4) τ ∧
        ∀ v : V,
          |(((sampledGraph G ω).neighborFinset v ∩ A).card : ℝ) - p * k / 2| <
            (ε + p * δ) * Fintype.card V ∧
          |(((sampledGraph G ω).neighborFinset v ∩ B).card : ℝ) - p * k / 2| <
            (ε + p * δ) * Fintype.card V := by
  obtain ⟨n₀, hn₀⟩ := exists_reserve_with_side_degree_control p ν ε hp hp1 hν hε hεp
  refine ⟨n₀, ?_⟩
  intro V _ _ G _ τ A B δ k hn hG hdegrees
  obtain ⟨ω, hsub, hrob, hside⟩ := hn₀ V G τ A B hn hG
  refine ⟨ω, hsub, hrob, ?_⟩
  intro v
  constructor
  · simpa only [mul_div_assoc] using side_degree_deviation_from_target G ω v A
      p ε δ (k / 2) hp.le (hside v).1 (hdegrees v).1
  · simpa only [mul_div_assoc] using side_degree_deviation_from_target G ω v B
      p ε δ (k / 2) hp.le (hside v).2 (hdegrees v).2

/-- A vertex partition splits every actual degree into its two side counts. -/
theorem degree_eq_side_counts (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (hAB : Disjoint A B) (hcover : A ∪ B = univ) (v : V) :
    G.degree v = (G.neighborFinset v ∩ A).card + (G.neighborFinset v ∩ B).card := by
  have hdisj : Disjoint (G.neighborFinset v ∩ A) (G.neighborFinset v ∩ B) :=
    hAB.mono Finset.inter_subset_right Finset.inter_subset_right
  have hunion : (G.neighborFinset v ∩ A) ∪ (G.neighborFinset v ∩ B) =
      G.neighborFinset v := by
    rw [← Finset.inter_union_distrib_left, hcover, Finset.inter_univ]
  change (G.neighborFinset v).card = _
  exact (congrArg Finset.card hunion).symm.trans (Finset.card_union_of_disjoint hdisj)

/-- For a vertex partition, the two side errors add to a total-degree error. -/
theorem degree_deviation_of_side_control (G : SimpleGraph V) [DecidableRel G.Adj]
    (ω : Sym2 V → Bool) (A B : Finset V) (hAB : Disjoint A B)
    (hcover : A ∪ B = univ) (p ε : ℝ) (v : V)
    (hA : |(((sampledGraph G ω).neighborFinset v ∩ A).card : ℝ) -
      p * (G.neighborFinset v ∩ A).card| < ε * Fintype.card V)
    (hB : |(((sampledGraph G ω).neighborFinset v ∩ B).card : ℝ) -
      p * (G.neighborFinset v ∩ B).card| < ε * Fintype.card V) :
    |((sampledGraph G ω).degree v : ℝ) - p * G.degree v| <
      2 * ε * Fintype.card V := by
  rw [degree_eq_side_counts (sampledGraph G ω) A B hAB hcover,
    degree_eq_side_counts G A B hAB hcover, Nat.cast_add, Nat.cast_add]
  have hsplit :
      (((sampledGraph G ω).neighborFinset v ∩ A).card : ℝ) +
          ((sampledGraph G ω).neighborFinset v ∩ B).card -
          p * ((G.neighborFinset v ∩ A).card + (G.neighborFinset v ∩ B).card) =
        ((((sampledGraph G ω).neighborFinset v ∩ A).card : ℝ) -
          p * (G.neighborFinset v ∩ A).card) +
        ((((sampledGraph G ω).neighborFinset v ∩ B).card : ℝ) -
          p * (G.neighborFinset v ∩ B).card) := by ring
  rw [hsplit]
  exact (abs_add_le _ _).trans_lt ((add_lt_add hA hB).trans_eq (by ring))

end Overfull.OrdinaryRandomReserve
