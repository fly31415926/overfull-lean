import Overfull.RobustExpansion
import Overfull.Probability.Bernoulli

/-!
# Random reserves in ordinary robust expanders

Each unordered edge is sampled once. For two possibly overlapping vertex
sets, their ordered incidences count any unordered edge at most twice.
This gives the concentration estimate without assuming independence of
the two orientations of an edge.
-/

namespace Overfull.OrdinaryRandomReserve

open Finset Classical
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

def sampledGraph (G : SimpleGraph V) (ω : Sym2 V → Bool) : SimpleGraph V where
  Adj v w := G.Adj v w ∧ ω s(v, w) = true
  symm := by
    intro v w h
    refine ⟨h.1.symm, ?_⟩
    rw [Sym2.eq_swap]
    exact h.2
  loopless := by intro v h; exact G.loopless v h.1

instance sampledGraph_decidable (G : SimpleGraph V) [DecidableRel G.Adj]
    (ω : Sym2 V → Bool) : DecidableRel (sampledGraph G ω).Adj := by
  intro v w
  change Decidable (G.Adj v w ∧ ω s(v, w) = true)
  infer_instance

omit [Fintype V] [DecidableEq V] in
theorem sampledGraph_le (G : SimpleGraph V) (ω : Sym2 V → Bool) :
    sampledGraph G ω ≤ G := fun _ _ h => h.1

noncomputable def orderedEdges (G : SimpleGraph V) (S Z : Finset V) : Finset (V × V) :=
  univ.filter (fun e => e.1 ∈ S ∧ e.2 ∈ Z ∧ G.Adj e.1 e.2)

noncomputable def crossingEdges (G : SimpleGraph V) (S Z : Finset V) : Finset (Sym2 V) :=
  (orderedEdges G S Z).image (fun e => s(e.1, e.2))

theorem orderedEdges_card (G : SimpleGraph V) [DecidableRel G.Adj] (S Z : Finset V) :
    (orderedEdges G S Z).card = ∑ z ∈ Z, (G.neighborFinset z ∩ S).card := by
  classical
  calc
    _ = ∑ z : V, ∑ v : V, if v ∈ S ∧ z ∈ Z ∧ G.Adj v z then 1 else 0 := by
      simp only [orderedEdges, Finset.card_eq_sum_ones, Finset.sum_filter]
      rw [Fintype.sum_prod_type_right]
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro v _
      by_cases h : v ∈ S ∧ z ∈ Z ∧ G.Adj v z <;> simp [h]
    _ = ∑ z : V, if z ∈ Z then (G.neighborFinset z ∩ S).card else 0 := by
      apply Finset.sum_congr rfl
      intro z _
      by_cases hz : z ∈ Z
      · simp only [hz, true_and, if_true]
        rw [Finset.sum_boole]
        simp only [Nat.cast_id]
        apply congrArg Finset.card
        ext v
        simp [G.adj_comm, and_comm]
      · simp [hz]
    _ = _ := by rw [← Finset.sum_filter]; simp

theorem crossingEdges_card_le (G : SimpleGraph V) (S Z : Finset V) :
    (crossingEdges G S Z).card ≤ (orderedEdges G S Z).card :=
  Finset.card_image_le

/-- Overlap can count an unordered edge twice, but never more than twice. -/
theorem orderedEdges_card_le_twice (G : SimpleGraph V) (S Z : Finset V) :
    (orderedEdges G S Z).card ≤ 2 * (crossingEdges G S Z).card := by
  classical
  have hcount : (orderedEdges G S Z).card =
      ∑ e ∈ crossingEdges G S Z,
        ((orderedEdges G S Z).filter (fun a => s(a.1, a.2) = e)).card :=
    Finset.card_eq_sum_card_fiberwise (fun _ h => Finset.mem_image_of_mem _ h)
  rw [hcount]
  calc
    _ ≤ ∑ _e ∈ crossingEdges G S Z, 2 := by
      apply Finset.sum_le_sum
      intro e _
      obtain ⟨v, w⟩ := e
      have hsub : (orderedEdges G S Z).filter (fun a => s(a.1, a.2) = s(v, w)) ⊆
          {(v, w), (w, v)} := by
        intro a ha
        have he := (Finset.mem_filter.mp ha).2
        rcases Sym2.eq_iff.mp he with ⟨hv, hw⟩ | ⟨hw, hv⟩
        · have : a = (v, w) := Prod.ext hv hw
          simp [this]
        · have : a = (w, v) := Prod.ext hw hv
          simp [this]
      exact (Finset.card_le_card hsub).trans Finset.card_le_two
    _ = _ := by simp [Nat.mul_comm]

theorem crossingEdges_sampled (G : SimpleGraph V) (S Z : Finset V) (ω : Sym2 V → Bool) :
    crossingEdges (sampledGraph G ω) S Z =
      (crossingEdges G S Z).filter (fun e => ω e = true) := by
  classical
  ext e
  simp only [crossingEdges, Finset.mem_image, orderedEdges, Finset.mem_filter,
    Finset.mem_univ, true_and, sampledGraph]
  constructor
  · rintro ⟨a, ⟨haS, haZ, hadj, hω⟩, rfl⟩
    exact ⟨⟨a, ⟨haS, haZ, hadj⟩, rfl⟩, hω⟩
  · rintro ⟨⟨a, ⟨haS, haZ, hadj⟩, rfl⟩, hω⟩
    exact ⟨a, ⟨haS, haZ, hadj, hω⟩, rfl⟩

theorem sampled_count (G : SimpleGraph V) (S Z : Finset V) (ω : Sym2 V → Bool) :
    (crossingEdges (sampledGraph G ω) S Z).card =
      Bernoulli.retainedCount (crossingEdges G S Z) ω := by
  rw [crossingEdges_sampled]
  rfl

theorem orderedEdges_card_real (G : SimpleGraph V) [DecidableRel G.Adj]
    (S Z : Finset V) : ((orderedEdges G S Z).card : ℝ) =
      ∑ z ∈ Z, ((G.neighborFinset z ∩ S).card : ℝ) := by
  exact_mod_cast orderedEdges_card G S Z

theorem crossingEdges_of_robust_neighbors (G : SimpleGraph V) [DecidableRel G.Adj]
    (ν : ℝ) (S Z : Finset V) (hZ : Z ⊆ robustNeighbors G ν S) :
    ν * Fintype.card V * Z.card / 2 ≤ ((crossingEdges G S Z).card : ℝ) := by
  have hlower : ν * Fintype.card V * Z.card ≤ ((orderedEdges G S Z).card : ℝ) := by
    rw [orderedEdges_card_real]
    calc
      _ = ∑ _z ∈ Z, ν * Fintype.card V := by simp; ring
      _ ≤ _ := Finset.sum_le_sum (fun z hz => (mem_robustNeighbors G ν S z).mp (hZ hz))
  have htwo : ((orderedEdges G S Z).card : ℝ) ≤ 2 * (crossingEdges G S Z).card := by
    exact_mod_cast orderedEdges_card_le_twice G S Z
  linarith

/-- Enough sampled unordered edges between each relevant pair of sets
implies robust expansion, even if those sets overlap. -/
theorem robust_of_pair_counts (G H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (p ν τ : ℝ) (hp1 : p ≤ 1) (hν : 0 < ν)
    (hG : IsRobustExpander G ν τ)
    (hpairs : ∀ S : Finset V,
      τ * Fintype.card V ≤ (S.card : ℝ) →
      (S.card : ℝ) ≤ (1 - τ) * Fintype.card V →
      ∀ Z : Finset V, Z ⊆ robustNeighbors G ν S →
      Z.card = ⌈ν * Fintype.card V / 2⌉₊ →
      p * ν * Fintype.card V * Z.card / 4 ≤ ((crossingEdges H S Z).card : ℝ)) :
    IsRobustExpander H (p * ν / 4) τ := by
  classical
  intro S hSlo hShi
  by_cases hm : Fintype.card V = 0
  · have hS : S.card = 0 := by have := Finset.card_le_univ S; omega
    simp [hm, hS]
  have hmpos : (0 : ℝ) < Fintype.card V := by exact_mod_cast Nat.pos_of_ne_zero hm
  let R := robustNeighbors G ν S
  let R' := robustNeighbors H (p * ν / 4) S
  let Zbad := R \ R'
  have hbad : Zbad.card < ⌈ν * Fintype.card V / 2⌉₊ := by
    by_contra hnot
    obtain ⟨Z, hZ, hcard⟩ := Finset.exists_subset_card_eq (Nat.le_of_not_gt hnot)
    have hZR : Z ⊆ robustNeighbors G ν S := by
      intro z hz
      exact (Finset.mem_sdiff.mp (hZ hz)).1
    have hnonempty : Z.Nonempty := Finset.card_pos.mp (by
      rw [hcard]
      exact Nat.ceil_pos.mpr (by positivity))
    have hsmall : ((orderedEdges H S Z).card : ℝ) <
        p * ν * Fintype.card V * Z.card / 4 := by
      rw [orderedEdges_card_real]
      calc
        _ < ∑ _z ∈ Z, (p * ν / 4) * Fintype.card V := by
          apply Finset.sum_lt_sum_of_nonempty hnonempty
          intro z hz
          have hznot := (Finset.mem_sdiff.mp (hZ hz)).2
          have hnr : ¬ (p * ν / 4) * Fintype.card V ≤
              ((H.neighborFinset z ∩ S).card : ℝ) := by
            simpa only [R', mem_robustNeighbors] using hznot
          exact lt_of_not_ge hnr
        _ = _ := by simp; ring
    have hle : ((crossingEdges H S Z).card : ℝ) ≤ (orderedEdges H S Z).card := by
      exact_mod_cast crossingEdges_card_le H S Z
    exact (not_lt_of_ge (hpairs S hSlo hShi Z hZR hcard)) (hle.trans_lt hsmall)
  have hbadR : (Zbad.card : ℝ) < ν * Fintype.card V / 2 := Nat.lt_ceil.mp hbad
  have hpart := Finset.card_sdiff_add_card_inter R R'
  have hinter := Finset.card_le_card (Finset.inter_subset_right : R ∩ R' ⊆ R')
  have hcardR : (R.card : ℝ) ≤ Zbad.card + R'.card := by
    have hh : R.card ≤ Zbad.card + R'.card := by dsimp [Zbad]; omega
    exact_mod_cast hh
  have hex := hG S hSlo hShi
  change (S.card : ℝ) + ν * Fintype.card V ≤ (R.card : ℝ) at hex
  change (S.card : ℝ) + (p * ν / 4) * Fintype.card V ≤ (R'.card : ℝ)
  have hpm := mul_le_mul_of_nonneg_right hp1 (mul_pos hν hmpos).le
  nlinarith

noncomputable def Relevant (G : SimpleGraph V) [DecidableRel G.Adj]
    (ν τ : ℝ) (S Z : Finset V) : Prop :=
  τ * Fintype.card V ≤ (S.card : ℝ) ∧
  (S.card : ℝ) ≤ (1 - τ) * Fintype.card V ∧
  Z ⊆ robustNeighbors G ν S ∧ Z.card = ⌈ν * Fintype.card V / 2⌉₊

theorem relevant_edges_lower (G : SimpleGraph V) [DecidableRel G.Adj]
    (ν τ : ℝ) (hν : 0 ≤ ν) (S Z : Finset V) (hrel : Relevant G ν τ S Z) :
    ν ^ 2 * (Fintype.card V : ℝ) ^ 2 / 4 ≤ (crossingEdges G S Z).card := by
  have hc := crossingEdges_of_robust_neighbors G ν S Z hrel.2.2.1
  have hz : ν * Fintype.card V / 2 ≤ (Z.card : ℝ) := by
    rw [hrel.2.2.2]
    exact Nat.le_ceil _
  have hmul := mul_le_mul_of_nonneg_left hz
    (mul_nonneg hν (Nat.cast_nonneg (Fintype.card V)))
  nlinarith

theorem relevant_pair_failure_probability (G : SimpleGraph V) [DecidableRel G.Adj]
    (p ν τ : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hν : 0 ≤ ν)
    (S Z : Finset V) (hrel : Relevant G ν τ S Z) :
    Bernoulli.probability p (fun ω =>
      ((crossingEdges (sampledGraph G ω) S Z).card : ℝ) <
        p * ν * Fintype.card V * Z.card / 4) ≤
      Real.exp (-p * ν ^ 2 * (Fintype.card V : ℝ) ^ 2 / 48) := by
  classical
  have hedge := crossingEdges_of_robust_neighbors G ν S Z hrel.2.2.1
  have hlarge := relevant_edges_lower G ν τ hν S Z hrel
  calc
    _ ≤ Bernoulli.probability p (fun ω =>
        (Bernoulli.retainedCount (crossingEdges G S Z) ω : ℝ) <
          p * (crossingEdges G S Z).card / 2) := by
      apply Bernoulli.probability_mono p hp hp1
      intro ω hω
      rw [sampled_count] at hω
      have hmul := mul_le_mul_of_nonneg_left hedge hp
      nlinarith
    _ ≤ Real.exp (-p * (crossingEdges G S Z).card / 12) :=
      Bernoulli.half_mean_lower_tail p hp hp1 _
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hmul := mul_le_mul_of_nonneg_left hlarge hp
      nlinarith

theorem failure_witness (G : SimpleGraph V) [DecidableRel G.Adj]
    (p ν τ : ℝ) (hp1 : p ≤ 1) (hν : 0 < ν)
    (hG : IsRobustExpander G ν τ) (ω : Sym2 V → Bool)
    (hfail : ¬ IsRobustExpander (sampledGraph G ω) (p * ν / 4) τ) :
    ∃ pair : Finset V × Finset V, Relevant G ν τ pair.1 pair.2 ∧
      ((crossingEdges (sampledGraph G ω) pair.1 pair.2).card : ℝ) <
        p * ν * Fintype.card V * pair.2.card / 4 := by
  classical
  by_contra hnot
  apply hfail
  apply robust_of_pair_counts G (sampledGraph G ω) p ν τ hp1 hν hG
  intro S hSlo hShi Z hZR hcard
  apply le_of_not_gt
  intro hsmall
  exact hnot ⟨(S, Z), ⟨hSlo, hShi, hZR, hcard⟩, hsmall⟩

/-- The union bound ranges over all pairs of vertex sets, including
overlapping pairs. The sampled choices remain independent unordered edges. -/
theorem failure_probability (G : SimpleGraph V) [DecidableRel G.Adj]
    (p ν τ : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hν : 0 < ν)
    (hG : IsRobustExpander G ν τ) :
    Bernoulli.probability p (fun ω =>
      ¬ IsRobustExpander (sampledGraph G ω) (p * ν / 4) τ) ≤
      (4 : ℝ) ^ Fintype.card V *
        Real.exp (-p * ν ^ 2 * (Fintype.card V : ℝ) ^ 2 / 48) := by
  classical
  let P := fun (pair : Finset V × Finset V) (ω : Sym2 V → Bool) =>
    Relevant G ν τ pair.1 pair.2 ∧
      ((crossingEdges (sampledGraph G ω) pair.1 pair.2).card : ℝ) <
        p * ν * Fintype.card V * pair.2.card / 4
  have hpair (pair : Finset V × Finset V) : Bernoulli.probability p (P pair) ≤
      Real.exp (-p * ν ^ 2 * (Fintype.card V : ℝ) ^ 2 / 48) := by
    by_cases hrel : Relevant G ν τ pair.1 pair.2
    · calc
        _ ≤ Bernoulli.probability p (fun ω =>
            ((crossingEdges (sampledGraph G ω) pair.1 pair.2).card : ℝ) <
              p * ν * Fintype.card V * pair.2.card / 4) :=
          Bernoulli.probability_mono p hp hp1 (fun _ h => h.2)
        _ ≤ _ := relevant_pair_failure_probability G p ν τ hp hp1 hν.le _ _ hrel
    · simp [P, hrel, Bernoulli.probability, MatchingProbability.probability,
        (Real.exp_pos _).le]
  calc
    _ ≤ Bernoulli.probability p (fun ω =>
        ∃ pair ∈ (univ : Finset (Finset V × Finset V)), P pair ω) := by
      apply Bernoulli.probability_mono p hp hp1
      intro ω hfail
      obtain ⟨pair, hpair⟩ := failure_witness G p ν τ hp1 hν hG ω hfail
      exact ⟨pair, Finset.mem_univ _, hpair⟩
    _ ≤ ∑ pair : Finset V × Finset V, Bernoulli.probability p (P pair) :=
      Bernoulli.probability_exists_le_sum p hp hp1 univ P
    _ ≤ ∑ _pair : Finset V × Finset V,
        Real.exp (-p * ν ^ 2 * (Fintype.card V : ℝ) ^ 2 / 48) :=
      Finset.sum_le_sum (fun pair _ => hpair pair)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
        Fintype.card_finset, nsmul_eq_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      rw [← mul_pow]
      norm_num

theorem ordinary_random_reserve (G : SimpleGraph V) [DecidableRel G.Adj]
    (p ν τ : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hν : 0 < ν)
    (hG : IsRobustExpander G ν τ) :
    1 - (4 : ℝ) ^ Fintype.card V *
        Real.exp (-p * ν ^ 2 * (Fintype.card V : ℝ) ^ 2 / 48) ≤
      Bernoulli.probability p (fun ω =>
        IsRobustExpander (sampledGraph G ω) (p * ν / 4) τ) := by
  have hf := failure_probability G p ν τ hp.le hp1 hν hG
  rw [Bernoulli.probability_compl] at hf
  linarith

end Overfull.OrdinaryRandomReserve
