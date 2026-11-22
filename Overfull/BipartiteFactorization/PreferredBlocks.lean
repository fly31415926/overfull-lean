import Overfull.BipartiteFactorization.UniformBudgets

/-!
# Preferred-row sampling when no correction score is required

Small correction pools have all their colors excluded. Such a pool needs
no correction-capacity event. This module samples the ordinary and special
preferred rows alone, retaining all supplied fine/coarse position relations.
The uniform threshold uses only active-row, special-count and label bounds.
-/

noncomputable section

namespace Overfull.BipartiteFactorization.PreferredBlocks

open Finset Classical FiniteProbability BlockProductSampling

universe u v w t

variable {V E ι γ : Type*} [Fintype E] [Fintype ι]

def bad (G : Multigraph V E) (U Wo Ws : Finset V)
    (F : V → Finset E) (β p : ℝ) (T : Finset V) : Prop :=
  (∃ x ∈ Wo, BlockSelectionBudget.ordinaryBad G U F β p T x) ∨
    ∃ x ∈ Ws, BlockSelectionBudget.specialBad G U p T x

def Good (G : Multigraph V E) (U Wo Ws : Finset V)
    (F : V → Finset E) (β p : ℝ) (T : Finset V) : Prop :=
  (∀ x ∈ Wo, β * p * (G.edgesTo x U).card / 8 ≤
    ((F x ∩ G.edgesTo x T).card : ℝ)) ∧
  ∀ x ∈ Ws, p * (G.edgesTo x U).card / 3 ≤ ((G.edgesTo x T).card : ℝ)

def failureBudget (G : Multigraph V E) (U Wo Ws : Finset V) (β p a : ℝ) : ℝ :=
  (∑ x ∈ Wo, Real.exp (-β * p * (G.edgesTo x U).card / 48)) +
    ∑ x ∈ Ws, 18 * a / (p * (G.edgesTo x U).card)

omit [Fintype ι] in
theorem not_bad_iff_good (G : Multigraph V E) (U Wo Ws : Finset V)
    (F : V → Finset E) (β p : ℝ) (T : Finset V) :
    ¬ bad G U Wo Ws F β p T ↔ Good G U Wo Ws F β p T := by
  simp only [bad, Good, BlockSelectionBudget.ordinaryBad, BlockSelectionBudget.specialBad,
    not_or, not_exists, not_and, not_lt]

/-- The actual preferred-row failure bound needs neither a correction pool
nor a cap, and does not require two sampled vertices in each nonempty part. -/
theorem probability_bad_le (G : Multigraph V E)
    (D : ι → Finset V) (hdisj : ∀ i j, i ≠ j → Disjoint (D i) (D j))
    (B U Wo Ws : Finset V) (hcover : univ.biUnion D = B)
    (s : ι → ℕ) (hs : ∀ i, s i ≤ (D i).card)
    (F : V → Finset E) (β p a : ℝ) (hp : 0 < p) (ha : 0 ≤ a)
    (hfraction : ∀ i, (s i : ℝ) = p * (D i).card)
    (hdegree : ∀ v ∈ B, (G.degree v : ℝ) ≤ a)
    (hF : ∀ x ∈ Wo, F x ⊆ G.edgesTo x B)
    (hinj : ∀ x ∈ Wo, Set.InjOn (G.otherEnd x) (F x))
    (hFsize : ∀ x ∈ Wo, β * (G.edgesTo x U).card / 4 ≤ (F x).card)
    (hspecial_c : ∀ x ∈ Ws, 0 < ((G.edgesTo x U).card : ℝ))
    (hspecial_side : ∀ x ∈ Ws,
      ((G.edgesTo x U).card : ℝ) / 2 ≤ (G.edgesTo x B).card) :
    MatchingProbability.probability
      (piWeight (fun i => Hypergeometric.weight (E := ↥(D i)) (s i)))
      (fun τ => bad G U Wo Ws F β p (sampledBlock D τ)) ≤
        failureBudget G U Wo Ws β p a := by
  have hw := piWeight_nonneg
    (fun i => Hypergeometric.weight (E := ↥(D i)) (s i))
    (fun i => Hypergeometric.weight_nonneg _)
  have hordinary : MatchingProbability.probability
      (piWeight (fun i => Hypergeometric.weight (E := ↥(D i)) (s i)))
      (fun τ => ∃ x ∈ Wo, BlockSelectionBudget.ordinaryBad G U F β p (sampledBlock D τ) x) ≤
      ∑ x ∈ Wo, Real.exp (-β * p * (G.edgesTo x U).card / 48) := by
    calc
      _ ≤ ∑ x ∈ Wo, MatchingProbability.probability
          (piWeight (fun i => Hypergeometric.weight (E := ↥(D i)) (s i)))
          (fun τ => BlockSelectionBudget.ordinaryBad G U F β p (sampledBlock D τ) x) :=
        MatchingProbability.probability_exists_le_sum _ hw Wo _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro x hx
        simpa only [BlockSelectionBudget.ordinaryBad] using
          PreferredSampling.representative_edges_lower_tail G D hdisj B hcover
            s hs p hp.le hfraction x (F x) (hF x hx) (hinj x hx)
            β (G.edgesTo x U).card (hFsize x hx)
  have hspecial : MatchingProbability.probability
      (piWeight (fun i => Hypergeometric.weight (E := ↥(D i)) (s i)))
      (fun τ => ∃ x ∈ Ws, BlockSelectionBudget.specialBad G U p (sampledBlock D τ) x) ≤
      ∑ x ∈ Ws, 18 * a / (p * (G.edgesTo x U).card) := by
    calc
      _ ≤ ∑ x ∈ Ws, MatchingProbability.probability
          (piWeight (fun i => Hypergeometric.weight (E := ↥(D i)) (s i)))
          (fun τ => BlockSelectionBudget.specialBad G U p (sampledBlock D τ) x) :=
        MatchingProbability.probability_exists_le_sum _ hw Ws _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro x hx
        simpa only [BlockSelectionBudget.specialBad] using
          PreferredSampling.special_preferred_lower_tail G D hdisj B hcover s hs p hp
            hfraction x U a ha hdegree (hspecial_c x hx) (hspecial_side x hx)
  exact (MatchingProbability.probability_union_le _ hw _ _).trans (add_le_add hordinary hspecial)

variable [Fintype γ]

/-- Simultaneously realize all position relations and preferred rows,
without imposing any condition on the correction pool. -/
theorem exists_preferred_blocks (G : Multigraph V E)
    (D : ι → Finset V) (hdisj : ∀ i j, i ≠ j → Disjoint (D i) (D j))
    (B U Wo Ws : Finset V) (hcover : univ.biUnion D = B)
    (S : γ → ∀ i, Finset (D i)) (F : V → Finset E) (β a : ℝ) (p : γ → ℝ)
    (hp : ∀ j, 0 < p j) (ha : 0 ≤ a)
    (hfraction : ∀ j i, ((S j i).card : ℝ) = p j * (D i).card)
    (hdegree : ∀ v ∈ B, (G.degree v : ℝ) ≤ a)
    (hF : ∀ x ∈ Wo, F x ⊆ G.edgesTo x B)
    (hinj : ∀ x ∈ Wo, Set.InjOn (G.otherEnd x) (F x))
    (hFsize : ∀ x ∈ Wo, β * (G.edgesTo x U).card / 4 ≤ (F x).card)
    (hspecial_c : ∀ x ∈ Ws, 0 < ((G.edgesTo x U).card : ℝ))
    (hspecial_side : ∀ x ∈ Ws,
      ((G.edgesTo x U).card : ℝ) / 2 ≤ (G.edgesTo x B).card)
    (hbudget : (∑ j, failureBudget G U Wo Ws β (p j) a) < 1) :
    ∃ T : γ → Finset V, SimultaneousBlocks.RealizesPositions D B S T ∧
      ∀ j, Good G U Wo Ws F β (p j) (T j) := by
  have hbad (j : γ) : MatchingProbability.probability
      (piWeight (fun i => Hypergeometric.weight (E := ↥(D i)) (S j i).card))
      (fun τ => bad G U Wo Ws F β (p j) (sampledBlock D τ)) ≤
        failureBudget G U Wo Ws β (p j) a := by
    exact probability_bad_le G D hdisj B U Wo Ws hcover
      (fun i => (S j i).card)
      (fun i => by simpa only [Fintype.card_coe] using Finset.card_le_univ (S j i))
      F β (p j) a (hp j) ha (hfraction j) hdegree hF hinj hFsize hspecial_c hspecial_side
  obtain ⟨σ, hσ⟩ := PartitionPermutation.exists_good_images S
    (fun j τ => bad G U Wo Ws F β (p j) (sampledBlock D τ))
    (fun j => failureBudget G U Wo Ws β (p j) a) hbad hbudget
  refine ⟨fun j => SimultaneousBlocks.permutedBlock D (S j) σ,
    SimultaneousBlocks.permutedBlocks_realize D hdisj B hcover S σ, ?_⟩
  intro j
  exact (not_bad_iff_good G U Wo Ws F β (p j) _).mp (hσ j)

omit [Fintype ι] in
/-- Derive the whole preferred-only budget from linearly large active rows
and bounded special and label counts. -/
theorem family_budget_le_scaled (G : Multigraph V E) (U Wo Ws : Finset V)
    (β a m pmin cmin rowBound specialBound labelBound : ℝ) (p : γ → ℝ)
    (hβ : 0 ≤ β) (ha : 0 ≤ a) (hm : 0 < m) (hpmin : 0 < pmin) (hcmin : 0 < cmin)
    (hrow : 0 ≤ rowBound) (hspecials : 0 ≤ specialBound)
    (hrows : (Wo.card : ℝ) ≤ rowBound * m) (hspecialcard : (Ws.card : ℝ) ≤ specialBound)
    (hlabels : (Fintype.card γ : ℝ) ≤ labelBound)
    (hp : ∀ j, pmin ≤ p j)
    (hordinary : ∀ x ∈ Wo, cmin * m ≤ (G.edgesTo x U).card)
    (hspecial : ∀ x ∈ Ws, cmin * m ≤ (G.edgesTo x U).card) :
    (∑ j, failureBudget G U Wo Ws β (p j) a) ≤
      labelBound * rowBound * m * Real.exp (-(β * pmin * cmin / 48) * m) +
        (18 * labelBound * specialBound / (pmin * cmin)) * a / m := by
  let b : ℝ := rowBound * m * Real.exp (-(β * pmin * cmin / 48) * m) +
    (18 * specialBound / (pmin * cmin)) * a / m
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hsingle (j : γ) : failureBudget G U Wo Ws β (p j) a ≤ b := by
    have hp0 : 0 ≤ p j := hpmin.le.trans (hp j)
    have hrowtail (x : V) (hx : x ∈ Wo) :
        Real.exp (-β * p j * (G.edgesTo x U).card / 48) ≤
          Real.exp (-(β * pmin * cmin / 48) * m) := by
      have hprod := mul_le_mul_of_nonneg_left
        (mul_le_mul (hp j) (hordinary x hx) (by positivity : 0 ≤ cmin * m) hp0) hβ
      exact Real.exp_le_exp.mpr (by nlinarith)
    have hspecialtail (x : V) (hx : x ∈ Ws) :
        18 * a / (p j * (G.edgesTo x U).card) ≤ 18 * a / (pmin * (cmin * m)) := by
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul (hp j) (hspecial x hx) (by positivity) hp0)
    have hrows' := mul_le_mul_of_nonneg_right hrows
      (Real.exp_nonneg (-(β * pmin * cmin / 48) * m))
    have hspecials' := mul_le_mul_of_nonneg_right hspecialcard
      (show 0 ≤ 18 * a / (pmin * (cmin * m)) by positivity)
    calc
      _ ≤ (∑ _x ∈ Wo, Real.exp (-(β * pmin * cmin / 48) * m)) +
          ∑ _x ∈ Ws, 18 * a / (pmin * (cmin * m)) :=
        add_le_add (Finset.sum_le_sum hrowtail) (Finset.sum_le_sum hspecialtail)
      _ = Wo.card * Real.exp (-(β * pmin * cmin / 48) * m) +
          Ws.card * (18 * a / (pmin * (cmin * m))) := by simp
      _ ≤ rowBound * m * Real.exp (-(β * pmin * cmin / 48) * m) +
          specialBound * (18 * a / (pmin * (cmin * m))) := add_le_add hrows' hspecials'
      _ = b := by dsimp [b]; ring
  calc
    _ ≤ ∑ _j : γ, b := Finset.sum_le_sum (fun j _ => hsingle j)
    _ = (Fintype.card γ : ℝ) * b := by simp
    _ ≤ labelBound * b := mul_le_mul_of_nonneg_right hlabels hb
    _ = _ := by dsimp [b]; ring

omit [Fintype ι] [Fintype γ] [Fintype E] in
/-- Uniform graph-specific preferred-only budgets, with constants preceding
every graph, row set, and finite label type. -/
theorem exists_uniform_preferred_budget
    (β pmin cmin rowBound : ℝ) (specialBound labelBound : ℕ)
    (hβ : 0 < β) (hpmin : 0 < pmin) (hcmin : 0 < cmin) (hrow : 0 ≤ rowBound) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ m₀ : ℕ, 1 ≤ m₀ ∧
      ∀ m : ℕ, m₀ ≤ m → ∀ a : ℝ, 0 ≤ a → a ≤ ε * m →
        ∀ (V : Type u) (E : Type v) [Fintype E]
          (γ : Type w) [Fintype γ] (G : Multigraph V E)
          (U Wo Ws : Finset V) (p : γ → ℝ),
          (Wo.card : ℝ) ≤ rowBound * m → Ws.card ≤ specialBound →
          Fintype.card γ ≤ labelBound → (∀ j, pmin ≤ p j) →
          (∀ x ∈ Wo, cmin * m ≤ (G.edgesTo x U).card) →
          (∀ x ∈ Ws, cmin * m ≤ (G.edgesTo x U).card) →
          (∑ j, failureBudget G U Wo Ws β (p j) a) < 1 := by
  let u : ℝ := labelBound * rowBound
  let v : ℝ := 18 * labelBound * specialBound / (pmin * cmin)
  let r : ℝ := β * pmin * cmin / 48
  obtain ⟨ε, hε, m₀, hbudget⟩ := FiniteProbability.exists_uniform_failure_budget
    u v 0 r (by dsimp [u]; positivity) (by dsimp [v]; positivity)
    (by norm_num) (by dsimp [r]; positivity)
  refine ⟨ε, hε, max m₀ 1, le_max_right _ _, ?_⟩
  intro m hm a ha haε V E _ γ _ G U Wo Ws p hrows hspecials hlabels hp hordinary hspecial
  have hmpos : (0 : ℝ) < m := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one ((le_max_right m₀ 1).trans hm))
  have hbase := family_budget_le_scaled G U Wo Ws β a m pmin cmin rowBound
    specialBound labelBound p hβ.le ha hmpos hpmin hcmin hrow (Nat.cast_nonneg _)
    hrows (by exact_mod_cast hspecials) (by exact_mod_cast hlabels) hp hordinary hspecial
  apply hbase.trans_lt
  simpa only [u, v, r, zero_div, add_zero] using
    hbudget m ((le_max_left m₀ 1).trans hm) a ha haε

omit [Fintype ι] [Fintype γ] [Fintype E] in
/-- Uniform actual preferred-block construction, valid regardless of the
correction-pool size. This supplies the branch in which no correction
score is needed, without adding a numerical success assumption. -/
theorem exists_uniform_preferred_blocks
    (β pmin cmin : ℝ) (specialBound labelBound : ℕ)
    (hβ : 0 < β) (hpmin : 0 < pmin) (hcmin : 0 < cmin) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ m₀ : ℕ, 1 ≤ m₀ ∧
      ∀ m : ℕ, m₀ ≤ m → ∀ a : ℝ, 0 ≤ a → a ≤ ε * m →
        ∀ (V : Type u) (E : Type v) [Fintype E]
          (ι : Type w) [Fintype ι] (γ : Type t) [Fintype γ]
          (G : Multigraph V E) (D : ι → Finset V)
          (B U Wo Ws : Finset V) (S : γ → ∀ i, Finset (D i))
          (F : V → Finset E) (p : γ → ℝ),
          (Wo.card : ℝ) ≤ ε * m → Ws.card ≤ specialBound →
          Fintype.card γ ≤ labelBound →
          (∀ i j, i ≠ j → Disjoint (D i) (D j)) → univ.biUnion D = B →
          (∀ j, pmin ≤ p j) →
          (∀ j i, ((S j i).card : ℝ) = p j * (D i).card) →
          (∀ v ∈ B, (G.degree v : ℝ) ≤ a) →
          (∀ x ∈ Wo, F x ⊆ G.edgesTo x B) →
          (∀ x ∈ Wo, Set.InjOn (G.otherEnd x) (F x)) →
          (∀ x ∈ Wo, β * (G.edgesTo x U).card / 4 ≤ (F x).card) →
          (∀ x ∈ Wo, cmin * m ≤ (G.edgesTo x U).card) →
          (∀ x ∈ Ws, cmin * m ≤ (G.edgesTo x U).card) →
          (∀ x ∈ Ws, ((G.edgesTo x U).card : ℝ) / 2 ≤ (G.edgesTo x B).card) →
          ∃ T : γ → Finset V, SimultaneousBlocks.RealizesPositions D B S T ∧
            ∀ j, Good G U Wo Ws F β (p j) (T j) := by
  obtain ⟨ε₀, hε₀, m₀, hm₀, hbudget⟩ := exists_uniform_preferred_budget
    β pmin cmin 1 specialBound labelBound hβ hpmin hcmin (by norm_num)
  let ε : ℝ := min ε₀ 1
  have hε : 0 < ε := lt_min hε₀ (by norm_num)
  have hε₀le : ε ≤ ε₀ := min_le_left _ _
  have hε1 : ε ≤ 1 := min_le_right _ _
  refine ⟨ε, hε, m₀, hm₀, ?_⟩
  intro m hm a ha haε V E _ ι _ γ _ G D B U Wo Ws S F p
    hWo hWs hγ hdisj hcover hp hfraction hdegree hF hinj hFsize hordinary hspecial hspecial_side
  have hmpos : (0 : ℝ) < m := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (hm₀.trans hm))
  have hfailure := hbudget m hm a ha
    (haε.trans (mul_le_mul_of_nonneg_right hε₀le hmpos.le)) V E γ G U Wo Ws p
    (hWo.trans (mul_le_mul_of_nonneg_right hε1 hmpos.le)) hWs hγ hp hordinary hspecial
  exact exists_preferred_blocks G D hdisj B U Wo Ws hcover S F β a p
    (fun j => hpmin.trans_le (hp j)) ha hfraction hdegree hF hinj hFsize
    (fun x hx => (mul_pos hcmin hmpos).trans_le (hspecial x hx)) hspecial_side hfailure

end Overfull.BipartiteFactorization.PreferredBlocks
