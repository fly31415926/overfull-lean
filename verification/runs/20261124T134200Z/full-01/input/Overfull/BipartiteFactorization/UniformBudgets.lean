import Overfull.BipartiteFactorization.SimultaneousPalettes
import Overfull.BipartiteFactorization.SimultaneousBlocks
import Overfull.Probability.UniformFailureBudget

/-!
# Uniform bounds for the actual palette and block failure budgets

Positive lower bounds for the sampling fractions, linearly large active
rows and correction pools, and a bounded number of special vertices give
explicit coefficients for the uniform failure-budget theorem.  In particular,
the numerical union bounds are conclusions, not additional hypotheses.
-/

noncomputable section

namespace Overfull.BipartiteFactorization.UniformBudgets

open Finset Classical

universe u v w t

variable {V E : Type*} [Fintype E]

/-- The actual block budget is controlled by a common sampling fraction,
active-row lower bound, and correction-pool lower bound. -/
theorem block_budget_le_uniform (G : Multigraph V E)
    (B U Wo Ws Zcorr : Finset V) (β p a pmin cmin Mmin : ℝ)
    (hβ : 0 ≤ β) (ha : 0 ≤ a) (hpmin : 0 < pmin)
    (hcmin : 0 < cmin) (hMmin : 0 < Mmin) (hp : pmin ≤ p)
    (hordinary : ∀ x ∈ Wo, cmin ≤ (G.edgesTo x U).card)
    (hspecial : ∀ x ∈ Ws, cmin ≤ (G.edgesTo x U).card)
    (hpool : Mmin ≤ (correctionPool G B Zcorr).card) :
    BlockSelectionBudget.failureBudget G B U Wo Ws Zcorr β p a ≤
      Wo.card * Real.exp (-β * pmin * cmin / 48) +
        (Ws.card * (18 * a / (pmin * cmin)) +
          (2 : ℝ)^21 * a / (pmin^3 * Mmin)) := by
  have hp0 : 0 ≤ p := hpmin.le.trans hp
  have hordinary_bound (x : V) (hx : x ∈ Wo) :
      Real.exp (-β * p * (G.edgesTo x U).card / 48) ≤
        Real.exp (-β * pmin * cmin / 48) := by
    have hpc := mul_le_mul hp (hordinary x hx) hcmin.le hp0
    have hprod := mul_le_mul_of_nonneg_left hpc hβ
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hspecial_bound (x : V) (hx : x ∈ Ws) :
      18 * a / (p * (G.edgesTo x U).card) ≤ 18 * a / (pmin * cmin) := by
    apply div_le_div_of_nonneg_left (by positivity) (mul_pos hpmin hcmin)
    exact mul_le_mul hp (hspecial x hx) hcmin.le hp0
  have hscore : (2 : ℝ)^21 * a /
      (p^3 * (correctionPool G B Zcorr).card) ≤
        (2 : ℝ)^21 * a / (pmin^3 * Mmin) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact mul_le_mul (pow_le_pow_left₀ hpmin.le hp 3) hpool hMmin.le
      (by positivity)
  unfold BlockSelectionBudget.failureBudget
  calc
    _ ≤ (∑ _x ∈ Wo, Real.exp (-β * pmin * cmin / 48)) +
        ((∑ _x ∈ Ws, 18 * a / (pmin * cmin)) +
          (2 : ℝ)^21 * a / (pmin^3 * Mmin)) := by
      exact add_le_add (Finset.sum_le_sum hordinary_bound)
        (add_le_add (Finset.sum_le_sum hspecial_bound) hscore)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]

/-- Linearly large active rows and correction pools turn one palette's
actual budget into an exponential term and a reciprocal-order term. -/
theorem palette_budget_le_scaled {κ : Type*} [Fintype κ] {k : ℕ}
    (G : Multigraph V E) (c : G.EdgeColoring k) (U Z : Finset V)
    (P : κ → Finset E) (B : ℝ) (s : ℕ)
    (m lammin cmin Mmin rowBound poolBound : ℝ)
    (hm : 0 < m) (hlammin : 0 < lammin) (hcmin : 0 < cmin)
    (hMmin : 0 < Mmin) (hB : 0 ≤ B)
    (hrowBound : (Z.card : ℝ) ≤ rowBound * m)
    (hpoolBound : (Fintype.card κ : ℝ) ≤ poolBound)
    (hlam : lammin ≤ (s : ℝ) / k)
    (hc : ∀ x ∈ Z, cmin * m ≤ (G.edgesTo x U).card)
    (hM : ∀ j, Mmin * m ≤ (P j).card) :
    SimultaneousPalettes.failureBudget c U Z P B s ≤
      2 * rowBound * m * Real.exp (-(lammin * cmin / 4096) * m) +
        poolBound * (32 * B / (lammin * Mmin)) / m := by
  have hbase := SimultaneousPalettes.failureBudget_le_uniform c U Z P B s
    lammin (cmin * m) (Mmin * m) hlammin (by positivity) (by positivity)
    hB hlam hc hM
  have hrows := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hrowBound (by norm_num : (0 : ℝ) ≤ 2))
    (Real.exp_nonneg (-lammin * (cmin * m) / 4096))
  have hpools := mul_le_mul_of_nonneg_right hpoolBound
    (show 0 ≤ 32 * B / (lammin * (Mmin * m)) by positivity)
  apply hbase.trans
  calc
    _ ≤ 2 * (rowBound * m) * Real.exp (-lammin * (cmin * m) / 4096) +
        poolBound * (32 * B / (lammin * (Mmin * m))) := add_le_add hrows hpools
    _ = _ := by ring_nf

/-- Linearly large rows and pools, with a bounded special set, give the
exact coefficients needed for the uniform block threshold. -/
theorem block_budget_le_scaled (G : Multigraph V E)
    (B U Wo Ws Zcorr : Finset V)
    (β p a m pmin cmin Mmin rowBound specialBound : ℝ)
    (hβ : 0 ≤ β) (ha : 0 ≤ a) (hm : 0 < m)
    (hpmin : 0 < pmin) (hcmin : 0 < cmin) (hMmin : 0 < Mmin)
    (hp : pmin ≤ p)
    (hordinary : ∀ x ∈ Wo, cmin * m ≤ (G.edgesTo x U).card)
    (hspecial : ∀ x ∈ Ws, cmin * m ≤ (G.edgesTo x U).card)
    (hpool : Mmin * m ≤ (correctionPool G B Zcorr).card)
    (hrowBound : (Wo.card : ℝ) ≤ rowBound * m)
    (hspecialBound : (Ws.card : ℝ) ≤ specialBound) :
    BlockSelectionBudget.failureBudget G B U Wo Ws Zcorr β p a ≤
      rowBound * m * Real.exp (-(β * pmin * cmin / 48) * m) +
        (18 * specialBound / (pmin * cmin) +
          (2 : ℝ)^21 / (pmin^3 * Mmin)) * a / m := by
  have hbase := block_budget_le_uniform G B U Wo Ws Zcorr β p a pmin
    (cmin * m) (Mmin * m) hβ ha hpmin (by positivity) (by positivity)
    hp hordinary hspecial hpool
  have hrows := mul_le_mul_of_nonneg_right hrowBound
    (Real.exp_nonneg (-β * pmin * (cmin * m) / 48))
  have hspecials := mul_le_mul_of_nonneg_right hspecialBound
    (show 0 ≤ 18 * a / (pmin * (cmin * m)) by positivity)
  apply hbase.trans
  calc
    _ ≤ (rowBound * m) * Real.exp (-β * pmin * (cmin * m) / 48) +
        (specialBound * (18 * a / (pmin * (cmin * m))) +
          (2 : ℝ)^21 * a / (pmin^3 * (Mmin * m))) :=
      add_le_add hrows (add_le_add_right hspecials _)
    _ = _ := by ring_nf

/-- A bounded family of palettes has a common scaled bound, independent
of the graph order and the precise choice of positive palette sizes. -/
theorem palette_family_budget_le_scaled {κ ι : Type*} [Fintype κ] [Fintype ι]
    {k : ℕ} (G : Multigraph V E) (c : G.EdgeColoring k) (U Z : Finset V)
    (P : κ → Finset E) (B : ℝ) (s : ι → ℕ)
    (m lammin cmin Mmin rowBound poolBound labelBound : ℝ)
    (hm : 0 < m) (hlammin : 0 < lammin) (hcmin : 0 < cmin)
    (hMmin : 0 < Mmin) (hB : 0 ≤ B)
    (hrow : 0 ≤ rowBound) (hpools : 0 ≤ poolBound)
    (hrowBound : (Z.card : ℝ) ≤ rowBound * m)
    (hpoolBound : (Fintype.card κ : ℝ) ≤ poolBound)
    (hlabelBound : (Fintype.card ι : ℝ) ≤ labelBound)
    (hlam : ∀ i, lammin ≤ (s i : ℝ) / k)
    (hc : ∀ x ∈ Z, cmin * m ≤ (G.edgesTo x U).card)
    (hM : ∀ j, Mmin * m ≤ (P j).card) :
    (∑ i, SimultaneousPalettes.failureBudget c U Z P B (s i)) ≤
      2 * labelBound * rowBound * m * Real.exp (-(lammin * cmin / 4096) * m) +
        labelBound * poolBound * (32 * B / (lammin * Mmin)) / m := by
  let b : ℝ := 2 * rowBound * m * Real.exp (-(lammin * cmin / 4096) * m) +
    poolBound * (32 * B / (lammin * Mmin)) / m
  have hb : 0 ≤ b := by dsimp [b]; positivity
  calc
    _ ≤ ∑ _i : ι, b := by
      apply Finset.sum_le_sum
      intro i _
      exact palette_budget_le_scaled G c U Z P B (s i) m lammin cmin Mmin
        rowBound poolBound hm hlammin hcmin hMmin hB hrowBound hpoolBound
        (hlam i) hc hM
    _ = (Fintype.card ι : ℝ) * b := by simp
    _ ≤ labelBound * b := mul_le_mul_of_nonneg_right hlabelBound hb
    _ = _ := by dsimp [b]; ring

/-- A bounded family of fine and coarse blocks has one common scaled
bound. Labels may overlap; this estimate requires no independence. -/
theorem block_family_budget_le_scaled {γ : Type*} [Fintype γ]
    (G : Multigraph V E) (B U Wo Ws Zcorr : Finset V)
    (β a m pmin cmin Mmin rowBound specialBound labelBound : ℝ)
    (p : γ → ℝ) (hβ : 0 ≤ β) (ha : 0 ≤ a) (hm : 0 < m)
    (hpmin : 0 < pmin) (hcmin : 0 < cmin) (hMmin : 0 < Mmin)
    (hrow : 0 ≤ rowBound) (hspecials : 0 ≤ specialBound)
    (hp : ∀ j, pmin ≤ p j)
    (hordinary : ∀ x ∈ Wo, cmin * m ≤ (G.edgesTo x U).card)
    (hspecial : ∀ x ∈ Ws, cmin * m ≤ (G.edgesTo x U).card)
    (hpool : Mmin * m ≤ (correctionPool G B Zcorr).card)
    (hrowBound : (Wo.card : ℝ) ≤ rowBound * m)
    (hspecialBound : (Ws.card : ℝ) ≤ specialBound)
    (hlabelBound : (Fintype.card γ : ℝ) ≤ labelBound) :
    (∑ j, BlockSelectionBudget.failureBudget G B U Wo Ws Zcorr β (p j) a) ≤
      labelBound * rowBound * m * Real.exp (-(β * pmin * cmin / 48) * m) +
        labelBound * (18 * specialBound / (pmin * cmin) +
          (2 : ℝ)^21 / (pmin^3 * Mmin)) * a / m := by
  let b : ℝ := rowBound * m * Real.exp (-(β * pmin * cmin / 48) * m) +
    (18 * specialBound / (pmin * cmin) + (2 : ℝ)^21 / (pmin^3 * Mmin)) * a / m
  have hb : 0 ≤ b := by dsimp [b]; positivity
  calc
    _ ≤ ∑ _j : γ, b := by
      apply Finset.sum_le_sum
      intro j _
      exact block_budget_le_scaled G B U Wo Ws Zcorr β (p j) a m pmin cmin Mmin
        rowBound specialBound hβ ha hm hpmin hcmin hMmin (hp j)
        hordinary hspecial hpool hrowBound hspecialBound
    _ = (Fintype.card γ : ℝ) * b := by simp
    _ ≤ labelBound * b := mul_le_mul_of_nonneg_right hlabelBound hb
    _ = _ := by dsimp [b]; ring

/-- Uniform palette thresholds from the actual graph bounds.  The constants
precede every finite vertex, edge, pool, and palette type, and every graph.
The bound `2*a/α+4` is the manuscript bound `2*m*a/k+4` after using
`α*m ≤ k`. No numerical or probabilistic success premise remains. -/
theorem exists_uniform_palette_budget
    (α lammin cmin Mmin rowBound : ℝ) (poolBound labelBound : ℕ)
    (hα : 0 < α) (hlammin : 0 < lammin) (hcmin : 0 < cmin)
    (hMmin : 0 < Mmin) (hrow : 0 ≤ rowBound) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ m₀ : ℕ, 1 ≤ m₀ ∧
      ∀ m : ℕ, m₀ ≤ m → ∀ a b : ℝ, 0 ≤ a → a ≤ ε * m →
        0 ≤ b → b ≤ 2 * a / α + 4 →
        ∀ (V : Type u) (E : Type v) [Fintype E]
          (κ : Type w) [Fintype κ] (ι : Type t) [Fintype ι]
          (G : Multigraph V E) (k : ℕ) (c : G.EdgeColoring k)
          (U Z : Finset V) (P : κ → Finset E) (s : ι → ℕ),
          (Z.card : ℝ) ≤ rowBound * m → Fintype.card κ ≤ poolBound →
          Fintype.card ι ≤ labelBound →
          (∀ i, lammin ≤ (s i : ℝ) / k) →
          (∀ x ∈ Z, cmin * m ≤ (G.edgesTo x U).card) →
          (∀ j, Mmin * m ≤ (P j).card) →
          (∑ i, SimultaneousPalettes.failureBudget c U Z P b (s i)) < 1 := by
  let u : ℝ := 2 * labelBound * rowBound
  let v : ℝ := labelBound * poolBound * 64 / (lammin * Mmin * α)
  let w : ℝ := labelBound * poolBound * 128 / (lammin * Mmin)
  let r : ℝ := lammin * cmin / 4096
  obtain ⟨ε, hε, m₀, hbudget⟩ := FiniteProbability.exists_uniform_failure_budget
    u v w r (by dsimp [u]; positivity) (by dsimp [v]; positivity)
    (by dsimp [w]; positivity) (by dsimp [r]; positivity)
  refine ⟨ε, hε, max m₀ 1, le_max_right _ _, ?_⟩
  intro m hm a b ha haε hb hbupper V E _ κ _ ι _ G k c U Z P s
    hrows hpools hlabels hlam hc hM
  have hmpos : (0 : ℝ) < m := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one ((le_max_right m₀ 1).trans hm))
  have hbase := palette_family_budget_le_scaled G c U Z P b s m lammin cmin Mmin
    rowBound poolBound labelBound hmpos hlammin hcmin hMmin hb hrow
    (Nat.cast_nonneg _) hrows (by exact_mod_cast hpools) (by exact_mod_cast hlabels)
    hlam hc hM
  have hnum := mul_le_mul_of_nonneg_left hbupper
    (show 0 ≤ (labelBound : ℝ) * poolBound * 32 / (lammin * Mmin) / m by positivity)
  have hpool : (labelBound : ℝ) * poolBound * (32 * b / (lammin * Mmin)) / m ≤
      v * a / m + w / m := by
    dsimp [v, w]
    calc
      _ = ((labelBound : ℝ) * poolBound * 32 / (lammin * Mmin) / m) * b := by ring
      _ ≤ ((labelBound : ℝ) * poolBound * 32 / (lammin * Mmin) / m) *
          (2 * a / α + 4) := hnum
      _ = _ := by ring
  apply (hbase.trans ?_).trans_lt
    (hbudget m ((le_max_left m₀ 1).trans hm) a ha haε)
  dsimp [u, r]
  linarith

/-- Uniform thresholds for the complete family of actual block budgets.
The number of ordinary vertices may be linear in the order; the special
set and the number of block labels have fixed bounds. -/
theorem exists_uniform_block_budget
    (β pmin cmin Mmin rowBound : ℝ) (specialBound labelBound : ℕ)
    (hβ : 0 < β) (hpmin : 0 < pmin) (hcmin : 0 < cmin)
    (hMmin : 0 < Mmin) (hrow : 0 ≤ rowBound) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ m₀ : ℕ, 1 ≤ m₀ ∧
      ∀ m : ℕ, m₀ ≤ m → ∀ a : ℝ, 0 ≤ a → a ≤ ε * m →
        ∀ (V : Type u) (E : Type v) [Fintype E]
          (γ : Type w) [Fintype γ] (G : Multigraph V E)
          (B U Wo Ws Zcorr : Finset V) (p : γ → ℝ),
          (Wo.card : ℝ) ≤ rowBound * m → Ws.card ≤ specialBound →
          Fintype.card γ ≤ labelBound → (∀ j, pmin ≤ p j) →
          (∀ x ∈ Wo, cmin * m ≤ (G.edgesTo x U).card) →
          (∀ x ∈ Ws, cmin * m ≤ (G.edgesTo x U).card) →
          Mmin * m ≤ (correctionPool G B Zcorr).card →
          (∑ j, BlockSelectionBudget.failureBudget G B U Wo Ws Zcorr β (p j) a) < 1 := by
  let u : ℝ := labelBound * rowBound
  let v : ℝ := labelBound * (18 * specialBound / (pmin * cmin) +
    (2 : ℝ)^21 / (pmin^3 * Mmin))
  let r : ℝ := β * pmin * cmin / 48
  obtain ⟨ε, hε, m₀, hbudget⟩ := FiniteProbability.exists_uniform_failure_budget
    u v 0 r (by dsimp [u]; positivity) (by dsimp [v]; positivity)
    (by norm_num) (by dsimp [r]; positivity)
  refine ⟨ε, hε, max m₀ 1, le_max_right _ _, ?_⟩
  intro m hm a ha haε V E _ γ _ G B U Wo Ws Zcorr p
    hrows hspecials hlabels hp hordinary hspecial hpool
  have hmpos : (0 : ℝ) < m := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one ((le_max_right m₀ 1).trans hm))
  have hbase := block_family_budget_le_scaled G B U Wo Ws Zcorr β a m pmin cmin Mmin
    rowBound specialBound labelBound p hβ.le ha hmpos hpmin hcmin hMmin hrow
    (Nat.cast_nonneg _) hp hordinary hspecial hpool hrows
    (by exact_mod_cast hspecials) (by exact_mod_cast hlabels)
  apply hbase.trans_lt
  simpa only [u, v, r, zero_div, add_zero] using
    hbudget m ((le_max_left m₀ 1).trans hm) a ha haε

end Overfull.BipartiteFactorization.UniformBudgets
