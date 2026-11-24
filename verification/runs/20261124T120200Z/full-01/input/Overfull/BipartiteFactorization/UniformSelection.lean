import Overfull.BipartiteFactorization.UniformBudgets
import Overfull.BipartiteFactorization.LocalizationBounds

/-!
# Uniform simultaneous palette and block constructions

The small error and the order threshold precede the graph.  The active-row
and large-pool thresholds are exactly the manuscript thresholds `θ*k` and
`θ*k/65536`.  Numerical failure budgets, positivity conditions, and the
integer cap interval are derived internally from those graph bounds.
-/

noncomputable section

namespace Overfull.BipartiteFactorization.UniformSelection

open Finset Classical UniformBudgets

universe u v w t

/-- Normalize the actual per-color copy bound using the linear degree
bound.  The graph-specific quotient does not survive in the coefficients. -/
theorem color_copy_bound (α m k a : ℝ) (hα : 0 < α) (hm : 0 < m)
    (ha : 0 ≤ a) (hk : α * m ≤ k) :
    2 * m * a / k + 4 ≤ 2 * a / α + 4 := by
  have hkpos : 0 < k := (mul_pos hα hm).trans_le hk
  apply add_le_add_right
  apply (div_le_iff₀ hkpos).mpr
  have h := mul_le_mul_of_nonneg_left hk (show 0 ≤ 2 * a / α by positivity)
  calc
    2 * m * a = (2 * a / α) * (α * m) := by field_simp
    _ ≤ (2 * a / α) * k := h

/-- Construct all prescribed disjoint palettes with one uniform error and
order threshold.  Only actual graph, color, row, pool and size bounds are
assumed; the full finite failure budget is proved inside the theorem.
The pool family lists the large pools. Small pools have their colors
excluded separately, as in the manuscript. -/
theorem exists_uniform_palettes (α θ lammin : ℝ) (poolBound labelBound : ℕ)
    (hα : 0 < α) (hθ : 0 < θ) (hlammin : 0 < lammin) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ m₀ : ℕ, 1 ≤ m₀ ∧
      ∀ m : ℕ, m₀ ≤ m → ∀ a : ℝ, 0 ≤ a → a ≤ ε * m →
        ∀ (V : Type u) (E : Type v) [Fintype E]
          (κ : Type w) [Fintype κ] (ι : Type t) [Fintype ι]
          (G : Multigraph V E) (k : ℕ) (c : G.EdgeColoring k)
          (C : Finset (Fin k)) (U Z : Finset V) (P : κ → Finset E) (s : ι → ℕ),
          α * m ≤ (k : ℝ) → (Z.card : ℝ) ≤ ε * m →
          Fintype.card κ ≤ poolBound → Fintype.card ι ≤ labelBound →
          (32 / 33 : ℝ) * k ≤ C.card →
          (∀ x ∈ Z, (31 / 32 : ℝ) * (G.edgesTo x U).card ≤
            (colorsOn c (G.edgesTo x U) ∩ C).card) →
          (∑ i, s i) ≤ C.card → (∀ i, lammin ≤ (s i : ℝ) / k) →
          (∀ x ∈ Z, θ * k ≤ (G.edgesTo x U).card) →
          (∀ j, θ * k / 65536 ≤ (P j).card) →
          (∀ j i, i ∈ C → PaletteSampling.poolColorWeight c (P j) i ≤
            2 * m * a / k + 4) →
          ∃ I : ι → Finset (Fin k),
            (∀ i, I i ⊆ C) ∧ (∀ i, (I i).card = s i) ∧
            (∀ i j, i ≠ j → Disjoint (I i) (I j)) ∧
            ∀ i, SimultaneousPalettes.Good c U Z P (s i) (I i) := by
  obtain ⟨ε₀, hε₀, m₀, hm₀, hbudget⟩ := exists_uniform_palette_budget
    α lammin (θ * α) (θ * α / 65536) 1 poolBound labelBound
    hα hlammin (by positivity) (by positivity) (by norm_num)
  let ε : ℝ := min ε₀ 1
  have hε : 0 < ε := lt_min hε₀ (by norm_num)
  have hε₀le : ε ≤ ε₀ := min_le_left _ _
  have hε1 : ε ≤ 1 := min_le_right _ _
  refine ⟨ε, hε, m₀, hm₀, ?_⟩
  intro m hm a ha haε V E _ κ _ ι _ G k c C U Z P s
    hk hZ hκ hι hC hretained hsum hlam hactive hlarge hcolor
  have hmpos : (0 : ℝ) < m := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (hm₀.trans hm))
  have hkpos : (0 : ℝ) < k := (mul_pos hα hmpos).trans_le hk
  have hkNat : 0 < k := by exact_mod_cast hkpos
  have hrows : (Z.card : ℝ) ≤ 1 * m :=
    hZ.trans (mul_le_mul_of_nonneg_right hε1 hmpos.le)
  have hc : ∀ x ∈ Z, (θ * α) * m ≤ (G.edgesTo x U).card := by
    intro x hx
    calc
      _ = θ * (α * m) := by ring
      _ ≤ θ * k := mul_le_mul_of_nonneg_left hk hθ.le
      _ ≤ _ := hactive x hx
  have hM : ∀ j, (θ * α / 65536) * m ≤ (P j).card := by
    intro j
    calc
      _ = θ * (α * m) / 65536 := by ring
      _ ≤ θ * k / 65536 := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hk hθ.le) (by norm_num)
      _ ≤ _ := hlarge j
  have hspos : ∀ i, 0 < s i := by
    intro i
    by_contra hn
    have hs : s i = 0 := Nat.eq_zero_of_not_pos hn
    have h := hlam i
    simp only [hs, Nat.cast_zero, zero_div] at h
    exact (not_le_of_gt hlammin) h
  let b : ℝ := 2 * m * a / k + 4
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hfailure := hbudget m hm a b ha
    (haε.trans (mul_le_mul_of_nonneg_right hε₀le hmpos.le)) hb
    (color_copy_bound α m k a hα hmpos ha hk)
    V E κ ι G k c U Z P s hrows hκ hι hlam hc hM
  exact SimultaneousPalettes.exists_simultaneous_palettes c C U Z P b s
    hsum hspos hkNat hC hretained hb hcolor hfailure

/-- Construct all actual blocks and preserve every supplied position
relation with uniform constants.  The caps are actual natural-number
floors; their intervals and all small-error conditions are derived here.
This interface treats a large correction pool, as required by the score
application; it does not assume any probability or failure-budget bound. -/
theorem exists_uniform_blocks (α θ β pmin lammin : ℝ)
    (specialBound labelBound : ℕ) (hα : 0 < α) (hθ : 0 < θ)
    (hβ : 0 < β) (hpmin : 0 < pmin) (hlammin : 0 < lammin) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ m₀ : ℕ, 1 ≤ m₀ ∧
      ∀ m : ℕ, m₀ ≤ m → ∀ a : ℝ, 0 ≤ a → a ≤ ε * m →
        ∀ (V : Type u) (E : Type v) [Fintype E]
          (ι : Type w) [Fintype ι] (γ : Type t) [Fintype γ]
          (G : Multigraph V E) (k : ℕ) (D : ι → Finset V)
          (B U Wo Ws Zcorr : Finset V) (S : γ → ∀ i, Finset (D i))
          (F : V → Finset E) (p lam : γ → ℝ),
          α * m ≤ (k : ℝ) → (Wo.card : ℝ) ≤ ε * m →
          Ws.card ≤ specialBound → Fintype.card γ ≤ labelBound →
          (∀ i j, i ≠ j → Disjoint (D i) (D j)) → univ.biUnion D = B →
          Disjoint B Zcorr → (∀ j, pmin ≤ p j) → (∀ j, p j ≤ 1) →
          (∀ j, lammin ≤ lam j) →
          (∀ j i, ((S j i).card : ℝ) = p j * (D i).card) →
          (∀ j i, (D i).Nonempty → 2 ≤ (S j i).card) →
          (∀ v ∈ B, (G.degree v : ℝ) ≤ a) →
          (∀ x ∈ Wo, F x ⊆ G.edgesTo x B) →
          (∀ x ∈ Wo, Set.InjOn (G.otherEnd x) (F x)) →
          (∀ x ∈ Wo, β * (G.edgesTo x U).card / 4 ≤ (F x).card) →
          (∀ x ∈ Wo, θ * k ≤ (G.edgesTo x U).card) →
          (∀ x ∈ Ws, θ * k ≤ (G.edgesTo x U).card) →
          (∀ x ∈ Ws, ((G.edgesTo x U).card : ℝ) / 2 ≤ (G.edgesTo x B).card) →
          (∀ x ∈ Zcorr, θ * k ≤ (G.edgesTo x U).card) →
          (∀ x ∈ Zcorr, ((G.edgesTo x B).card : ℝ) ≤ (G.edgesTo x U).card / 2) →
          θ * k / 65536 ≤ (correctionPool G B Zcorr).card →
          ∃ T : γ → Finset V, SimultaneousBlocks.RealizesPositions D B S T ∧
            ∀ j, BlockSelectionBudget.GoodBlock G B U Wo Ws Zcorr F β (p j) (lam j)
              (fun x => (⌊(15 / 16 : ℝ) * lam j * (G.edgesTo x U).card⌋₊ : ℝ))
              (T j) := by
  let cmin : ℝ := θ * α
  have hcmin : 0 < cmin := mul_pos hθ hα
  obtain ⟨ε₀, hε₀, m₀, hm₀, hbudget⟩ := exists_uniform_block_budget
    β pmin cmin (cmin / 65536) 1 specialBound labelBound
    hβ hpmin hcmin (by positivity) (by norm_num)
  obtain ⟨m₁, hcaps⟩ := LocalizationBounds.exists_uniform_floor_caps lammin cmin hlammin hcmin
  let ε : ℝ := min ε₀ (min 1 (pmin * cmin / 4096))
  have hε : 0 < ε := lt_min hε₀ (lt_min (by norm_num) (by positivity))
  have hε₀le : ε ≤ ε₀ := min_le_left _ _
  have hε1 : ε ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hεsmall : ε ≤ pmin * cmin / 4096 :=
    (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ε, hε, max m₀ m₁, hm₀.trans (le_max_left _ _), ?_⟩
  intro m hm a ha haε V E _ ι _ γ _ G k D B U Wo Ws Zcorr S F p lam
    hk hWo hWs hγ hdisj hcover hBZ hp hp1 hlam hfraction hselect hdegree hF hinj hFsize
    hordinary hspecial hspecial_side hcorr hdc hlarge
  have hm₀' : m₀ ≤ m := (le_max_left _ _).trans hm
  have hm₁' : m₁ ≤ m := (le_max_right _ _).trans hm
  have hmpos : (0 : ℝ) < m := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (hm₀.trans hm₀'))
  have hscaled (x : V) (hx : θ * k ≤ (G.edgesTo x U).card) :
      cmin * m ≤ (G.edgesTo x U).card := by
    calc
      _ = θ * (α * m) := by dsimp [cmin]; ring
      _ ≤ θ * k := mul_le_mul_of_nonneg_left hk hθ.le
      _ ≤ _ := hx
  have hpool : cmin / 65536 * m ≤ (correctionPool G B Zcorr).card := by
    calc
      _ = θ * (α * m) / 65536 := by dsimp [cmin]; ring
      _ ≤ θ * k / 65536 := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hk hθ.le) (by norm_num)
      _ ≤ _ := hlarge
  have hMreal : (0 : ℝ) < (correctionPool G B Zcorr).card :=
    (show 0 < cmin / 65536 * m by positivity).trans_le hpool
  have hM : 0 < (correctionPool G B Zcorr).card := by exact_mod_cast hMreal
  have hcap (j : γ) (x : V) (hx : x ∈ Zcorr) :=
    hcaps m hm₁' (lam j) (G.edgesTo x U).card (hlam j) (hscaled x (hcorr x hx))
  have hasmall (j : γ) (x : V) (hx : x ∈ Zcorr) :
      a ≤ p j * (G.edgesTo x U).card / 4096 := by
    have hp0 : 0 ≤ p j := hpmin.le.trans (hp j)
    have hprod := mul_le_mul (hp j) (hscaled x (hcorr x hx))
      (mul_nonneg hcmin.le hmpos.le) hp0
    calc
      a ≤ ε * m := haε
      _ ≤ (pmin * cmin / 4096) * m :=
        mul_le_mul_of_nonneg_right hεsmall hmpos.le
      _ = pmin * (cmin * m) / 4096 := by ring
      _ ≤ p j * (G.edgesTo x U).card / 4096 :=
        div_le_div_of_nonneg_right hprod (by norm_num)
  have hfailure := hbudget m hm₀' a ha
    (haε.trans (mul_le_mul_of_nonneg_right hε₀le hmpos.le)) V E γ G B U Wo Ws Zcorr p
    (hWo.trans (mul_le_mul_of_nonneg_right hε1 hmpos.le)) hWs hγ hp
    (fun x hx => hscaled x (hordinary x hx))
    (fun x hx => hscaled x (hspecial x hx)) hpool
  exact SimultaneousBlocks.exists_good_blocks G D hdisj B U Wo Ws Zcorr hcover hBZ
    S F β a p lam (fun j => hpmin.trans_le (hp j)) hp1
    (fun j => hlammin.trans_le (hlam j)) ha hfraction hselect hdegree hF hinj hFsize
    (fun x hx => (mul_pos hcmin hmpos).trans_le (hscaled x (hspecial x hx))) hspecial_side
    (fun j x => (⌊(15 / 16 : ℝ) * lam j * (G.edgesTo x U).card⌋₊ : ℝ))
    (fun x hx => (mul_pos hcmin hmpos).trans_le (hscaled x (hcorr x hx))) hdc
    (fun j x hx => (hcap j x hx).1) (fun j x hx => (hcap j x hx).2)
    hasmall hM hfailure

end Overfull.BipartiteFactorization.UniformSelection
