import Overfull.ColoringExtension.Uniform
import Overfull.ColoringExtension.Deficits

/-!
# Uniform near-perfect internal color classes

A simple graph with linear minimum degree and a small degree spread can
be colored compatibly with fixed small exterior footprints so that every
class, and every vertex, has a small actual uncovered deficit. The order
threshold absorbs the two integral rounding units.
-/

namespace Overfull.ColoringExtension

open Finset Classical
open Multigraph

/-- Choose the slack and constraint tolerances before the graph. The
constructed coloring has at most twice the order many colors; every fixed
footprint, uncovered class, and per-vertex missing-color set is small. -/
theorem exists_uniform_near_perfect_coloring (ζ η : ℝ)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hη : 0 < η) :
    ∃ κ ε : ℝ, 0 < κ ∧ κ ≤ 1 / 4 ∧ κ ≤ ζ / 64 ∧
      0 < ε ∧ ε ≤ η ∧ ∃ n₀ : ℕ,
      ∀ (V : Type*) [Fintype V] (J : SimpleGraph V) [DecidableRel J.Adj],
        n₀ ≤ Fintype.card V →
        (∀ v, ζ * Fintype.card V ≤ (J.degree v : ℝ)) →
        (∀ v, (J.maxDegree : ℝ) - J.degree v ≤ κ * Fintype.card V) →
        let h := J.maxDegree + 1 + Nat.ceil (κ * Fintype.card V)
        ∀ F : Fin h → Finset V,
          (∀ i, ((F i).card : ℝ) ≤ ε * Fintype.card V) →
          (∀ v, ((forbiddenColors F v).card : ℝ) ≤ ε * Fintype.card V) →
          h ≤ 2 * Fintype.card V ∧
          ∃ c : (Multigraph.ofSimpleGraph J).EdgeColoring h,
            c.AvoidsVertices F ∧
            (∀ i, ((F i).card : ℝ) ≤ η * Fintype.card V) ∧
            (∀ i, ((c.uncoveredVertices i).card : ℝ) ≤ η * Fintype.card V) ∧
            (∀ v, ((c.missingColors v).card : ℝ) ≤ η * Fintype.card V) ∧
            (∀ i, ((c.repairVertices F i).card : ℝ) ≤ η * Fintype.card V) ∧
            (∀ v, ((univ.filter (fun i => v ∈ c.repairVertices F i)).card : ℝ) ≤
              η * Fintype.card V) := by
  classical
  let κ := min (ζ / 64) (min (1 / 4 : ℝ) (ζ * η / 64))
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hκζ : κ ≤ ζ / 64 := min_le_left _ _
  have hκ1 : κ ≤ 1 / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hκζη : κ ≤ ζ * η / 64 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨ε₀, hε₀, nColor, hColor⟩ := exists_uniform_simple_balanced_avoiding κ hκ
  let ε := min ε₀ (η / 64)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hε₀' : ε ≤ ε₀ := min_le_left _ _
  have hεη : ε ≤ η / 64 := min_le_right _ _
  have hεη' : ε ≤ η := by linarith only [hεη, hη]
  obtain ⟨nRound, hnRound⟩ := exists_nat_gt (max (4 : ℝ) (max (16 / (ζ * η)) (16 / η)))
  refine ⟨κ, ε, hκ, hκ1, hκζ, hε, hεη', max nColor nRound, ?_⟩
  intro V _ J _ hn hmin hspread
  dsimp only
  intro F hF hload
  let n := Fintype.card V
  let h := J.maxDegree + 1 + Nat.ceil (κ * n)
  let f := Nat.floor (ε * n)
  have hnC : nColor ≤ n := (le_max_left _ _).trans hn
  have hnR : max (4 : ℝ) (max (16 / (ζ * η)) (16 / η)) < n :=
    hnRound.trans_le (by exact_mod_cast (le_max_right nColor nRound).trans hn)
  have hn4 : (4 : ℝ) < n := (le_max_left _ _).trans_lt hnR
  have hn0 : (0 : ℝ) < n := by linarith only [hn4]
  have hn0N : 0 < n := by exact_mod_cast hn0
  have hζηn : 16 < ζ * η * n := by
    have hh : 16 / (ζ * η) < n :=
      (le_trans (le_max_left _ _) (le_max_right _ _)).trans_lt hnR
    have ht := (div_lt_iff₀ (mul_pos hζ hη)).mp hh
    nlinarith only [ht]
  have hηn : 16 < η * n := by
    have hh : 16 / η < n :=
      (le_trans (le_max_right _ _) (le_max_right _ _)).trans_lt hnR
    have ht := (div_lt_iff₀ hη).mp hh
    nlinarith only [ht]
  have hf : (f : ℝ) ≤ ε * n := Nat.floor_le (by positivity)
  have hFn : ∀ i, (F i).card ≤ f := fun i => Nat.le_floor (hF i)
  obtain ⟨c, hc, hcspread⟩ := hColor V J hnC F f hFn (by
    intro v
    exact (hload v).trans (mul_le_mul_of_nonneg_right hε₀' hn0.le))
  have hceil : (Nat.ceil (κ * n) : ℝ) < κ * n + 1 := Nat.ceil_lt_add_one (by positivity)
  have hmax : J.maxDegree ≤ n := J.maxDegree_le_of_forall_degree_le n (by
    intro v
    exact (J.degree_lt_card_verts v).le)
  have hhupper : h ≤ 2 * n := by
    have hmaxR : (J.maxDegree : ℝ) ≤ n := by exact_mod_cast hmax
    have hκn := mul_le_mul_of_nonneg_right hκ1 hn0.le
    have hh : (h : ℝ) = J.maxDegree + 1 + (Nat.ceil (κ * n) : ℝ) := by
      simp only [h, Nat.cast_add, Nat.cast_one]
    have hr : (h : ℝ) ≤ 2 * n := by linarith only [hmaxR, hκn, hceil, hh, hn4]
    exact_mod_cast hr
  have hhposN : 0 < h := by dsimp [h]; omega
  have hhpos : (0 : ℝ) < h := by exact_mod_cast hhposN
  have hhlower : ζ * n ≤ (h : ℝ) := by
    obtain ⟨v⟩ := Fintype.card_pos_iff.mp hn0N
    have hv := hmin v
    have hvmax : (J.degree v : ℝ) ≤ J.maxDegree := by exact_mod_cast J.degree_le_maxDegree v
    have hh : (J.maxDegree : ℝ) ≤ h := by
      exact_mod_cast (show J.maxDegree ≤ h by dsimp [h]; omega)
    exact hv.trans (hvmax.trans hh)
  let D : ℝ := κ * n + 1 + Nat.ceil (κ * n)
  have hD : D ≤ ζ * η * n / 4 := by
    have hκn := mul_le_mul_of_nonneg_right hκζη hn0.le
    dsimp [D]
    nlinarith only [hceil, hκn, hζηn]
  have hDη : D ≤ η * n := by
    have hh := mul_le_mul_of_nonneg_right hζ1 (mul_nonneg hη.le hn0.le)
    nlinarith only [hD, hh, hηn]
  have hDh : D ≤ η * h / 4 := by
    have hh := mul_le_mul_of_nonneg_left hhlower (div_nonneg hη.le (by norm_num : (0 : ℝ) ≤ 4))
    nlinarith only [hD, hh]
  have hdegree : ∀ v, (h : ℝ) - D ≤ (Multigraph.ofSimpleGraph J).degree v := by
    intro v
    rw [Multigraph.ofSimpleGraph_degree]
    have hv := hspread v
    dsimp [h, D]
    simp only [Nat.cast_add, Nat.cast_one]
    linarith only [hv]
  have hfsmall : (f : ℝ) + 1 ≤ η * n / 8 := by
    have hh := mul_le_mul_of_nonneg_right hεη hn0.le
    nlinarith only [hf, hh, hηn]
  have hsize (i : Fin h) : ((c.uncoveredVertices i).card : ℝ) ≤ η * n := by
    have hs := c.uncovered_scaled_bound f hcspread D hdegree i
    have hmD := mul_le_mul_of_nonneg_left hDh hn0.le
    have hmf := mul_le_mul_of_nonneg_left hfsmall (show 0 ≤ (2 : ℝ) * h by positivity)
    have hh : (h : ℝ) * (c.uncoveredVertices i).card ≤ (h : ℝ) * (η * n) := by
      change (h : ℝ) * (c.uncoveredVertices i).card ≤ n * D + 2 * h * ((f : ℝ) + 1) at hs
      have hnonneg : (0 : ℝ) ≤ h * (η * n) := by positivity
      nlinarith only [hs, hmD, hmf, hnonneg]
    exact (mul_le_mul_iff_right₀ hhpos).mp hh
  refine ⟨hhupper, c, hc, ?_, hsize, ?_, ?_, ?_⟩
  · intro i
    exact (hF i).trans (mul_le_mul_of_nonneg_right hεη' hn0.le)
  · intro v
    exact (c.missingColors_card_le_error D hdegree v).trans hDη
  · intro i
    have hh : ((c.repairVertices F i).card : ℝ) ≤ (c.uncoveredVertices i).card := by
      exact_mod_cast c.repairVertices_card_le_uncovered F i
    exact hh.trans (hsize i)
  · intro v
    exact (c.repairVertices_incidence_le_error F D hdegree v).trans hDη

end Overfull.ColoringExtension
