import Overfull.BipartiteFactorization.PaletteRowTails

/-!
# Simultaneous actual palettes with explicit failure budgets

Row and pool failure bounds are derived from the graph and combined before
applying the disjoint permutation-sampling construction. The public existence
theorem assumes a numerical sum below one, not the desired probability bounds.
-/

noncomputable section

namespace Overfull.BipartiteFactorization.SimultaneousPalettes

open Finset Classical PaletteSampling PaletteBudgets PaletteRowTails

variable {V E : Type*} [Fintype E] {G : Multigraph V E} {k : ℕ}
variable {κ : Type*} [Fintype κ]

/-- Count the actual original copies in a selected palette and a specified pool. -/
def selectedCount (c : G.EdgeColoring k) (I : Finset (Fin k)) (P : Finset E) : ℝ :=
  (paletteEdges c I ∩ P).card

def rowBad (c : G.EdgeColoring k) (U : Finset V) (s : ℕ)
    (I : Finset (Fin k)) (x : V) : Prop :=
  selectedCount c I (G.edgesTo x U) <
      (15 / 16 : ℝ) * ((s : ℝ) / k) * (G.edgesTo x U).card ∨
  2 * ((s : ℝ) / k) * (G.edgesTo x U).card < selectedCount c I (G.edgesTo x U)

def poolBad (c : G.EdgeColoring k) (P : Finset E) (s : ℕ)
    (I : Finset (Fin k)) : Prop :=
  (5 / 4 : ℝ) * ((s : ℝ) / k) * P.card < selectedCount c I P

def bad (c : G.EdgeColoring k) (U Z : Finset V) (P : κ → Finset E)
    (s : ℕ) (I : Finset (Fin k)) : Prop :=
  (∃ x ∈ Z, rowBad c U s I x) ∨ ∃ j, poolBad c (P j) s I

/-- A single numerical budget covers all active rows and all correction pools. -/
def failureBudget (_c : G.EdgeColoring k) (U Z : Finset V)
    (P : κ → Finset E) (B : ℝ) (s : ℕ) : ℝ :=
  (∑ x ∈ Z, 2 * Real.exp (-((s : ℝ) / k) * (G.edgesTo x U).card / 4096)) +
    ∑ j, 32 * B / (((s : ℝ) / k) * (P j).card)

/-- The actual row and correction-pool inequalities needed by palette selection. -/
def Good (c : G.EdgeColoring k) (U Z : Finset V) (P : κ → Finset E)
    (s : ℕ) (I : Finset (Fin k)) : Prop :=
  (∀ x ∈ Z,
    (15 / 16 : ℝ) * ((s : ℝ) / k) * (G.edgesTo x U).card ≤
        selectedCount c I (G.edgesTo x U) ∧
    selectedCount c I (G.edgesTo x U) ≤
        2 * ((s : ℝ) / k) * (G.edgesTo x U).card) ∧
  ∀ j, selectedCount c I (P j) ≤ (5 / 4 : ℝ) * ((s : ℝ) / k) * (P j).card

omit [Fintype κ] in
theorem not_bad_iff_good (c : G.EdgeColoring k) (U Z : Finset V)
    (P : κ → Finset E) (s : ℕ) (I : Finset (Fin k)) :
    ¬ bad c U Z P s I ↔ Good c U Z P s I := by
  simp only [bad, Good, rowBad, poolBad, not_or, not_exists, not_and, not_lt]

/-- Every probability estimate in the union bound is supplied by an actual
row or pool theorem, including an empty correction pool. -/
theorem probability_bad_le (c : G.EdgeColoring k) (C : Finset (Fin k))
    (U Z : Finset V) (P : κ → Finset E) (B : ℝ) (s : ℕ)
    (hs : s ≤ C.card) (hspos : 0 < s) (hk : 0 < k)
    (hC : (32 / 33 : ℝ) * k ≤ C.card)
    (hretained : ∀ x ∈ Z, (31 / 32 : ℝ) * (G.edgesTo x U).card ≤
      (colorsOn c (G.edgesTo x U) ∩ C).card)
    (hB : 0 ≤ B) (hcolor : ∀ j i, i ∈ C → poolColorWeight c (P j) i ≤ B) :
    Hypergeometric.probability s (fun T : Finset C => bad c U Z P s (liftPalette C T)) ≤
      failureBudget c U Z P B s := by
  have hrows : Hypergeometric.probability s
      (fun T : Finset C => ∃ x ∈ Z, rowBad c U s (liftPalette C T) x) ≤
      ∑ x ∈ Z, 2 * Real.exp (-((s : ℝ) / k) * (G.edgesTo x U).card / 4096) := by
    calc
      _ ≤ ∑ x ∈ Z, Hypergeometric.probability s
          (fun T : Finset C => rowBad c U s (liftPalette C T) x) :=
        MatchingProbability.probability_exists_le_sum _ (Hypergeometric.weight_nonneg s)
          Z (fun x T => rowBad c U s (liftPalette C T) x)
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro x hx
        simpa only [rowBad, selectedCount, poolDemand] using
          palette_row_tail c C U x s hs hk hC (hretained x hx)
  have hpools : Hypergeometric.probability s
      (fun T : Finset C => ∃ j, poolBad c (P j) s (liftPalette C T)) ≤
      ∑ j, 32 * B / (((s : ℝ) / k) * (P j).card) := by
    have hu := MatchingProbability.probability_exists_le_sum
      (Hypergeometric.weight (E := C) s) (Hypergeometric.weight_nonneg s)
      univ (fun j T => poolBad c (P j) s (liftPalette C T))
    have hu' : Hypergeometric.probability s
        (fun T : Finset C => ∃ j, poolBad c (P j) s (liftPalette C T)) ≤
        ∑ j, Hypergeometric.probability s
          (fun T : Finset C => poolBad c (P j) s (liftPalette C T)) := by
      simpa only [Hypergeometric.probability, mem_univ, true_and] using hu
    apply hu'.trans
    apply Finset.sum_le_sum
    intro j _
    simpa only [poolBad, selectedCount, poolDemand] using
      poolDemand_upper_tail_all c C (P j) s hs hk hC hspos B hB (hcolor j)
  unfold bad failureBudget
  exact (MatchingProbability.probability_union_le _ (Hypergeometric.weight_nonneg s)
    (fun T : Finset C => ∃ x ∈ Z, rowBad c U s (liftPalette C T) x)
    (fun T : Finset C => ∃ j, poolBad c (P j) s (liftPalette C T))).trans
      (add_le_add hrows hpools)

/-- Construct all actual disjoint palettes simultaneously from a numerical
budget on graph data. Independence between the palettes is not assumed. -/
theorem exists_simultaneous_palettes {ι : Type*} [Fintype ι]
    (c : G.EdgeColoring k) (C : Finset (Fin k)) (U Z : Finset V)
    (P : κ → Finset E) (B : ℝ) (n : ι → ℕ)
    (hn : (∑ i, n i) ≤ C.card) (hnpos : ∀ i, 0 < n i) (hk : 0 < k)
    (hC : (32 / 33 : ℝ) * k ≤ C.card)
    (hretained : ∀ x ∈ Z, (31 / 32 : ℝ) * (G.edgesTo x U).card ≤
      (colorsOn c (G.edgesTo x U) ∩ C).card)
    (hB : 0 ≤ B) (hcolor : ∀ j i, i ∈ C → poolColorWeight c (P j) i ≤ B)
    (hbudget : (∑ i, failureBudget c U Z P B (n i)) < 1) :
    ∃ I : ι → Finset (Fin k),
      (∀ i, I i ⊆ C) ∧ (∀ i, (I i).card = n i) ∧
      (∀ i j, i ≠ j → Disjoint (I i) (I j)) ∧
      ∀ i, Good c U Z P (n i) (I i) := by
  have hsize (i : ι) : n i ≤ C.card := by
    exact (Finset.single_le_sum (fun j _ => Nat.zero_le (n j)) (mem_univ i)).trans hn
  obtain ⟨I, hsub, hcard, hdisj, hgood⟩ := exists_disjoint_allowed_palettes C n hn
    (fun i I => bad c U Z P (n i) I) (fun i => failureBudget c U Z P B (n i))
    (fun i => probability_bad_le c C U Z P B (n i) (hsize i) (hnpos i) hk hC
      hretained hB hcolor) hbudget
  exact ⟨I, hsub, hcard, hdisj, fun i =>
    (not_bad_iff_good c U Z P (n i) (I i)).mp (hgood i)⟩

/-- Uniform lower bounds on fractions, row sizes, and pool sizes give a
single explicit scalar sufficient for the complete palette failure budget. -/
theorem failureBudget_le_uniform (c : G.EdgeColoring k) (U Z : Finset V)
    (P : κ → Finset E) (B : ℝ) (s : ℕ) (lam0 c₀ M₀ : ℝ)
    (hlam0 : 0 < lam0) (hc₀ : 0 ≤ c₀) (hM₀ : 0 < M₀) (hB : 0 ≤ B)
    (hlam : lam0 ≤ (s : ℝ) / k)
    (hc : ∀ x ∈ Z, c₀ ≤ (G.edgesTo x U).card)
    (hM : ∀ j, M₀ ≤ (P j).card) :
    failureBudget c U Z P B s ≤
      2 * Z.card * Real.exp (-lam0 * c₀ / 4096) +
        Fintype.card κ * (32 * B / (lam0 * M₀)) := by
  have hs0 : 0 ≤ (s : ℝ) / k := hlam0.le.trans hlam
  have hrow (x : V) (hx : x ∈ Z) :
      2 * Real.exp (-((s : ℝ) / k) * (G.edgesTo x U).card / 4096) ≤
        2 * Real.exp (-lam0 * c₀ / 4096) := by
    have hp := mul_le_mul hlam (hc x hx) hc₀ hs0
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (by norm_num)
  have hpool (j : κ) : 32 * B / (((s : ℝ) / k) * (P j).card) ≤
      32 * B / (lam0 * M₀) := by
    have hp := mul_le_mul hlam (hM j) hM₀.le hs0
    exact div_le_div_of_nonneg_left (by positivity) (mul_pos hlam0 hM₀) hp
  calc
    _ ≤ (∑ _x ∈ Z, 2 * Real.exp (-lam0 * c₀ / 4096)) +
        ∑ _j : κ, 32 * B / (lam0 * M₀) := by
      exact add_le_add (Finset.sum_le_sum hrow) (Finset.sum_le_sum (fun j _ => hpool j))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

/-- The uniform scalar budget also produces the actual disjoint family. -/
theorem exists_simultaneous_palettes_of_uniform_budget {ι : Type*} [Fintype ι]
    (c : G.EdgeColoring k) (C : Finset (Fin k)) (U Z : Finset V)
    (P : κ → Finset E) (B : ℝ) (n : ι → ℕ)
    (hn : (∑ i, n i) ≤ C.card) (hnpos : ∀ i, 0 < n i) (hk : 0 < k)
    (hC : (32 / 33 : ℝ) * k ≤ C.card)
    (hretained : ∀ x ∈ Z, (31 / 32 : ℝ) * (G.edgesTo x U).card ≤
      (colorsOn c (G.edgesTo x U) ∩ C).card)
    (hB : 0 ≤ B) (hcolor : ∀ j i, i ∈ C → poolColorWeight c (P j) i ≤ B)
    (lam0 c₀ M₀ : ℝ) (hlam0 : 0 < lam0) (hc₀ : 0 ≤ c₀) (hM₀ : 0 < M₀)
    (hlam : ∀ i, lam0 ≤ (n i : ℝ) / k)
    (hc : ∀ x ∈ Z, c₀ ≤ (G.edgesTo x U).card)
    (hM : ∀ j, M₀ ≤ (P j).card)
    (hbudget : (Fintype.card ι : ℝ) *
      (2 * Z.card * Real.exp (-lam0 * c₀ / 4096) +
        Fintype.card κ * (32 * B / (lam0 * M₀))) < 1) :
    ∃ I : ι → Finset (Fin k),
      (∀ i, I i ⊆ C) ∧ (∀ i, (I i).card = n i) ∧
      (∀ i j, i ≠ j → Disjoint (I i) (I j)) ∧
      ∀ i, Good c U Z P (n i) (I i) := by
  apply exists_simultaneous_palettes c C U Z P B n hn hnpos hk hC hretained hB hcolor
  calc
    _ ≤ ∑ _i : ι, (2 * Z.card * Real.exp (-lam0 * c₀ / 4096) +
        Fintype.card κ * (32 * B / (lam0 * M₀))) := by
      apply Finset.sum_le_sum
      intro i _
      exact failureBudget_le_uniform c U Z P B (n i) lam0 c₀ M₀ hlam0 hc₀ hM₀ hB
        (hlam i) hc hM
    _ = (Fintype.card ι : ℝ) *
        (2 * Z.card * Real.exp (-lam0 * c₀ / 4096) +
          Fintype.card κ * (32 * B / (lam0 * M₀))) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ < 1 := hbudget

/-- Instantiate the simultaneous construction with the actual excluded-color
set; the retained-row hypotheses follow from the original exclusion count. -/
theorem exists_simultaneous_palettes_of_exclusions {ι : Type*} [Fintype ι]
    (c : G.EdgeColoring k) (U L Z : Finset V) (P₀ Q₀ : Finset E) (T : ℝ)
    (P : κ → Finset E) (B : ℝ) (n : ι → ℕ)
    (hn : (∑ i, n i) ≤ (allowedColors c U L P₀ Q₀ (T / 65536)).card)
    (hnpos : ∀ i, 0 < n i) (hk : 0 < k) (hTk : T ≤ k)
    (hexcluded : ((excludedColors c U L P₀ Q₀ (T / 65536)).card : ℝ) < T / 512)
    (hactive : ∀ x ∈ Z, T ≤ ((G.edgesTo x U).card : ℝ))
    (hB : 0 ≤ B)
    (hcolor : ∀ j i, i ∈ allowedColors c U L P₀ Q₀ (T / 65536) →
      poolColorWeight c (P j) i ≤ B)
    (hbudget : (∑ i, failureBudget c U Z P B (n i)) < 1) :
    ∃ I : ι → Finset (Fin k),
      (∀ i, I i ⊆ allowedColors c U L P₀ Q₀ (T / 65536)) ∧
      (∀ i, (I i).card = n i) ∧
      (∀ i j, i ≠ j → Disjoint (I i) (I j)) ∧
      ∀ i, Good c U Z P (n i) (I i) := by
  apply exists_simultaneous_palettes c _ U Z P B n hn hnpos hk _ _ hB hcolor hbudget
  · have hcard := allowedColors_card_lower c U L P₀ Q₀ T hexcluded
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    linarith
  · intro x hx
    have hret := active_core_colors_retained c U L P₀ Q₀ T x hexcluded (hactive x hx)
    have hc0 : (0 : ℝ) ≤ (G.edgesTo x U).card := Nat.cast_nonneg _
    linarith

end Overfull.BipartiteFactorization.SimultaneousPalettes
