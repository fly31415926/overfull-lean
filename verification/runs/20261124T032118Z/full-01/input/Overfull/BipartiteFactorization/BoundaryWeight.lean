import Overfull.BipartiteFactorization.LocalizationBounds

/-!
# Normalized boundary weights on original copies

Each correction pool contributes at most two to the total normalized
incidence weight, and each special row contributes at most one. A light
member of any disjoint cluster family therefore exists. The same weights
bound actual pool and special-row copies lost at any chosen boundary;
no independence of the boundary choice is required.
-/

noncomputable section

namespace Overfull.BipartiteFactorization.BoundaryWeight

open Finset Classical

variable {V E κ : Type*} [Fintype E] [Fintype κ]

/-- Normalized actual-copy incidences from pools and special rows. -/
def weight (G : Multigraph V E) (U : Finset V) (P : κ → Finset E)
    (Z : Finset V) (v : V) : ℝ :=
  (∑ j, ((G.restrictEdges (P j)).degree v : ℝ) / (P j).card) +
    ∑ x ∈ Z, ((G.parallelEdges v x).card : ℝ) / (G.edgesTo x U).card

/-- Every normalized incidence contribution is nonnegative. -/
theorem weight_nonneg (G : Multigraph V E) (U : Finset V) (P : κ → Finset E)
    (Z : Finset V) (v : V) : 0 ≤ weight G U P Z v := by
  unfold weight
  positivity

omit [Fintype κ] in
/-- Each original edge copy has at most two ends in a given finite set. -/
theorem pool_incidence_sum_le (G : Multigraph V E) (U : Finset V) (P : Finset E) :
    (∑ v ∈ U, ((G.restrictEdges P).degree v : ℝ)) ≤ 2 * P.card := by
  have hside (e : E) : sideIncidence G U e ≤ 2 := by
    unfold sideIncidence
    split_ifs <;> norm_num
  have hi : (∑ v ∈ U, ((G.restrictEdges P).degree v : ℤ)) ≤ 2 * (P.card : ℤ) := by
    rw [restricted_degree_sum G P U]
    calc
      _ ≤ ∑ _e ∈ P, (2 : ℤ) := sum_le_sum (fun e _ => hside e)
      _ = _ := by simp; ring
  exact_mod_cast hi

omit [Fintype κ] in
/-- A pool contributes at most two to the normalized mass; an empty pool
contributes zero and does not require an arbitrary nonzero denominator. -/
theorem normalized_pool_sum_le_two (G : Multigraph V E) (U : Finset V) (P : Finset E) :
    (∑ v ∈ U, ((G.restrictEdges P).degree v : ℝ) / P.card) ≤ 2 := by
  rw [← Finset.sum_div]
  by_cases hP : P.card = 0
  · simp [hP]
  · have hpos : (0 : ℝ) < P.card := by exact_mod_cast Nat.pos_of_ne_zero hP
    exact (div_le_iff₀ hpos).mpr (pool_incidence_sum_le G U P)

omit [Fintype κ] in
/-- A special row contributes at most one, with equality for a positive
core degree. The zero row contributes zero. -/
theorem normalized_row_sum_le_one (G : Multigraph V E) (U : Finset V) (x : V) :
    (∑ v ∈ U, ((G.parallelEdges v x).card : ℝ) / (G.edgesTo x U).card) ≤ 1 := by
  rw [← Finset.sum_div]
  have hs : (∑ v ∈ U, ((G.parallelEdges v x).card : ℝ)) = (G.edgesTo x U).card := by
    exact_mod_cast BlockSampling.sum_parallel_card G x U
  rw [hs]
  by_cases hx : (G.edgesTo x U).card = 0
  · simp [hx]
  · rw [div_self (by exact_mod_cast hx : ((G.edgesTo x U).card : ℝ) ≠ 0)]

/-- The complete normalized mass is bounded independently of graph order
and of the cardinalities of the positive pools and rows. -/
theorem total_weight_le (G : Multigraph V E) (U : Finset V) (P : κ → Finset E)
    (Z : Finset V) :
    (∑ v ∈ U, weight G U P Z v) ≤ 2 * Fintype.card κ + Z.card := by
  unfold weight
  rw [sum_add_distrib, sum_comm (s := U) (t := univ), sum_comm (s := U) (t := Z)]
  have hp := sum_le_sum (s := (univ : Finset κ))
    (fun j _ => normalized_pool_sum_le_two G U (P j))
  have hr := sum_le_sum (s := Z) (fun x _ => normalized_row_sum_le_one G U x)
  have hh := add_le_add hp hr
  simpa only [sum_const, card_univ, nsmul_eq_mul, mul_one, mul_comm] using hh

/-- A pool's normalized incidence is one of the nonnegative contributions
to the weight at an actual vertex. -/
theorem pool_contribution_le (G : Multigraph V E) (U : Finset V) (P : κ → Finset E)
    (Z : Finset V) (j : κ) (v : V) :
    ((G.restrictEdges (P j)).degree v : ℝ) / (P j).card ≤ weight G U P Z v := by
  unfold weight
  have h : ((G.restrictEdges (P j)).degree v : ℝ) / (P j).card ≤
      ∑ l, ((G.restrictEdges (P l)).degree v : ℝ) / (P l).card :=
    single_le_sum (f := fun l => ((G.restrictEdges (P l)).degree v : ℝ) / (P l).card)
      (fun _ _ => by positivity) (mem_univ j)
  exact h.trans (le_add_of_nonneg_right (by positivity))

/-- The same bound applies to every indexed special row. -/
theorem row_contribution_le (G : Multigraph V E) (U : Finset V) (P : κ → Finset E)
    (Z : Finset V) (x : V) (hx : x ∈ Z) (v : V) :
    ((G.parallelEdges v x).card : ℝ) / (G.edgesTo x U).card ≤ weight G U P Z v := by
  unfold weight
  have h : ((G.parallelEdges v x).card : ℝ) / (G.edgesTo x U).card ≤
      ∑ y ∈ Z, ((G.parallelEdges v y).card : ℝ) / (G.edgesTo y U).card :=
    single_le_sum (f := fun y => ((G.parallelEdges v y).card : ℝ) / (G.edgesTo y U).card)
      (fun _ _ => by positivity) hx
  exact h.trans (le_add_of_nonneg_left (by positivity))

/-- Nonnegative weights cannot increase when vertices are discarded. -/
theorem sum_weight_mono (G : Multigraph V E) (U : Finset V) (P : κ → Finset E)
    (Z Y Y' : Finset V) (hsub : Y' ⊆ Y) :
    (∑ v ∈ Y', weight G U P Z v) ≤ ∑ v ∈ Y, weight G U P Z v :=
  sum_le_sum_of_subset_of_nonneg hsub (fun v _ _ => weight_nonneg G U P Z v)

/-- An actual disjoint family of clusters contained in the core has a
member with normalized mass at most the total budget divided by its size. -/
theorem exists_light_cluster {ι : Type*} [Fintype ι] [Nonempty ι]
    (G : Multigraph V E) (U : Finset V) (P : κ → Finset E) (Z : Finset V)
    (D : ι → Finset V) (hsub : ∀ i, D i ⊆ U)
    (hdisj : ∀ i j, i ≠ j → Disjoint (D i) (D j)) :
    ∃ i, (∑ v ∈ D i, weight G U P Z v) ≤
      (2 * (Fintype.card κ : ℝ) + Z.card) / Fintype.card ι := by
  have hU : univ.biUnion D ⊆ U := by
    intro v hv
    obtain ⟨i, _, hi⟩ := mem_biUnion.mp hv
    exact hsub i hi
  have hmass : (∑ i, ∑ v ∈ D i, weight G U P Z v) ≤
      2 * (Fintype.card κ : ℝ) + Z.card := by
    rw [← Finset.sum_biUnion (fun i _ j _ hij => hdisj i j hij)]
    exact (sum_weight_mono G U P Z U _ hU).trans (total_weight_le G U P Z)
  have hcount : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hcompare : (∑ i, ∑ v ∈ D i, weight G U P Z v) ≤
      ∑ _i : ι, (2 * (Fintype.card κ : ℝ) + Z.card) / Fintype.card ι := by
    simpa only [sum_const, card_univ, nsmul_eq_mul, mul_div_cancel₀ _ hcount] using hmass
  obtain ⟨i, _, hi⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hcompare
  exact ⟨i, hi⟩

omit [Fintype κ] in
/-- Every deleted pool copy is charged to at least one of its actual
boundary endpoints, even when both endpoints lie on the boundary. -/
theorem pool_boundary_loss_le_incidence (G : Multigraph V E) (Y : Finset V) (P : Finset E) :
    (LocalizationBounds.boundaryCopies G Y ∩ P).card ≤
      ∑ v ∈ Y, (G.restrictEdges P).degree v := by
  have heq : LocalizationBounds.boundaryCopies G Y ∩ P =
      Y.biUnion (fun v => P ∩ G.incidenceEdges v) := by
    ext e
    simp only [LocalizationBounds.boundaryCopies, mem_inter, mem_biUnion]
    aesop
  rw [heq]
  simpa only [G.restrictEdges_degree] using
    (Finset.card_biUnion_le (s := Y) (t := fun v => P ∩ G.incidenceEdges v))

/-- A bound on the boundary weight gives the stated relative loss from
each large pool of original copies. -/
theorem pool_boundary_loss (G : Multigraph V E) (U : Finset V) (P : κ → Finset E)
    (Z Y : Finset V) (δ : ℝ) (hweight : (∑ v ∈ Y, weight G U P Z v) ≤ δ)
    (j : κ) (hP : 0 < (P j).card) :
    ((LocalizationBounds.boundaryCopies G Y ∩ P j).card : ℝ) ≤ δ * (P j).card := by
  have hnorm := (sum_le_sum (s := Y) (fun v _ => pool_contribution_le G U P Z j v)).trans hweight
  rw [← Finset.sum_div] at hnorm
  have hpos : (0 : ℝ) < (P j).card := by exact_mod_cast hP
  have hi : ((LocalizationBounds.boundaryCopies G Y ∩ P j).card : ℝ) ≤
      ∑ v ∈ Y, ((G.restrictEdges (P j)).degree v : ℝ) := by
    exact_mod_cast pool_boundary_loss_le_incidence G Y (P j)
  exact hi.trans ((div_le_iff₀ hpos).mp hnorm)

/-- The same boundary weight controls original copies in every active
special row. The source is outside the chosen boundary. -/
theorem row_boundary_loss (G : Multigraph V E) (U : Finset V) (P : κ → Finset E)
    (Z Y : Finset V) (hYU : Y ⊆ U) (δ : ℝ)
    (hweight : (∑ v ∈ Y, weight G U P Z v) ≤ δ)
    (x : V) (hx : x ∈ Z) (hxY : x ∉ Y) (hc : 0 < (G.edgesTo x U).card) :
    ((LocalizationBounds.boundaryCopies G Y ∩ G.edgesTo x U).card : ℝ) ≤
      δ * (G.edgesTo x U).card := by
  rw [LocalizationBounds.boundaryCopies_inter_row G Y U x hxY, inter_eq_left.mpr hYU]
  have hnorm := (sum_le_sum (s := Y) (fun v _ => row_contribution_le G U P Z x hx v)).trans hweight
  rw [← Finset.sum_div] at hnorm
  have hs : (∑ v ∈ Y, ((G.parallelEdges v x).card : ℝ)) = (G.edgesTo x Y).card := by
    exact_mod_cast BlockSampling.sum_parallel_card G x Y
  rw [hs] at hnorm
  exact (div_le_iff₀ (by exact_mod_cast hc : (0 : ℝ) < (G.edgesTo x U).card)).mp hnorm

end Overfull.BipartiteFactorization.BoundaryWeight
