import Overfull.RobustPartition.Conclusion
import Overfull.Arithmetic

/-!
# Quantitative consequences of a robust partition

The actual partition supplies the ordinary and bipartite degree, size, and
component-count conclusions used in Proposition 2.24.  This file takes the
minimum-degree transfer after deleting the low-degree vertices as input.  It
does not assert the separate asymptotic average-degree theorem for critical
graphs.
-/

noncomputable section

namespace Overfull.RobustPartition

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V]

/-- An internal edge contributes two off-opposite incidences, and an edge
leaving the whole bipartite piece contributes one. -/
theorem bad_le_twice_edge_error (G : SimpleGraph V) (A B : Finset V)
    (hAB : Disjoint A B) (b : ℝ)
    (herror : ((internalEdges G A).card : ℝ) + (internalEdges G B).card +
      cut G (A ∪ B) ≤ b) : bad G A B ≤ 2 * b := by
  rw [bad_eq_internal_add_cut G A B hAB, ecount_self G A, ecount_self G B]
  have hcut := cut_nonneg G (A ∪ B)
  linarith

/-- Vertices whose off-opposite degree exceeds a prescribed threshold. -/
def offBad (G : SimpleGraph V) (A B : Finset V) (t : ℝ) : Finset V :=
  A.filter (fun v => t < ((G.neighborFinset v ∩ Bᶜ).card : ℝ))

/-- The actual number of bad vertices is charged to actual incidences. -/
theorem offBad_mul_threshold_le (G : SimpleGraph V) (A B : Finset V) (t : ℝ) :
    ((offBad G A B t).card : ℝ) * t ≤ ecount G A Bᶜ := by
  calc
    _ = ∑ _v ∈ offBad G A B t, t := by simp
    _ ≤ ∑ v ∈ offBad G A B t, ((G.neighborFinset v ∩ Bᶜ).card : ℝ) := by
      apply Finset.sum_le_sum
      intro v hv
      exact (Finset.mem_filter.mp hv).2.le
    _ ≤ ∑ v ∈ A, ((G.neighborFinset v ∩ Bᶜ).card : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => Nat.cast_nonneg _)
    _ = _ := (ecount_eq_sum G A Bᶜ).symm

/-- Outside the actual bad set, all but the threshold many neighbors lie
in the opposite shore. -/
theorem opposite_degree_of_not_offBad (G : SimpleGraph V) (d t : ℝ)
    (hdegree : ∀ v, d ≤ (G.degree v : ℝ))
    (A B : Finset V) (v : V) (hv : v ∈ A) (hgood : v ∉ offBad G A B t) :
    d - t ≤ ((G.neighborFinset v ∩ B).card : ℝ) := by
  have hoff : ((G.neighborFinset v ∩ Bᶜ).card : ℝ) ≤ t := by
    simpa only [offBad, Finset.mem_filter, hv, true_and, not_lt] using hgood
  have hsum : ((G.neighborFinset v ∩ B).card : ℝ) +
      (G.neighborFinset v ∩ Bᶜ).card = G.degree v := by
    have h := Finset.card_inter_add_card_sdiff (G.neighborFinset v) B
    rw [Finset.sdiff_eq_inter_compl, SimpleGraph.card_neighborFinset_eq_degree] at h
    exact_mod_cast h
  linarith [hdegree v]

/-- One actual exceptional set controls the opposite degrees on both shores. -/
theorem exists_opposite_degree_exceptional_set (G : SimpleGraph V) (d ρ : ℝ)
    (hdegree : ∀ v, d ≤ (G.degree v : ℝ)) (hρ : 0 < ρ)
    (hn : 0 < (Fintype.card V : ℝ)) (A B : Finset V)
    (hAB : Disjoint A B)
    (hbad : bad G A B ≤ 2 * ρ * (Fintype.card V : ℝ)^2) :
    ∃ Z : Finset V, Z ⊆ A ∪ B ∧
      (Z.card : ℝ) ≤ 2 * Real.sqrt ρ * Fintype.card V ∧
      (∀ v ∈ A, v ∉ Z → d - Real.sqrt ρ * Fintype.card V ≤
        ((G.neighborFinset v ∩ B).card : ℝ)) ∧
      (∀ v ∈ B, v ∉ Z → d - Real.sqrt ρ * Fintype.card V ≤
        ((G.neighborFinset v ∩ A).card : ℝ)) := by
  let t : ℝ := Real.sqrt ρ * Fintype.card V
  let Z := offBad G A B t ∪ offBad G B A t
  have ht : 0 < t := mul_pos (Real.sqrt_pos.2 hρ) hn
  have hdisj : Disjoint (offBad G A B t) (offBad G B A t) :=
    hAB.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hcard : (Z.card : ℝ) = (offBad G A B t).card + (offBad G B A t).card := by
    dsimp [Z]
    rw [Finset.card_union_of_disjoint hdisj, Nat.cast_add]
  have hsum : (Z.card : ℝ) * t ≤ bad G A B := by
    rw [hcard]
    have hleft := offBad_mul_threshold_le G A B t
    have hright := offBad_mul_threshold_le G B A t
    dsimp [bad]
    nlinarith
  have hsq : t^2 = ρ * (Fintype.card V : ℝ)^2 := by
    dsimp [t]
    rw [mul_pow, Real.sq_sqrt hρ.le]
  refine ⟨Z, Finset.union_subset_union (Finset.filter_subset _ _)
    (Finset.filter_subset _ _), ?_, ?_, ?_⟩
  · change (Z.card : ℝ) ≤ 2 * Real.sqrt ρ * Fintype.card V
    have h : (Z.card : ℝ) * t ≤ (2 * t) * t := by nlinarith
    have hh := (mul_le_mul_iff_left₀ ht).mp h
    dsimp [t] at hh
    nlinarith
  · intro v hv hgood
    exact opposite_degree_of_not_offBad G d t hdegree A B v hv
      (fun h => hgood (Finset.mem_union_left _ h))
  · intro v hv hgood
    exact opposite_degree_of_not_offBad G d t hdegree B A v hv
      (fun h => hgood (Finset.mem_union_right _ h))

/-- Small positive partition errors are strictly smaller than their square root. -/
theorem error_lt_sqrt (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    ρ < Real.sqrt ρ := by
  have hroot := Real.sqrt_nonneg ρ
  have hsq := Real.sq_sqrt hρ.le
  nlinarith [mul_pos hρ (sub_pos.mpr hρ1)]

/-- A vertex in a simple induced subgraph has at most order minus one neighbors. -/
theorem internal_neighbors_add_one_le (G : SimpleGraph V) (U : Finset V)
    (v : V) (hv : v ∈ U) :
    (G.neighborFinset v ∩ U).card + 1 ≤ U.card := by
  have hsub : G.neighborFinset v ∩ U ⊆ U.erase v := by
    intro w hw
    refine Finset.mem_erase.mpr ⟨?_, (Finset.mem_inter.mp hw).2⟩
    intro heq
    subst w
    exact G.loopless v ((G.mem_neighborFinset v v).mp (Finset.mem_inter.mp hw).1)
  have h := Finset.card_le_card hsub
  have hc := Finset.card_erase_add_one hv
  omega

/-- An ordinary part contains an actual good vertex; its degree supplies
both the sharp size lower bound and the original exceptional-degree estimate. -/
theorem PartitionConclusion.ordinary_degree_size
    {G : SimpleGraph V} {d ρ ν τ : ℝ} {L : List (Piece V)}
    (hpart : PartitionConclusion G d ρ ν τ L)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hn : 0 < (Fintype.card V : ℝ))
    (U : Finset V) (hU : Piece.ordinary U ∈ L) :
    d - ρ * Fintype.card V + 1 ≤ (U.card : ℝ) ∧
      ∃ Z : Finset V, Z ⊆ U ∧ (Z.card : ℝ) ≤ ρ * Fintype.card V ∧
        ∀ v ∈ U, v ∉ Z →
          d - ρ * Fintype.card V ≤ ((G.neighborFinset v ∩ U).card : ℝ) := by
  obtain ⟨Z, hZU, hZ, hgood⟩ := hpart.internal_degree (.ordinary U) hU
  change Z ⊆ U at hZU
  change ∀ v ∈ U, v ∉ Z →
    d - ρ * Fintype.card V ≤ ((G.neighborFinset v ∩ U).card : ℝ) at hgood
  have hZlt : Z.card < U.card := by
    have hroot := mul_lt_mul_of_pos_right (error_lt_sqrt ρ hρ hρ1) hn
    have hsize := (hpart.ordinary U hU).2
    exact_mod_cast lt_of_le_of_lt hZ (hroot.trans_le hsize)
  obtain ⟨v, hv⟩ := Finset.sdiff_nonempty_of_card_lt_card hZlt
  obtain ⟨hvU, hvZ⟩ := Finset.mem_sdiff.mp hv
  have hdeg := hgood v hvU hvZ
  have hsize : ((G.neighborFinset v ∩ U).card : ℝ) + 1 ≤ U.card := by
    exact_mod_cast internal_neighbors_add_one_le G U v hvU
  exact ⟨by linarith, Z, hZU, hZ, hgood⟩

/-- Both shores of a bipartite part are almost as large as the minimum degree. -/
theorem PartitionConclusion.bipartite_sizes
    {G : SimpleGraph V} {d ρ ν τ : ℝ} {L : List (Piece V)}
    (hpart : PartitionConclusion G d ρ ν τ L)
    (hdegree : ∀ v, d ≤ (G.degree v : ℝ))
    (hρ : 0 < ρ) (hn : 0 < (Fintype.card V : ℝ))
    (A B : Finset V) (hAB : Piece.bipartite A B ∈ L) :
    d - 2 * Real.sqrt ρ * Fintype.card V ≤ (A.card : ℝ) ∧
    d - 2 * Real.sqrt ρ * Fintype.card V ≤ (B.card : ℝ) := by
  obtain ⟨hdisj, hA, hB, _, herr⟩ := hpart.bipartite A B hAB
  have hbad := bad_le_twice_edge_error G A B hdisj _ herr
  have hroot : 0 < Real.sqrt ρ := Real.sqrt_pos.2 hρ
  have heq : 2 * ρ / Real.sqrt ρ = 2 * Real.sqrt ρ := by
    apply (div_eq_iff (ne_of_gt hroot)).mpr
    nlinarith [Real.sq_sqrt hρ.le]
  constructor
  · have h := card_lower_of_small_off G d (Real.sqrt ρ) (2 * ρ) hdegree
      hroot (by positivity) hn B A hB
      ((ecount_off_right_le_bad G A B).trans (by nlinarith [hbad]))
    rwa [heq] at h
  · have h := card_lower_of_small_off G d (Real.sqrt ρ) (2 * ρ) hdegree
      hroot (by positivity) hn A B hA
      ((ecount_off_left_le_bad G A B).trans (by nlinarith [hbad]))
    rwa [heq] at h

/-- The bipartite exceptional set is constructed from actual bad incidences. -/
theorem PartitionConclusion.bipartite_degree_exceptional_set
    {G : SimpleGraph V} {d ρ ν τ : ℝ} {L : List (Piece V)}
    (hpart : PartitionConclusion G d ρ ν τ L)
    (hdegree : ∀ v, d ≤ (G.degree v : ℝ))
    (hρ : 0 < ρ) (hn : 0 < (Fintype.card V : ℝ))
    (A B : Finset V) (hAB : Piece.bipartite A B ∈ L) :
    ∃ Z : Finset V, Z ⊆ A ∪ B ∧
      (Z.card : ℝ) ≤ 2 * Real.sqrt ρ * Fintype.card V ∧
      (∀ v ∈ A, v ∉ Z → d - Real.sqrt ρ * Fintype.card V ≤
        ((G.neighborFinset v ∩ B).card : ℝ)) ∧
      (∀ v ∈ B, v ∉ Z → d - Real.sqrt ρ * Fintype.card V ≤
        ((G.neighborFinset v ∩ A).card : ℝ)) := by
  obtain ⟨hdisj, _, _, _, herr⟩ := hpart.bipartite A B hAB
  apply exists_opposite_degree_exceptional_set G d ρ hdegree hρ hn A B hdisj
  have h := bad_le_twice_edge_error G A B hdisj _ herr
  nlinarith


/-- The manuscript's explicit cubic error bound gives the strict weighted-count
inequality, together with the small-error bounds used in the degree estimates. -/
theorem cubic_error_bounds (θ ρ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 12)
    (hρ : 0 < ρ) (hsmall : ρ ≤ (θ / 100)^3) :
    ρ < 1 ∧ ρ < θ ∧ ρ ^ (1 / (3 : ℝ)) + 4 * ρ < 4 * θ := by
  let a : ℝ := θ / 100
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : a < 1 := by dsimp [a]; linarith
  have hsquare : a^2 ≤ a := by nlinarith
  have hcube : a^3 ≤ a := by
    calc
      a^3 = a * a^2 := by ring
      _ ≤ a * a := mul_le_mul_of_nonneg_left hsquare ha.le
      _ ≤ a := by nlinarith
  have hρa : ρ ≤ a := hsmall.trans hcube
  have hroot := Real.rpow_le_rpow hρ.le hsmall (by norm_num : 0 ≤ 1 / (3 : ℝ))
  have hcube_root : (a^3) ^ (1 / (3 : ℝ)) = a := by
    simpa only [one_div] using
      (Real.pow_rpow_inv_natCast ha.le (by norm_num : (3 : ℕ) ≠ 0))
  change ρ ^ (1 / (3 : ℝ)) ≤ (a^3) ^ (1 / (3 : ℝ)) at hroot
  rw [hcube_root] at hroot
  dsimp [a] at hρa hroot
  exact ⟨hρa.trans_lt (by linarith), by linarith, by linarith⟩

/-- The actual weighted component count is strictly below four. -/
theorem PartitionConclusion.weighted_count_lt_four
    {G : SimpleGraph V} {d ρ ν τ : ℝ} {L : List (Piece V)}
    (hpart : PartitionConclusion G d ρ ν τ L)
    (n Δ θ : ℝ) (hn : 0 < n) (horder : (Fintype.card V : ℝ) ≤ n)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 12) (hρ : 0 < ρ)
    (hsmall : ρ ≤ (θ / 100)^3)
    (hdensity : (1 / 4 + θ) * n ≤ Δ) (htransfer : Δ - ρ * n ≤ d) :
    ordinaryCount L + 2 * bipartiteCount L < 4 := by
  obtain ⟨_, hρθ, hroot⟩ := cubic_error_bounds θ ρ hθ hθ1 hρ hsmall
  have hd : 0 < d := by
    have hmul := mul_pos (sub_pos.mpr hρθ) hn
    nlinarith
  have hrootpos : 0 ≤ ρ ^ (1 / (3 : ℝ)) := Real.rpow_nonneg hρ.le _
  have hnum := mul_le_mul_of_nonneg_left horder (by positivity : 0 ≤ 1 + ρ ^ (1 / (3 : ℝ)))
  have hnumlt : (1 + ρ ^ (1 / (3 : ℝ))) * Fintype.card V < 4 * d := by
    have hmul := mul_lt_mul_of_pos_right hroot hn
    nlinarith
  have hquot : (1 + ρ ^ (1 / (3 : ℝ))) * Fintype.card V / d < (4 : ℕ) := by
    apply (div_lt_iff₀ hd).mpr
    norm_num
    exact hnumlt
  exact hpart.weighted_count.trans_lt ((Nat.floor_lt' (by norm_num : (4 : ℕ) ≠ 0)).mpr hquot)

/-- An actual partition of a nonempty vertex set has a nonzero shore count. -/
theorem IsPartition.rank_pos {L : List (Piece V)} (hpart : IsPartition L)
    (hn : 0 < Fintype.card V) : 0 < rank L := by
  by_contra h
  have hz : (shoreList L).length = 0 := by change rank L = 0; omega
  have hnil := List.length_eq_zero_iff.mp hz
  have hempty : (Finset.univ : Finset V) = ∅ := by rw [← hpart.2, hnil]; rfl
  have hzcard : Fintype.card V = 0 := by simpa using congrArg Finset.card hempty
  omega

/-- All five alternatives concern the counts of the supplied actual partition. -/
theorem PartitionConclusion.five_cases
    {G : SimpleGraph V} {d ρ ν τ : ℝ} {L : List (Piece V)}
    (hpart : PartitionConclusion G d ρ ν τ L)
    (n Δ θ : ℝ) (hn : 0 < (Fintype.card V : ℝ))
    (horder : (Fintype.card V : ℝ) ≤ n)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 12) (hρ : 0 < ρ)
    (hsmall : ρ ≤ (θ / 100)^3)
    (hdensity : (1 / 4 + θ) * n ≤ Δ) (htransfer : Δ - ρ * n ≤ d) :
    (ordinaryCount L = 1 ∧ bipartiteCount L = 0) ∨
    (ordinaryCount L = 0 ∧ bipartiteCount L = 1) ∨
    (ordinaryCount L = 2 ∧ bipartiteCount L = 0) ∨
    (ordinaryCount L = 3 ∧ bipartiteCount L = 0) ∨
    (ordinaryCount L = 1 ∧ bipartiteCount L = 1) := by
  have hcount := hpart.weighted_count_lt_four n Δ θ (hn.trans_le horder) horder
    hθ hθ1 hρ hsmall hdensity htransfer
  have hrank := hpart.partition.rank_pos (by exact_mod_cast hn)
  rw [rank_eq_weighted_count] at hrank
  exact Overfull.Arithmetic.five_component_cases _ _ (by omega) hcount

/-- The ordinary size and exceptional-degree estimates on the original order
and maximum-degree scale, after the actual minimum-degree transfer. -/
theorem PartitionConclusion.ordinary_transferred_bounds
    {G : SimpleGraph V} {d ρ ν τ : ℝ} {L : List (Piece V)}
    (hpart : PartitionConclusion G d ρ ν τ L)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hn : 0 < (Fintype.card V : ℝ))
    (n Δ : ℝ) (horder : (Fintype.card V : ℝ) ≤ n)
    (htransfer : Δ - ρ * n ≤ d)
    (U : Finset V) (hU : Piece.ordinary U ∈ L) :
    Δ - 2 * ρ * n + 1 ≤ (U.card : ℝ) ∧
      ∃ Z : Finset V, Z ⊆ U ∧ (Z.card : ℝ) ≤ ρ * n ∧
        ∀ v ∈ U, v ∉ Z →
          Δ - 2 * ρ * n ≤ ((G.neighborFinset v ∩ U).card : ℝ) := by
  obtain ⟨hsize, Z, hZU, hZ, hgood⟩ := hpart.ordinary_degree_size hρ hρ1 hn U hU
  have hmul := mul_le_mul_of_nonneg_left horder hρ.le
  refine ⟨by linarith, Z, hZU, hZ.trans hmul, ?_⟩
  intro v hv hnot
  have h := hgood v hv hnot
  linarith

/-- The bipartite size and exceptional-degree estimates on the original
order and maximum-degree scale. -/
theorem PartitionConclusion.bipartite_transferred_bounds
    {G : SimpleGraph V} {d ρ ν τ : ℝ} {L : List (Piece V)}
    (hpart : PartitionConclusion G d ρ ν τ L)
    (hdegree : ∀ v, d ≤ (G.degree v : ℝ))
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hn : 0 < (Fintype.card V : ℝ))
    (n Δ : ℝ) (horder : (Fintype.card V : ℝ) ≤ n)
    (htransfer : Δ - ρ * n ≤ d)
    (A B : Finset V) (hAB : Piece.bipartite A B ∈ L) :
    Δ - 3 * Real.sqrt ρ * n ≤ (A.card : ℝ) ∧
    Δ - 3 * Real.sqrt ρ * n ≤ (B.card : ℝ) ∧
    ∃ Z : Finset V, Z ⊆ A ∪ B ∧ (Z.card : ℝ) ≤ 2 * Real.sqrt ρ * n ∧
      (∀ v ∈ A, v ∉ Z → Δ - 2 * Real.sqrt ρ * n ≤
        ((G.neighborFinset v ∩ B).card : ℝ)) ∧
      (∀ v ∈ B, v ∉ Z → Δ - 2 * Real.sqrt ρ * n ≤
        ((G.neighborFinset v ∩ A).card : ℝ)) := by
  obtain ⟨hA, hB⟩ := hpart.bipartite_sizes hdegree hρ hn A B hAB
  obtain ⟨Z, hZAB, hZ, hgoodA, hgoodB⟩ :=
    hpart.bipartite_degree_exceptional_set hdegree hρ hn A B hAB
  have hmul := mul_le_mul_of_nonneg_left horder (Real.sqrt_nonneg ρ)
  have hmul' := mul_le_mul_of_nonneg_right (error_lt_sqrt ρ hρ hρ1).le
    (hn.trans_le horder).le
  refine ⟨by linarith, by linarith, Z, hZAB, by linarith, ?_, ?_⟩
  · intro v hv hnot
    have h := hgoodA v hv hnot
    linarith
  · intro v hv hnot
    have h := hgoodB v hv hnot
    linarith

/-- The same lower bound holds for every actual shore, including ordinary parts. -/
theorem PartitionConclusion.shore_transferred_lower
    {G : SimpleGraph V} {d ρ ν τ : ℝ} {L : List (Piece V)}
    (hpart : PartitionConclusion G d ρ ν τ L)
    (hdegree : ∀ v, d ≤ (G.degree v : ℝ))
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hn : 0 < (Fintype.card V : ℝ))
    (n Δ : ℝ) (horder : (Fintype.card V : ℝ) ≤ n)
    (htransfer : Δ - ρ * n ≤ d) :
    ∀ X ∈ shoreList L, Δ - 3 * Real.sqrt ρ * n ≤ (X.card : ℝ) := by
  intro X hX
  obtain ⟨p, hp, hXp⟩ := List.mem_flatMap.mp hX
  cases p with
  | ordinary U =>
      have hXU : X = U := by simpa [Piece.shoreList] using hXp
      subst X
      have h := (hpart.ordinary_transferred_bounds hρ hρ1 hn n Δ horder htransfer U hp).1
      have hmul := mul_le_mul_of_nonneg_right (error_lt_sqrt ρ hρ hρ1).le
        (hn.trans_le horder).le
      have hnonneg := mul_nonneg (Real.sqrt_nonneg ρ) (hn.trans_le horder).le
      linarith
  | bipartite A B =>
      have hXAB : X = A ∨ X = B := by simpa [Piece.shoreList] using hXp
      have h := hpart.bipartite_transferred_bounds hdegree hρ hρ1 hn n Δ horder htransfer A B hp
      rcases hXAB with rfl | rfl
      · exact h.1
      · exact h.2.1

/-- In a partition into exactly three shores, the other two lower bounds give
an upper bound for each actual shore. -/
theorem three_shore_card_upper (S : List (Finset V)) (hS : S.Pairwise Disjoint)
    (hthree : S.length = 3) (huniv : unionList S = Finset.univ)
    (b n : ℝ) (horder : (Fintype.card V : ℝ) ≤ n)
    (hlower : ∀ X ∈ S, b ≤ (X.card : ℝ)) :
    ∀ X ∈ S, (X.card : ℝ) ≤ n - 2 * b := by
  obtain ⟨A, B, C, rfl⟩ := List.length_eq_three.mp hthree
  have hAB : Disjoint A B := (List.pairwise_cons.mp hS).1 B (by simp)
  have hAC : Disjoint A C := (List.pairwise_cons.mp hS).1 C (by simp)
  have hBC : Disjoint B C := (List.pairwise_cons.mp (List.pairwise_cons.mp hS).2).1 C (by simp)
  have hsum : (A.card : ℝ) + B.card + C.card = Fintype.card V := by
    have hcard := congrArg Finset.card huniv
    simp only [unionList_cons, unionList_nil, Finset.union_empty,
      Finset.card_union_of_disjoint (Finset.disjoint_union_right.mpr ⟨hAB, hAC⟩),
      Finset.card_union_of_disjoint hBC, Finset.card_univ] at hcard
    exact_mod_cast (show A.card + B.card + C.card = Fintype.card V by omega)
  have hA := hlower A (by simp)
  have hB := hlower B (by simp)
  have hC := hlower C (by simp)
  intro X hX
  have hcases : X = A ∨ X = B ∨ X = C := by simpa using hX
  rcases hcases with rfl | rfl | rfl <;> linarith

/-- Both bounds in equation `bip:part:orders` hold for every actual shore. -/
theorem PartitionConclusion.three_shore_transferred_bounds
    {G : SimpleGraph V} {d ρ ν τ : ℝ} {L : List (Piece V)}
    (hpart : PartitionConclusion G d ρ ν τ L)
    (hdegree : ∀ v, d ≤ (G.degree v : ℝ))
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hn : 0 < (Fintype.card V : ℝ))
    (n Δ : ℝ) (horder : (Fintype.card V : ℝ) ≤ n)
    (htransfer : Δ - ρ * n ≤ d)
    (hthree : ordinaryCount L + 2 * bipartiteCount L = 3) :
    ∀ X ∈ shoreList L, Δ - 3 * Real.sqrt ρ * n ≤ (X.card : ℝ) ∧
      (X.card : ℝ) ≤ n - 2 * Δ + 6 * Real.sqrt ρ * n := by
  have hlower := hpart.shore_transferred_lower hdegree hρ hρ1 hn n Δ horder htransfer
  have hupper := three_shore_card_upper (shoreList L) hpart.partition.1
    (by change rank L = 3; rwa [rank_eq_weighted_count]) hpart.partition.2
    (Δ - 3 * Real.sqrt ρ * n) n horder hlower
  intro X hX
  exact ⟨hlower X hX, by linarith [hupper X hX]⟩

end Overfull.RobustPartition
