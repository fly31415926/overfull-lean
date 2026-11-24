import Overfull.CutCounting
import Mathlib.Combinatorics.SimpleGraph.Density

/-!
# Incidence counting for a robust partition

The edge counts are counts of actual ordered adjacent pairs in the ambient
simple graph.  In particular, an edge internal to a shore contributes twice
and a cut edge contributes once.  The size and exceptional-vertex estimates
below use only degree bounds and these incidence counts.
-/

namespace Overfull.RobustPartition

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V]

noncomputable def ecount (G : SimpleGraph V) (X Y : Finset V) : ℝ :=
  ((G.interedges X Y).card : ℝ)

noncomputable def cut (G : SimpleGraph V) (U : Finset V) : ℝ :=
  ecount G U Uᶜ

noncomputable def bad (G : SimpleGraph V) (A B : Finset V) : ℝ :=
  ecount G A Bᶜ + ecount G B Aᶜ

omit [Fintype V] in
theorem ecount_nonneg (G : SimpleGraph V) (X Y : Finset V) :
    0 ≤ ecount G X Y := by
  unfold ecount
  positivity

theorem cut_nonneg (G : SimpleGraph V) (U : Finset V) :
    0 ≤ cut G U := ecount_nonneg G U Uᶜ

theorem bad_nonneg (G : SimpleGraph V) (A B : Finset V) :
    0 ≤ bad G A B :=
  add_nonneg (ecount_nonneg G A Bᶜ) (ecount_nonneg G B Aᶜ)

omit [Fintype V] in
theorem ecount_symm (G : SimpleGraph V) (X Y : Finset V) :
    ecount G X Y = ecount G Y X := by
  unfold ecount
  exact_mod_cast Rel.card_interedges_comm G.symm X Y

theorem bad_symm (G : SimpleGraph V) (A B : Finset V) :
    bad G A B = bad G B A := by
  unfold bad
  ring

omit [Fintype V] in
theorem ecount_mono (G : SimpleGraph V) {X X' Y Y' : Finset V}
    (hX : X ⊆ X') (hY : Y ⊆ Y') :
    ecount G X Y ≤ ecount G X' Y' := by
  unfold ecount
  exact_mod_cast Finset.card_le_card (G.interedges_mono hX hY)

omit [Fintype V] in
theorem ecount_le_mul_card (G : SimpleGraph V) (X Y : Finset V) :
    ecount G X Y ≤ (X.card : ℝ) * Y.card := by
  unfold ecount
  exact_mod_cast G.card_interedges_le_mul X Y

omit [Fintype V] in
private theorem interedges_union_left (G : SimpleGraph V) (X Y Z : Finset V) :
    G.interedges (X ∪ Y) Z = G.interedges X Z ∪ G.interedges Y Z := by
  ext ⟨v, w⟩
  simp only [SimpleGraph.mem_interedges_iff, Finset.mem_union]
  tauto

omit [Fintype V] in
theorem ecount_union_left_le (G : SimpleGraph V) (X Y Z : Finset V) :
    ecount G (X ∪ Y) Z ≤ ecount G X Z + ecount G Y Z := by
  unfold ecount
  rw [interedges_union_left]
  exact_mod_cast Finset.card_union_le (G.interedges X Z) (G.interedges Y Z)

omit [Fintype V] in
theorem ecount_union_right_le (G : SimpleGraph V) (X Y Z : Finset V) :
    ecount G X (Y ∪ Z) ≤ ecount G X Y + ecount G X Z := by
  rw [ecount_symm G X (Y ∪ Z)]
  calc
    _ ≤ ecount G Y X + ecount G Z X := ecount_union_left_le G Y Z X
    _ = _ := by rw [ecount_symm G Y X, ecount_symm G Z X]

omit [Fintype V] in
theorem ecount_union_left (G : SimpleGraph V) (X Y Z : Finset V)
    (hXY : Disjoint X Y) :
    ecount G (X ∪ Y) Z = ecount G X Z + ecount G Y Z := by
  unfold ecount
  rw [interedges_union_left, Finset.card_union_of_disjoint
    (G.interedges_disjoint_left hXY Z), Nat.cast_add]

omit [Fintype V] in
theorem ecount_union_right (G : SimpleGraph V) (X Y Z : Finset V)
    (hYZ : Disjoint Y Z) :
    ecount G X (Y ∪ Z) = ecount G X Y + ecount G X Z := by
  rw [ecount_symm G X (Y ∪ Z), ecount_union_left G Y Z X hYZ,
    ecount_symm G Y X, ecount_symm G Z X]

/-- Count the ordered incidences by their first endpoint. -/
theorem ecount_eq_sum (G : SimpleGraph V) (X Y : Finset V) :
    ecount G X Y = ∑ v ∈ X, ((G.neighborFinset v ∩ Y).card : ℝ) := by
  have hnat : (G.interedges X Y).card =
      ∑ v ∈ X, (G.neighborFinset v ∩ Y).card := by
    calc
      _ = ∑ v ∈ X, ∑ w ∈ Y, if G.Adj v w then (1 : ℕ) else 0 := by
        simp only [SimpleGraph.interedges_def, Finset.card_eq_sum_ones,
          Finset.sum_filter, Finset.sum_product]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro v _
        have hY : Y.filter (fun w => G.Adj v w) = G.neighborFinset v ∩ Y := by
          ext w
          simp [and_comm]
        simp only [Finset.sum_boole, Nat.cast_id, hY]
  unfold ecount
  exact_mod_cast hnat

theorem ecount_univ (G : SimpleGraph V) (X : Finset V) :
    ecount G X univ = ∑ v ∈ X, (G.degree v : ℝ) := by
  simp only [ecount_eq_sum, Finset.inter_univ, SimpleGraph.card_neighborFinset_eq_degree]

theorem ecount_add_compl (G : SimpleGraph V) (X Y : Finset V) :
    ecount G X Y + ecount G X Yᶜ = ∑ v ∈ X, (G.degree v : ℝ) := by
  rw [← ecount_union_right G X Y Yᶜ disjoint_compl_right,
    Finset.union_compl, ecount_univ]

theorem ecount_self (G : SimpleGraph V) (X : Finset V) :
    ecount G X X = 2 * ((internalEdges G X).card : ℝ) := by
  rw [ecount_eq_sum]
  exact_mod_cast (internal_degree_sum G X).symm

theorem cut_eq_sum (G : SimpleGraph V) (U : Finset V) :
    cut G U = ∑ v ∈ U, ((G.neighborFinset v \ U).card : ℝ) := by
  simp only [cut, ecount_eq_sum, Finset.sdiff_eq_inter_compl]

theorem cut_compl (G : SimpleGraph V) (U : Finset V) :
    cut G Uᶜ = cut G U := by
  simp only [cut, compl_compl, ecount_symm G Uᶜ U]

/-- Removing a piece creates at most the two previous boundaries. -/
theorem cut_sdiff_le (G : SimpleGraph V) (U P : Finset V) :
    cut G (U \ P) ≤ cut G U + cut G P := by
  have hcomp : (U \ P)ᶜ = Uᶜ ∪ P := by
    ext v
    simp only [Finset.mem_compl, Finset.mem_sdiff, Finset.mem_union]
    tauto
  have hsub : U \ P ⊆ Pᶜ := by
    intro v hv
    exact Finset.mem_compl.mpr (Finset.mem_sdiff.mp hv).2
  unfold cut
  rw [hcomp]
  calc
    _ ≤ ecount G (U \ P) Uᶜ + ecount G (U \ P) P :=
      ecount_union_right_le G (U \ P) Uᶜ P
    _ ≤ ecount G U Uᶜ + ecount G P Pᶜ := by
      apply add_le_add (ecount_mono G Finset.sdiff_subset (Finset.Subset.refl _))
      rw [ecount_symm G (U \ P) P]
      exact ecount_mono G (Finset.Subset.refl _) hsub

/-- The external boundary of two shores is part of their off-opposite incidences. -/
theorem cut_union_le_bad (G : SimpleGraph V) (A B : Finset V) :
    cut G (A ∪ B) ≤ bad G A B := by
  have hA : (A ∪ B)ᶜ ⊆ Aᶜ := by
    intro v hv
    simp only [Finset.mem_compl, Finset.mem_union] at hv ⊢
    tauto
  have hB : (A ∪ B)ᶜ ⊆ Bᶜ := by
    intro v hv
    simp only [Finset.mem_compl, Finset.mem_union] at hv ⊢
    tauto
  exact (ecount_union_left_le G A B (A ∪ B)ᶜ).trans
    (add_le_add (ecount_mono G (Finset.Subset.refl _) hB)
      (ecount_mono G (Finset.Subset.refl _) hA))

theorem ecount_off_left_le_bad (G : SimpleGraph V) (A B : Finset V) :
    ecount G A Bᶜ ≤ bad G A B := by
  exact le_add_of_nonneg_right (ecount_nonneg G B Aᶜ)

theorem ecount_off_right_le_bad (G : SimpleGraph V) (A B : Finset V) :
    ecount G B Aᶜ ≤ bad G A B := by
  exact le_add_of_nonneg_left (ecount_nonneg G A Bᶜ)

/-- Off-opposite incidences count internal edges twice and boundary edges once. -/
theorem bad_eq_internal_add_cut (G : SimpleGraph V) (A B : Finset V)
    (hAB : Disjoint A B) :
    bad G A B = ecount G A A + ecount G B B + cut G (A ∪ B) := by
  have hcompB : Bᶜ = A ∪ (A ∪ B)ᶜ := by
    ext v
    have hv : ¬ (v ∈ A ∧ v ∈ B) := by
      rintro ⟨hA, hB⟩
      exact Finset.disjoint_left.mp hAB hA hB
    simp only [Finset.mem_compl, Finset.mem_union]
    tauto
  have hcompA : Aᶜ = B ∪ (A ∪ B)ᶜ := by
    ext v
    have hv : ¬ (v ∈ A ∧ v ∈ B) := by
      rintro ⟨hA, hB⟩
      exact Finset.disjoint_left.mp hAB hA hB
    simp only [Finset.mem_compl, Finset.mem_union]
    tauto
  have hAdisj : Disjoint A (A ∪ B)ᶜ := by
    apply Finset.disjoint_left.mpr
    intro v hA hv
    exact Finset.mem_compl.mp hv (Finset.mem_union_left _ hA)
  have hBdisj : Disjoint B (A ∪ B)ᶜ := by
    apply Finset.disjoint_left.mpr
    intro v hB hv
    exact Finset.mem_compl.mp hv (Finset.mem_union_right _ hB)
  unfold bad cut
  rw [hcompB, hcompA, ecount_union_right G A A (A ∪ B)ᶜ hAdisj,
    ecount_union_right G B B (A ∪ B)ᶜ hBdisj,
    ecount_union_left G A B (A ∪ B)ᶜ hAB]
  ring

theorem internal_edges_add_cut_le_bad (G : SimpleGraph V) (A B : Finset V)
    (hAB : Disjoint A B) :
    ((internalEdges G A).card : ℝ) + (internalEdges G B).card + cut G (A ∪ B) ≤
      bad G A B := by
  rw [bad_eq_internal_add_cut G A B hAB, ecount_self G A, ecount_self G B]
  have hA : 0 ≤ ((internalEdges G A).card : ℝ) := Nat.cast_nonneg _
  have hB : 0 ≤ ((internalEdges G B).card : ℝ) := Nat.cast_nonneg _
  linarith

/-- Minimum degree, counted on any actual shore. -/
theorem min_degree_mul_card_le (G : SimpleGraph V) (d : ℝ)
    (hdegree : ∀ v, d ≤ (G.degree v : ℝ)) (X Y : Finset V) :
    d * X.card ≤ ecount G X Y + ecount G X Yᶜ := by
  rw [ecount_add_compl]
  calc
    _ = ∑ _v ∈ X, d := by simp; ring
    _ ≤ _ := Finset.sum_le_sum (fun v _ => hdegree v)

/-- Maximum degree bounds the incidences out of any actual shore. -/
theorem ecount_le_max_degree_mul_card (G : SimpleGraph V) (D : ℝ)
    (hdegree : ∀ v, (G.degree v : ℝ) ≤ D) (X Y : Finset V) :
    ecount G X Y ≤ D * X.card := by
  calc
    _ ≤ ecount G X univ := ecount_mono G (Finset.Subset.refl _) (Finset.subset_univ _)
    _ = ∑ v ∈ X, (G.degree v : ℝ) := ecount_univ G X
    _ ≤ ∑ _v ∈ X, D := Finset.sum_le_sum (fun v _ => hdegree v)
    _ = _ := by simp; ring

/-- A large source shore with few neighbors outside `X` forces `X` to be large. -/
theorem card_lower_of_small_off (G : SimpleGraph V) (d r ε : ℝ)
    (hdegree : ∀ v, d ≤ (G.degree v : ℝ)) (hr : 0 < r) (hε : 0 ≤ ε)
    (hn : 0 < (Fintype.card V : ℝ)) (A X : Finset V)
    (hA : r * Fintype.card V ≤ (A.card : ℝ))
    (hoff : ecount G A Xᶜ ≤ ε * (Fintype.card V : ℝ)^2) :
    d - (ε / r) * Fintype.card V ≤ (X.card : ℝ) := by
  let n : ℝ := Fintype.card V
  have hn' : 0 < n := hn
  have hA' : r * n ≤ (A.card : ℝ) := hA
  have hdegree' := min_degree_mul_card_le G d hdegree A X
  have hcross := ecount_le_mul_card G A X
  have hbound : (d - X.card) * (A.card : ℝ) ≤ ε * n^2 := by
    dsimp [n]
    nlinarith
  by_contra h
  have hlt : ε / r * n < d - X.card := by
    dsimp [n]
    linarith
  have herror : 0 ≤ ε / r * n := mul_nonneg (div_nonneg hε hr.le) hn'.le
  have hpos : 0 < d - X.card := herror.trans_lt hlt
  have hmul := mul_le_mul_of_nonneg_left hA' hpos.le
  have hstrict := mul_lt_mul_of_pos_right hlt (mul_pos hr hn')
  have heq : (ε / r * n) * (r * n) = ε * n^2 := by
    field_simp [ne_of_gt hr]
  rw [heq] at hstrict
  nlinarith

/-- The ordinary-block size estimate used after the refinement terminates. -/
theorem block_size_lower (G : SimpleGraph V) (d a ε : ℝ)
    (hdegree : ∀ v, d ≤ (G.degree v : ℝ)) (ha : 0 < a) (hε : 0 ≤ ε)
    (hn : 0 < (Fintype.card V : ℝ)) (U : Finset V)
    (hU : a * Fintype.card V / 2 ≤ (U.card : ℝ))
    (hcut : cut G U ≤ ε * (Fintype.card V : ℝ)^2) :
    d - (2 * ε / a) * Fintype.card V ≤ (U.card : ℝ) := by
  have h := card_lower_of_small_off G d (a / 2) ε hdegree (by positivity) hε hn U U
    (by nlinarith) hcut
  have heq : ε / (a / 2) = 2 * ε / a := by ring
  rwa [heq] at h

/-- Each shore of an almost bipartite block satisfies the same size estimate. -/
theorem bipartite_sizes_lower (G : SimpleGraph V) (d a ε : ℝ)
    (hdegree : ∀ v, d ≤ (G.degree v : ℝ)) (ha : 0 < a) (hε : 0 ≤ ε)
    (hn : 0 < (Fintype.card V : ℝ)) (A B : Finset V)
    (hA : a * Fintype.card V / 2 ≤ (A.card : ℝ))
    (hB : a * Fintype.card V / 2 ≤ (B.card : ℝ))
    (hbad : bad G A B ≤ ε * (Fintype.card V : ℝ)^2) :
    d - (2 * ε / a) * Fintype.card V ≤ (A.card : ℝ) ∧
    d - (2 * ε / a) * Fintype.card V ≤ (B.card : ℝ) := by
  have hleft := card_lower_of_small_off G d (a / 2) ε hdegree (by positivity) hε hn B A
    (by nlinarith) ((ecount_off_right_le_bad G A B).trans hbad)
  have hright := card_lower_of_small_off G d (a / 2) ε hdegree (by positivity) hε hn A B
    (by nlinarith) ((ecount_off_left_le_bad G A B).trans hbad)
  have heq : ε / (a / 2) = 2 * ε / a := by ring
  exact ⟨by rwa [heq] at hleft, by rwa [heq] at hright⟩

noncomputable def internalBad (G : SimpleGraph V) (d ρ : ℝ) (U : Finset V) : Finset V :=
  U.filter (fun v => ((G.neighborFinset v ∩ U).card : ℝ) < d - ρ * Fintype.card V)

theorem internal_good_of_not_bad (G : SimpleGraph V) (d ρ : ℝ) (U : Finset V)
    (v : V) (hv : v ∈ U) (hgood : v ∉ internalBad G d ρ U) :
    d - ρ * Fintype.card V ≤ ((G.neighborFinset v ∩ U).card : ℝ) := by
  simpa only [internalBad, Finset.mem_filter, hv, true_and, not_lt] using hgood

/-- A quadratic boundary budget gives a linear exceptional-vertex budget. -/
theorem bad_internal_degree_count (G : SimpleGraph V) (d ρ : ℝ)
    (hdegree : ∀ v, d ≤ (G.degree v : ℝ)) (hρ : 0 < ρ)
    (hn : 0 < (Fintype.card V : ℝ)) (U : Finset V)
    (hcut : cut G U ≤ ρ^2 * (Fintype.card V : ℝ)^2) :
    ((internalBad G d ρ U).card : ℝ) ≤ ρ * Fintype.card V := by
  have hvertex (v : V) (hv : v ∈ internalBad G d ρ U) :
      ρ * Fintype.card V ≤ ((G.neighborFinset v \ U).card : ℝ) := by
    have hbad := (Finset.mem_filter.mp hv).2
    have hpart : ((G.neighborFinset v ∩ U).card : ℝ) +
        ((G.neighborFinset v \ U).card : ℝ) = G.degree v := by
      have hnat := Finset.card_inter_add_card_sdiff (G.neighborFinset v) U
      rw [SimpleGraph.card_neighborFinset_eq_degree] at hnat
      exact_mod_cast hnat
    linarith [hdegree v]
  have hsum : (ρ * Fintype.card V) * ((internalBad G d ρ U).card : ℝ) ≤ cut G U := by
    calc
      _ = ∑ _v ∈ internalBad G d ρ U, ρ * Fintype.card V := by simp; ring
      _ ≤ ∑ v ∈ internalBad G d ρ U, ((G.neighborFinset v \ U).card : ℝ) :=
        Finset.sum_le_sum hvertex
      _ ≤ ∑ v ∈ U, ((G.neighborFinset v \ U).card : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => Nat.cast_nonneg _)
      _ = _ := (cut_eq_sum G U).symm
  have hbound : (ρ * Fintype.card V) * ((internalBad G d ρ U).card : ℝ) ≤
      (ρ * Fintype.card V) * (ρ * Fintype.card V) := by
    nlinarith
  exact (mul_le_mul_iff_right₀ (mul_pos hρ hn)).mp hbound

/-- Compare two degree sums through the common crossing-edge count. -/
theorem degree_gap_le_off (G : SimpleGraph V) (d D : ℝ)
    (hmin : ∀ v, d ≤ (G.degree v : ℝ))
    (hmax : ∀ v, (G.degree v : ℝ) ≤ D) (A B : Finset V) :
    d * A.card - D * B.card ≤ ecount G A Bᶜ := by
  have hlow := min_degree_mul_card_le G d hmin A B
  have hhigh := ecount_le_max_degree_mul_card G D hmax B A
  rw [ecount_symm G B A] at hhigh
  linarith

/-- Near regularity makes the two shores of an almost bipartite block balanced. -/
theorem bipartite_imbalance (G : SimpleGraph V) (d a γ ε : ℝ)
    (ha : 0 < a) (hγ : 0 ≤ γ)
    (hn : 0 < (Fintype.card V : ℝ))
    (hd : a * Fintype.card V ≤ d)
    (hmin : ∀ v, d ≤ (G.degree v : ℝ))
    (hmax : ∀ v, (G.degree v : ℝ) ≤ d + γ * Fintype.card V)
    (A B : Finset V) (hbad : bad G A B ≤ ε * (Fintype.card V : ℝ)^2) :
    |(A.card : ℝ) - B.card| ≤ (γ + ε) / a * Fintype.card V := by
  let n : ℝ := Fintype.card V
  have hdir (X Y : Finset V)
      (hoff : ecount G X Yᶜ ≤ ε * n^2)
      (horder : (Y.card : ℝ) ≤ X.card) :
      (X.card : ℝ) - Y.card ≤ (γ + ε) / a * n := by
    have hgap := degree_gap_le_off G d (d + γ * Fintype.card V) hmin hmax X Y
    have hY : (Y.card : ℝ) ≤ n := by
      change (Y.card : ℝ) ≤ (Fintype.card V : ℝ)
      exact_mod_cast Finset.card_le_univ Y
    have hmul := mul_le_mul_of_nonneg_left hY
      (mul_nonneg hγ (show 0 ≤ n from hn.le))
    have hdiff := mul_le_mul_of_nonneg_right hd (sub_nonneg.mpr horder)
    have hbound : (a * n) * ((X.card : ℝ) - Y.card) ≤ (γ + ε) * n^2 := by
      dsimp [n] at *
      nlinarith
    have heq : (γ + ε) * n^2 = (a * n) * ((γ + ε) / a * n) := by
      field_simp [ne_of_gt ha]
    rw [heq] at hbound
    exact (mul_le_mul_iff_right₀ (mul_pos ha hn)).mp hbound
  by_cases horder : (B.card : ℝ) ≤ A.card
  · rw [abs_of_nonneg (sub_nonneg.mpr horder)]
    exact hdir A B ((ecount_off_left_le_bad G A B).trans hbad) horder
  · have horder' : (A.card : ℝ) ≤ B.card := le_of_lt (lt_of_not_ge horder)
    rw [abs_of_nonpos (sub_nonpos.mpr horder')]
    have h := hdir B A ((ecount_off_right_le_bad G A B).trans hbad) horder'
    linarith

/-- The coarse lower size of every counted shore bounds the number of shores. -/
theorem coarse_count_bound (c n a : ℝ) (hn : 0 < n)
    (hmass : c * (a * n / 2) ≤ n) : c * a ≤ 2 := by
  have h : (c * a) * n ≤ 2 * n := by nlinarith
  exact (mul_le_mul_iff_left₀ hn).mp h

/-- Upgrade the coarse count using the degree-based size of every shore. -/
theorem sharp_count_estimate (c n d a ρ : ℝ)
    (hc : 0 ≤ c) (hn : 0 ≤ n) (ha : 0 < a) (hρ : 0 ≤ ρ)
    (hsmall : ρ ≤ a^2 / 4) (hcoarse : c * a ≤ 2)
    (hmass : c * (d - (2 * ρ^2 / a) * n) ≤ n) :
    c * d ≤ (1 + ρ) * n := by
  have herr : c * (2 * ρ^2 / a) ≤ ρ := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ ha).mpr
    have hsmall' : 4 * ρ ≤ a^2 := by linarith
    have h1 := mul_le_mul_of_nonneg_left hsmall' (mul_nonneg hc hρ)
    have h2 := mul_le_mul_of_nonneg_right hcoarse (mul_nonneg hρ ha.le)
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right herr hn
  nlinarith

end Overfull.RobustPartition
