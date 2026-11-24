import Overfull.RobustStability
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal

/-!
# Equal regularity clusters with a robust reduced graph

The equitable regularity lemma gives an actual partition with boundedly
many parts. Removing the irregular, sparse, and within-part edges loses
little total degree, which preserves robust expansion after a small
change in the neighborhood parameter. Passing to the actual graph on
the parts then preserves robust expansion. Finally, trimming each part
to the common minimum size gives equal clusters and a small exceptional
set. Every reduced edge satisfies the lower edge-count inequality needed
for the paired-cut lifting argument.

This proof uses the equitable regularity theorem available in mathlib;
no degree-form regularity theorem or reduced-expansion existence is
assumed.
-/

namespace Overfull.PairedCut

open Finset Classical
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem intersection_loss_bound (A B S : Finset V) (hBA : B ⊆ A) :
    (A ∩ S).card + B.card ≤ (B ∩ S).card + A.card := by
  have hsub : A ∩ S ⊆ (B ∩ S) ∪ (A \ B) := by
    intro v hv
    obtain ⟨hvA, hvS⟩ := Finset.mem_inter.mp hv
    by_cases hvB : v ∈ B
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hvB, hvS⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hvA, hvB⟩)
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have ht := Finset.card_sdiff_add_card_eq_card hBA
  omega

/-- A small total number of deleted incidences preserves robust expansion.
Only the vertices with a large individual loss need to be discarded from
each original robust neighborhood. -/
theorem robust_after_total_degree_loss (G H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (ν τ : ℝ)
    (hν : 0 < ν) (hn : 0 < Fintype.card V) (hHG : H ≤ G)
    (hG : IsRobustExpander G ν τ)
    (hloss : (∑ v : V, ((G.degree v : ℝ) - H.degree v)) ≤
      ν^2 / 16 * (Fintype.card V : ℝ)^2) :
    IsRobustExpander H (3*ν/4) τ := by
  classical
  let n : ℝ := Fintype.card V
  have hnR : 0 < n := by dsimp [n]; exact_mod_cast hn
  have hdegree (v : V) : (H.degree v : ℝ) ≤ G.degree v := by
    exact_mod_cast H.degree_le_of_le hHG (v := v)
  intro S hS hS'
  let A := robustNeighbors G ν S
  let B := robustNeighbors H (3*ν/4) S
  have hsmall (v : V) (hv : v ∈ A \ B) :
      ν*n/4 ≤ (G.degree v : ℝ) - H.degree v := by
    obtain ⟨hvA, hvB⟩ := Finset.mem_sdiff.mp hv
    have hA := (mem_robustNeighbors G ν S v).mp hvA
    have hB := lt_of_not_ge ((mem_robustNeighbors H (3*ν/4) S v).not.mp hvB)
    have hsub : H.neighborFinset v ⊆ G.neighborFinset v := by
      intro w hw
      simpa using hHG (by simpa using hw)
    have hc := intersection_loss_bound (G.neighborFinset v) (H.neighborFinset v) S hsub
    have hcR : ((G.neighborFinset v ∩ S).card : ℝ) + H.degree v ≤
        (H.neighborFinset v ∩ S).card + G.degree v := by exact_mod_cast hc
    change ν*n ≤ _ at hA
    change _ < (3*ν/4)*n at hB
    linarith
  have hbad : ((A \ B).card : ℝ) ≤ ν*n/4 := by
    have hsum : (A \ B).card * (ν*n/4) ≤
        ∑ v : V, ((G.degree v : ℝ) - H.degree v) := by
      calc
        _ = ∑ _v ∈ A \ B, ν*n/4 := by simp
        _ ≤ ∑ v ∈ A \ B, ((G.degree v : ℝ) - H.degree v) :=
          Finset.sum_le_sum hsmall
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun v _ _ => sub_nonneg.mpr (hdegree v))
    change _ ≤ ν^2/16*n^2 at hloss
    nlinarith only [hsum, hloss, mul_pos hν hnR]
  have hcard : A.card ≤ B.card + (A \ B).card := by
    have hpart := Finset.card_inter_add_card_sdiff A B
    have hi := Finset.card_le_card (Finset.inter_subset_right : A ∩ B ⊆ B)
    omega
  have hcardR : (A.card : ℝ) ≤ B.card + (A \ B).card := by exact_mod_cast hcard
  have hrobust := hG S hS hS'
  change (S.card : ℝ) + ν*n ≤ A.card at hrobust
  change (S.card : ℝ) + (3*ν/4)*n ≤ B.card
  linarith

variable {J : Type*} [Fintype J] [DecidableEq J]

omit [DecidableEq V] [Fintype J] in
theorem fiber_union_card_bounds (f : V → J) (w : ℕ)
    (hlower : ∀ i, w ≤ (univ.filter (fun v => f v = i)).card)
    (hupper : ∀ i, (univ.filter (fun v => f v = i)).card ≤ w+1)
    (S : Finset J) :
    w*S.card ≤ (univ.filter (fun v => f v ∈ S)).card ∧
      (univ.filter (fun v => f v ∈ S)).card ≤ (w+1)*S.card := by
  have hsum := Finset.sum_card_fiberwise_eq_card_filter (univ : Finset V) S f
  constructor
  · calc
      _ = ∑ _i ∈ S, w := by simp [Nat.mul_comm]
      _ ≤ ∑ i ∈ S, (univ.filter (fun v => f v = i)).card :=
        Finset.sum_le_sum (fun i _ => hlower i)
      _ = _ := hsum
  · calc
      _ = ∑ i ∈ S, (univ.filter (fun v => f v = i)).card := hsum.symm
      _ ≤ ∑ _i ∈ S, (w+1) := Finset.sum_le_sum (fun i _ => hupper i)
      _ = _ := by simp [Nat.mul_comm]

/-- Robust expansion passes to an actual quotient whose fibers have
sizes `w` or `w+1`. The lower bound on `w` absorbs the equitability error. -/
theorem robust_quotient (G : SimpleGraph V) (R : SimpleGraph J)
    [DecidableRel G.Adj] [DecidableRel R.Adj] (f : V → J) (w : ℕ)
    (ν τ : ℝ) (hν : 0 < ν) (hν1 : ν ≤ 1) (hτ : 0 ≤ τ)
    (hw : 8 ≤ ν*w)
    (hlower : ∀ i, w ≤ (univ.filter (fun v => f v = i)).card)
    (hupper : ∀ i, (univ.filter (fun v => f v = i)).card ≤ w+1)
    (hmap : ∀ v u, G.Adj v u → R.Adj (f v) (f u))
    (hG : IsRobustExpander G (3*ν/4) τ) :
    IsRobustExpander R (ν/2) (2*τ) := by
  classical
  let n : ℝ := Fintype.card V
  let t : ℝ := Fintype.card J
  have hwR : 2 ≤ (w : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hν1 (Nat.cast_nonneg w)
    nlinarith
  have hwpos : 0 < (w : ℝ)+1 := by positivity
  have ht : 0 ≤ t := Nat.cast_nonneg _
  have hfull := fiber_union_card_bounds f w hlower hupper univ
  have hfull' : w * Fintype.card J ≤ Fintype.card V ∧
      Fintype.card V ≤ (w+1)*Fintype.card J := by simpa using hfull
  have hnlow : (w : ℝ)*t ≤ n := by dsimp [n,t]; exact_mod_cast hfull'.1
  have hnhigh : n ≤ ((w : ℝ)+1)*t := by dsimp [n,t]; exact_mod_cast hfull'.2
  have hsize (S : Finset J) :
      (w : ℝ)*S.card ≤ (univ.filter (fun v => f v ∈ S)).card ∧
      ((univ.filter (fun v => f v ∈ S)).card : ℝ) ≤ ((w : ℝ)+1)*S.card := by
    exact_mod_cast fiber_union_card_bounds f w hlower hupper S
  have hrange (S : Finset J) (hS : 2*τ*t ≤ (S.card : ℝ)) :
      τ*n ≤ ((univ.filter (fun v => f v ∈ S)).card : ℝ) := by
    have h₁ := mul_le_mul_of_nonneg_left hnhigh hτ
    have h₂ := mul_le_mul_of_nonneg_left hS (Nat.cast_nonneg w (α := ℝ))
    have h₃ := mul_nonneg (show 0 ≤ (w : ℝ)-1 by linarith) (mul_nonneg hτ ht)
    have h₄ := (hsize S).1
    nlinarith only [h₁, h₂, h₃, h₄]
  intro S hS hS'
  let X := univ.filter (fun v => f v ∈ S)
  have hXlower : τ*n ≤ (X.card : ℝ) := hrange S hS
  have hcompl : (univ.filter (fun v => f v ∈ Sᶜ)) = Xᶜ := by
    ext v
    simp [X]
  have hScompl : 2*τ*t ≤ (Sᶜ.card : ℝ) := by
    have hc : (S.card : ℝ) + Sᶜ.card = t := by
      dsimp [t]
      exact_mod_cast Finset.card_add_card_compl S
    change (S.card : ℝ) ≤ (1-2*τ)*t at hS'
    linarith
  have hXupper : (X.card : ℝ) ≤ (1-τ)*n := by
    have hh := hrange Sᶜ hScompl
    rw [hcompl] at hh
    have hc : (X.card : ℝ) + Xᶜ.card = n := by
      dsimp [n]
      exact_mod_cast Finset.card_add_card_compl X
    linarith
  let A := robustNeighbors G (3*ν/4) X
  let B := robustNeighbors R (ν/2) S
  have hneighbor (v : V) :
      (G.neighborFinset v ∩ X).card ≤
        (univ.filter (fun u => f u ∈ R.neighborFinset (f v) ∩ S)).card := by
    apply Finset.card_le_card
    intro u hu
    obtain ⟨huG, huX⟩ := Finset.mem_inter.mp hu
    have huS : f u ∈ S := (Finset.mem_filter.mp huX).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_inter.mpr
      ⟨by simpa using hmap v u (by simpa using huG), huS⟩⟩
  have hmapA (v : V) (hv : v ∈ A) : f v ∈ B := by
    have hcount := (mem_robustNeighbors G (3*ν/4) X v).mp hv
    have hcount' : ((G.neighborFinset v ∩ X).card : ℝ) ≤
        ((w : ℝ)+1)*(R.neighborFinset (f v) ∩ S).card := by
      have hh : ((G.neighborFinset v ∩ X).card : ℝ) ≤
          (univ.filter (fun u => f u ∈ R.neighborFinset (f v) ∩ S)).card := by
        exact_mod_cast hneighbor v
      exact hh.trans (hsize (R.neighborFinset (f v) ∩ S)).2
    have hcoef : (ν/2)*((w : ℝ)+1) ≤ (3*ν/4)*w := by
      have hh := mul_nonneg hν.le (show 0 ≤ (w : ℝ)-2 by linarith)
      nlinarith only [hh]
    have hcoef' := mul_le_mul_of_nonneg_right hcoef ht
    have hnlow' := mul_le_mul_of_nonneg_left hnlow (show 0 ≤ 3*ν/4 by positivity)
    rw [mem_robustNeighbors]
    change (ν/2)*t ≤ _
    change (3*ν/4)*n ≤ _ at hcount
    nlinarith only [hcount, hcount', hcoef', hnlow', hwpos]
  have hAsub : A ⊆ univ.filter (fun v => f v ∈ B) := by
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmapA v hv⟩
  have hAcard : (A.card : ℝ) ≤ ((w : ℝ)+1)*B.card := by
    have hh : (A.card : ℝ) ≤ (univ.filter (fun v => f v ∈ B)).card := by
      exact_mod_cast Finset.card_le_card hAsub
    exact hh.trans (hsize B).2
  have hrobust := hG X hXlower hXupper
  change (X.card : ℝ) + (3*ν/4)*n ≤ A.card at hrobust
  have hXcard := (hsize S).1
  change (w : ℝ)*S.card ≤ (X.card : ℝ) at hXcard
  have hScard : (S.card : ℝ) ≤ t := by
    dsimp [t]
    exact_mod_cast Finset.card_le_univ S
  have hcoef : 1 + ν/2 ≤ ν*w/4 := by linarith
  have hcoef' := mul_le_mul_of_nonneg_right hcoef ht
  have hnlow' := mul_le_mul_of_nonneg_left hnlow (show 0 ≤ 3*ν/4 by positivity)
  change (S.card : ℝ) + (ν/2)*t ≤ B.card
  nlinarith only [hAcard, hrobust, hXcard, hScard, hcoef', hnlow', hwpos]

noncomputable def partIndex (P : Finpartition (univ : Finset V)) (v : V) : P.parts :=
  ⟨(P.exists_mem (Finset.mem_univ v)).choose,
    (P.exists_mem (Finset.mem_univ v)).choose_spec.1⟩

theorem mem_partIndex (P : Finpartition (univ : Finset V)) (v : V) :
    v ∈ (partIndex P v).val :=
  (P.exists_mem (Finset.mem_univ v)).choose_spec.2

theorem partIndex_eq_iff (P : Finpartition (univ : Finset V)) (v : V) (i : P.parts) :
    partIndex P v = i ↔ v ∈ i.val := by
  constructor
  · rintro rfl
    exact mem_partIndex P v
  · intro hv
    exact Subtype.ext (P.eq_of_mem_parts (partIndex P v).property i.property
      (mem_partIndex P v) hv)

theorem partIndex_fiber (P : Finpartition (univ : Finset V)) (i : P.parts) :
    univ.filter (fun v => partIndex P v = i) = i.val := by
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, partIndex_eq_iff]

/-- The actual graph on the regular, dense pairs of parts. -/
noncomputable def clusterGraph (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)) (ε d : ℝ) : SimpleGraph P.parts where
  Adj i j := i ≠ j ∧ G.IsUniform ε i.val j.val ∧ d ≤ G.edgeDensity i.val j.val
  symm := by
    intro i j h
    exact ⟨h.1.symm, h.2.1.symm, by simpa only [G.edgeDensity_comm] using h.2.2⟩
  loopless := by intro i h; exact h.1 rfl

theorem reduced_edge_maps (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)) (ε d : ℝ) (v u : V)
    (hvu : (G.regularityReduced P ε d).Adj v u) :
    (clusterGraph G P ε d).Adj (partIndex P v) (partIndex P u) := by
  obtain ⟨_, A, hA, B, hB, hv, hu, hAB, hreg, hdense⟩ := hvu
  have hv' : partIndex P v = ⟨A,hA⟩ := (partIndex_eq_iff P v ⟨A,hA⟩).mpr hv
  have hu' : partIndex P u = ⟨B,hB⟩ := (partIndex_eq_iff P u ⟨B,hB⟩).mpr hu
  rw [hv', hu']
  exact ⟨fun h => hAB (congrArg Subtype.val h), hreg, hdense⟩

/-- The regular/dense spanning subgraph loses little total degree. -/
theorem regularity_total_degree_loss (G : SimpleGraph V) [DecidableRel G.Adj]
    [Nonempty V] (P : Finpartition (univ : Finset V)) (κ : ℝ)
    (hκ : 0 < κ) (hP : P.IsEquipartition) (hreg : P.IsUniform G (κ/8))
    (ht : 4/κ ≤ (P.parts.card : ℝ)) :
    (∑ v : V, ((G.degree v : ℝ) - (G.regularityReduced P (κ/8) (κ/4)).degree v)) <
      2*κ*(Fintype.card V : ℝ)^2 := by
  have h₁ : (∑ v : V, (G.degree v : ℝ)) = 2*(G.edgeFinset.card : ℝ) := by
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  have h₂ : (∑ v : V, ((G.regularityReduced P (κ/8) (κ/4)).degree v : ℝ)) =
      2*((G.regularityReduced P (κ/8) (κ/4)).edgeFinset.card : ℝ) := by
    exact_mod_cast (G.regularityReduced P (κ/8) (κ/4)).sum_degrees_eq_twice_card_edges
  rw [Finset.sum_sub_distrib, h₁, h₂]
  have hh := SimpleGraph.regularityReduced_edges_card_aux hκ hP hreg ht
  simp only [Nat.cast_pow] at hh
  nlinarith only [hh]

/-- Equalizing an equitable partition discards fewer than one vertex
per original part. -/
theorem equalized_clusters (P : Finpartition (univ : Finset V))
    (hP : P.IsEquipartition) (ht : 0 < P.parts.card) :
    ∃ C : P.parts → Finset V,
      (∀ i, C i ⊆ i.val) ∧
      (∀ i, (C i).card = Fintype.card V / P.parts.card) ∧
      (∀ i j, i ≠ j → Disjoint (C i) (C j)) ∧
      (univ \ univ.biUnion C).card ≤ P.parts.card := by
  classical
  have hexist (i : P.parts) : ∃ T : Finset V,
      T ⊆ i.val ∧ T.card = Fintype.card V / P.parts.card := by
    apply Finset.exists_subset_card_eq
    simpa only [Finset.card_univ] using hP.average_le_card_part i.property
  choose C hsub hcard using hexist
  have hdisjoint (i j : P.parts) (hij : i ≠ j) : Disjoint (C i) (C j) := by
    have hne : i.val ≠ j.val := fun h => hij (Subtype.ext h)
    exact (P.disjoint i.property j.property hne).mono (hsub i) (hsub j)
  have hunion : (univ.biUnion C).card = P.parts.card * (Fintype.card V / P.parts.card) := by
    rw [Finset.card_biUnion (fun i _ j _ hij => hdisjoint i j hij)]
    simp only [hcard, Finset.sum_const, Finset.card_univ, Fintype.card_coe,
      nsmul_eq_mul, Nat.cast_id]
  refine ⟨C, hsub, hcard, hdisjoint, ?_⟩
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hunion]
  have hdiv := Nat.mod_add_div (Fintype.card V) P.parts.card
  have hmod := Nat.mod_lt (Fintype.card V) ht
  omega

theorem interedges_card_eq_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (X Z : Finset V) :
    (G.interedges X Z).card = ∑ z ∈ Z, (G.neighborFinset z ∩ X).card := by
  classical
  calc
    _ = ∑ x ∈ X, ∑ z ∈ Z, if G.Adj x z then (1 : ℕ) else 0 := by
      simp only [G.interedges_def, Finset.card_eq_sum_ones, Finset.sum_filter,
        Finset.sum_product]
    _ = ∑ z ∈ Z, ∑ x ∈ X, if G.Adj x z then (1 : ℕ) else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro z _
      have hh : X.filter (fun x => G.Adj x z) = G.neighborFinset z ∩ X := by
        ext x
        simp [G.adj_comm, and_comm]
      simp only [Finset.sum_boole, Nat.cast_id, hh]

/-- Uniformity and density of the original parts give precisely the
large-subset edge-count inequality used in the lifting argument. -/
theorem trimmed_pair_lower_regular (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B C D X Z : Finset V) (κ ε : ℝ) (w : ℕ)
    (hκ : 0 < κ) (hκeps : κ ≤ ε) (hw : 1 ≤ w)
    (hA : A.card ≤ w+1) (hB : B.card ≤ w+1)
    (hC : C ⊆ A) (hD : D ⊆ B) (hX : X ⊆ C) (hZ : Z ⊆ D)
    (hreg : G.IsUniform (κ/8) A B) (hdense : κ/4 ≤ (G.edgeDensity A B : ℝ))
    (hXlarge : ε*w ≤ (X.card : ℝ)) (hZlarge : ε*w ≤ (Z.card : ℝ)) :
    (κ/8)*X.card*Z.card ≤ ∑ z ∈ Z, ((G.neighborFinset z ∩ X).card : ℝ) := by
  have hwR : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hε : 0 < ε := hκ.trans_le hκeps
  have hXpos : (0 : ℝ) < X.card := lt_of_lt_of_le (by positivity) hXlarge
  have hZpos : (0 : ℝ) < Z.card := lt_of_lt_of_le (by positivity) hZlarge
  have hAth : (A.card : ℝ)*(κ/8) ≤ X.card := by
    have hAR : (A.card : ℝ) ≤ (w : ℝ)+1 := by exact_mod_cast hA
    have hmul := mul_le_mul_of_nonneg_right hAR (show 0 ≤ κ/8 by positivity)
    have heps := mul_le_mul_of_nonneg_right hκeps (Nat.cast_nonneg w (α := ℝ))
    have hsmall := mul_nonneg hκ.le (show 0 ≤ (w : ℝ)-1 by linarith)
    nlinarith only [hmul, heps, hsmall, hXlarge]
  have hBth : (B.card : ℝ)*(κ/8) ≤ Z.card := by
    have hBR : (B.card : ℝ) ≤ (w : ℝ)+1 := by exact_mod_cast hB
    have hmul := mul_le_mul_of_nonneg_right hBR (show 0 ≤ κ/8 by positivity)
    have heps := mul_le_mul_of_nonneg_right hκeps (Nat.cast_nonneg w (α := ℝ))
    have hsmall := mul_nonneg hκ.le (show 0 ≤ (w : ℝ)-1 by linarith)
    nlinarith only [hmul, heps, hsmall, hZlarge]
  have hd := (abs_lt.mp (hreg (hX.trans hC) (hZ.trans hD) hAth hBth)).1
  have hden : κ/8 ≤ (G.edgeDensity X Z : ℝ) := by linarith
  have hformula : (G.edgeDensity X Z : ℝ) =
      (G.interedges X Z).card / ((X.card : ℝ)*Z.card) := by
    simp only [SimpleGraph.edgeDensity_def, Rat.cast_div, Rat.cast_natCast, Rat.cast_mul]
  rw [hformula] at hden
  have hcount := (le_div_iff₀ (mul_pos hXpos hZpos)).mp hden
  have hsum : ((G.interedges X Z).card : ℝ) =
      ∑ z ∈ Z, ((G.neighborFinset z ∩ X).card : ℝ) := by
    exact_mod_cast interedges_card_eq_sum G X Z
  rw [hsum] at hcount
  nlinarith only [hcount]

set_option maxHeartbeats 1200000 in
/-- Actual equal clusters and a robust reduced graph are obtained from
the equitable regularity lemma. The upper bound, density, and order
threshold all precede the graph. -/
theorem exists_robust_regular_clusters (ν τ ε : ℝ)
    (hν : 0 < ν) (hν1 : ν ≤ 1) (hτ : 0 ≤ τ) (hε : 0 < ε) :
    ∃ K : ℕ, 0 < K ∧ ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧ ∃ n₀ : ℕ,
      ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V → IsRobustExpander G ν τ →
        ∃ P : Finpartition (univ : Finset V), ∃ w : ℕ,
          ∃ C : P.parts → Finset V, ∃ R : SimpleGraph P.parts,
            P.parts.card ≤ K ∧ 1 ≤ (ν/4)*P.parts.card ∧ 0 < w ∧
            (∀ i, (C i).card = w) ∧
            (∀ i j, i ≠ j → Disjoint (C i) (C j)) ∧
            ((univ \ univ.biUnion C).card : ℝ) ≤ ε*Fintype.card V ∧
            (1/(2*(K : ℝ)))*Fintype.card V ≤ w ∧
            IsRobustExpander R (ν/2) (2*τ) ∧
            (∀ i j, R.Adj i j → ∀ X Z : Finset V,
              X ⊆ C i → Z ⊆ C j → ε*w ≤ (X.card : ℝ) → ε*w ≤ (Z.card : ℝ) →
              d*X.card*Z.card ≤ ∑ z ∈ Z, ((G.neighborFinset z ∩ X).card : ℝ)) := by
  classical
  let κ := min (ν^2/64) ε
  have hκ : 0 < κ := lt_min (by positivity) hε
  have hκν : κ ≤ ν^2/64 := min_le_left _ _
  have hκε : κ ≤ ε := min_le_right _ _
  have hκ1 : κ/8 ≤ 1 := by nlinarith only [hκν, hν, hν1]
  let L := Nat.ceil (max (4/κ) (4/ν))
  let K := SzemerediRegularity.bound (κ/8) L
  have hK : 0 < K := SzemerediRegularity.bound_pos _ _
  have hLK : L ≤ K := SzemerediRegularity.le_bound _ _
  have hκL : 4/κ ≤ (L : ℝ) := (le_max_left _ _).trans (Nat.le_ceil _)
  have hνL : 4/ν ≤ (L : ℝ) := (le_max_right _ _).trans (Nat.le_ceil _)
  have hL : 0 < L := by
    have hh : (0 : ℝ) < L := lt_of_lt_of_le (by positivity) hκL
    exact_mod_cast hh
  obtain ⟨q, hq⟩ := exists_nat_gt (max (8/ν) (max (1/ε) 2))
  have hqν : 8/ν < (q : ℝ) := (le_max_left _ _).trans_lt hq
  have hqε : 1/ε < (q : ℝ) :=
    (le_trans (le_max_left _ _) (le_max_right _ _)).trans_lt hq
  have hq2 : (2 : ℝ) < q :=
    (le_trans (le_max_right _ _) (le_max_right _ _)).trans_lt hq
  refine ⟨K, hK, κ/8, by positivity, hκ1, K*(q+1), ?_⟩
  intro V _ _ G _ hn hG
  let n := Fintype.card V
  have hKbase : K ≤ K*(q+1) := by
    have hh := Nat.mul_le_mul_left K (show 1 ≤ q+1 by omega)
    simpa only [Nat.mul_one] using hh
  have hKn : K ≤ n := hKbase.trans hn
  have hnpos : 0 < n := hK.trans_le hKn
  letI : Nonempty V := Fintype.card_pos_iff.mp hnpos
  obtain ⟨P, hP, hLt, htK, hreg⟩ := szemeredi_regularity G (by positivity : 0 < κ/8)
    (hLK.trans hKn)
  let t := P.parts.card
  let w := n/t
  have ht : 0 < t := hL.trans_le hLt
  have hqw : q ≤ w := by
    apply (Nat.le_div_iff_mul_le ht).mpr
    calc
      q*t ≤ q*K := Nat.mul_le_mul_left q htK
      _ ≤ K*(q+1) := by nlinarith
      _ ≤ n := hn
  have hqwR : (q : ℝ) ≤ w := by exact_mod_cast hqw
  have hw2 : (2 : ℝ) ≤ w := hq2.le.trans hqwR
  have hwpos : 0 < w := by
    have hh : (0 : ℝ) < w := by linarith
    exact_mod_cast hh
  have hwν : 8 ≤ ν*w := by
    have hh := (div_lt_iff₀ hν).mp (hqν.trans_le hqwR)
    nlinarith only [hh]
  have hwε : 1 ≤ ε*w := by
    have hh := (div_lt_iff₀ hε).mp (hqε.trans_le hqwR)
    nlinarith only [hh]
  have htR : (t : ℝ) ≤ K := by exact_mod_cast htK
  have hLtR : (L : ℝ) ≤ t := by exact_mod_cast hLt
  have hκt : 4/κ ≤ (P.parts.card : ℝ) := hκL.trans hLtR
  have hνt : 1 ≤ (ν/4)*P.parts.card := by
    have hh := (div_le_iff₀ hν).mp (hνL.trans hLtR)
    nlinarith only [hh]
  let H := G.regularityReduced P (κ/8) (κ/4)
  let R := clusterGraph G P (κ/8) (κ/4)
  have hHloss : (∑ v : V, ((G.degree v : ℝ) - H.degree v)) ≤
      ν^2/16*(Fintype.card V : ℝ)^2 := by
    have hh := regularity_total_degree_loss G P κ hκ hP hreg hκt
    have hc : 2*κ ≤ ν^2/16 := by nlinarith only [hκν, sq_nonneg ν]
    exact hh.le.trans (mul_le_mul_of_nonneg_right hc (sq_nonneg _))
  have hH : IsRobustExpander H (3*ν/4) τ :=
    robust_after_total_degree_loss G H ν τ hν hnpos
      SimpleGraph.regularityReduced_le hG hHloss
  have hpartsLow (i : P.parts) : w ≤ (univ.filter (fun v => partIndex P v = i)).card := by
    rw [partIndex_fiber]
    simpa only [Finset.card_univ] using hP.average_le_card_part i.property
  have hpartsHigh (i : P.parts) :
      (univ.filter (fun v => partIndex P v = i)).card ≤ w+1 := by
    rw [partIndex_fiber]
    simpa only [Finset.card_univ] using hP.card_part_le_average_add_one i.property
  have hR : IsRobustExpander R (ν/2) (2*τ) :=
    robust_quotient H R (partIndex P) w ν τ hν hν1 hτ hwν hpartsLow hpartsHigh
      (reduced_edge_maps G P (κ/8) (κ/4)) hH
  obtain ⟨C, hC, hCcard, hCdisjoint, hexception⟩ := equalized_clusters P hP ht
  have hnlow : (t : ℝ)*w ≤ n := by
    exact_mod_cast Nat.mul_div_le n t
  have hnhigh : (n : ℝ) ≤ ((w : ℝ)+1)*t := by
    have hh := (fiber_union_card_bounds (partIndex P) w hpartsLow hpartsHigh univ).2
    simpa only [Finset.mem_univ, Finset.filter_true, Finset.card_univ,
      Fintype.card_coe, Nat.cast_mul, Nat.cast_add, Nat.cast_one] using
      (show ((univ.filter (fun v => partIndex P v ∈ (univ : Finset P.parts))).card : ℝ) ≤
        ((w : ℝ)+1)*(univ : Finset P.parts).card by exact_mod_cast hh)
  have htε : (t : ℝ) ≤ ε*n := by
    have hh₁ := mul_le_mul_of_nonneg_left hnlow hε.le
    have hh₂ := mul_le_mul_of_nonneg_right hwε (Nat.cast_nonneg t (α := ℝ))
    nlinarith only [hh₁, hh₂]
  have hlinear : (1/(2*(K : ℝ)))*n ≤ w := by
    have hKreal : (0 : ℝ) < K := by exact_mod_cast hK
    have hh₁ := mul_le_mul_of_nonneg_right
      (show (w : ℝ)+1 ≤ 2*w by linarith) (Nat.cast_nonneg t (α := ℝ))
    have hh₂ := mul_le_mul_of_nonneg_left htR (show 0 ≤ 2*(w : ℝ) by positivity)
    have hh : (n : ℝ) ≤ (w : ℝ)*(2*K) := by nlinarith only [hnhigh, hh₁, hh₂]
    calc
      _ = (n : ℝ)/(2*K) := by ring
      _ ≤ w := (div_le_iff₀ (by positivity)).mpr hh
  refine ⟨P, w, C, R, htK, hνt, hwpos, hCcard, hCdisjoint, ?_, hlinear, hR, ?_⟩
  · have hh : ((univ \ univ.biUnion C).card : ℝ) ≤ t := by exact_mod_cast hexception
    exact hh.trans htε
  · intro i j hij X Z hX hZ hXlarge hZlarge
    exact trimmed_pair_lower_regular G i.val j.val (C i) (C j) X Z κ ε w
      hκ hκε (by omega)
      (by simpa only [Finset.card_univ] using hP.card_part_le_average_add_one i.property)
      (by simpa only [Finset.card_univ] using hP.card_part_le_average_add_one j.property)
      (hC i) (hC j) hX hZ hij.2.1 hij.2.2 hXlarge hZlarge

end Overfull.PairedCut
