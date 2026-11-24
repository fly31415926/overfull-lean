import Overfull.PairedCut.Sides

/-!
# Deterministic lifting from lower-regular cluster pairs

This file proves the lifting step for the paired cut. It takes an actual
reduced robust graph and lower bounds on actual edge counts between large
subsets of its adjacent clusters. Existence and robust inheritance of a
regularity partition are separate from this implication.
-/

namespace Overfull.PairedCut

open Finset Classical
open scoped BigOperators

variable {V J : Type*} [DecidableEq V]

theorem card_cluster_union (C : J → Finset V)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (C i) (C j)) (T : Finset J) :
    (T.biUnion C).card = ∑ i ∈ T, (C i).card := by
  apply Finset.card_biUnion
  intro i _ j _ hij
  exact hdisjoint i j hij

theorem sum_cluster_inter_card (C : J → Finset V)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (S : Finset V) (T : Finset J) :
    (∑ i ∈ T, (S ∩ C i).card) = (S ∩ T.biUnion C).card := by
  have hd : ∀ i j, i ≠ j → Disjoint (S ∩ C i) (S ∩ C j) := by
    intro i j hij
    exact (hdisjoint i j hij).mono Finset.inter_subset_right Finset.inter_subset_right
  rw [← card_cluster_union (fun i => S ∩ C i) hd T]
  congr 1
  ext v
  simp only [Finset.mem_biUnion,Finset.mem_inter]
  constructor
  · rintro ⟨i,hi,hS,hiC⟩
    exact ⟨hS,i,hi,hiC⟩
  · rintro ⟨hS,i,hi,hiC⟩
    exact ⟨i,hi,hS,hiC⟩

theorem sum_cluster_inter_card_le (C : J → Finset V)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (S : Finset V) (T : Finset J) :
    (∑ i ∈ T, (S ∩ C i).card) ≤ S.card := by
  rw [sum_cluster_inter_card C hdisjoint S T]
  exact Finset.card_le_card Finset.inter_subset_left

theorem cluster_partition_count [Fintype J] (C : J → Finset V)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (C i) (C j)) (S : Finset V) :
    S.card = (S \ univ.biUnion C).card + ∑ i : J, (S ∩ C i).card := by
  rw [sum_cluster_inter_card C hdisjoint S univ]
  have h := Finset.card_inter_add_card_sdiff S (univ.biUnion C)
  omega

/-- Robust expansion continues above the tested range with a capped lower
bound. The extra robust-neighborhood margin absorbs the integral rounding. -/
theorem reduced_robust_large_set [Fintype J] [DecidableEq J]
    (R : SimpleGraph J) [DecidableRel R.Adj]
    (γ τ : ℝ) (hγ : 0 < γ) (hγτ : γ ≤ τ) (hτ : τ ≤ 1 / 8)
    (ht : 1 ≤ γ * Fintype.card J) (hR : IsRobustExpander R (2 * γ) (2 * τ))
    (I : Finset J) (hI : 2 * τ * Fintype.card J ≤ (I.card : ℝ)) :
    (I.card : ℝ) + γ * Fintype.card J ≤ (robustNeighbors R γ I).card ∨
    (1 - 2 * τ + γ) * Fintype.card J ≤ (robustNeighbors R γ I).card := by
  classical
  let t : ℝ := Fintype.card J
  have ht0 : 0 ≤ t := Nat.cast_nonneg _
  have hγ1 : γ ≤ 1 / 8 := hγτ.trans hτ
  have hτ0 : 0 < τ := hγ.trans_le hγτ
  have ht8 : 8 ≤ t := by dsimp [t] at *; nlinarith
  by_cases hupper : (I.card : ℝ) ≤ (1 - 2 * τ) * t
  · left
    have hex := hR I hI hupper
    have hmono : ((robustNeighbors R (2 * γ) I).card : ℝ) ≤
        (robustNeighbors R γ I).card := by
      exact_mod_cast Finset.card_le_card
        (robustNeighbors_mono_parameter R (2 * γ) γ (by linarith) I)
    have hnonneg : 0 ≤ γ * t := mul_nonneg hγ.le ht0
    dsimp [t] at *
    linarith
  · right
    let a := ⌊(1 - 2 * τ) * t⌋₊
    have hu0 : 0 ≤ (1 - 2 * τ) * t := mul_nonneg (by linarith) ht0
    have haf : (a : ℝ) ≤ (1 - 2 * τ) * t := Nat.floor_le hu0
    have hal : (1 - 2 * τ) * t - 1 < (a : ℝ) := by
      have h := Nat.lt_floor_add_one ((1 - 2 * τ) * t)
      dsimp [a]
      linarith
    have haI : a ≤ I.card := by exact_mod_cast haf.trans (le_of_not_ge hupper)
    obtain ⟨I',hsub,hcard⟩ := Finset.exists_subset_card_eq haI
    have hlow : 2 * τ * Fintype.card J ≤ (I'.card : ℝ) := by
      rw [hcard]
      have hbound : 4 * τ * t ≤ t / 2 := by nlinarith
      dsimp [t] at *
      linarith
    have hex := hR I' hlow (by simpa only [hcard] using haf)
    have hmono : robustNeighbors R (2 * γ) I' ⊆ robustNeighbors R γ I := by
      intro v hv
      rw [mem_robustNeighbors] at hv ⊢
      have hcount : ((R.neighborFinset v ∩ I').card : ℝ) ≤
          (R.neighborFinset v ∩ I).card := by
        exact_mod_cast Finset.card_le_card (Finset.inter_subset_inter_left hsub)
      dsimp [t] at *
      nlinarith
    have hmono' : ((robustNeighbors R (2 * γ) I').card : ℝ) ≤
        (robustNeighbors R γ I).card := by exact_mod_cast Finset.card_le_card hmono
    rw [hcard] at hex
    dsimp [t] at *
    nlinarith

variable [Fintype V] [Fintype J] [DecidableEq J]

/-- Lower regularity on each edge of the actual reduced graph, expressed
using incidences of the original graph. -/
def LowerRegularPairs (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : SimpleGraph J) (C : J → Finset V) (ε d : ℝ) (w : ℕ) : Prop :=
  ∀ i j, R.Adj i j → ∀ X Z : Finset V,
    X ⊆ C i → Z ⊆ C j → ε * w ≤ (X.card : ℝ) → ε * w ≤ (Z.card : ℝ) →
    d * X.card * Z.card ≤ ∑ z ∈ Z, ((G.neighborFinset z ∩ X).card : ℝ)

theorem lower_regular_incidence (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : SimpleGraph J) [DecidableRel R.Adj] (C : J → Finset V)
    (ε d q : ℝ) (w : ℕ) (hd : 0 ≤ d)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hregular : LowerRegularPairs G R C ε d w)
    (I : Finset J) (S Z : Finset V) (j : J)
    (hZ : Z ⊆ C j) (hZlarge : ε * w ≤ (Z.card : ℝ))
    (hq : ε * w ≤ q) (hactive : ∀ i ∈ I, q ≤ ((S ∩ C i).card : ℝ)) :
    d * q * (R.neighborFinset j ∩ I).card * Z.card ≤
      ∑ z ∈ Z, ((G.neighborFinset z ∩ S).card : ℝ) := by
  let T := R.neighborFinset j ∩ I
  have hlower (i : J) (hi : i ∈ T) : d * q * Z.card ≤
      ∑ z ∈ Z, ((G.neighborFinset z ∩ (S ∩ C i)).card : ℝ) := by
    have hi' := Finset.mem_inter.mp hi
    have hadj' : R.Adj j i := by simpa using hi'.1
    have hadj : R.Adj i j := hadj'.symm
    have hq' := hactive i hi'.2
    have hreg := hregular i j hadj (S ∩ C i) Z Finset.inter_subset_right hZ
      (hq.trans hq') hZlarge
    have hmono := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq' hd)
      (Nat.cast_nonneg Z.card : (0 : ℝ) ≤ Z.card)
    exact hmono.trans hreg
  have hsum : d * q * T.card * Z.card ≤
      ∑ i ∈ T, ∑ z ∈ Z, ((G.neighborFinset z ∩ (S ∩ C i)).card : ℝ) := by
    calc
      _ = ∑ _i ∈ T, d * q * Z.card := by
        simp only [Finset.sum_const,nsmul_eq_mul]
        ring
      _ ≤ _ := Finset.sum_le_sum hlower
  rw [Finset.sum_comm] at hsum
  apply hsum.trans
  apply Finset.sum_le_sum
  intro z _
  have h := sum_cluster_inter_card_le C hdisjoint (G.neighborFinset z ∩ S) T
  simp only [Finset.inter_assoc] at h
  exact_mod_cast h

/-- In a reduced robust-neighbor cluster, fewer than `γw/20` vertices
can have fewer than `dγ²n/200` neighbors in the tested set. -/
theorem bad_cluster_small (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : SimpleGraph J) [DecidableRel R.Adj] (C : J → Finset V)
    (ε d γ : ℝ) (w : ℕ) (hd : 0 < d) (hγ : 0 < γ) (hw : 0 < w)
    (hε : ε ≤ γ / 20) (hm : 0 < (Fintype.card V : ℝ))
    (hcover : (Fintype.card V : ℝ) ≤ 2 * Fintype.card J * w)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hregular : LowerRegularPairs G R C ε d w)
    (I : Finset J) (S Z : Finset V) (j : J)
    (hj : j ∈ robustNeighbors R γ I) (hZ : Z ⊆ C j)
    (hactive : ∀ i ∈ I, γ * w / 20 ≤ ((S ∩ C i).card : ℝ))
    (hbad : ∀ z ∈ Z, ((G.neighborFinset z ∩ S).card : ℝ) <
      d * γ ^ 2 * Fintype.card V / 200) :
    (Z.card : ℝ) < γ * w / 20 := by
  by_contra hZsmall
  have hZlarge := le_of_not_gt hZsmall
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  have hZpos : (0 : ℝ) < Z.card := lt_of_lt_of_le (by positivity) hZlarge
  have hεw : ε * w ≤ γ * w / 20 := by nlinarith
  have hlow := lower_regular_incidence G R C ε d (γ * w / 20) w hd.le hdisjoint
    hregular I S Z j hZ (hεw.trans hZlarge) hεw hactive
  have hcount := (mem_robustNeighbors R γ I j).mp hj
  have hcount' := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcount (show 0 ≤ d * (γ * w / 20) by positivity))
    (Nat.cast_nonneg Z.card : (0 : ℝ) ≤ Z.card)
  have hlow' : d * γ ^ 2 * Fintype.card J * w * Z.card / 20 ≤
      ∑ z ∈ Z, ((G.neighborFinset z ∩ S).card : ℝ) := by
    nlinarith
  have hcov := mul_le_mul_of_nonneg_left hcover
    (show 0 ≤ d * γ ^ 2 * Z.card / 40 by positivity)
  have hlow'' : d * γ ^ 2 * Fintype.card V * Z.card / 40 ≤
      ∑ z ∈ Z, ((G.neighborFinset z ∩ S).card : ℝ) := by nlinarith
  have hupp : (∑ z ∈ Z, ((G.neighborFinset z ∩ S).card : ℝ)) ≤
      d * γ ^ 2 * Fintype.card V * Z.card / 200 := by
    calc
      _ ≤ ∑ _z ∈ Z, d * γ ^ 2 * Fintype.card V / 200 :=
        Finset.sum_le_sum (fun z hz => (hbad z hz).le)
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring
  have hp : 0 < d * γ ^ 2 * Fintype.card V * Z.card := by positivity
  linarith

omit [DecidableEq J] in
theorem cluster_size_bounds (C : J → Finset V) (ε : ℝ) (w : ℕ)
    (hε : ε ≤ 1 / 2)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hsize : ∀ i, (C i).card = w)
    (hexception : (((univ.biUnion C)ᶜ).card : ℝ) ≤ ε * Fintype.card V) :
    (Fintype.card J : ℝ) * w ≤ Fintype.card V ∧
    (1 - ε) * Fintype.card V ≤ (Fintype.card J : ℝ) * w ∧
    (Fintype.card V : ℝ) ≤ 2 * Fintype.card J * w := by
  have hcard : (univ.biUnion C).card = Fintype.card J * w := by
    rw [card_cluster_union C hdisjoint]
    simp only [hsize,Finset.sum_const,Finset.card_univ,smul_eq_mul]
  have hle : (Fintype.card J : ℝ) * w ≤ Fintype.card V := by
    exact_mod_cast hcard ▸ Finset.card_le_univ (univ.biUnion C)
  have hsum : ((univ.biUnion C).card : ℝ) + ((univ.biUnion C)ᶜ).card =
      Fintype.card V := by exact_mod_cast Finset.card_add_card_compl (univ.biUnion C)
  rw [hcard,Nat.cast_mul] at hsum
  have hm : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  refine ⟨hle,by linarith,?_⟩
  nlinarith

noncomputable def activeClusters (C : J → Finset V) (γ : ℝ) (w : ℕ)
    (S : Finset V) : Finset J :=
  univ.filter (fun i => γ * w / 20 ≤ ((S ∩ C i).card : ℝ))

theorem active_clusters_bound (C : J → Finset V) (ε γ : ℝ) (w : ℕ)
    (hε : 0 ≤ ε) (hεγ : ε ≤ γ / 100) (hγ : 0 ≤ γ)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hcover : (Fintype.card V : ℝ) ≤ 2 * Fintype.card J * w)
    (hexception : (((univ.biUnion C)ᶜ).card : ℝ) ≤ ε * Fintype.card V)
    (A S : Finset V) (hS : S ⊆ A)
    (hA : ∀ i, ((A ∩ C i).card : ℝ) ≤ (1 / 2 + ε) * w) :
    2 * (S.card : ℝ) ≤ (activeClusters C γ w S).card * (w : ℝ) +
      γ * Fintype.card J * w / 4 := by
  let I := activeClusters C γ w S
  have hper (i : J) : ((S ∩ C i).card : ℝ) ≤
      (if i ∈ I then (w : ℝ) / 2 else 0) + (ε + γ / 20) * w := by
    by_cases hi : i ∈ I
    · rw [if_pos hi]
      have hle : ((S ∩ C i).card : ℝ) ≤ (A ∩ C i).card := by
        exact_mod_cast Finset.card_le_card (Finset.inter_subset_inter_right hS)
      have hp : 0 ≤ γ * (w : ℝ) := mul_nonneg hγ (Nat.cast_nonneg _)
      nlinarith [hA i]
    · rw [if_neg hi]
      have hsmall : ((S ∩ C i).card : ℝ) < γ * w / 20 := by
        exact lt_of_not_ge (fun h => hi (by simp [I,activeClusters,h]))
      have hp : 0 ≤ ε * (w : ℝ) := mul_nonneg hε (Nat.cast_nonneg _)
      linarith
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (univ : Finset J)) => hper i)
  have hif : (∑ i : J, if i ∈ I then (w : ℝ) / 2 else 0) = I.card * ((w : ℝ) / 2) := by
    rw [← Finset.sum_filter]
    simp
  rw [Finset.sum_add_distrib,hif,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hsum
  have hpart : (S.card : ℝ) = (S \ univ.biUnion C).card +
      ∑ i : J, ((S ∩ C i).card : ℝ) := by
    exact_mod_cast cluster_partition_count C hdisjoint S
  have hremain : ((S \ univ.biUnion C).card : ℝ) ≤ ε * Fintype.card V := by
    apply le_trans _ hexception
    exact_mod_cast Finset.card_le_card (show S \ univ.biUnion C ⊆ (univ.biUnion C)ᶜ by
      intro v hv
      exact Finset.mem_compl.mpr (Finset.mem_sdiff.mp hv).2)
  have hc := mul_le_mul_of_nonneg_left hcover hε
  have he := mul_le_mul_of_nonneg_right hεγ
    (show 0 ≤ (Fintype.card J : ℝ) * w by positivity)
  change 2 * (S.card : ℝ) ≤ I.card * (w : ℝ) + γ * Fintype.card J * w / 4
  nlinarith

theorem reduced_neighbor_union_surplus (R : SimpleGraph J) [DecidableRel R.Adj]
    (C : J → Finset V) (ε γ τ : ℝ) (w : ℕ)
    (hγ : 0 < γ) (hγτ : γ ≤ τ) (hτ : τ ≤ 1 / 8)
    (hε : 0 ≤ ε) (hεγ : ε ≤ γ / 100) (hw : 0 < w)
    (ht : 1 ≤ γ * Fintype.card J)
    (hR : IsRobustExpander R (2 * γ) (2 * τ))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hsize : ∀ i, (C i).card = w)
    (hexception : (((univ.biUnion C)ᶜ).card : ℝ) ≤ ε * Fintype.card V)
    (A B S : Finset V) (hS : S ⊆ A)
    (hA : ∀ i, ((A ∩ C i).card : ℝ) ≤ (1 / 2 + ε) * w)
    (hB : ∀ i, (1 / 2 - ε) * w ≤ ((B ∩ C i).card : ℝ))
    (hSlower : 2 * τ * Fintype.card V ≤ (S.card : ℝ))
    (hSupper : (S.card : ℝ) ≤ (1 - 4 * τ) * Fintype.card V / 2) :
    (S.card : ℝ) + γ * Fintype.card V / 8 ≤
      (B ∩ (robustNeighbors R γ (activeClusters C γ w S)).biUnion C).card := by
  have hγ1 : γ ≤ 1 / 8 := hγτ.trans hτ
  have hτ0 : 0 ≤ τ := hγ.le.trans hγτ
  have hε1 : ε ≤ 1 / 2 := by linarith
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  have hn0 : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have ht0 : (0 : ℝ) ≤ Fintype.card J := Nat.cast_nonneg _
  obtain ⟨htw,hcovered,hcover⟩ := cluster_size_bounds C ε w hε1 hdisjoint hsize hexception
  let I := activeClusters C γ w S
  let T := robustNeighbors R γ I
  have hactive := active_clusters_bound C ε γ w hε hεγ hγ.le hdisjoint
    hcover hexception A S hS hA
  change 2 * (S.card : ℝ) ≤ I.card * (w : ℝ) + γ * Fintype.card J * w / 4 at hactive
  have hI : 2 * τ * Fintype.card J ≤ (I.card : ℝ) := by
    apply (mul_le_mul_iff_of_pos_right hwR).mp
    have htwmul := mul_le_mul_of_nonneg_left htw (show 0 ≤ 4 * τ by positivity)
    have hg := mul_le_mul_of_nonneg_right hγτ
      (show 0 ≤ (Fintype.card J : ℝ) * w by positivity)
    nlinarith only [hactive,htwmul,hg,hSlower]
  have hcases := reduced_robust_large_set R γ τ hγ hγτ hτ ht hR I hI
  have hTcard : (T.card : ℝ) ≤ Fintype.card J := by exact_mod_cast Finset.card_le_univ T
  have hunion : (1 / 2 - ε) * w * T.card ≤ (B ∩ T.biUnion C).card := by
    have heq : ((B ∩ T.biUnion C).card : ℝ) = ∑ j ∈ T, ((B ∩ C j).card : ℝ) := by
      exact_mod_cast (sum_cluster_inter_card C hdisjoint B T).symm
    rw [heq]
    calc
      _ = ∑ _j ∈ T, (1 / 2 - ε) * (w : ℝ) := by
        simp only [Finset.sum_const,nsmul_eq_mul]
        ring
      _ ≤ _ := Finset.sum_le_sum (fun j _ => hB j)
  have hTr : ε * T.card * (w : ℝ) ≤ ε * Fintype.card J * w := by
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hTcard hε) hwR.le
  have hu : (T.card : ℝ) * w / 2 - ε * Fintype.card J * w ≤
      (B ∩ T.biUnion C).card := by nlinarith only [hunion,hTr]
  change (S.card : ℝ) + γ * Fintype.card V / 8 ≤ (B ∩ T.biUnion C).card
  rcases hcases with hcase | hcase
  · change (I.card : ℝ) + γ * Fintype.card J ≤ (T.card : ℝ) at hcase
    have hc := mul_le_mul_of_nonneg_right hcase (show 0 ≤ (w : ℝ) / 2 by positivity)
    have he := mul_le_mul_of_nonneg_right (show ε ≤ γ / 8 by linarith)
      (show 0 ≤ (Fintype.card J : ℝ) * w by positivity)
    have hn := mul_le_mul_of_nonneg_left hcover (show 0 ≤ γ / 8 by positivity)
    nlinarith only [hc,he,hn,hu,hactive]
  · change (1 - 2 * τ + γ) * Fintype.card J ≤ (T.card : ℝ) at hcase
    have hc := mul_le_mul_of_nonneg_right hcase (show 0 ≤ (w : ℝ) / 2 by positivity)
    let a := (1 : ℝ) / 2 - τ + γ / 2
    have ha0 : 0 ≤ a := by dsimp only [a]; linarith only [hτ,hγ]
    have ha1 : a ≤ 1 := by dsimp only [a]; linarith only [hγτ,hτ0]
    have hn := mul_le_mul_of_nonneg_left hcovered ha0
    have hep := mul_le_mul_of_nonneg_left htw hε
    have hloss := mul_le_mul_of_nonneg_right ha1
      (show 0 ≤ ε * Fintype.card V by positivity)
    have hcoef : (1 / 2 - 2 * τ) + γ / 8 ≤ a - 2 * ε := by
      dsimp only [a]
      linarith only [hγτ,hεγ,hγ]
    have hcoef' := mul_le_mul_of_nonneg_right hcoef hn0
    dsimp only [a] at hn hloss hcoef'
    nlinarith only [hc,hn,hep,hloss,hcoef',hu,hSupper]

/-- The set version of deterministic lifting. The robust neighbors are
actual vertices of `B`, counted using their actual neighbors in `S`. -/
theorem lower_regular_cut_expansion (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : SimpleGraph J) [DecidableRel R.Adj] (C : J → Finset V)
    (ε d γ τ : ℝ) (w : ℕ)
    (hd : 0 < d) (hd1 : d ≤ 1) (hγ : 0 < γ) (hγτ : γ ≤ τ) (hτ : τ ≤ 1 / 8)
    (hε : 0 ≤ ε) (hεγ : ε ≤ γ / 100) (hw : 0 < w)
    (ht : 1 ≤ γ * Fintype.card J)
    (hR : IsRobustExpander R (2 * γ) (2 * τ))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hsize : ∀ i, (C i).card = w)
    (hexception : (((univ.biUnion C)ᶜ).card : ℝ) ≤ ε * Fintype.card V)
    (hregular : LowerRegularPairs G R C ε d w)
    (A B S : Finset V) (hS : S ⊆ A)
    (hA : ∀ i, ((A ∩ C i).card : ℝ) ≤ (1 / 2 + ε) * w)
    (hB : ∀ i, (1 / 2 - ε) * w ≤ ((B ∩ C i).card : ℝ))
    (hSlower : 2 * τ * Fintype.card V ≤ (S.card : ℝ))
    (hSupper : (S.card : ℝ) ≤ (1 - 4 * τ) * Fintype.card V / 2) :
    (S.card : ℝ) + d * γ ^ 2 * Fintype.card V / 200 ≤
      (B ∩ robustNeighbors G (d * γ ^ 2 / 200) S).card := by
  have hγ1 : γ ≤ 1 / 8 := hγτ.trans hτ
  have hε1 : ε ≤ 1 / 2 := by linarith
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  have htR : (0 : ℝ) < Fintype.card J := by
    have ht0 : (0 : ℝ) ≤ Fintype.card J := Nat.cast_nonneg _
    by_contra h
    have hz : (Fintype.card J : ℝ) = 0 := le_antisymm (le_of_not_gt h) ht0
    rw [hz,mul_zero] at ht
    norm_num at ht
  obtain ⟨htw,hcovered,hcover⟩ := cluster_size_bounds C ε w hε1 hdisjoint hsize hexception
  have hm : (0 : ℝ) < Fintype.card V := (mul_pos htR hwR).trans_le htw
  let I := activeClusters C γ w S
  let T := robustNeighbors R γ I
  let U := B ∩ T.biUnion C
  let Q := robustNeighbors G (d * γ ^ 2 / 200) S
  let Z := U \ Q
  have hU : (S.card : ℝ) + γ * Fintype.card V / 8 ≤ (U.card : ℝ) :=
    reduced_neighbor_union_surplus R C ε γ τ w hγ hγτ hτ hε hεγ hw ht hR
      hdisjoint hsize hexception A B S hS hA hB hSlower hSupper
  have hZT : Z ⊆ T.biUnion C := by
    intro z hz
    exact (Finset.mem_inter.mp (Finset.mem_sdiff.mp hz).1).2
  have hbad (j : J) (hj : j ∈ T) : ((Z ∩ C j).card : ℝ) < γ * w / 20 := by
    apply bad_cluster_small G R C ε d γ w hd hγ hw (by linarith) hm hcover
      hdisjoint hregular I S (Z ∩ C j) j hj Finset.inter_subset_right
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
    · intro z hz
      have hzQ : z ∉ Q := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hz).1).2
      have hz' : ((G.neighborFinset z ∩ S).card : ℝ) <
          (d * γ ^ 2 / 200) * Fintype.card V := by
        exact lt_of_not_ge (fun h => hzQ ((mem_robustNeighbors G _ S z).mpr h))
      nlinarith
  have hZeq : (Z.card : ℝ) = ∑ j ∈ T, ((Z ∩ C j).card : ℝ) := by
    have h := sum_cluster_inter_card C hdisjoint Z T
    rw [Finset.inter_eq_left.mpr hZT] at h
    exact_mod_cast h.symm
  have hZbound : (Z.card : ℝ) ≤ γ * Fintype.card V / 20 := by
    have hTcard : (T.card : ℝ) ≤ Fintype.card J := by exact_mod_cast Finset.card_le_univ T
    have hcount := mul_le_mul_of_nonneg_left hTcard
      (show 0 ≤ γ * (w : ℝ) / 20 by positivity)
    have horder := mul_le_mul_of_nonneg_left htw (show 0 ≤ γ / 20 by positivity)
    calc
      _ = ∑ j ∈ T, ((Z ∩ C j).card : ℝ) := hZeq
      _ ≤ ∑ _j ∈ T, γ * (w : ℝ) / 20 :=
        Finset.sum_le_sum (fun j hj => (hbad j hj).le)
      _ ≤ _ := by simp only [Finset.sum_const,nsmul_eq_mul]; nlinarith
  have hpart : (U.card : ℝ) = (U ∩ Q).card + Z.card := by
    exact_mod_cast (Finset.card_inter_add_card_sdiff U Q).symm
  have hQ : ((U ∩ Q).card : ℝ) ≤ (B ∩ Q).card := by
    exact_mod_cast Finset.card_le_card (Finset.inter_subset_inter_right
      (show U ⊆ B from Finset.inter_subset_left))
  have hdγ : d * γ ^ 2 ≤ γ := by
    have hd' := mul_le_mul_of_nonneg_right hd1 (sq_nonneg γ)
    nlinarith
  have hdγn := mul_le_mul_of_nonneg_right hdγ hm.le
  change (S.card : ℝ) + d * γ ^ 2 * Fintype.card V / 200 ≤ (B ∩ Q).card
  linarith

/-- A balanced cut respecting the clusters lifts the reduced graph's
robust expansion to the actual bipartite crossing graph. -/
theorem balanced_cluster_cut_expands (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : SimpleGraph J) [DecidableRel R.Adj] (C : J → Finset V)
    (ε d γ τ : ℝ) (w : ℕ)
    (hd : 0 < d) (hd1 : d ≤ 1) (hγ : 0 < γ) (hγτ : γ ≤ τ) (hτ : τ ≤ 1 / 8)
    (hε : 0 ≤ ε) (hεγ : ε ≤ γ / 100) (hw : 0 < w)
    (ht : 1 ≤ γ * Fintype.card J)
    (hR : IsRobustExpander R (2 * γ) (2 * τ))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hsize : ∀ i, (C i).card = w)
    (hexception : (((univ.biUnion C)ᶜ).card : ℝ) ≤ ε * Fintype.card V)
    (hregular : LowerRegularPairs G R C ε d w)
    (A B : Finset V) (hAB : Disjoint A B) (hunion : A ∪ B = univ)
    (hbalance : A.card = B.card)
    (hA : ∀ i, ((A ∩ C i).card : ℝ) ≤ (1 / 2 + ε) * w)
    (hB : ∀ i, (1 / 2 - ε) * w ≤ ((B ∩ C i).card : ℝ)) :
    IsBipartiteRobustExpander (cutSidesGraph G A B) (d * γ ^ 2 / 100) (4 * τ) := by
  have hsum : A.card + B.card = Fintype.card V := by
    rw [← Finset.card_union_of_disjoint hAB,hunion,Finset.card_univ]
  have hhalf : (Fintype.card V : ℝ) = 2 * Fintype.card A := by
    rw [Fintype.card_coe]
    have hsumR : (A.card : ℝ) + B.card = Fintype.card V := by exact_mod_cast hsum
    rw [← hbalance] at hsumR
    linarith
  intro S hSlower hSupper
  let S' : Finset V := S.image Subtype.val
  have hScard : S'.card = S.card := Finset.card_image_of_injective S Subtype.val_injective
  have hS : S' ⊆ A := by
    intro v hv
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hv
    exact a.property
  have hSlower' : 2 * τ * Fintype.card V ≤ (S'.card : ℝ) := by
    rw [hScard,hhalf]
    nlinarith only [hSlower]
  have hSupper' : (S'.card : ℝ) ≤ (1 - 4 * τ) * Fintype.card V / 2 := by
    rw [hScard,hhalf]
    nlinarith only [hSupper]
  have hlift := lower_regular_cut_expansion G R C ε d γ τ w hd hd1 hγ hγτ hτ
    hε hεγ hw ht hR hdisjoint hsize hexception hregular A B S' hS hA hB
    hSlower' hSupper'
  have hthreshold : (d * γ ^ 2 / 100) * Fintype.card A =
      d * γ ^ 2 * Fintype.card V / 200 := by rw [hhalf]; ring
  rw [cutSides_robustNeighbors_card G A B hAB hhalf,
    show d * γ ^ 2 / 100 / 2 = d * γ ^ 2 / 200 by ring,hthreshold]
  simpa only [hScard] using hlift

end Overfull.PairedCut
