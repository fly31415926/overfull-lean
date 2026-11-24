import Overfull.Dense.BalanceRepair.Model

/-!
# Finite cancellation of directed degree imbalance

A state consists of actual deleted arcs. Short directed paths increase its
repaired positive mass by one while preserving the internal-load capacity.
A maximum state therefore repairs every vertex imbalance.
-/

namespace Overfull.Dense.BalanceRepair

open Finset Classical
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def positiveMass (E : Finset (V × V)) : ℕ :=
  ∑ v : V, (arcBalance E v).toNat

structure CancellationState (E : Finset (V × V)) (L : ℕ)
    (F : Finset (V × V)) : Prop where
  subset : F ⊆ E
  balance : ∀ v, min 0 (arcBalance E v) ≤ arcBalance F v ∧
    arcBalance F v ≤ max 0 (arcBalance E v)
  capacity : ∀ v, min (arcOut F v) (arcIn F v) ≤ L
  size : F.card ≤ 4 * positiveMass F

noncomputable def saturated (F : Finset (V × V)) (L : ℕ) : Finset V :=
  univ.filter (fun v => L ≤ min (arcOut F v) (arcIn F v))

@[simp] theorem positiveMass_empty : positiveMass (∅ : Finset (V × V)) = 0 := by
  simp [positiveMass, arcBalance, arcOut, arcIn]

theorem cancellationState_empty (E : Finset (V × V)) (L : ℕ) :
    CancellationState E L ∅ := by
  refine ⟨empty_subset _, ?_, ?_, ?_⟩
  · intro v
    simp only [arcBalance, arcOut, arcIn, sum_empty, Nat.cast_zero, sub_self]
    exact ⟨min_le_left _ _, le_max_left _ _⟩
  · simp [arcOut, arcIn]
  · simp

theorem CancellationState.positiveMass_le {E F : Finset (V × V)} {L : ℕ}
    (hF : CancellationState E L F) : positiveMass F ≤ positiveMass E := by
  unfold positiveMass
  apply Finset.sum_le_sum
  intro v _
  have h := hF.balance v
  omega

theorem CancellationState.deleted_degree_le {E F : Finset (V × V)} {L : ℕ}
    (hF : CancellationState E L F) (v : V) :
    arcOut F v + arcIn F v ≤ 2 * L + (arcBalance E v).natAbs := by
  have hb := hF.balance v
  have hc := hF.capacity v
  have hbF : arcBalance F v = (arcOut F v : ℤ) - arcIn F v := rfl
  omega

theorem CancellationState.saturated_card_bound {E F : Finset (V × V)} {L : ℕ}
    (hF : CancellationState E L F) (hL : 0 < L) (B : ℝ)
    (hB : (positiveMass E : ℝ) ≤ B) :
    ((saturated F L).card : ℝ) ≤ 4 * B / L := by
  have hcount : L * (saturated F L).card ≤ F.card := by
    calc
      _ = ∑ v ∈ saturated F L, L := by simp [mul_comm]
      _ ≤ ∑ v ∈ saturated F L, arcOut F v := by
        apply Finset.sum_le_sum
        intro v hv
        have hh := (Finset.mem_filter.mp hv).2
        exact hh.trans (min_le_left _ _)
      _ ≤ ∑ v : V, arcOut F v :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (by intros; exact Nat.zero_le _)
      _ = _ := sum_arcOut F
  have hmass := hF.positiveMass_le
  have hsize := hF.size
  have hnat : L * (saturated F L).card ≤ 4 * positiveMass E := by
    omega
  have hreal : (L : ℝ) * (saturated F L).card ≤ 4 * positiveMass E := by
    exact_mod_cast hnat
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  apply (le_div_iff₀ hL').mpr
  nlinarith only [hreal, hB]

omit [Fintype V] in
theorem arcOut_union (F P : Finset (V × V)) (h : Disjoint F P) (v : V) :
    arcOut (F ∪ P) v = arcOut F v + arcOut P v := by
  unfold arcOut
  exact Finset.sum_union h

omit [Fintype V] in
theorem arcIn_union (F P : Finset (V × V)) (h : Disjoint F P) (v : V) :
    arcIn (F ∪ P) v = arcIn F v + arcIn P v := by
  unfold arcIn
  exact Finset.sum_union h

omit [Fintype V] in
theorem arcBalance_union (F P : Finset (V × V)) (h : Disjoint F P) (v : V) :
    arcBalance (F ∪ P) v = arcBalance F v + arcBalance P v := by
  rw [arcBalance, arcOut_union F P h v, arcIn_union F P h v]
  simp [arcBalance]
  ring

omit [Fintype V] in
theorem RoutingPath.disjoint_deleted {E F : Finset (V × V)} {u v : V}
    (P : RoutingPath (E \ F) u v) : Disjoint F P.arcs := by
  apply Finset.disjoint_left.mpr
  intro e heF heP
  exact (Finset.mem_sdiff.mp (P.subset heP)).2 heF

omit [Fintype V] in
theorem RoutingPath.balance {E : Finset (V × V)} {u v : V}
    (P : RoutingPath E u v) (x : V) :
    arcBalance P.arcs x = (if x = u then 1 else 0) - (if x = v then 1 else 0) := by
  rw [arcBalance, P.out_count, P.in_count]
  push_cast
  omega

theorem CancellationState.positiveMass_union {E F : Finset (V × V)} {L : ℕ}
    (hF : CancellationState E L F) {u v : V}
    (hu : arcBalance F u < arcBalance E u)
    (hv : arcBalance E v < arcBalance F v) (P : RoutingPath (E \ F) u v) :
    positiveMass (F ∪ P.arcs) = positiveMass F + 1 := by
  have hs : 0 ≤ arcBalance F u := by have hh := hF.balance u; omega
  have ht : arcBalance F v ≤ 0 := by have hh := hF.balance v; omega
  have hpoint (x : V) : (arcBalance (F ∪ P.arcs) x).toNat =
      (arcBalance F x).toNat + if x = u then 1 else 0 := by
    rw [arcBalance_union F P.arcs P.disjoint_deleted x, P.balance]
    by_cases hxu : x = u
    · subst x
      simp [P.distinct]; omega
    · by_cases hxv : x = v
      · subst x
        simp [hxu]; omega
      · simp only [if_neg hxu, if_neg hxv]
        omega
  unfold positiveMass
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib]
  simp

theorem CancellationState.add_path {E F : Finset (V × V)} {L : ℕ}
    (hF : CancellationState E L F) {u v : V}
    (hu : arcBalance F u < arcBalance E u)
    (hv : arcBalance E v < arcBalance F v) (P : RoutingPath (E \ F) u v)
    (havoid : Disjoint P.internal (saturated F L)) :
    CancellationState E L (F ∪ P.arcs) := by
  have hs : 0 ≤ arcBalance F u := by have hh := hF.balance u; omega
  have ht : arcBalance F v ≤ 0 := by have hh := hF.balance v; omega
  have hsd : arcIn F u ≤ arcOut F u := by unfold arcBalance at hs; omega
  have htd : arcOut F v ≤ arcIn F v := by unfold arcBalance at ht; omega
  refine ⟨Finset.union_subset hF.subset (P.subset.trans Finset.sdiff_subset), ?_, ?_, ?_⟩
  · intro x
    have hx := hF.balance x
    rw [arcBalance_union F P.arcs P.disjoint_deleted x, P.balance]
    by_cases hxu : x = u
    · subst x
      simp [P.distinct]; omega
    · by_cases hxv : x = v
      · subst x
        simp [hxu]; omega
      · simp only [if_neg hxu, if_neg hxv]
        omega
  · intro x
    have hx := hF.capacity x
    rw [arcOut_union F P.arcs P.disjoint_deleted x,
      arcIn_union F P.arcs P.disjoint_deleted x, P.out_count, P.in_count]
    by_cases hxu : x = u
    · subst x
      simp [P.distinct, P.source_not_internal]; omega
    · by_cases hxv : x = v
      · subst x
        simp [hxu, P.target_not_internal]; omega
      · simp only [if_neg hxu, if_neg hxv]
        by_cases hxi : x ∈ P.internal
        · have hnot : x ∉ saturated F L :=
            fun hsat => Finset.disjoint_left.mp havoid hxi hsat
          have hlt : min (arcOut F x) (arcIn F x) < L := by
            apply lt_of_not_ge
            intro hge
            exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hge⟩)
          rw [if_pos hxi]
          omega
        · simp only [if_neg hxi]
          omega
  · rw [hF.positiveMass_union hu hv P]
    have hcard := Finset.card_union_le F P.arcs
    have hshort := P.short
    have hsize := hF.size
    omega

theorem exists_residual_endpoints (E F : Finset (V × V))
    (hneq : ¬ ∀ x, arcBalance F x = arcBalance E x) :
    ∃ u v, arcBalance F u < arcBalance E u ∧ arcBalance E v < arcBalance F v := by
  obtain ⟨x, hx⟩ := not_forall.mp hneq
  have hsum : (∑ y : V, (arcBalance E y - arcBalance F y)) = 0 := by
    rw [Finset.sum_sub_distrib, sum_arcBalance, sum_arcBalance, sub_self]
  have hsum' : (∑ y : V, (arcBalance F y - arcBalance E y)) = 0 := by
    rw [Finset.sum_sub_distrib, sum_arcBalance, sum_arcBalance, sub_self]
  obtain ⟨u, _, hu⟩ := Finset.exists_pos_of_sum_zero_of_exists_nonzero
    (fun y => arcBalance E y - arcBalance F y) hsum
    ⟨x, Finset.mem_univ x, sub_ne_zero.mpr (Ne.symm hx)⟩
  obtain ⟨v, _, hv⟩ := Finset.exists_pos_of_sum_zero_of_exists_nonzero
    (fun y => arcBalance F y - arcBalance E y) hsum'
    ⟨x, Finset.mem_univ x, sub_ne_zero.mpr hx⟩
  exact ⟨u, v, by omega, by omega⟩

/-- Actual deleted arcs cancel all imbalance when every incomplete state
admits a short route avoiding the internally saturated vertices. -/
theorem exists_balanced_deletion (E : Finset (V × V)) (L : ℕ)
    (hroute : ∀ F, CancellationState E L F → ∀ u v,
      arcBalance F u < arcBalance E u → arcBalance E v < arcBalance F v →
      ∃ P : RoutingPath (E \ F) u v, Disjoint P.internal (saturated F L)) :
    ∃ F, CancellationState E L F ∧ ∀ v, arcBalance F v = arcBalance E v := by
  let S := E.powerset.filter (CancellationState E L)
  have hS : S.Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr ⟨?_, cancellationState_empty E L⟩⟩
    exact Finset.mem_powerset.mpr (Finset.empty_subset E)
  obtain ⟨F, hFS, hmax⟩ := Finset.exists_max_image S positiveMass hS
  have hF : CancellationState E L F := (Finset.mem_filter.mp hFS).2
  refine ⟨F, hF, ?_⟩
  by_contra hneq
  obtain ⟨u, v, hu, hv⟩ := exists_residual_endpoints E F hneq
  obtain ⟨P, havoid⟩ := hroute F hF u v hu hv
  have hFP := hF.add_path hu hv P havoid
  have hFPS : F ∪ P.arcs ∈ S :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hFP.subset, hFP⟩
  have hbound := hmax _ hFPS
  rw [hF.positiveMass_union hu hv P] at hbound
  omega

end Overfull.Dense.BalanceRepair
