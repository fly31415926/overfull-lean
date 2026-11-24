import Overfull.BipartitePackingAccounting

/-!
# Internal and endpoint incidences in matching repair

The load is defined from the actual reserve edges in the repaired
matchings. Endpoint incidences are bounded separately, while the internal
load has an integral capacity preserved by each actual matching update.
-/

namespace Overfull.MatchingRepairLoad

open Finset Classical SimpleGraph
open BipartitePackingAccounting
open scoped BigOperators

variable {V I : Type*} [Fintype V]

noncomputable def internalLoad (G R : SimpleGraph V) (N : I → G.Subgraph)
    (Y : I → Finset V) (T : Finset I) (v : V) : ℕ :=
  ∑ i ∈ T, if v ∈ Y i then 0 else ((N i).spanningCoe ⊓ R).degree v

noncomputable def endpointCount (Y : I → Finset V) (T : Finset I) (v : V) : ℕ :=
  (T.filter (fun i => v ∈ Y i)).card

theorem actual_load_eq_sum (G R : SimpleGraph V) (N : I → G.Subgraph) (T : Finset I)
    (hdisj : ∀ i ∈ T, ∀ j ∈ T, i ≠ j →
      Disjoint (N i).spanningCoe (N j).spanningCoe) (v : V) :
    reserveLoad G R N T v = ∑ i ∈ T, ((N i).spanningCoe ⊓ R).degree v := by
  rw [reserveLoad_eq_sum G R N T hdisj]
  apply Finset.sum_congr rfl
  intro i _
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
  rw [inf_comm]

theorem internal_le_actual (G R : SimpleGraph V) (N : I → G.Subgraph)
    (Y : I → Finset V) (T : Finset I)
    (hdisj : ∀ i ∈ T, ∀ j ∈ T, i ≠ j →
      Disjoint (N i).spanningCoe (N j).spanningCoe) (v : V) :
    internalLoad G R N Y T v ≤ reserveLoad G R N T v := by
  rw [actual_load_eq_sum G R N T hdisj]
  apply Finset.sum_le_sum
  intro i _
  split_ifs <;> omega

theorem total_internal_le_actual (G R : SimpleGraph V) (N : I → G.Subgraph)
    (Y : I → Finset V) (T : Finset I)
    (hdisj : ∀ i ∈ T, ∀ j ∈ T, i ≠ j →
      Disjoint (N i).spanningCoe (N j).spanningCoe) :
    (∑ v, internalLoad G R N Y T v) ≤ ∑ v, reserveLoad G R N T v :=
  Finset.sum_le_sum (fun v _ => internal_le_actual G R N Y T hdisj v)

theorem actual_load_le_internal_add_endpoints (G R : SimpleGraph V)
    (N : I → G.Subgraph) (Y : I → Finset V) (T : Finset I)
    (hN : ∀ i ∈ T, (N i).IsMatching)
    (hdisj : ∀ i ∈ T, ∀ j ∈ T, i ≠ j →
      Disjoint (N i).spanningCoe (N j).spanningCoe) (v : V) :
    reserveLoad G R N T v ≤ internalLoad G R N Y T v + endpointCount Y T v := by
  have hc : endpointCount Y T v = ∑ i ∈ T, if v ∈ Y i then 1 else 0 := by
    simp [endpointCount]
  rw [actual_load_eq_sum G R N T hdisj,internalLoad,hc,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hv : v ∈ Y i
  · simp only [if_pos hv,zero_add]
    exact (((N i).spanningCoe ⊓ R).degree_le_of_le
      (show (N i).spanningCoe ⊓ R ≤ (N i).spanningCoe from inf_le_left)).trans
      (matching_degree_le_one G (N i) (hN i hi) v)
  · simp only [if_neg hv,Nat.add_zero,le_refl]

omit [Fintype V] in
theorem endpointCount_mono (Y : I → Finset V) (T S : Finset I) (hTS : T ⊆ S) (v : V) :
    endpointCount Y T v ≤ endpointCount Y S v :=
  Finset.card_le_card (Finset.filter_subset_filter _ hTS)

@[simp] theorem internalLoad_empty (G R : SimpleGraph V) (N : I → G.Subgraph)
    (Y : I → Finset V) (v : V) : internalLoad G R N Y ∅ v = 0 := by
  simp [internalLoad]

omit [Fintype V] in
@[simp] theorem endpointCount_empty (Y : I → Finset V) (v : V) : endpointCount Y ∅ v = 0 := by
  simp [endpointCount]

variable [DecidableEq I]

theorem internalLoad_update_of_not_mem (G R : SimpleGraph V) (N : I → G.Subgraph)
    (Y : I → Finset V) (T : Finset I) (i : I) (P : G.Subgraph) (hi : i ∉ T) (v : V) :
    internalLoad G R (Function.update N i P) Y T v = internalLoad G R N Y T v := by
  unfold internalLoad
  apply Finset.sum_congr rfl
  intro j hj
  have hji : j ≠ i := by intro h; subst j; exact hi hj
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card,
    Function.update_of_ne hji]

theorem internalLoad_update_insert (G R : SimpleGraph V) (N : I → G.Subgraph)
    (Y : I → Finset V) (T : Finset I) (i : I) (P : G.Subgraph) (hi : i ∉ T) (v : V) :
    internalLoad G R (Function.update N i P) Y (insert i T) v =
      internalLoad G R N Y T v + if v ∈ Y i then 0 else (P.spanningCoe ⊓ R).degree v := by
  have hsum : internalLoad G R (Function.update N i P) Y (insert i T) v =
      (if v ∈ Y i then 0 else (P.spanningCoe ⊓ R).degree v) +
        internalLoad G R (Function.update N i P) Y T v := by
    simp only [internalLoad,Finset.sum_insert hi,
      ← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card,Function.update_self]
  rw [hsum,internalLoad_update_of_not_mem G R N Y T i P hi v]
  omega

/-- Endpoints may be saturated: their contribution is excluded from the
internal load. Other saturated vertices must receive no new reserve edge. -/
theorem internalLoad_update_insert_le_capacity (G R : SimpleGraph V)
    (N : I → G.Subgraph) (Y : I → Finset V) (T : Finset I)
    (i : I) (P : G.Subgraph) (hi : i ∉ T) (cap : ℕ)
    (hcapacity : ∀ v, internalLoad G R N Y T v ≤ cap)
    (hnew : ∀ v, (P.spanningCoe ⊓ R).degree v ≤ 1)
    (hzero : ∀ v, v ∉ Y i → internalLoad G R N Y T v = cap →
      (P.spanningCoe ⊓ R).degree v = 0) (v : V) :
    internalLoad G R (Function.update N i P) Y (insert i T) v ≤ cap := by
  rw [internalLoad_update_insert G R N Y T i P hi v]
  by_cases hv : v ∈ Y i
  · simpa only [if_pos hv,Nat.add_zero] using hcapacity v
  · rw [if_neg hv]
    by_cases hs : internalLoad G R N Y T v = cap
    · rw [hzero v hv hs,Nat.add_zero]
      exact hcapacity v
    · have hcap := hcapacity v
      have hstep := hnew v
      omega

theorem internalLoad_update_insert_matching (G R : SimpleGraph V)
    (N : I → G.Subgraph) (Y : I → Finset V) (T : Finset I)
    (i : I) (P : G.Subgraph) (hi : i ∉ T) (hP : P.IsMatching) (cap : ℕ)
    (hcapacity : ∀ v, internalLoad G R N Y T v ≤ cap)
    (hzero : ∀ v, v ∉ Y i → internalLoad G R N Y T v = cap →
      (P.spanningCoe ⊓ R).degree v = 0) (v : V) :
    internalLoad G R (Function.update N i P) Y (insert i T) v ≤ cap := by
  apply internalLoad_update_insert_le_capacity G R N Y T i P hi cap hcapacity _ hzero v
  intro w
  exact ((P.spanningCoe ⊓ R).degree_le_of_le
    (show P.spanningCoe ⊓ R ≤ P.spanningCoe from inf_le_left)).trans
    (matching_degree_le_one G P hP w)

omit [Fintype V] in
theorem matchingUnion_update_of_not_mem (G : SimpleGraph V) (N : I → G.Subgraph)
    (T : Finset I) (i : I) (P : G.Subgraph) (hi : i ∉ T) :
    edgeUnion (fun j => (Function.update N i P j).spanningCoe) T =
      edgeUnion (fun j => (N j).spanningCoe) T := by
  have hN (j : I) (hj : j ∈ T) : Function.update N i P j = N j := by
    apply Function.update_of_ne
    intro h
    subst j
    exact hi hj
  ext v w
  simp only [edgeUnion_adj]
  constructor
  · rintro ⟨j,hj,hvw⟩
    exact ⟨j,hj,by simpa only [hN j hj] using hvw⟩
  · rintro ⟨j,hj,hvw⟩
    exact ⟨j,hj,by simpa only [hN j hj] using hvw⟩

omit [Fintype V] in
theorem matchingUnion_update_insert (G : SimpleGraph V) (N : I → G.Subgraph)
    (T : Finset I) (i : I) (P : G.Subgraph) (hi : i ∉ T) :
    edgeUnion (fun j => (Function.update N i P j).spanningCoe) (insert i T) =
      P.spanningCoe ⊔ edgeUnion (fun j => (N j).spanningCoe) T := by
  have heq : edgeUnion (fun j => (Function.update N i P j).spanningCoe) (insert i T) =
      (Function.update N i P i).spanningCoe ⊔
        edgeUnion (fun j => (Function.update N i P j).spanningCoe) T := by
    ext v w
    simp only [edgeUnion_adj,Finset.mem_insert,SimpleGraph.sup_adj]
    aesop
  rw [heq,matchingUnion_update_of_not_mem G N T i P hi]
  simp only [Function.update_self]

theorem actual_load_update_insert (G R : SimpleGraph V) (N : I → G.Subgraph)
    (T : Finset I) (i : I) (P : G.Subgraph) (hi : i ∉ T)
    (hdisj : ∀ j ∈ insert i T, ∀ k ∈ insert i T, j ≠ k →
      Disjoint (Function.update N i P j).spanningCoe (Function.update N i P k).spanningCoe)
    (v : V) :
    reserveLoad G R (Function.update N i P) (insert i T) v =
      reserveLoad G R N T v + (P.spanningCoe ⊓ R).degree v := by
  have hN (j : I) (hj : j ∈ T) : Function.update N i P j = N j := by
    apply Function.update_of_ne
    intro h
    subst j
    exact hi hj
  have hold : ∀ j ∈ T, ∀ k ∈ T, j ≠ k →
      Disjoint (N j).spanningCoe (N k).spanningCoe := by
    intro j hj k hk hjk
    simpa only [hN j hj,hN k hk] using
      hdisj j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hjk
  rw [actual_load_eq_sum G R (Function.update N i P) (insert i T) hdisj,
    Finset.sum_insert hi,Function.update_self,actual_load_eq_sum G R N T hold]
  have heq : (∑ j ∈ T, ((Function.update N i P j).spanningCoe ⊓ R).degree v) =
      ∑ j ∈ T, ((N j).spanningCoe ⊓ R).degree v := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hN j hj]
  rw [heq]
  omega

theorem total_actual_load_update_insert (G R : SimpleGraph V) (N : I → G.Subgraph)
    (T : Finset I) (i : I) (P : G.Subgraph) (hi : i ∉ T)
    (hdisj : ∀ j ∈ insert i T, ∀ k ∈ insert i T, j ≠ k →
      Disjoint (Function.update N i P j).spanningCoe (Function.update N i P k).spanningCoe) :
    (∑ v, reserveLoad G R (Function.update N i P) (insert i T) v) =
      (∑ v, reserveLoad G R N T v) + ∑ v, (P.spanningCoe ⊓ R).degree v := by
  simp_rw [actual_load_update_insert G R N T i P hi hdisj]
  exact Finset.sum_add_distrib

omit [DecidableEq I] in
/-- Every vertex reaching the internal capacity contributes that many
actual incidences to the total used reserve. -/
theorem saturated_internal_count_le_actual (G R : SimpleGraph V)
    (N : I → G.Subgraph) (Y : I → Finset V) (T : Finset I) (cap : ℕ)
    (hdisj : ∀ i ∈ T, ∀ j ∈ T, i ≠ j →
      Disjoint (N i).spanningCoe (N j).spanningCoe) :
    cap * (univ.filter (fun v => cap ≤ internalLoad G R N Y T v)).card ≤
      ∑ v, reserveLoad G R N T v := by
  let Z := univ.filter (fun v => cap ≤ internalLoad G R N Y T v)
  have hcap : cap * Z.card ≤ ∑ v ∈ Z, internalLoad G R N Y T v := by
    calc
      _ = ∑ _v ∈ Z, cap := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun v hv => (Finset.mem_filter.mp hv).2)
  have hsum : (∑ v ∈ Z, internalLoad G R N Y T v) ≤
      ∑ v, internalLoad G R N Y T v :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ Z) (fun _ _ _ => Nat.zero_le _)
  exact hcap.trans (hsum.trans (total_internal_le_actual G R N Y T hdisj))

end Overfull.MatchingRepairLoad
