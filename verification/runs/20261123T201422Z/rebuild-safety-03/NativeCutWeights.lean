import Overfull.NativeReserve.RoundedPools
import Overfull.NativeReserve.WeightedSafety

/-!
# Whole-cut demands of the native assignment signatures

Every native pool is uniform on a shore containing each old core wholly
or not at all. Its exact usage therefore determines the original-copy cut
count, including the full parallel exceptional-pair pool.
-/

noncomputable section

namespace Overfull.NativeReserve

open Finset Classical AssignedParts ForceMatching
open scoped BigOperators

variable {V E : Type*} [Fintype E]

def poolCutIndicator (G : Multigraph V E) (U₀ U₁ Z X : Finset V)
    (j : PoolKind Z) : ℕ :=
  if ∃ e ∈ poolCopies G U₀ U₁ Z j, e ∈ G.cutEdges X then 1 else 0

theorem poolCutIndicator_le_one (G : Multigraph V E) (U₀ U₁ Z X : Finset V)
    (j : PoolKind Z) : poolCutIndicator G U₀ U₁ Z X j ≤ 1 := by
  unfold poolCutIndicator
  split_ifs <;> omega

private theorem cut_membership_of_edge_eq (G : Multigraph V E) (X : Finset V)
    (e : E) (u v : V) (he : G.edge e = s(u, v)) :
    e ∈ G.cutEdges X ↔ (u ∈ X) ≠ (v ∈ X) := by
  have hh := (G.edge_eq e).trans he
  rcases Sym2.eq_iff.mp hh with ⟨hu, hv⟩ | ⟨hv, hu⟩
  · simp only [G.mem_cutEdges, hu, hv]
  · simp only [G.mem_cutEdges, hu, hv, ne_comm]

theorem poolCopies_cut_uniform (G : Multigraph V E) (U₀ U₁ Z X : Finset V)
    (h01 : Disjoint U₀ U₁) (hZ : Z.card ≤ 2)
    (hwhole0 : U₀ ⊆ X ∨ Disjoint U₀ X)
    (hwhole1 : U₁ ⊆ X ∨ Disjoint U₁ X)
    (j : PoolKind Z) {e f : E}
    (he : e ∈ poolCopies G U₀ U₁ Z j) (hf : f ∈ poolCopies G U₀ U₁ Z j) :
    e ∈ G.cutEdges X ↔ f ∈ G.cutEdges X := by
  cases j with
  | pair =>
    have hends (g : E) (hg : g ∈ G.internalOn univ Z) : (G.edge g).toFinset = Z := by
      have hsub : (G.edge g).toFinset ⊆ Z := by
        intro v hv
        rcases (G.incident_iff g v).mp (by simpa using hv) with h | h
        · exact h ▸ (mem_filter.mp hg).2.1
        · exact h ▸ (mem_filter.mp hg).2.2
      apply eq_of_subset_of_card_le hsub
      simpa only [Sym2.card_toFinset_of_not_isDiag _ (G.loopless g)] using hZ
    have hsets := (hends e he).trans (hends f hf).symm
    have hedge : G.edge e = G.edge f := by
      apply SetLike.ext
      intro v
      simpa only [Sym2.mem_toFinset] using (Finset.ext_iff.mp hsets v)
    simp only [G.mem_cutEdges, Multigraph.firstEnd, Multigraph.secondEnd, hedge]
  | exception z i =>
    obtain ⟨_, hze, heU⟩ := mem_filter.mp he
    obtain ⟨_, hzf, hfU⟩ := mem_filter.mp hf
    have hwhole : (if i = 0 then U₀ else U₁) ⊆ X ∨
        Disjoint (if i = 0 then U₀ else U₁) X := by split_ifs <;> assumption
    have ho := whole_core_membership_iff _ X hwhole heU hfU
    rw [cut_membership_of_edge_eq G X e z.val (G.otherEnd z.val e)
      (G.edge_eq_otherEnd z.val e hze),
      cut_membership_of_edge_eq G X f z.val (G.otherEnd z.val f)
        (G.edge_eq_otherEnd z.val f hzf)]
    rw [propext ho]
  | crossing =>
    have he' := (mem_coreCrossings_iff G univ U₀ U₁ h01 e).mp he |>.2
    have hf' := (mem_coreCrossings_iff G univ U₀ U₁ h01 f).mp hf |>.2
    simp only [G.mem_cutEdges]
    rcases he' with he' | he' <;> rcases hf' with hf' | hf'
    · rw [propext (whole_core_membership_iff U₀ X hwhole0 he'.1 hf'.1),
        propext (whole_core_membership_iff U₁ X hwhole1 he'.2 hf'.2)]
    · rw [propext (whole_core_membership_iff U₀ X hwhole0 he'.1 hf'.2),
        propext (whole_core_membership_iff U₁ X hwhole1 he'.2 hf'.1)]
      exact ne_comm
    · rw [propext (whole_core_membership_iff U₁ X hwhole1 he'.1 hf'.2),
        propext (whole_core_membership_iff U₀ X hwhole0 he'.2 hf'.1)]
      exact ne_comm
    · rw [propext (whole_core_membership_iff U₁ X hwhole1 he'.1 hf'.1),
        propext (whole_core_membership_iff U₀ X hwhole0 he'.2 hf'.2)]

theorem poolCutIndicator_eq_one_iff (G : Multigraph V E) (U₀ U₁ Z X : Finset V)
    (h01 : Disjoint U₀ U₁) (hZ : Z.card ≤ 2)
    (hwhole0 : U₀ ⊆ X ∨ Disjoint U₀ X)
    (hwhole1 : U₁ ⊆ X ∨ Disjoint U₁ X)
    (j : PoolKind Z) (e : E) (he : e ∈ poolCopies G U₀ U₁ Z j) :
    poolCutIndicator G U₀ U₁ Z X j = 1 ↔ e ∈ G.cutEdges X := by
  unfold poolCutIndicator
  by_cases h : ∃ f ∈ poolCopies G U₀ U₁ Z j, f ∈ G.cutEdges X
  · rw [if_pos h]
    obtain ⟨f, hf, hfx⟩ := h
    have hex := (poolCopies_cut_uniform G U₀ U₁ Z X h01 hZ hwhole0 hwhole1 j he hf).mpr hfx
    exact ⟨fun _ => hex, fun _ => rfl⟩
  · rw [if_neg h]
    simp only [Nat.zero_ne_one, false_iff]
    exact fun hx => h ⟨e, he, hx⟩

theorem native_pool_cut_card (G : Multigraph V E) (U₀ U₁ Z X : Finset V)
    (h01 : Disjoint U₀ U₁) (hZ : Z.card ≤ 2)
    (hwhole0 : U₀ ⊆ X ∨ Disjoint U₀ X)
    (hwhole1 : U₁ ⊆ X ∨ Disjoint U₁ X) (F : Finset E) (j : PoolKind Z) :
    (G.cutOn (F ∩ poolCopies G U₀ U₁ Z j) X).card =
      (F ∩ poolCopies G U₀ U₁ Z j).card * poolCutIndicator G U₀ U₁ Z X j := by
  by_cases h : ∃ e ∈ poolCopies G U₀ U₁ Z j, e ∈ G.cutEdges X
  · have hi : poolCutIndicator G U₀ U₁ Z X j = 1 := by simp only [poolCutIndicator, if_pos h]
    rw [hi, mul_one]
    congr 1
    rw [cutOn_eq_inter]
    apply inter_eq_left.mpr
    intro e he
    exact (poolCutIndicator_eq_one_iff G U₀ U₁ Z X h01 hZ hwhole0 hwhole1
      j e (mem_inter.mp he).2).mp hi
  · have hi : poolCutIndicator G U₀ U₁ Z X j = 0 := by simp only [poolCutIndicator, if_neg h]
    rw [hi, mul_zero, card_eq_zero]
    apply eq_empty_iff_forall_notMem.mpr
    intro e he
    rw [cutOn_eq_inter] at he
    exact h ⟨e, (mem_inter.mp (mem_inter.mp he).1).2, (mem_inter.mp he).2⟩

theorem native_cut_count_eq_sum_pools (G : Multigraph V E) (U₀ U₁ Z X : Finset V)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hZ : Z.card ≤ 2)
    (hwhole0 : U₀ ⊆ X ∨ Disjoint U₀ X)
    (hwhole1 : U₁ ⊆ X ∨ Disjoint U₁ X) (F : Finset E)
    (hpool : ∀ e ∈ F, ∃ j, e ∈ poolCopies G U₀ U₁ Z j) :
    (G.cutOn F X).card = ∑ j : PoolKind Z,
      (F ∩ poolCopies G U₀ U₁ Z j).card * poolCutIndicator G U₀ U₁ Z X j := by
  have hset : G.cutOn F X =
      univ.biUnion (fun j : PoolKind Z => G.cutOn (F ∩ poolCopies G U₀ U₁ Z j) X) := by
    ext e
    simp only [mem_biUnion, mem_univ, true_and, Multigraph.mem_cutOn, mem_inter]
    constructor
    · rintro ⟨he, hx⟩
      obtain ⟨j, hj⟩ := hpool e he
      exact ⟨j, ⟨he, hj⟩, hx⟩
    · rintro ⟨j, ⟨he, _⟩, hx⟩
      exact ⟨he, hx⟩
  rw [hset, card_biUnion]
  · apply sum_congr rfl
    intro j _
    exact native_pool_cut_card G U₀ U₁ Z X h01 hZ hwhole0 hwhole1 F j
  · intro i _ j _ hij
    apply (poolCopies_pairwiseDisjoint G U₀ U₁ Z h01 h0Z h1Z hZ hij).mono
    · intro e he
      exact (mem_inter.mp ((G.mem_cutOn _ X e).mp he).1).2
    · intro e he
      exact (mem_inter.mp ((G.mem_cutOn _ X e).mp he).1).2

def originalCores (U₀ U₁ : Finset V) (i : Fin 2) : Finset V :=
  if i = 0 then U₀ else U₁

theorem originalCores_disjoint (U₀ U₁ : Finset V) (h01 : Disjoint U₀ U₁) :
    Pairwise (fun i j => Disjoint (originalCores U₀ U₁ i) (originalCores U₀ U₁ j)) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [originalCores, disjoint_comm]

theorem originalCores_disjoint_exceptions (U₀ U₁ Z : Finset V)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z) :
    ∀ i, Disjoint (originalCores U₀ U₁ i) Z := by
  intro i
  fin_cases i <;> simp_all [originalCores]

theorem originalCores_whole (U₀ U₁ Z X : Finset V)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hX : X ∈ wholeUnions (originalCores U₀ U₁) Z) :
    (U₀ ⊆ X ∨ Disjoint U₀ X) ∧ (U₁ ⊆ X ∨ Disjoint U₁ X) := by
  have hh := wholeUnions_whole (originalCores U₀ U₁) Z X
    (originalCores_disjoint U₀ U₁ h01)
    (originalCores_disjoint_exceptions U₀ U₁ Z h0Z h1Z) hX
  exact ⟨by simpa [originalCores] using hh 0, by simpa [originalCores] using hh 1⟩

variable {S : Type*} [Fintype S] {k : ℕ}

def wholeCutDemand (G : Multigraph V E)
    (D : MultigraphMatchingProbability.Distribution G k S)
    (U₀ U₁ Z X : Finset V) (p : AssignmentSignature Z) : ℕ :=
  ∑ j : PoolKind Z, poolDemand D U₀ U₁ Z j p * poolCutIndicator G U₀ U₁ Z X j

theorem native_cut_count_eq_demand (G : Multigraph V E)
    (D : MultigraphMatchingProbability.Distribution G k S)
    (U₀ U₁ Z X : Finset V)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hZ : Z.card ≤ 2) (hX : X ∈ wholeUnions (originalCores U₀ U₁) Z)
    (F : Finset E) (p : AssignmentSignature Z)
    (hpool : ∀ e ∈ F, ∃ j, e ∈ poolCopies G U₀ U₁ Z j)
    (huse : ∀ j, (F ∩ poolCopies G U₀ U₁ Z j).card = poolDemand D U₀ U₁ Z j p) :
    (G.cutOn F X).card = wholeCutDemand G D U₀ U₁ Z X p := by
  obtain ⟨hwhole0, hwhole1⟩ := originalCores_whole U₀ U₁ Z X h01 h0Z h1Z hX
  rw [native_cut_count_eq_sum_pools G U₀ U₁ Z X h01 h0Z h1Z hZ hwhole0 hwhole1 F hpool]
  simp_rw [huse]
  rfl

theorem wholeCutDemand_at_sample (G : Multigraph V E)
    (D : MultigraphMatchingProbability.Distribution G k S)
    (U₀ U₁ Z X : Finset V)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2)
    (hX : X ∈ wholeUnions (originalCores U₀ U₁) Z) (s : S) :
    wholeCutDemand G D U₀ U₁ Z X (coarseSignature G (D.matching s) U₀ Z) =
      (G.cutOn (compressedBoundary G (D.matching s) U₀ U₁ Z) X).card := by
  symm
  exact native_cut_count_eq_demand G D U₀ U₁ Z X h01 h0Z h1Z hZ hX _ _
    (fun _ he => compressedBoundary_exists_pool G (D.matching s) U₀ U₁ Z hcover he)
    (compressedBoundary_pool_usage_at_sample D U₀ U₁ Z h01 h0Z h1Z hcover hZ s)

theorem wholeCutDemand_capacity (G : Multigraph V E)
    (D : MultigraphMatchingProbability.Distribution G k S) (hk : 0 < k)
    (U₀ U₁ Z X : Finset V)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2)
    (hX : X ∈ wholeUnions (originalCores U₀ U₁) Z) :
    (∑ p, signatureWeight D U₀ Z p * (wholeCutDemand G D U₀ U₁ Z X p : ℝ)) ≤
      G.cutSize X := by
  apply AssignedParts.NativeWeights.aggregate_capacity D hk
    (fun s => coarseSignature G (D.matching s) U₀ Z)
    (fun s => compressedBoundary G (D.matching s) U₀ U₁ Z)
    (fun s => compressedBoundary_subset G (D.matching s) U₀ U₁ Z)
  intro s
  rw [wholeCutDemand_at_sample G D U₀ U₁ Z X h01 h0Z h1Z hcover hZ hX s,
    cutOn_eq_inter]

theorem even_uncovered_whole_union {I : Type*} [Fintype I]
    (U : I → Finset V) (Z F : Finset V)
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hcovered : Z ⊆ F) (hparity : ∀ i, Even (U i \ F).card)
    (X : Finset V) (hX : X ∈ wholeUnions U Z) : Even (X \ F).card := by
  obtain ⟨A, B, hB, rfl⟩ := (mem_wholeUnions U Z X).mp hX
  have heq : (A.biUnion U ∪ B) \ F = A.biUnion (fun i => U i \ F) := by
    ext v
    simp only [mem_sdiff, mem_union, mem_biUnion]
    constructor
    · rintro ⟨hA | hBv, hFv⟩
      · obtain ⟨i, hi, hvi⟩ := hA
        exact ⟨i, hi, hvi, hFv⟩
      · exact (hFv (hcovered (hB hBv))).elim
    · rintro ⟨i, hi, hvi, hFv⟩
      exact ⟨Or.inl ⟨i, hi, hvi⟩, hFv⟩
  rw [heq, card_biUnion]
  · clear hX heq
    induction A using Finset.induction_on with
    | empty => simp
    | @insert i A hi ih =>
      rw [sum_insert hi]
      exact (hparity i).add ih
  · intro i _ j _ hij
    exact (hdisj hij).mono sdiff_subset sdiff_subset

theorem compressedBoundary_whole_cut_parity (G : Multigraph V E)
    {M : Finset E} (hM : G.IsPerfectMatching M) (U₀ U₁ Z X : Finset V)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (hX : X ∈ wholeUnions (originalCores U₀ U₁) Z) :
    (G.cutOn (compressedBoundary G M U₀ U₁ Z) X).card % 2 = X.card % 2 := by
  have heven := compressedBoundary_uncovered_even G hM U₀ U₁ Z h01 h0Z h1Z hcover
  have hparity : ∀ i, Even (originalCores U₀ U₁ i \
      G.edgeSupport (compressedBoundary G M U₀ U₁ Z)).card := by
    intro i
    fin_cases i
    · simpa only [originalCores, if_pos rfl] using heven.1
    · simpa only [originalCores, show (1 : Fin 2) ≠ 0 by decide, if_false] using heven.2
  have hunc := even_uncovered_whole_union (originalCores U₀ U₁) Z
    (G.edgeSupport (compressedBoundary G M U₀ U₁ Z))
    (originalCores_disjoint U₀ U₁ h01)
    (compressedBoundary_covers_exceptional G hM U₀ U₁ Z) hparity X hX
  have hm := compressedBoundary_isMatching G (hM.isMatching G) U₀ U₁ Z
  exact ((hm.uncovered_even_iff_cut_parity G X).mp hunc).symm

theorem wholeCutDemand_odd_positive (G : Multigraph V E)
    (D : MultigraphMatchingProbability.Distribution G k S)
    (U₀ U₁ Z X : Finset V)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2)
    (hX : X ∈ wholeUnions (originalCores U₀ U₁) Z) (hodd : X.card % 2 = 1)
    (p : AssignmentSignature Z) (hp : 0 < signatureWeight D U₀ Z p) :
    1 ≤ wholeCutDemand G D U₀ U₁ Z X p := by
  obtain ⟨s, hs, _⟩ := CircuitPatterns.aggregateWeight_pos_witness
    (AssignedParts.NativeWeights.scaledWeight D)
    (fun s => coarseSignature G (D.matching s) U₀ Z) p hp
  rw [← hs, wholeCutDemand_at_sample G D U₀ U₁ Z X h01 h0Z h1Z hcover hZ hX s]
  have hparity := compressedBoundary_whole_cut_parity G (D.perfect s)
    U₀ U₁ Z X h01 h0Z h1Z hcover hX
  omega

theorem completed_native_cutOn_eq (G : Multigraph V E) (U₀ U₁ Z X : Finset V)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hX : X ∈ wholeUnions (originalCores U₀ U₁) Z) (F N : Finset E)
    (hFN : F ⊆ N)
    (hadded : ∀ e ∈ N, e ∈ F ∨ e ∈ G.internalOn univ U₀ ∨ e ∈ G.internalOn univ U₁) :
    G.cutOn N X = G.cutOn F X := by
  have hwhole := originalCores_whole U₀ U₁ Z X h01 h0Z h1Z hX
  have hnocut (U : Finset V) (hU : U ⊆ X ∨ Disjoint U X) (e : E)
      (he : e ∈ G.internalOn univ U) :
      (G.firstEnd e ∈ X) = (G.secondEnd e ∈ X) := by
    exact propext (whole_core_membership_iff U X hU
      (mem_filter.mp he).2.1 (mem_filter.mp he).2.2)
  ext e
  simp only [Multigraph.mem_cutOn]
  constructor
  · rintro ⟨heN, heX⟩
    refine ⟨?_, heX⟩
    rcases hadded e heN with he | he | he
    · exact he
    · exact (heX (hnocut U₀ hwhole.1 e he)).elim
    · exact (heX (hnocut U₁ hwhole.2 e he)).elim
  · rintro ⟨heF, heX⟩
    exact ⟨hFN heF, heX⟩

theorem completed_native_cut_count_eq_demand (G : Multigraph V E)
    (D : MultigraphMatchingProbability.Distribution G k S)
    (U₀ U₁ Z X : Finset V)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hZ : Z.card ≤ 2) (hX : X ∈ wholeUnions (originalCores U₀ U₁) Z)
    (F N : Finset E) (p : AssignmentSignature Z) (hFN : F ⊆ N)
    (hadded : ∀ e ∈ N, e ∈ F ∨ e ∈ G.internalOn univ U₀ ∨ e ∈ G.internalOn univ U₁)
    (hpool : ∀ e ∈ F, ∃ j, e ∈ poolCopies G U₀ U₁ Z j)
    (huse : ∀ j, (F ∩ poolCopies G U₀ U₁ Z j).card = poolDemand D U₀ U₁ Z j p) :
    (G.cutOn N X).card = wholeCutDemand G D U₀ U₁ Z X p := by
  rw [completed_native_cutOn_eq G U₀ U₁ Z X h01 h0Z h1Z hX F N hFN hadded]
  exact native_cut_count_eq_demand G D U₀ U₁ Z X h01 h0Z h1Z hZ hX F p hpool huse

variable [Fintype V]

/-- Native boundary counts, their internal completions, and embedded
retained cores give the actual residual no-overfull conclusion. -/
theorem native_residual_no_overfull {J : Type*} (G : Multigraph V E)
    (D : MultigraphMatchingProbability.Distribution G k S) (hk : 0 < k)
    (U₀ U₁ Z : Finset V)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2)
    (B N : J → Finset E) (T : Finset J) (kind : J → AssignmentSignature Z)
    (hNdisj : (T : Set J).Pairwise (fun i j => Disjoint (N i) (N j)))
    (hperfect : ∀ j ∈ T, G.IsPerfectMatching (N j)) (hT : T.card ≤ k)
    (hBN : ∀ j ∈ T, B j ⊆ N j)
    (hadded : ∀ j ∈ T, ∀ e ∈ N j,
      e ∈ B j ∨ e ∈ G.internalOn univ U₀ ∨ e ∈ G.internalOn univ U₁)
    (hpool : ∀ j ∈ T, ∀ e ∈ B j, ∃ r, e ∈ poolCopies G U₀ U₁ Z r)
    (huse : ∀ j ∈ T, ∀ r,
      (B j ∩ poolCopies G U₀ U₁ Z r).card = poolDemand D U₀ U₁ Z r (kind j))
    (hregular : ∀ v, G.degree v = k) (hno : ∀ X, ¬ G.IsOverfull k X)
    (C : ∀ i, SmallCuts.Core (residualGraph G N T) (originalCores U₀ U₁ i))
    (α c ν τ a : ℝ)
    (hα : 0 < α) (hc : 0 < c) (hν : 0 < ν) (hτ : 0 ≤ τ) (hτα : τ ≤ α / 10)
    (hklo : α * Fintype.card V ≤ ((k - T.card : ℕ) : ℝ))
    (hkhi : ((k - T.card : ℕ) : ℝ) ≤ 2 * Fintype.card V)
    (ha : a ≤ α * Fintype.card V / 10)
    (hlarge : 3 < ν ^ 2 * c ^ 2 * (Fintype.card V : ℝ))
    (hsize : ∀ i, c * Fintype.card V ≤ ((originalCores U₀ U₁ i).card : ℝ))
    (hrobust : ∀ i, IsRobustExpander (C i).graph ν τ)
    (hdegree : ∀ i v, ((k - T.card : ℕ) : ℝ) - a ≤ ((C i).graph.degree v : ℝ))
    (proposal accepted : AssignmentSignature Z → ℕ)
    (hn : ∀ p, familyMultiplicity kind T p ≤ accepted p)
    (hm : ∀ p, accepted p ≤ proposal p)
    (hweight : ∀ p, (proposal p : ℝ) ≤ signatureWeight D U₀ Z p)
    (hprotected : ∀ X ∈ wholeUnions (originalCores U₀ U₁) Z, X.card % 2 = 0 →
      (G.cutSize X : ℝ) -
        (∑ p, (proposal p : ℝ) * wholeCutDemand G D U₀ U₁ Z X p) < 2 * a →
          ∀ p, accepted p * wholeCutDemand G D U₀ U₁ Z X p = 0) :
    ∀ X, ¬ (residualGraph G N T).IsOverfull (k - T.card) X := by
  have hcover' : ∀ v, v ∈ Z ∨ ∃ i, v ∈ originalCores U₀ U₁ i := by
    intro v
    rcases hcover v with h0 | h1 | hz
    · exact Or.inr ⟨0, by simpa [originalCores] using h0⟩
    · exact Or.inr ⟨1, by simpa [originalCores] using h1⟩
    · exact Or.inl hz
  apply residual_no_overfull_of_pattern_counts G N T hNdisj hperfect
    (originalCores U₀ U₁) Z (originalCores_disjoint U₀ U₁ h01)
    (originalCores_disjoint_exceptions U₀ U₁ Z h0Z h1Z) hcover'
    kind k hT hregular hno C α c ν τ a hα hc hν hτ hτα hklo hkhi ha hlarge
    hsize hrobust hdegree (signatureWeight D U₀ Z) (signatureWeight_sum D U₀ Z)
    proposal accepted hn hm hweight (wholeCutDemand G D U₀ U₁ Z)
  · intro X hX j hj
    exact completed_native_cut_count_eq_demand G D U₀ U₁ Z X h01 h0Z h1Z hZ hX
      (B j) (N j) (kind j) (hBN j hj) (hadded j hj) (hpool j hj) (huse j hj)
  · intro X hX hodd p hp
    exact wholeCutDemand_odd_positive G D U₀ U₁ Z X h01 h0Z h1Z hcover hZ hX hodd p hp
  · intro X hX
    exact wholeCutDemand_capacity G D hk U₀ U₁ Z X h01 h0Z h1Z hcover hZ hX
  · exact hprotected

end Overfull.NativeReserve
