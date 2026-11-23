import Overfull.NativeReserve.Rounding
import Overfull.NativeReserve.Greedy
import Overfull.AssignedParts.NativePatternConstruction

/-!
# Native rounded demands on the six actual-copy pools

The paired exceptional pool retains its full parallel multiplicity. Each
signature uses zero or one copy of a pool. Weighted capacities and every
prefix inequality refer to the original distribution.
-/

noncomputable section

namespace Overfull.NativeReserve

open Finset Classical AssignedParts AssignedParts.NativeWeights CircuitPatterns
open scoped BigOperators

variable {V E S : Type*} [Fintype S] [Fintype E] {G : Multigraph V E} {k : ℕ}
  (D : MultigraphMatchingProbability.Distribution G k S)

def internalDemand {Z : Finset V} (p : AssignmentSignature Z) : ℕ :=
  if p = none then 1 else 0

def exceptionDemand {Z : Finset V} (z : ↥Z) (i : Fin 2)
    (p : AssignmentSignature Z) : ℕ :=
  if signatureAssignsCore p z i then 1 else 0

def crossingDemand (U₀ U₁ Z : Finset V) (p : AssignmentSignature Z) : ℕ :=
  if h : ∃ s, coarseSignature G (D.matching s) U₀ Z = p then
    (G.cutOn (D.matching h.choose) U₀ ∩ G.cutOn (D.matching h.choose) U₁).card % 2
  else 0

def poolDemand (U₀ U₁ Z : Finset V) : PoolKind Z → AssignmentSignature Z → ℕ
  | .pair => internalDemand
  | .exception z i => exceptionDemand z i
  | .crossing => crossingDemand D U₀ U₁ Z

private def poolKindEquiv (Z : Finset V) :
    PoolKind Z ≃ Unit ⊕ ((↥Z × Fin 2) ⊕ Unit) where
  toFun
    | .pair => .inl ()
    | .exception z i => .inr (.inl (z, i))
    | .crossing => .inr (.inr ())
  invFun
    | .inl _ => .pair
    | .inr (.inl (z, i)) => .exception z i
    | .inr (.inr _) => .crossing
  left_inv := by intro j; cases j <;> rfl
  right_inv := by
    rintro (u | (h | u))
    · cases u; rfl
    · rcases h with ⟨z, i⟩; rfl
    · cases u; rfl

theorem poolKind_card (Z : Finset V) : Fintype.card (PoolKind Z) = 2+2*Z.card := by
  rw [Fintype.card_congr (poolKindEquiv Z)]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_unit,
    Fintype.card_coe, Fintype.card_fin]
  omega

theorem poolKind_card_le_six (Z : Finset V) (hZ : Z.card ≤ 2) :
    Fintype.card (PoolKind Z) ≤ 6 := by
  rw [poolKind_card]
  omega

theorem poolDemand_le_one (U₀ U₁ Z : Finset V) (j : PoolKind Z)
    (p : AssignmentSignature Z) : poolDemand D U₀ U₁ Z j p ≤ 1 := by
  cases j with
  | pair => simp only [poolDemand, internalDemand]; split_ifs <;> omega
  | exception z i => simp only [poolDemand, exceptionDemand]; split_ifs <;> omega
  | crossing =>
    simp only [poolDemand, crossingDemand]
    split_ifs <;> omega

theorem crossingDemand_at_sample (U₀ U₁ Z : Finset V)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2) (s : S) :
    crossingDemand D U₀ U₁ Z (coarseSignature G (D.matching s) U₀ Z) =
      (G.cutOn (D.matching s) U₀ ∩ G.cutOn (D.matching s) U₁).card % 2 := by
  unfold crossingDemand
  rw [dif_pos (show ∃ t, coarseSignature G (D.matching t) U₀ Z =
      coarseSignature G (D.matching s) U₀ Z from ⟨s, rfl⟩)]
  exact coreCrossing_parity_eq_of_signature_eq G (D.perfect _) (D.perfect s)
    U₀ U₁ Z h01 h0Z h1Z hcover hZ (Classical.choose_spec _)

private theorem compressed_inter_exception_pool (M : Finset E)
    (U₀ U₁ Z U : Finset V) (z : ↥Z) :
    compressedBoundary G M U₀ U₁ Z ∩ exceptionCorePool G z.val U =
      M ∩ exceptionCorePool G z.val U := by
  ext e
  constructor
  · intro he
    exact mem_inter.mpr ⟨compressedBoundary_subset G M U₀ U₁ Z (mem_inter.mp he).1,
      (mem_inter.mp he).2⟩
  · intro he
    obtain ⟨heM, heA⟩ := mem_inter.mp he
    exact mem_inter.mpr ⟨compressedBoundary_retains_exceptional G M U₀ U₁ Z
      (mem_exceptionalCopies_of_incident G heM z.property (mem_filter.mp heA).2.1), heA⟩

private theorem inter_coreCrossingPool (M : Finset E) (U₀ U₁ : Finset V) :
    M ∩ coreCrossingPool G U₀ U₁ = G.cutOn M U₀ ∩ G.cutOn M U₁ := by
  ext e
  simp only [coreCrossingPool, mem_inter, Multigraph.mem_cutOn, mem_univ, true_and]
  tauto

theorem compressedBoundary_pool_usage (U₀ U₁ Z : Finset V)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2)
    {M : Finset E} (hM : G.IsPerfectMatching M) (s : S)
    (hcode : coarseSignature G M U₀ Z = coarseSignature G (D.matching s) U₀ Z)
    (j : PoolKind Z) :
    (compressedBoundary G M U₀ U₁ Z ∩ poolCopies G U₀ U₁ Z j).card =
      poolDemand D U₀ U₁ Z j (coarseSignature G (D.matching s) U₀ Z) := by
  cases j with
  | pair =>
    change (_ ∩ G.internalOn univ Z).card = internalDemand _
    rw [inter_internalPool_eq, compressedBoundary_internalOn,
      ← inter_internalPool_eq G M Z,
      internalPool_usage_eq_signature G (hM.isMatching G) U₀ Z hZ, hcode]
    rfl
  | exception z i =>
    change (_ ∩ exceptionCorePool G z.val (if i = 0 then U₀ else U₁)).card =
      exceptionDemand z i _
    rw [compressed_inter_exception_pool,
      exceptionCorePool_usage_eq_assignment G hM U₀ U₁ Z
        h01 h0Z h1Z hcover hZ z i, hcode]
    rfl
  | crossing =>
    change (_ ∩ coreCrossingPool G U₀ U₁).card = crossingDemand D U₀ U₁ Z _
    rw [inter_coreCrossingPool, compressedBoundary_coreCrossing_card G U₀ U₁ Z h01 h0Z h1Z,
      crossingDemand_at_sample D U₀ U₁ Z h01 h0Z h1Z hcover hZ s]
    exact coreCrossing_parity_eq_of_signature_eq G hM (D.perfect s)
      U₀ U₁ Z h01 h0Z h1Z hcover hZ hcode

theorem compressedBoundary_pool_usage_at_sample (U₀ U₁ Z : Finset V)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2)
    (s : S) (j : PoolKind Z) :
    (compressedBoundary G (D.matching s) U₀ U₁ Z ∩ poolCopies G U₀ U₁ Z j).card =
      poolDemand D U₀ U₁ Z j (coarseSignature G (D.matching s) U₀ Z) :=
  compressedBoundary_pool_usage D U₀ U₁ Z h01 h0Z h1Z hcover hZ (D.perfect s) s rfl j

theorem internalDemand_weight_eq_pool (hk : 0 < k) (U₀ Z : Finset V)
    (hZ : Z.card ≤ 2) :
    (∑ p, signatureWeight D U₀ Z p * (internalDemand p : ℝ)) =
      (G.internalOn univ Z).card := by
  simpa [internalDemand] using signatureWeight_none_eq_internalPool D hk U₀ Z hZ

theorem exceptionDemand_weight_eq_pool (hk : 0 < k) (U₀ U₁ Z : Finset V)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2)
    (z : ↥Z) (i : Fin 2) :
    (∑ p, signatureWeight D U₀ Z p * (exceptionDemand z i p : ℝ)) =
      (exceptionCorePool G z.val (if i = 0 then U₀ else U₁)).card := by
  simpa [exceptionDemand, sum_filter, mul_ite] using
    signature_assignment_weight_eq_pool G D hk U₀ U₁ Z h01 h0Z h1Z hcover hZ z i

theorem poolDemand_weight_capacity (hk : 0 < k) (U₀ U₁ Z : Finset V)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2) (j : PoolKind Z) :
    (∑ p, signatureWeight D U₀ Z p * (poolDemand D U₀ U₁ Z j p : ℝ)) ≤
      (poolCopies G U₀ U₁ Z j).card := by
  apply aggregate_capacity D hk (fun s => coarseSignature G (D.matching s) U₀ Z)
    (fun s => compressedBoundary G (D.matching s) U₀ U₁ Z)
    (fun s => compressedBoundary_subset G (D.matching s) U₀ U₁ Z)
  intro s
  rw [compressedBoundary_pool_usage_at_sample D U₀ U₁ Z h01 h0Z h1Z hcover hZ]

theorem signatureWeight_mul_poolDemand_le (hk : 0 < k) (U₀ U₁ Z : Finset V)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2)
    (j : PoolKind Z) (p : AssignmentSignature Z) :
    signatureWeight D U₀ Z p * (poolDemand D U₀ U₁ Z j p : ℝ) ≤
      (poolCopies G U₀ U₁ Z j).card := by
  apply le_trans (single_le_sum (fun q _ => mul_nonneg
    (signatureWeight_nonneg D U₀ Z q) (Nat.cast_nonneg _)) (mem_univ p))
  exact poolDemand_weight_capacity D hk U₀ U₁ Z h01 h0Z h1Z hcover hZ j

theorem prefix_pool_demand_reserved (η : ℝ) (hη₁ : η ≤ 1) (hk : 0 < k)
    (U₀ U₁ Z : Finset V) (h01 : Disjoint U₀ U₁)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2)
    (s : S) (m : AssignmentSignature Z → ℕ)
    (hm : ∀ p, m p ≤ multiplicity D η U₀ Z s p) (j : PoolKind Z) :
    (∑ p, (m p : ℝ)*poolDemand D U₀ U₁ Z j p) ≤
      (1-η)*((poolCopies G U₀ U₁ Z j).card -
        (reserveSize D U₀ Z s : ℝ)*
          poolDemand D U₀ U₁ Z j (coarseSignature G (D.matching s) U₀ Z)) := by
  apply le_trans _ (proposed_demand_le η (signatureWeight D U₀ Z)
    (fun p => (poolDemand D U₀ U₁ Z j p : ℝ))
    (coarseSignature G (D.matching s) U₀ Z) (reserveSize D U₀ Z s)
    (poolCopies G U₀ U₁ Z j).card hη₁ (signatureWeight_nonneg D U₀ Z)
    (reserveSize_le_weight D U₀ Z s) (fun _ => Nat.cast_nonneg _)
    (poolDemand_weight_capacity D hk U₀ U₁ Z h01 h0Z h1Z hcover hZ j))
  apply sum_le_sum
  intro p _
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hm p) (Nat.cast_nonneg _)

theorem prefix_pool_reserve (η : ℝ) (hη₀ : 0 ≤ η) (hη₁ : η ≤ 1) (hk : 0 < k)
    (U₀ U₁ Z : Finset V) (h01 : Disjoint U₀ U₁)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2)
    (s : S) (m : AssignmentSignature Z → ℕ)
    (hm : ∀ p, m p ≤ multiplicity D η U₀ Z s p) (j : PoolKind Z) :
    (reserveSize D U₀ Z s : ℝ)*
        poolDemand D U₀ U₁ Z j (coarseSignature G (D.matching s) U₀ Z) ≤
      (poolCopies G U₀ U₁ Z j).card - ∑ p, (m p : ℝ)*poolDemand D U₀ U₁ Z j p := by
  exact prefix_pair_reserve η (signatureWeight D U₀ Z)
    (coarseSignature G (D.matching s) U₀ Z) (reserveSize D U₀ Z s) m
    (poolDemand D U₀ U₁ Z j) (poolCopies G U₀ U₁ Z j).card hη₀ hη₁
    (signatureWeight_nonneg D U₀ Z) (reserveSize_le_weight D U₀ Z s) hm
    (poolDemand_weight_capacity D hk U₀ U₁ Z h01 h0Z h1Z hcover hZ j)

end Overfull.NativeReserve
