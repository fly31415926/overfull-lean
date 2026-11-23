import Overfull.NativeReserve.RoundedPools

/-!
# Discarding signatures that use a sparse original pool

At most six original-copy pools are tested. All decisions use the same
initial rounded proposal and the reserve remains excluded in the capacity
bound for every accepted prefix.
-/

noncomputable section

namespace Overfull.NativeReserve

open Finset Classical AssignedParts AssignedParts.NativeWeights CircuitPatterns
open scoped BigOperators

variable {V E S : Type*} [Fintype S] [Fintype E] {G : Multigraph V E} {k : ℕ}
  (D : MultigraphMatchingProbability.Distribution G k S)

def densePoolKeep (U₀ U₁ Z : Finset V) (L : ℝ) (p : AssignmentSignature Z) : Prop :=
  ∀ j, ((poolCopies G U₀ U₁ Z j).card : ℝ) < L → poolDemand D U₀ U₁ Z j p = 0

def denseMultiplicity (η : ℝ) (U₀ U₁ Z : Finset V) (s : S) (L : ℝ) :
    AssignmentSignature Z → ℕ :=
  acceptedMultiplicity (densePoolKeep D U₀ U₁ Z L) (multiplicity D η U₀ Z s)

theorem denseMultiplicity_le (η : ℝ) (U₀ U₁ Z : Finset V) (s : S)
    (L : ℝ) (p : AssignmentSignature Z) :
    denseMultiplicity D η U₀ U₁ Z s L p ≤ multiplicity D η U₀ Z s p :=
  acceptedMultiplicity_le _ _ p

theorem denseMultiplicity_pos_pool (η : ℝ) (U₀ U₁ Z : Finset V) (s : S)
    (L : ℝ) (p : AssignmentSignature Z)
    (hp : 0 < denseMultiplicity D η U₀ U₁ Z s L p) (j : PoolKind Z)
    (hj : 0 < poolDemand D U₀ U₁ Z j p) :
    L ≤ (poolCopies G U₀ U₁ Z j).card := by
  by_contra hL
  have hnot : ¬densePoolKeep D U₀ U₁ Z L p := by
    intro hkeep
    have hzero := hkeep j (not_le.mp hL)
    omega
  simp [denseMultiplicity, acceptedMultiplicity, hnot] at hp

theorem dense_discard_bound (η : ℝ) (hη₀ : 0 ≤ η) (hη₁ : η ≤ 1) (hk : 0 < k)
    (U₀ U₁ Z : Finset V) (h01 : Disjoint U₀ U₁)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2)
    (s : S) (L : ℝ) (hL : 0 ≤ L) :
    (∑ p, (multiplicity D η U₀ Z s p : ℝ)) ≤
      (∑ p, (denseMultiplicity D η U₀ U₁ Z s L p : ℝ)) + 6*L := by
  let bad (j : PoolKind Z) (p : AssignmentSignature Z) :=
    ((poolCopies G U₀ U₁ Z j).card : ℝ) < L ∧ 0 < poolDemand D U₀ U₁ Z j p
  letI (j : PoolKind Z) (p : AssignmentSignature Z) : Decidable (bad j p) :=
    Classical.propDecidable _
  have hcoverBad (p : AssignmentSignature Z) (hp : ¬densePoolKeep D U₀ U₁ Z L p) :
      ∃ j, bad j p := by
    by_contra hn
    apply hp
    intro j hj
    have hnp : ¬0 < poolDemand D U₀ U₁ Z j p := fun hpos => hn ⟨j, hj, hpos⟩
    omega
  have hbase := discard_union_bound (multiplicity D η U₀ Z s)
    (densePoolKeep D U₀ U₁ Z L) bad hcoverBad
  have htest (j : PoolKind Z) :
      (∑ p, if bad j p then (multiplicity D η U₀ Z s p : ℝ) else 0) ≤ L := by
    by_cases hj : ((poolCopies G U₀ U₁ Z j).card : ℝ) < L
    · simp only [bad, hj, true_and]
      exact (crossing_multiplicity_le_capacity (multiplicity D η U₀ Z s)
        (signatureWeight D U₀ Z) (poolDemand D U₀ U₁ Z j)
        (poolCopies G U₀ U₁ Z j).card
        (multiplicity_le_weight D η hη₀ hη₁ U₀ Z s)
        (poolDemand_weight_capacity D hk U₀ U₁ Z h01 h0Z h1Z hcover hZ j)).trans hj.le
    · simp only [bad, hj, false_and, if_false, sum_const_zero]
      exact hL
  have htests : (∑ j, ∑ p, if bad j p then
      (multiplicity D η U₀ Z s p : ℝ) else 0) ≤ 6*L := by
    calc
      _ ≤ ∑ _j : PoolKind Z, L := sum_le_sum (fun j _ => htest j)
      _ = (Fintype.card (PoolKind Z) : ℝ)*L := by simp
      _ ≤ 6*L := mul_le_mul_of_nonneg_right
        (by exact_mod_cast poolKind_card_le_six Z hZ) hL
  exact hbase.trans (add_le_add_left htests _)

theorem dense_retainedDegree_bounds (η : ℝ) (hη₀ : 0 ≤ η) (hη₁ : η ≤ 1)
    (hk : 0 < k) (U₀ U₁ Z : Finset V) (h01 : Disjoint U₀ U₁)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2)
    (s : S) (L : ℝ) (hL : 0 ≤ L) :
    let m := denseMultiplicity D η U₀ U₁ Z s L
    (k-∑ p, m p)+(∑ p, m p) = k ∧ reserveSize D U₀ Z s ≤ k-∑ p, m p ∧
      ((k-∑ p, m p : ℕ) : ℝ) ≤ reserveSize D U₀ Z s+η*k+5+6*L := by
  exact accepted_retainedDegree_bounds D η hη₀ hη₁ U₀ Z hZ s
    (densePoolKeep D U₀ U₁ Z L) (6*L)
    (dense_discard_bound D η hη₀ hη₁ hk U₀ U₁ Z h01 h0Z h1Z hcover hZ s L hL)

theorem dense_prefix_pool_demand_reserved (η : ℝ) (hη₁ : η ≤ 1) (hk : 0 < k)
    (U₀ U₁ Z : Finset V) (h01 : Disjoint U₀ U₁)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2)
    (s : S) (L : ℝ) (m : AssignmentSignature Z → ℕ)
    (hm : ∀ p, m p ≤ denseMultiplicity D η U₀ U₁ Z s L p) (j : PoolKind Z) :
    (∑ p, (m p : ℝ)*poolDemand D U₀ U₁ Z j p) ≤
      (1-η)*((poolCopies G U₀ U₁ Z j).card -
        (reserveSize D U₀ Z s : ℝ)*
          poolDemand D U₀ U₁ Z j (coarseSignature G (D.matching s) U₀ Z)) :=
  prefix_pool_demand_reserved D η hη₁ hk U₀ U₁ Z h01 h0Z h1Z hcover hZ s m
    (fun p => (hm p).trans (denseMultiplicity_le D η U₀ U₁ Z s L p)) j

theorem dense_prefix_pool_demand (η : ℝ) (hη₁ : η ≤ 1) (hk : 0 < k)
    (U₀ U₁ Z : Finset V) (h01 : Disjoint U₀ U₁)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2)
    (s : S) (L : ℝ) (m : AssignmentSignature Z → ℕ)
    (hm : ∀ p, m p ≤ denseMultiplicity D η U₀ U₁ Z s L p) (j : PoolKind Z) :
    (∑ p, (m p : ℝ)*poolDemand D U₀ U₁ Z j p) ≤
      (1-η)*(poolCopies G U₀ U₁ Z j).card := by
  apply (dense_prefix_pool_demand_reserved D η hη₁ hk U₀ U₁ Z
    h01 h0Z h1Z hcover hZ s L m hm j).trans
  exact mul_le_mul_of_nonneg_left (sub_le_self _ (mul_nonneg (Nat.cast_nonneg _)
    (Nat.cast_nonneg _))) (sub_nonneg.mpr hη₁)

end Overfull.NativeReserve
