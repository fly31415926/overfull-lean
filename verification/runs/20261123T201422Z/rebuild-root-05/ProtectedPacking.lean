import Overfull.NativeReserve.PackingConstruction
import Overfull.NativeReserve.RoundedPools
import Overfull.NativeReserve.Residual

/-!
# Exact accounting for the protected native reserve

The actually packed boundaries, not numerical placeholders, are removed
from the pool available to later rounds. At least two thirds of every
original pool remains before those later rounds begin.
-/

noncomputable section

namespace Overfull.NativeReserve

open Finset Classical AssignedParts AssignedParts.NativeWeights
open scoped BigOperators

variable {V E S : Type*} [Fintype S] [Fintype E] {G : Multigraph V E} {k : ℕ}
  (D : MultigraphMatchingProbability.Distribution G k S)

omit [Fintype E] in
theorem exists_rounded_boundary_reserve (hk : 0 < k) (U₀ U₁ Z : Finset V)
    (hZ : Z.card ≤ 2) (s : S) :
    Nonempty (BoundaryPacking G U₀ U₁ Z (D.matching s) (reserveSize D U₀ Z s)) := by
  apply exists_boundaryPacking D hk U₀ U₁ Z hZ s
  simpa [mul_comm] using three_mul_reserveSize_le_weight D U₀ Z s

namespace BoundaryPacking

variable {U₀ U₁ Z : Finset V} {s : S} {r : ℕ}
  (Q : BoundaryPacking G U₀ U₁ Z (D.matching s) r)

def reservedCopies : Finset E := removedCopies Q.boundary univ

omit [Fintype E] in
theorem reserved_degree {z : V} (hz : z ∈ Z) :
    G.degreeOn (Q.reservedCopies D) z = r := by
  rw [reservedCopies, removed_degreeOn G Q.boundary univ
    (fun _ _ _ _ hij => Q.pairwise_disjoint hij)]
  have hu (i : Fin r) : G.degreeOn (Q.boundary i) z = 1 := Q.exceptional_degree i hz
  simp only [hu, sum_const, card_univ, Fintype.card_fin, smul_eq_mul,
    mul_one]

omit [Fintype E] in
theorem reserved_card : (Q.reservedCopies D).card ≤ r*(Z.card+1) := by
  calc
    _ ≤ ∑ i : Fin r, (Q.boundary i).card := card_biUnion_le
    _ ≤ ∑ _i : Fin r, (Z.card+1) := sum_le_sum (fun i _ => Q.card_le i)
    _ = _ := by simp

theorem reserved_pool_card
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2)
    (j : PoolKind Z) :
    (Q.reservedCopies D ∩ poolCopies G U₀ U₁ Z j).card =
      r*poolDemand D U₀ U₁ Z j (coarseSignature G (D.matching s) U₀ Z) := by
  rw [reservedCopies, removed_pool_card Q.boundary univ
    (fun _ _ _ _ hij => Q.pairwise_disjoint hij)]
  have hu (i : Fin r) : (Q.boundary i ∩ poolCopies G U₀ U₁ Z j).card =
      poolDemand D U₀ U₁ Z j (coarseSignature G (D.matching s) U₀ Z) :=
    compressedBoundary_pool_usage D U₀ U₁ Z h01 h0Z h1Z hcover hZ
      (Q.perfect i) s (Q.sameSignature i) j
  simp_rw [hu]
  simp

theorem unreserved_pool_accounting
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2)
    (j : PoolKind Z) :
    (poolCopies G U₀ U₁ Z j \ Q.reservedCopies D).card +
      r*poolDemand D U₀ U₁ Z j (coarseSignature G (D.matching s) U₀ Z) =
        (poolCopies G U₀ U₁ Z j).card := by
  rw [← Q.reserved_pool_card D h01 h0Z h1Z hcover hZ j,
    inter_comm (Q.reservedCopies D)]
  exact card_sdiff_add_card_inter _ _

theorem unreserved_pool_lower (hk : 0 < k)
    (hr : 3*(r : ℝ) ≤ signatureWeight D U₀ Z
      (coarseSignature G (D.matching s) U₀ Z))
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2)
    (j : PoolKind Z) :
    (2/3 : ℝ)*(poolCopies G U₀ U₁ Z j).card ≤
      (poolCopies G U₀ U₁ Z j \ Q.reservedCopies D).card := by
  have hcap := signatureWeight_mul_poolDemand_le D hk U₀ U₁ Z
    h01 h0Z h1Z hcover hZ j (coarseSignature G (D.matching s) U₀ Z)
  have hmul := mul_le_mul_of_nonneg_right hr
    (show (0 : ℝ) ≤ poolDemand D U₀ U₁ Z j
      (coarseSignature G (D.matching s) U₀ Z) from Nat.cast_nonneg _)
  have hacct : ((poolCopies G U₀ U₁ Z j \ Q.reservedCopies D).card : ℝ) +
      (r : ℝ)*poolDemand D U₀ U₁ Z j (coarseSignature G (D.matching s) U₀ Z) =
        (poolCopies G U₀ U₁ Z j).card := by
    exact_mod_cast Q.unreserved_pool_accounting D h01 h0Z h1Z hcover hZ j
  nlinarith

end BoundaryPacking

end Overfull.NativeReserve
