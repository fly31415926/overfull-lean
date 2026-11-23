import Overfull.NativeReserve.Schedule
import Overfull.NativeReserve.DenseSelection
import Overfull.NativeReserve.ProtectedPacking
import Overfull.CircuitPatterns.Multiplicity

/-!
# Realizing accepted native multiplicities outside the actual reserve

Every multiplicity below the single dense-pool proposal is realized by
pairwise disjoint boundary matchings on original edge copies. The construction
protects the actual reserve already built for the same heavy signature. Each
round has the exact native pool use prescribed by its accepted code, retains
the exceptional pair when present, and covers every exceptional vertex.

The input `12*a ≤ η*L` makes the sparse-pool threshold large enough for the
greedy endpoint avoidance after reserving at most one third of each used
pool. Perfect-matching completion in the robust cores remains a later step.
-/

noncomputable section

namespace Overfull.NativeReserve

open Finset Classical AssignedParts AssignedParts.NativeWeights CircuitPatterns
open scoped BigOperators

variable {V E S : Type*} [Fintype S] [Fintype E] {G : Multigraph V E} {k : ℕ}
  (D : MultigraphMatchingProbability.Distribution G k S)

/-- Any accepted subproposal is genuinely realized outside the already chosen
boundary reserve. Both families use the original edge-copy type. -/
theorem exists_accepted_family_avoiding_reserve
    (U₀ U₁ Z : Finset V) (C₀ : SmallCuts.Core G U₀) (C₁ : SmallCuts.Core G U₁)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2)
    (hk : 0 < k) (a η L : ℝ) (ha : 0 < a) (hη₀ : 0 ≤ η) (hη₁ : η ≤ 1)
    (hbudget : 12*a ≤ η*L)
    (hregular : ∀ v, G.degree v = k)
    (hdegree₀ : ∀ v, (k : ℝ)-a ≤ (C₀.graph.degree v : ℝ))
    (hdegree₁ : ∀ v, (k : ℝ)-a ≤ (C₁.graph.degree v : ℝ))
    (s : S) (Q : BoundaryPacking G U₀ U₁ Z (D.matching s) (reserveSize D U₀ Z s))
    (m : AssignmentSignature Z → ℕ)
    (hm : ∀ p, m p ≤ denseMultiplicity D η U₀ U₁ Z s L p) :
    ∃ F : PatternCopies m → Finset E,
      (∀ r, G.IsMatching (F r)) ∧
      (∀ r r', r ≠ r' → Disjoint (F r) (F r')) ∧
      (∀ r, Disjoint (F r) (Q.reservedCopies D)) ∧
      (∀ r, Z ⊆ G.edgeSupport (F r)) ∧
      (∀ r, ∀ e ∈ F r, ∃ p : PoolKind Z, e ∈ poolCopies G U₀ U₁ Z p) ∧
      (∀ r, (F r).card ≤ 3) ∧
      (∀ r j, (F r ∩ poolCopies G U₀ U₁ Z j).card = poolDemand D U₀ U₁ Z j r.1) := by
  have hwitness (r : PatternCopies m) :
      ∃ t, coarseSignature G (D.matching t) U₀ Z = r.1 := by
    have hr : 0 < m r.1 := Nat.zero_lt_of_lt r.2.isLt
    have hp : 0 < multiplicity D η U₀ Z s r.1 :=
      hr.trans_le ((hm r.1).trans (denseMultiplicity_le D η U₀ U₁ Z s L r.1))
    obtain ⟨t, ht, _hpos⟩ := multiplicity_pos_witness D η hη₀ hη₁ U₀ Z s r.1 hp
    exact ⟨t, ht⟩
  choose sample hsample using hwitness
  let B (r : PatternCopies m) := compressedBoundary G (D.matching (sample r)) U₀ U₁ Z
  have hmatching (r : PatternCopies m) : G.IsMatching (B r) :=
    compressedBoundary_isMatching G ((D.perfect (sample r)).isMatching G) U₀ U₁ Z
  have hcoverZ (r : PatternCopies m) : Z ⊆ G.edgeSupport (B r) :=
    compressedBoundary_covers_exceptional G (D.perfect (sample r)) U₀ U₁ Z
  have hcard (r : PatternCopies m) : (B r).card ≤ 3 := by
    have h := compressedBoundary_card_le G ((D.perfect (sample r)).isMatching G) U₀ U₁ Z
    dsimp only [B]
    omega
  have hB (r : PatternCopies m) (e : E) (he : e ∈ B r) :
      ∃ p : PoolKind Z, e ∈ poolCopies G U₀ U₁ Z p :=
    compressedBoundary_exists_pool G (D.matching (sample r)) U₀ U₁ Z hcover he
  have husage (r : PatternCopies m) (j : PoolKind Z) :
      (B r ∩ poolCopies G U₀ U₁ Z j).card = poolDemand D U₀ U₁ Z j r.1 := by
    dsimp only [B]
    rw [compressedBoundary_pool_usage_at_sample D U₀ U₁ Z h01 h0Z h1Z hcover hZ,
      hsample]
  have htotal (j : PoolKind Z) : (∑ r, (B r ∩ poolCopies G U₀ U₁ Z j).card) =
      ∑ p, m p * poolDemand D U₀ U₁ Z j p := by
    simp_rw [husage]
    simp [PatternCopies, Fintype.sum_sigma]
  have huse (j : PoolKind Z) : ((∑ r, (B r ∩ poolCopies G U₀ U₁ Z j).card : ℕ) : ℝ) ≤
      (1-η) * (poolCopies G U₀ U₁ Z j \ Q.reservedCopies D).card := by
    have h := dense_prefix_pool_demand_reserved D η hη₁ hk U₀ U₁ Z
      h01 h0Z h1Z hcover hZ s L m hm j
    have hacct : ((poolCopies G U₀ U₁ Z j \ Q.reservedCopies D).card : ℝ) +
        (reserveSize D U₀ Z s : ℝ) *
          poolDemand D U₀ U₁ Z j (coarseSignature G (D.matching s) U₀ Z) =
          (poolCopies G U₀ U₁ Z j).card := by
      exact_mod_cast Q.unreserved_pool_accounting D h01 h0Z h1Z hcover hZ j
    rw [htotal]
    push_cast
    have heq : ((poolCopies G U₀ U₁ Z j).card : ℝ) -
        (reserveSize D U₀ Z s : ℝ) *
          poolDemand D U₀ U₁ Z j (coarseSignature G (D.matching s) U₀ Z) =
          (poolCopies G U₀ U₁ Z j \ Q.reservedCopies D).card := by linarith
    rw [heq] at h
    exact h
  have hslack (j : PoolKind Z)
      (hj : ∃ r, (B r ∩ poolCopies G U₀ U₁ Z j).Nonempty) :
      8*a ≤ η * (poolCopies G U₀ U₁ Z j \ Q.reservedCopies D).card := by
    obtain ⟨r, hr⟩ := hj
    have hpos : 0 < poolDemand D U₀ U₁ Z j r.1 := by
      rw [← husage r j]
      exact hr.card_pos
    have hmpos : 0 < denseMultiplicity D η U₀ U₁ Z s L r.1 :=
      (Nat.zero_lt_of_lt r.2.isLt).trans_le (hm r.1)
    have hL := denseMultiplicity_pos_pool D η U₀ U₁ Z s L r.1 hmpos j hpos
    have hlower := Q.unreserved_pool_lower D hk (three_mul_reserveSize_le_weight D U₀ Z s)
      h01 h0Z h1Z hcover hZ j
    have hηL := mul_le_mul_of_nonneg_left hL hη₀
    have hηlower := mul_le_mul_of_nonneg_left hlower hη₀
    nlinarith
  obtain ⟨F, hmatch, hdisj, havoid, hcov, hboundary, hsize, hpools⟩ :=
    exists_family_avoiding_with_representative_pools G U₀ U₁ Z C₀ C₁
      h01 h0Z h1Z hcover hZ k a η ha hregular hdegree₀ hdegree₁
      B hmatching hcoverZ hcard hB (Q.reservedCopies D) huse hslack
  exact ⟨F, hmatch, hdisj, havoid, hcov, hboundary,
    fun r => (hsize r).trans_le (hcard r), fun r j => (hpools r j).trans (husage r j)⟩

end Overfull.NativeReserve
