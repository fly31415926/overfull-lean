import Overfull.AssignedParts.SignaturePools
import Overfull.AssignedParts.NativeWeights

/-!
# A heavy native assignment signature and its actual-copy supplies

There are at most five signatures for two cores and at most two exceptions.
The actual perfect-matching distribution therefore provides a representative
whose signature has scaled weight at least one fifth of the regular degree.
Every pool forced by that signature contains at least this many original
copies. These are pool capacities, not distinct-neighbor or simultaneous
reserve assertions, and no residual safety is inferred from them.
-/

noncomputable section

namespace Overfull.AssignedParts

open Finset Classical
open NativeWeights
open Overfull.CircuitPatterns (aggregateWeight)
open scoped BigOperators

variable {V E S : Type*} [Fintype S] {G : Multigraph V E} {k : ℕ}
  (D : MultigraphMatchingProbability.Distribution G k S)

def signatureWeight (U₀ Z : Finset V) (p : AssignmentSignature Z) : ℝ :=
  aggregateWeight (scaledWeight D) (fun s => coarseSignature G (D.matching s) U₀ Z) p

theorem signatureWeight_nonneg (U₀ Z : Finset V) (p : AssignmentSignature Z) :
    0 ≤ signatureWeight D U₀ Z p :=
  CircuitPatterns.aggregateWeight_nonneg _ (scaledWeight_nonneg D) _ p

theorem signatureWeight_sum (U₀ Z : Finset V) :
    ∑ p, signatureWeight D U₀ Z p = k :=
  aggregateWeight_total D _

/-- The chosen positive-weight sample realizes the same heavy signature. -/
theorem exists_heavy_signature (hk : 0 < k) (U₀ Z : Finset V) (hZ : Z.card ≤ 2) :
    ∃ s, 0 < scaledWeight D s ∧
      (k : ℝ) / 5 ≤ signatureWeight D U₀ Z (coarseSignature G (D.matching s) U₀ Z) := by
  obtain ⟨p, s, hs, hpos, hweight⟩ := exists_heavy_code D hk
    (fun s => coarseSignature G (D.matching s) U₀ Z) 5 (by omega)
    (card_assignmentSignature_le_five Z hZ)
  exact ⟨s, hpos, by simpa [signatureWeight, hs] using hweight⟩

variable [Fintype E]

/-- The paired signature is bounded by the whole parallel-copy pool. -/
theorem signatureWeight_none_le_internalPool (hk : 0 < k) (U₀ Z : Finset V) :
    signatureWeight D U₀ Z none ≤ (G.internalOn univ Z).card := by
  apply aggregateWeight_le_pool D hk _ none (G.internalOn univ Z)
  intro s hs
  exact signature_none_uses_internalPool G (D.matching s) U₀ Z hs

theorem signatureWeight_some_le_exceptionCorePool (hk : 0 < k)
    (U₀ U₁ Z : Finset V) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (σ : ↥Z → Fin 2) (z : ↥Z) :
    signatureWeight D U₀ Z (some σ) ≤
      (exceptionCorePool G z.val (if σ z = 0 then U₀ else U₁)).card := by
  apply aggregateWeight_le_pool D hk _ (some σ)
    (exceptionCorePool G z.val (if σ z = 0 then U₀ else U₁))
  intro s hs
  exact signature_some_uses_exceptionCorePool G (D.perfect s)
    U₀ U₁ Z h0Z h1Z hcover σ hs z

theorem signatureWeight_le_coreCrossingPool_of_odd (hk : 0 < k)
    (U₀ U₁ Z : Finset V) (h01 : Disjoint U₀ U₁)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2)
    (s : S) (hodd : (G.cutOn (D.matching s) U₀ ∩ G.cutOn (D.matching s) U₁).card % 2 = 1) :
    signatureWeight D U₀ Z (coarseSignature G (D.matching s) U₀ Z) ≤
      (coreCrossingPool G U₀ U₁).card := by
  apply aggregateWeight_le_pool D hk _ _ (coreCrossingPool G U₀ U₁)
  intro t ht
  exact signature_uses_coreCrossingPool_of_odd G (D.perfect s) (D.perfect t)
    U₀ U₁ Z h01 h0Z h1Z hcover hZ ht.symm hodd

/-- One actual representative simultaneously certifies every pool forced by
its heavy signature. The bounds concern the original host. -/
theorem exists_heavy_signature_with_pools (hk : 0 < k)
    (U₀ U₁ Z : Finset V) (h01 : Disjoint U₀ U₁)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2) :
    ∃ s, 0 < scaledWeight D s ∧
      (k : ℝ) / 5 ≤ signatureWeight D U₀ Z (coarseSignature G (D.matching s) U₀ Z) ∧
      (coarseSignature G (D.matching s) U₀ Z = none →
        (k : ℝ) / 5 ≤ (G.internalOn univ Z).card) ∧
      (∀ σ, coarseSignature G (D.matching s) U₀ Z = some σ → ∀ z : ↥Z,
        (k : ℝ) / 5 ≤ (exceptionCorePool G z.val (if σ z = 0 then U₀ else U₁)).card) ∧
      ((G.cutOn (D.matching s) U₀ ∩ G.cutOn (D.matching s) U₁).card % 2 = 1 →
        (k : ℝ) / 5 ≤ (coreCrossingPool G U₀ U₁).card) ∧
      (∀ t, coarseSignature G (D.matching t) U₀ Z =
          coarseSignature G (D.matching s) U₀ Z →
        assignedLabel G (D.matching t) U₀ U₁ Z = assignedLabel G (D.matching s) U₀ U₁ Z) := by
  obtain ⟨s, hpos, hweight⟩ := exists_heavy_signature D hk U₀ Z hZ
  refine ⟨s, hpos, hweight, ?_, ?_, ?_, ?_⟩
  · intro hc
    rw [hc] at hweight
    exact hweight.trans (signatureWeight_none_le_internalPool D hk U₀ Z)
  · intro σ hc z
    rw [hc] at hweight
    exact hweight.trans (signatureWeight_some_le_exceptionCorePool D hk
      U₀ U₁ Z h0Z h1Z hcover σ z)
  · intro hodd
    exact hweight.trans (signatureWeight_le_coreCrossingPool_of_odd D hk
      U₀ U₁ Z h01 h0Z h1Z hcover hZ s hodd)
  · intro t ht
    exact assignedLabel_eq_of_signature_eq G (D.perfect t) (D.perfect s)
      U₀ U₁ Z h01 h0Z h1Z hcover hZ ht

omit D in
/-- Positive regular degree and absence of overfull sets construct the
distribution and its actual matching representative. There is no assumed
heavy pattern or copy-supply hypothesis. -/
theorem exists_assignment_matching_with_linear_pools [Fintype V]
    (G : Multigraph V E) (hk : 0 < k) (hregular : ∀ v, G.degree v = k)
    (hno : ∀ X : Finset V, ¬ G.IsOverfull k X)
    (U₀ U₁ Z : Finset V) (h01 : Disjoint U₀ U₁)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2) :
    ∃ M : Finset E, G.IsPerfectMatching M ∧
      (coarseSignature G M U₀ Z = none → (k : ℝ) / 5 ≤ (G.internalOn univ Z).card) ∧
      (∀ σ, coarseSignature G M U₀ Z = some σ → ∀ z : ↥Z,
        (k : ℝ) / 5 ≤ (exceptionCorePool G z.val (if σ z = 0 then U₀ else U₁)).card) ∧
      ((G.cutOn M U₀ ∩ G.cutOn M U₁).card % 2 = 1 →
        (k : ℝ) / 5 ≤ (coreCrossingPool G U₀ U₁).card) := by
  obtain ⟨T, hT, ⟨D⟩⟩ := MultigraphMatchingProbability.exists_distribution hk hregular hno
  letI := hT
  obtain ⟨s, _, _, hpair, hex, hcross, _⟩ := exists_heavy_signature_with_pools D hk
    U₀ U₁ Z h01 h0Z h1Z hcover hZ
  exact ⟨D.matching s, D.perfect s, hpair, hex, hcross⟩

end Overfull.AssignedParts
