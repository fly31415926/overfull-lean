import Overfull.NativeReserve.DenseSelection
import Overfull.NativeReserve.NativeCutWeights

/-!
# Protecting small even whole-core cuts before realization

Every cut is tested against the single original rounded proposal. Sparse
pool discards and cut discards may overlap; the union bound counts their
combined loss without changing the tests after a discard.
-/

noncomputable section

namespace Overfull.NativeReserve

open Finset Classical AssignedParts AssignedParts.NativeWeights CircuitPatterns
open scoped BigOperators

variable {V E S : Type*} [Fintype S] [Fintype E] {G : Multigraph V E} {k : ℕ}
  (D : MultigraphMatchingProbability.Distribution G k S)

theorem two_core_wholeUnions_card (U₀ U₁ Z : Finset V) (hZ : Z.card ≤ 2) :
    (ForceMatching.wholeUnions (originalCores U₀ U₁) Z).card ≤ 16 := by
  apply (ForceMatching.wholeUnions_card (originalCores U₀ U₁) Z).trans
  have hpow : 2^(Fintype.card (Fin 2)+Z.card) ≤ 2^4 :=
    Nat.pow_le_pow_right (by omega) (by simpa using hZ)
  norm_num at hpow ⊢
  exact hpow

def smallEvenWholeCut (η : ℝ) (U₀ U₁ Z : Finset V) (s : S) (a : ℝ)
    (X : Finset V) : Prop :=
  X.card % 2 = 0 ∧ (G.cutSize X : ℝ) -
    (∑ p, (multiplicity D η U₀ Z s p : ℝ) * wholeCutDemand G D U₀ U₁ Z X p) < 2*a

def cutSafeKeep (η : ℝ) (U₀ U₁ Z : Finset V) (s : S) (a : ℝ)
    (p : AssignmentSignature Z) : Prop :=
  ∀ X ∈ ForceMatching.wholeUnions (originalCores U₀ U₁) Z,
    smallEvenWholeCut D η U₀ U₁ Z s a X → wholeCutDemand G D U₀ U₁ Z X p = 0

def protectedMultiplicity (η : ℝ) (U₀ U₁ Z : Finset V) (s : S) (L a : ℝ) :
    AssignmentSignature Z → ℕ :=
  acceptedMultiplicity (cutSafeKeep D η U₀ U₁ Z s a)
    (denseMultiplicity D η U₀ U₁ Z s L)

theorem protectedMultiplicity_le_dense (η : ℝ) (U₀ U₁ Z : Finset V) (s : S)
    (L a : ℝ) (p : AssignmentSignature Z) :
    protectedMultiplicity D η U₀ U₁ Z s L a p ≤ denseMultiplicity D η U₀ U₁ Z s L p :=
  acceptedMultiplicity_le _ _ p

theorem protectedMultiplicity_eq_accepted (η : ℝ) (U₀ U₁ Z : Finset V) (s : S)
    (L a : ℝ) :
    protectedMultiplicity D η U₀ U₁ Z s L a =
      acceptedMultiplicity (fun p => densePoolKeep D U₀ U₁ Z L p ∧
        cutSafeKeep D η U₀ U₁ Z s a p) (multiplicity D η U₀ Z s) := by
  funext p
  unfold protectedMultiplicity denseMultiplicity acceptedMultiplicity
  split_ifs <;> simp_all

theorem protectedMultiplicity_cut_zero (η : ℝ) (U₀ U₁ Z : Finset V) (s : S)
    (L a : ℝ) (X : Finset V)
    (hX : X ∈ ForceMatching.wholeUnions (originalCores U₀ U₁) Z)
    (hsmall : smallEvenWholeCut D η U₀ U₁ Z s a X) (p : AssignmentSignature Z) :
    protectedMultiplicity D η U₀ U₁ Z s L a p * wholeCutDemand G D U₀ U₁ Z X p = 0 := by
  unfold protectedMultiplicity acceptedMultiplicity
  split_ifs with hp
  · rw [hp X hX hsmall, Nat.mul_zero]
  · exact Nat.zero_mul _

theorem protected_cut_discard_bound (η : ℝ) (hη₀ : 0 < η) (hη₁ : η ≤ 1)
    (hk : 0 < k) (U₀ U₁ Z : Finset V) (h01 : Disjoint U₀ U₁)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2)
    (s : S) (L a : ℝ) (ha : 0 ≤ a) :
    (∑ p, (denseMultiplicity D η U₀ U₁ Z s L p : ℝ)) ≤
      (∑ p, (protectedMultiplicity D η U₀ U₁ Z s L a p : ℝ)) + 32*a/η := by
  let Xs := ForceMatching.wholeUnions (originalCores U₀ U₁) Z
  let bad (X : ↥Xs) (p : AssignmentSignature Z) :=
    smallEvenWholeCut D η U₀ U₁ Z s a X.val ∧ 0 < wholeCutDemand G D U₀ U₁ Z X.val p
  letI (X : ↥Xs) (p : AssignmentSignature Z) : Decidable (bad X p) :=
    Classical.propDecidable _
  have hcoverBad (p : AssignmentSignature Z) (hp : ¬cutSafeKeep D η U₀ U₁ Z s a p) :
      ∃ X : ↥Xs, bad X p := by
    by_contra hn
    apply hp
    intro X hX hsmall
    have hnp : ¬0 < wholeCutDemand G D U₀ U₁ Z X p :=
      fun hpos => hn ⟨⟨X, hX⟩, hsmall, hpos⟩
    omega
  have hbase := discard_union_bound (denseMultiplicity D η U₀ U₁ Z s L)
    (cutSafeKeep D η U₀ U₁ Z s a) bad hcoverBad
  have htest (X : ↥Xs) :
      (∑ p, if bad X p then (denseMultiplicity D η U₀ U₁ Z s L p : ℝ) else 0) ≤
        2*a/η := by
    by_cases hsmall : smallEvenWholeCut D η U₀ U₁ Z s a X.val
    · simp only [bad, hsmall, true_and]
      apply le_trans _ (small_proposed_cut_discard_bound η a (G.cutSize X.val)
        (signatureWeight D U₀ Z) (wholeCutDemand G D U₀ U₁ Z X.val)
        (coarseSignature G (D.matching s) U₀ Z) (reserveSize D U₀ Z s)
        hη₀ hη₁ (signatureWeight_nonneg D U₀ Z) (reserveSize_le_weight D U₀ Z s)
        (wholeCutDemand_capacity G D hk U₀ U₁ Z X.val h01 h0Z h1Z hcover hZ X.property)
        hsmall.2)
      apply sum_le_sum
      intro p _
      split_ifs
      · exact_mod_cast denseMultiplicity_le D η U₀ U₁ Z s L p
      · exact le_rfl
    · simp only [bad, hsmall, false_and, if_false, sum_const_zero]
      positivity
  have htests : (∑ X : ↥Xs, ∑ p, if bad X p then
      (denseMultiplicity D η U₀ U₁ Z s L p : ℝ) else 0) ≤ 32*a/η := by
    calc
      _ ≤ ∑ _X : ↥Xs, 2*a/η := sum_le_sum (fun X _ => htest X)
      _ = (Xs.card : ℝ)*(2*a/η) := by simp
      _ ≤ 16*(2*a/η) := mul_le_mul_of_nonneg_right
        (by exact_mod_cast two_core_wholeUnions_card U₀ U₁ Z hZ) (by positivity)
      _ = _ := by ring
  exact hbase.trans (add_le_add_left htests _)

theorem protected_retainedDegree_bounds (η : ℝ) (hη₀ : 0 < η) (hη₁ : η ≤ 1)
    (hk : 0 < k) (U₀ U₁ Z : Finset V) (h01 : Disjoint U₀ U₁)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2)
    (s : S) (L a : ℝ) (hL : 0 ≤ L) (ha : 0 ≤ a) :
    let m := protectedMultiplicity D η U₀ U₁ Z s L a
    (k-∑ p, m p)+(∑ p, m p) = k ∧ reserveSize D U₀ Z s ≤ k-∑ p, m p ∧
      ((k-∑ p, m p : ℕ) : ℝ) ≤ reserveSize D U₀ Z s+η*k+5+6*L+32*a/η := by
  have hdense := dense_discard_bound D η hη₀.le hη₁ hk U₀ U₁ Z
    h01 h0Z h1Z hcover hZ s L hL
  have hcuts := protected_cut_discard_bound D η hη₀ hη₁ hk U₀ U₁ Z
    h01 h0Z h1Z hcover hZ s L a ha
  have hdiscard : (∑ p, (multiplicity D η U₀ Z s p : ℝ)) ≤
      (∑ p, (protectedMultiplicity D η U₀ U₁ Z s L a p : ℝ)) + (6*L+32*a/η) := by
    linarith
  rw [protectedMultiplicity_eq_accepted] at hdiscard ⊢
  have h := accepted_retainedDegree_bounds D η hη₀.le hη₁ U₀ Z hZ s
    (fun p => densePoolKeep D U₀ U₁ Z L p ∧ cutSafeKeep D η U₀ U₁ Z s a p)
    (6*L+32*a/η) hdiscard
  simpa only [add_assoc] using h

end Overfull.NativeReserve
