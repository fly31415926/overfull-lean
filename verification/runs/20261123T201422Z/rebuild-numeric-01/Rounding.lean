import Overfull.AssignedParts.HeavySignature

/-!
# Native signature rounding with a one-third reserve

The weights refer to original edge copies and to one fixed matching
distribution. The distinguished signature is realized by an actual sample.
-/

noncomputable section

namespace Overfull.NativeReserve

open Finset Classical AssignedParts AssignedParts.NativeWeights CircuitPatterns
open scoped BigOperators

variable {V E S : Type*} [Fintype S] {G : Multigraph V E} {k : ℕ}
  (D : MultigraphMatchingProbability.Distribution G k S)

def reserveSize (U₀ Z : Finset V) (s : S) : ℕ :=
  ⌊signatureWeight D U₀ Z (coarseSignature G (D.matching s) U₀ Z) / 3⌋₊

def multiplicity (η : ℝ) (U₀ Z : Finset V) (s : S) (p : AssignmentSignature Z) : ℕ :=
  proposedMultiplicity η (signatureWeight D U₀ Z)
    (coarseSignature G (D.matching s) U₀ Z) (reserveSize D U₀ Z s) p

def retainedDegree (η : ℝ) (U₀ Z : Finset V) (s : S) : ℕ :=
  k - ∑ p, multiplicity D η U₀ Z s p

theorem reserveSize_le_third (U₀ Z : Finset V) (s : S) :
    (reserveSize D U₀ Z s : ℝ) ≤
      signatureWeight D U₀ Z (coarseSignature G (D.matching s) U₀ Z) / 3 := by
  exact Nat.floor_le (div_nonneg (signatureWeight_nonneg D U₀ Z _) (by norm_num))

theorem three_mul_reserveSize_le_weight (U₀ Z : Finset V) (s : S) :
    3 * (reserveSize D U₀ Z s : ℝ) ≤
      signatureWeight D U₀ Z (coarseSignature G (D.matching s) U₀ Z) := by
  have h := reserveSize_le_third D U₀ Z s
  linarith

theorem reserveSize_le_weight (U₀ Z : Finset V) (s : S) :
    (reserveSize D U₀ Z s : ℝ) ≤
      signatureWeight D U₀ Z (coarseSignature G (D.matching s) U₀ Z) := by
  have h := three_mul_reserveSize_le_weight D U₀ Z s
  have hn : (0 : ℝ) ≤ reserveSize D U₀ Z s := Nat.cast_nonneg _
  linarith

theorem multiplicity_le_scaled (η : ℝ) (hη₁ : η ≤ 1) (U₀ Z : Finset V)
    (s : S) (p : AssignmentSignature Z) :
    (multiplicity D η U₀ Z s p : ℝ) ≤ (1-η) *
      remainingWeight (signatureWeight D U₀ Z)
        (coarseSignature G (D.matching s) U₀ Z) (reserveSize D U₀ Z s) p :=
  proposedMultiplicity_le_scaled η _ _ _ hη₁ (signatureWeight_nonneg D U₀ Z)
    (reserveSize_le_weight D U₀ Z s) p

theorem multiplicity_le_weight (η : ℝ) (hη₀ : 0 ≤ η) (hη₁ : η ≤ 1)
    (U₀ Z : Finset V) (s : S) (p : AssignmentSignature Z) :
    (multiplicity D η U₀ Z s p : ℝ) ≤ signatureWeight D U₀ Z p :=
  proposedMultiplicity_le_weight η _ _ _ hη₀ hη₁
    (signatureWeight_nonneg D U₀ Z) (reserveSize_le_weight D U₀ Z s) p

theorem multiplicity_pos_witness (η : ℝ) (hη₀ : 0 ≤ η) (hη₁ : η ≤ 1)
    (U₀ Z : Finset V) (s : S) (p : AssignmentSignature Z)
    (hp : 0 < multiplicity D η U₀ Z s p) :
    ∃ t, coarseSignature G (D.matching t) U₀ Z = p ∧ 0 < scaledWeight D t := by
  have hpR : (0 : ℝ) < multiplicity D η U₀ Z s p := by exact_mod_cast hp
  exact aggregateWeight_pos_witness _ _ p
    (hpR.trans_le (multiplicity_le_weight D η hη₀ hη₁ U₀ Z s p))

theorem prefix_signature_reserve (η : ℝ) (hη₀ : 0 ≤ η) (hη₁ : η ≤ 1)
    (U₀ Z : Finset V) (s : S) (m : AssignmentSignature Z → ℕ)
    (hm : ∀ p, m p ≤ multiplicity D η U₀ Z s p) :
    (reserveSize D U₀ Z s : ℝ) ≤
      signatureWeight D U₀ Z (coarseSignature G (D.matching s) U₀ Z) -
        m (coarseSignature G (D.matching s) U₀ Z) := by
  let p₀ := coarseSignature G (D.matching s) U₀ Z
  have hmR : (m p₀ : ℝ) ≤ multiplicity D η U₀ Z s p₀ := by exact_mod_cast hm p₀
  have h := proposedMultiplicity_le_remaining η (signatureWeight D U₀ Z) p₀
    (reserveSize D U₀ Z s) hη₀ hη₁ (signatureWeight_nonneg D U₀ Z)
    (reserveSize_le_weight D U₀ Z s) p₀
  simp only [remainingWeight, if_pos rfl] at h
  change _ ≤ signatureWeight D U₀ Z p₀ - m p₀
  change (multiplicity D η U₀ Z s p₀ : ℝ) ≤ _ at h
  linarith

theorem accepted_retainedDegree_bounds (η : ℝ) (hη₀ : 0 ≤ η) (hη₁ : η ≤ 1)
    (U₀ Z : Finset V) (hZ : Z.card ≤ 2) (s : S)
    (keep : AssignmentSignature Z → Prop) (loss : ℝ)
    (hdiscard : (∑ p, (multiplicity D η U₀ Z s p : ℝ)) ≤
      (∑ p, (acceptedMultiplicity keep (multiplicity D η U₀ Z s) p : ℝ)) + loss) :
    let m := acceptedMultiplicity keep (multiplicity D η U₀ Z s)
    (k-∑ p, m p)+(∑ p, m p) = k ∧ reserveSize D U₀ Z s ≤ k-∑ p, m p ∧
      ((k-∑ p, m p : ℕ) : ℝ) ≤ reserveSize D U₀ Z s+η*k+5+loss := by
  have h := accepted_natural_residual_bounds η (signatureWeight D U₀ Z)
    (coarseSignature G (D.matching s) U₀ Z) (reserveSize D U₀ Z s) k loss keep
    hη₀ hη₁ (signatureWeight_nonneg D U₀ Z) (reserveSize_le_weight D U₀ Z s)
    (signatureWeight_sum D U₀ Z) hdiscard
  have hcard : (Fintype.card (AssignmentSignature Z) : ℝ) ≤ 5 := by
    exact_mod_cast card_assignmentSignature_le_five Z hZ
  refine ⟨h.1, h.2.1, ?_⟩
  exact h.2.2.trans (by gcongr)

theorem retainedDegree_bounds (η : ℝ) (hη₀ : 0 ≤ η) (hη₁ : η ≤ 1)
    (U₀ Z : Finset V) (hZ : Z.card ≤ 2) (s : S) :
    retainedDegree D η U₀ Z s + (∑ p, multiplicity D η U₀ Z s p) = k ∧
      reserveSize D U₀ Z s ≤ retainedDegree D η U₀ Z s ∧
      (retainedDegree D η U₀ Z s : ℝ) ≤ reserveSize D U₀ Z s+η*k+5 := by
  have h := accepted_retainedDegree_bounds D η hη₀ hη₁ U₀ Z hZ s (fun _ => True) 0
    (by simp [acceptedMultiplicity])
  simpa [acceptedMultiplicity, retainedDegree] using h

theorem exists_rounded_signature_choice (η : ℝ) (hη₀ : 0 ≤ η) (hη₁ : η ≤ 1)
    (hk : 30 ≤ k) (U₀ Z : Finset V) (hZ : Z.card ≤ 2) :
    ∃ s, 0 < scaledWeight D s ∧
      (k : ℝ)/5 ≤ signatureWeight D U₀ Z (coarseSignature G (D.matching s) U₀ Z) ∧
      (k : ℝ)/30 ≤ reserveSize D U₀ Z s ∧
      3*(reserveSize D U₀ Z s : ℝ) ≤
        signatureWeight D U₀ Z (coarseSignature G (D.matching s) U₀ Z) ∧
      (retainedDegree D η U₀ Z s + (∑ p, multiplicity D η U₀ Z s p) = k ∧
        reserveSize D U₀ Z s ≤ retainedDegree D η U₀ Z s ∧
        (retainedDegree D η U₀ Z s : ℝ) ≤ reserveSize D U₀ Z s+η*k+5) := by
  obtain ⟨s, hs, hw⟩ := exists_heavy_signature D (by omega) U₀ Z hZ
  have hkR : (30 : ℝ) ≤ k := by exact_mod_cast hk
  have hf := Nat.lt_floor_add_one
    (signatureWeight D U₀ Z (coarseSignature G (D.matching s) U₀ Z)/3)
  have hr : (k : ℝ)/30 ≤ reserveSize D U₀ Z s := by
    change (k : ℝ)/30 ≤ (⌊signatureWeight D U₀ Z
      (coarseSignature G (D.matching s) U₀ Z)/3⌋₊ : ℝ)
    linarith
  exact ⟨s, hs, hw, hr, three_mul_reserveSize_le_weight D U₀ Z s,
    retainedDegree_bounds D η hη₀ hη₁ U₀ Z hZ s⟩

end Overfull.NativeReserve
