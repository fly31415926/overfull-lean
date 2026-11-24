import Overfull.NativeReserve.BoundaryProperties
import Overfull.NativeReserve.ProtectedSelection
import Overfull.NativeReserve.AcceptedRealization

/-!
# Selecting native boundaries with an actual protected reserve

This theorem performs the complete finite selection in the original host.
Its residual cut certificates concern deletion of the selected boundaries;
regularity is established only after their later perfect completions.
-/

noncomputable section

namespace Overfull.NativeReserve

open Finset Classical AssignedParts AssignedParts.NativeWeights CircuitPatterns ForceMatching
open scoped BigOperators

theorem patternCopies_familyMultiplicity {P : Type*} [Fintype P]
    (m : P → ℕ) (p : P) :
    familyMultiplicity (fun r : PatternCopies m => r.1) univ p = m p := by
  unfold familyMultiplicity
  rw [card_eq_sum_ones, sum_filter, Fintype.sum_sigma]
  rw [sum_eq_single p]
  · simp
  · intro b _ hbp
    simp [hbp]
  · simp

variable {V E : Type*} [Fintype V] [Fintype E]

/-- The original host supplies the reserve, accepted actual boundaries,
their parity, and the whole-cut certificates needed after core completion. -/
theorem native_boundary_reserve_selection (G : Multigraph V E) (k : ℕ)
    (hk : 30 ≤ k) (hregular : ∀ v, G.degree v = k)
    (hno : ∀ X : Finset V, ¬ G.IsOverfull k X)
    (U₀ U₁ Z : Finset V) (C₀ : SmallCuts.Core G U₀) (C₁ : SmallCuts.Core G U₁)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2)
    (a η : ℝ) (ha : 0 < a) (hη₀ : 0 < η) (hη₁ : η ≤ 1)
    (hdegree₀ : ∀ v, (k : ℝ)-a ≤ (C₀.graph.degree v : ℝ))
    (hdegree₁ : ∀ v, (k : ℝ)-a ≤ (C₁.graph.degree v : ℝ)) :
    ∃ (r h : ℕ) (M : Finset E) (Q : BoundaryPacking G U₀ U₁ Z M r)
      (m : AssignmentSignature Z → ℕ) (F : PatternCopies m → Finset E),
      G.IsPerfectMatching M ∧ (k : ℝ)/30 ≤ r ∧ h+(∑ p, m p)=k ∧ r≤h ∧
      (h : ℝ) ≤ r+η*k+5+104*a/η ∧
      (∀ i, G.IsMatching (F i)) ∧
      (∀ i j, i ≠ j → Disjoint (F i) (F j)) ∧
      (∀ i, Disjoint (F i) (removedCopies Q.boundary univ)) ∧
      (∀ i, Z ⊆ G.edgeSupport (F i)) ∧
      (∀ i, ∀ e ∈ F i, ∃ p : PoolKind Z, e ∈ poolCopies G U₀ U₁ Z p) ∧
      (∀ i, (F i).card ≤ 3) ∧
      (∀ i, coarseSignature G (F i) U₀ Z = i.1 ∧
        Even (U₀ \ G.edgeSupport (F i)).card ∧
        Even (U₁ \ G.edgeSupport (F i)).card) ∧
      (∀ X ∈ wholeUnions (originalCores U₀ U₁) Z, X.card%2=1 →
        h ≤ (residualGraph G F univ).cutSize X) ∧
      (∀ X ∈ wholeUnions (originalCores U₀ U₁) Z, X.card%2=0 →
        2*a ≤ ((residualGraph G F univ).cutSize X : ℝ) ∨
          G.cutEdges X \ removedCopies F univ = G.cutEdges X) := by
  have hkpos : 0 < k := by omega
  obtain ⟨S, hS, ⟨D⟩⟩ := MultigraphMatchingProbability.exists_distribution
    (G := G) hkpos hregular hno
  letI := hS
  obtain ⟨s, _hs, _hw, hr, _hthree, _hrounded⟩ :=
    exists_rounded_signature_choice D η hη₀.le hη₁ hk U₀ Z hZ
  obtain ⟨Q⟩ := exists_rounded_boundary_reserve D hkpos U₀ U₁ Z hZ s
  let L : ℝ := 12*a/η
  let m := protectedMultiplicity D η U₀ U₁ Z s L a
  have hm (p : AssignmentSignature Z) : m p ≤ denseMultiplicity D η U₀ U₁ Z s L p :=
    protectedMultiplicity_le_dense D η U₀ U₁ Z s L a p
  have hbudget : 12*a ≤ η*L := by
    dsimp [L]
    field_simp
    nlinarith
  obtain ⟨F, hF, hdisj, havoid, hcov, hpool, hsize, huse⟩ :=
    exists_accepted_family_avoiding_reserve D U₀ U₁ Z C₀ C₁ h01 h0Z h1Z hcover hZ
      hkpos a η L ha hη₀.le hη₁ hbudget hregular hdegree₀ hdegree₁ s Q m hm
  have hbounds := protected_retainedDegree_bounds D η hη₀ hη₁ hkpos U₀ U₁ Z
    h01 h0Z h1Z hcover hZ s L a (by dsimp [L]; positivity) ha.le
  change (k-∑ p, m p)+(∑ p, m p)=k ∧ reserveSize D U₀ Z s≤k-∑ p, m p ∧
    ((k-∑ p, m p : ℕ) : ℝ) ≤ reserveSize D U₀ Z s+η*k+5+6*L+32*a/η at hbounds
  have hupper : ((k-∑ p, m p : ℕ) : ℝ) ≤ reserveSize D U₀ Z s+η*k+5+104*a/η := by
    have heq : (reserveSize D U₀ Z s : ℝ)+η*k+5+6*L+32*a/η =
        reserveSize D U₀ Z s+η*k+5+104*a/η := by dsimp [L]; ring
    exact hbounds.2.2.trans_eq heq
  have hprops := accepted_family_boundary_properties G D U₀ U₁ Z
    h01 h0Z h1Z hcover hZ η L hη₀.le hη₁ s m hm F hF hpool huse
  have hdisjSet : ((univ : Finset (PatternCopies m)) : Set (PatternCopies m)).Pairwise
      (fun i j => Disjoint (F i) (F j)) := fun i _ j _ hij => hdisj i j hij
  have hcount (X : Finset V) (hX : X ∈ wholeUnions (originalCores U₀ U₁) Z)
      (i : PatternCopies m) (_hi : i ∈ (univ : Finset (PatternCopies m))) :
      (G.cutOn (F i) X).card = wholeCutDemand G D U₀ U₁ Z X i.1 :=
    native_cut_count_eq_demand G D U₀ U₁ Z X h01 h0Z h1Z hZ hX
      (F i) i.1 (hpool i) (huse i)
  have hT : (univ : Finset (PatternCopies m)).card ≤ k := by
    simp only [card_univ, card_patternCopies]
    omega
  have hweight (p : AssignmentSignature Z) :
      (familyMultiplicity (fun i : PatternCopies m => i.1) univ p : ℝ) ≤
        signatureWeight D U₀ Z p := by
    rw [patternCopies_familyMultiplicity]
    exact (show (m p : ℝ) ≤ multiplicity D η U₀ Z s p from
      by exact_mod_cast (hm p).trans (denseMultiplicity_le D η U₀ U₁ Z s L p)).trans
        (multiplicity_le_weight D η hη₀.le hη₁ U₀ Z s p)
  refine ⟨reserveSize D U₀ Z s, k-∑ p, m p, D.matching s, Q, m, F,
    D.perfect s, hr, hbounds.1, hbounds.2.1, hupper, hF, hdisj, havoid,
    hcov, hpool, hsize, hprops, ?_, ?_⟩
  · intro X hX hodd
    have h := residual_weighted_odd_cut G F univ hdisjSet (fun i => i.1) k hT
      (signatureWeight D U₀ Z) (signatureWeight_sum D U₀ Z) hweight X
      (wholeCutDemand G D U₀ U₁ Z X) (hcount X hX)
      (wholeCutDemand_odd_positive G D U₀ U₁ Z X h01 h0Z h1Z hcover hZ hX hodd)
      (wholeCutDemand_capacity G D hkpos U₀ U₁ Z X h01 h0Z h1Z hcover hZ hX)
    simpa only [card_univ, card_patternCopies] using h
  · intro X hX heven
    apply residual_proposed_cut_dichotomy G F univ hdisjSet (fun i => i.1)
      (multiplicity D η U₀ Z s) m
      (fun p => (patternCopies_familyMultiplicity m p).le)
      (fun p => (hm p).trans (denseMultiplicity_le D η U₀ U₁ Z s L p))
      X (wholeCutDemand G D U₀ U₁ Z X) a (hcount X hX)
    intro hsmall p
    exact protectedMultiplicity_cut_zero D η U₀ U₁ Z s L a X hX ⟨heven, hsmall⟩ p

end Overfull.NativeReserve
