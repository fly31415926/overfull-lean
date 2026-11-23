import Overfull.NativeReserve.DenseSelection
import Overfull.NativeReserve.NativeCutWeights
import Overfull.CircuitPatterns.Multiplicity

/-!
# Signatures and uncovered parity of the realized native boundaries

Exact native-pool counts recover the actual assigned parts and preserve
whole-core cut counts. Positive accepted multiplicity supplies an original
sample, whose compressed boundary provides the required even remainders.
-/

noncomputable section

namespace Overfull.NativeReserve

open Finset Classical AssignedParts AssignedParts.NativeWeights CircuitPatterns
open scoped BigOperators

variable {V E : Type*} [Fintype E] (G : Multigraph V E)

theorem corePart_eq_of_exception_pool_counts (U Z : Finset V)
    (hUZ : Disjoint U Z) (F B : Finset E)
    (hcounts : ∀ z : ↥Z, (F ∩ exceptionCorePool G z.val U).card =
      (B ∩ exceptionCorePool G z.val U).card) :
    corePart G F Z U = corePart G B Z U := by
  ext v
  by_cases hv : v ∈ Z
  · have hF := exceptionCorePool_nonempty_iff_corePart G F U Z hUZ ⟨v,hv⟩
    have hB := exceptionCorePool_nonempty_iff_corePart G B U Z hUZ ⟨v,hv⟩
    rw [← hF, ← hB, ← card_pos, ← card_pos, hcounts]
  · simp [mem_corePart, hv]

theorem boundary_signature_eq_of_pool_counts (U₀ U₁ Z : Finset V)
    (h0Z : Disjoint U₀ Z) (F B : Finset E)
    (hcounts : ∀ p, (F ∩ poolCopies G U₀ U₁ Z p).card =
      (B ∩ poolCopies G U₀ U₁ Z p).card) :
    coarseSignature G F U₀ Z = coarseSignature G B U₀ Z := by
  have hpair : (G.internalOn F Z).Nonempty ↔ (G.internalOn B Z).Nonempty := by
    rw [← card_pos, ← card_pos, ← inter_internalPool_eq G F Z, ← inter_internalPool_eq G B Z]
    exact congrArg (fun n => 0 < n) (hcounts .pair) |> Eq.to_iff
  have hparts : corePart G F Z U₀ = corePart G B Z U₀ :=
    corePart_eq_of_exception_pool_counts G U₀ Z h0Z F B (fun z => by
      simpa only [poolCopies, if_pos rfl] using hcounts (.exception z 0))
  have hchoice : assignmentChoice G F U₀ Z = assignmentChoice G B U₀ Z := by
    funext z
    simp only [assignmentChoice, hparts]
  simp only [coarseSignature, hpair, hchoice]

theorem boundary_assignedLabel_eq_of_pool_counts (U₀ U₁ Z : Finset V)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z) (F B : Finset E)
    (hcounts : ∀ p, (F ∩ poolCopies G U₀ U₁ Z p).card =
      (B ∩ poolCopies G U₀ U₁ Z p).card) :
    assignedLabel G F U₀ U₁ Z = assignedLabel G B U₀ U₁ Z := by
  have hparts₀ : corePart G F Z U₀ = corePart G B Z U₀ :=
    corePart_eq_of_exception_pool_counts G U₀ Z h0Z F B (fun z => by
      simpa only [poolCopies, if_pos rfl] using hcounts (.exception z 0))
  have hparts₁ : corePart G F Z U₁ = corePart G B Z U₁ :=
    corePart_eq_of_exception_pool_counts G U₁ Z h1Z F B (fun z => by
      simpa [poolCopies] using hcounts (.exception z 1))
  simp only [assignedLabel, hparts₀, hparts₁]

theorem boundary_whole_cut_eq_of_pool_counts (U₀ U₁ Z X : Finset V)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hZ : Z.card ≤ 2) (hwhole₀ : U₀ ⊆ X ∨ Disjoint U₀ X)
    (hwhole₁ : U₁ ⊆ X ∨ Disjoint U₁ X) (F B : Finset E)
    (hFpool : ∀ e ∈ F, ∃ p, e ∈ poolCopies G U₀ U₁ Z p)
    (hBpool : ∀ e ∈ B, ∃ p, e ∈ poolCopies G U₀ U₁ Z p)
    (hcounts : ∀ p, (F ∩ poolCopies G U₀ U₁ Z p).card =
      (B ∩ poolCopies G U₀ U₁ Z p).card) :
    (G.cutOn F X).card = (G.cutOn B X).card := by
  rw [native_cut_count_eq_sum_pools G U₀ U₁ Z X h01 h0Z h1Z hZ hwhole₀ hwhole₁ F hFpool,
    native_cut_count_eq_sum_pools G U₀ U₁ Z X h01 h0Z h1Z hZ hwhole₀ hwhole₁ B hBpool]
  simp_rw [hcounts]

theorem realized_sample_boundary_properties (U₀ U₁ Z : Finset V)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2)
    (M F : Finset E) (hM : G.IsPerfectMatching M) (hF : G.IsMatching F)
    (hpool : ∀ e ∈ F, ∃ p, e ∈ poolCopies G U₀ U₁ Z p)
    (hcounts : ∀ p, (F ∩ poolCopies G U₀ U₁ Z p).card =
      (compressedBoundary G M U₀ U₁ Z ∩ poolCopies G U₀ U₁ Z p).card) :
    coarseSignature G F U₀ Z = coarseSignature G M U₀ Z ∧
      assignedLabel G F U₀ U₁ Z = assignedLabel G M U₀ U₁ Z ∧
      Even (U₀ \ G.edgeSupport F).card ∧ Even (U₁ \ G.edgeSupport F).card := by
  let B := compressedBoundary G M U₀ U₁ Z
  have hBpool : ∀ e ∈ B, ∃ p, e ∈ poolCopies G U₀ U₁ Z p :=
    fun _ he => compressedBoundary_exists_pool G M U₀ U₁ Z hcover he
  have hB := compressedBoundary_isMatching G (hM.isMatching G) U₀ U₁ Z
  have heven := compressedBoundary_uncovered_even G hM U₀ U₁ Z h01 h0Z h1Z hcover
  refine ⟨(boundary_signature_eq_of_pool_counts G U₀ U₁ Z h0Z F B hcounts).trans
    (compressedBoundary_coarseSignature G M U₀ U₁ Z),
    (boundary_assignedLabel_eq_of_pool_counts G U₀ U₁ Z h0Z h1Z F B hcounts).trans
      (compressedBoundary_assignedLabel G M U₀ U₁ Z), ?_, ?_⟩
  · apply (hF.uncovered_even_iff_cut_parity G U₀).mpr
    rw [boundary_whole_cut_eq_of_pool_counts G U₀ U₁ Z U₀ h01 h0Z h1Z hZ
      (Or.inl (subset_refl _)) (Or.inr h01.symm) F B hpool hBpool hcounts]
    exact (hB.uncovered_even_iff_cut_parity G U₀).mp heven.1
  · apply (hF.uncovered_even_iff_cut_parity G U₁).mpr
    rw [boundary_whole_cut_eq_of_pool_counts G U₀ U₁ Z U₁ h01 h0Z h1Z hZ
      (Or.inr h01) (Or.inl (subset_refl _)) F B hpool hBpool hcounts]
    exact (hB.uncovered_even_iff_cut_parity G U₁).mp heven.2

variable {S : Type*} [Fintype S] {k : ℕ}
  (D : MultigraphMatchingProbability.Distribution G k S)

theorem accepted_family_boundary_properties (U₀ U₁ Z : Finset V)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2)
    (η L : ℝ) (hη₀ : 0 ≤ η) (hη₁ : η ≤ 1) (s : S)
    (m : AssignmentSignature Z → ℕ)
    (hm : ∀ p, m p ≤ denseMultiplicity D η U₀ U₁ Z s L p)
    (F : PatternCopies m → Finset E) (hF : ∀ r, G.IsMatching (F r))
    (hpool : ∀ r, ∀ e ∈ F r, ∃ p, e ∈ poolCopies G U₀ U₁ Z p)
    (huse : ∀ r p, (F r ∩ poolCopies G U₀ U₁ Z p).card =
      poolDemand D U₀ U₁ Z p r.1) :
    ∀ r, coarseSignature G (F r) U₀ Z = r.1 ∧
      Even (U₀ \ G.edgeSupport (F r)).card ∧ Even (U₁ \ G.edgeSupport (F r)).card := by
  intro r
  have hmpos : 0 < multiplicity D η U₀ Z s r.1 :=
    (Nat.zero_lt_of_lt r.2.isLt).trans_le
      ((hm r.1).trans (denseMultiplicity_le D η U₀ U₁ Z s L r.1))
  obtain ⟨t, ht, _⟩ := multiplicity_pos_witness D η hη₀ hη₁ U₀ Z s r.1 hmpos
  have hcounts (p : PoolKind Z) : (F r ∩ poolCopies G U₀ U₁ Z p).card =
      (compressedBoundary G (D.matching t) U₀ U₁ Z ∩ poolCopies G U₀ U₁ Z p).card := by
    rw [huse, compressedBoundary_pool_usage_at_sample D U₀ U₁ Z h01 h0Z h1Z hcover hZ t p, ht]
  have h := realized_sample_boundary_properties G U₀ U₁ Z h01 h0Z h1Z hcover hZ
    (D.matching t) (F r) (D.perfect t) (hF r) (hpool r) hcounts
  exact ⟨h.1.trans ht, h.2.2⟩

end Overfull.NativeReserve
