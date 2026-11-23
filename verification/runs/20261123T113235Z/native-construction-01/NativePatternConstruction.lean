import Overfull.AssignedParts.ExactPoolWeights
import Overfull.AssignedParts.CompressionCuts

/-!
# A native heavy assignment and its compressed original-copy boundary

The same actual matching supplies the assignment, its pool capacities, and
the small retained boundary. Compression preserves its exceptional pair and
core assignment, and the retained crossing statistic is exactly the parity
of the original matching's core-crossing count.

This is a finite stage toward Corollary 4.6. It neither chooses simultaneous
disjoint reserves nor proves safety of a residual after their deletion.
-/

noncomputable section

namespace Overfull.AssignedParts

open Finset Classical

variable {V E : Type*} (G : Multigraph V E)

/-- Compressing the boundary does not change the supplied matching's code. -/
theorem compressedBoundary_coarseSignature (M : Finset E) (U₀ U₁ Z : Finset V) :
    coarseSignature G (compressedBoundary G M U₀ U₁ Z) U₀ Z =
      coarseSignature G M U₀ Z := by
  simp only [coarseSignature, assignmentChoice, compressedBoundary_internalOn,
    compressedBoundary_corePart]

/-- The number of retained old-core crossing copies is the exact original
crossing parity, so it is zero or one. -/
theorem compressedBoundary_coreCrossing_card {M : Finset E}
    (U₀ U₁ Z : Finset V) (h01 : Disjoint U₀ U₁)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z) :
    (G.cutOn (compressedBoundary G M U₀ U₁ Z) U₀ ∩
      G.cutOn (compressedBoundary G M U₀ U₁ Z) U₁).card =
      (G.cutOn M U₀ ∩ G.cutOn M U₁).card % 2 := by
  rw [compressedBoundary_core_crossings G M U₀ U₁ Z h01 h0Z h1Z,
    paritySelection_card]

/-- Equal native signatures fix the retained crossing statistic, as well as
the actual assigned parts. The uncompressed counts may differ. -/
theorem compressedBoundary_crossing_card_eq_of_signature_eq {M N : Finset E}
    (hM : G.IsPerfectMatching M) (hN : G.IsPerfectMatching N)
    (U₀ U₁ Z : Finset V) (h01 : Disjoint U₀ U₁)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2)
    (hcode : coarseSignature G M U₀ Z = coarseSignature G N U₀ Z) :
    (G.cutOn (compressedBoundary G M U₀ U₁ Z) U₀ ∩
      G.cutOn (compressedBoundary G M U₀ U₁ Z) U₁).card =
      (G.cutOn (compressedBoundary G N U₀ U₁ Z) U₀ ∩
        G.cutOn (compressedBoundary G N U₀ U₁ Z) U₁).card := by
  rw [compressedBoundary_coreCrossing_card G U₀ U₁ Z h01 h0Z h1Z,
    compressedBoundary_coreCrossing_card G U₀ U₁ Z h01 h0Z h1Z]
  exact coreCrossing_parity_eq_of_signature_eq G hM hN
    U₀ U₁ Z h01 h0Z h1Z hcover hZ hcode

variable [Fintype V] [Fintype E]

/-- Construct one actual matching and its compressed boundary directly from
the regular non-overfull host. Every supplied pool refers to that matching's
own assignment; the internal exceptional pair is retained. -/
theorem exists_compressed_assignment_with_linear_pools {k : ℕ}
    (hk : 0 < k) (hregular : ∀ v, G.degree v = k)
    (hno : ∀ X : Finset V, ¬ G.IsOverfull k X)
    (U₀ U₁ Z : Finset V) (h01 : Disjoint U₀ U₁)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2) :
    ∃ M F : Finset E, G.IsPerfectMatching M ∧
      F = compressedBoundary G M U₀ U₁ Z ∧ F ⊆ M ∧ G.IsMatching F ∧
      F.card ≤ Z.card + 1 ∧ exceptionalCopies G M Z ⊆ F ∧
      G.internalOn F Z = G.internalOn M Z ∧
      assignedLabel G F U₀ U₁ Z = assignedLabel G M U₀ U₁ Z ∧
      coarseSignature G F U₀ Z = coarseSignature G M U₀ Z ∧
      Even (U₀ \ G.edgeSupport F).card ∧ Even (U₁ \ G.edgeSupport F).card ∧
      (G.cutOn F U₀ ∩ G.cutOn F U₁).card =
        (G.cutOn M U₀ ∩ G.cutOn M U₁).card % 2 ∧
      (coarseSignature G M U₀ Z = none →
        (k : ℝ) / 5 ≤ (G.internalOn univ Z).card) ∧
      (∀ σ, coarseSignature G M U₀ Z = some σ → ∀ z : ↥Z,
        (k : ℝ) / 5 ≤ (exceptionCorePool G z.val (if σ z = 0 then U₀ else U₁)).card) ∧
      ((G.cutOn F U₀ ∩ G.cutOn F U₁).card = 1 →
        (k : ℝ) / 5 ≤ (coreCrossingPool G U₀ U₁).card) := by
  obtain ⟨M, hM, hpair, hex, hcross⟩ := exists_assignment_matching_with_linear_pools
    G hk hregular hno U₀ U₁ Z h01 h0Z h1Z hcover hZ
  have heven := compressedBoundary_uncovered_even G hM U₀ U₁ Z h01 h0Z h1Z hcover
  have hcount := compressedBoundary_coreCrossing_card G (M := M) U₀ U₁ Z h01 h0Z h1Z
  refine ⟨M, compressedBoundary G M U₀ U₁ Z, hM, rfl,
    compressedBoundary_subset G M U₀ U₁ Z,
    compressedBoundary_isMatching G (hM.isMatching G) U₀ U₁ Z,
    compressedBoundary_card_le G (hM.isMatching G) U₀ U₁ Z,
    compressedBoundary_retains_exceptional G M U₀ U₁ Z,
    compressedBoundary_internalOn G M U₀ U₁ Z,
    compressedBoundary_assignedLabel G M U₀ U₁ Z,
    compressedBoundary_coarseSignature G M U₀ U₁ Z,
    heven.1, heven.2, hcount, hpair, hex, ?_⟩
  intro hodd
  exact hcross (hcount.symm.trans hodd)

end Overfull.AssignedParts
