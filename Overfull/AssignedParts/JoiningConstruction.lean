import Overfull.AssignedParts.MatchedCuts
import Overfull.CompatibleCircuits.TwoOddDecomposition

/-! Joining decompositions for the actual matched-core assignment.
The supplied perfect-matching representative is retained. Reserves, residual
safety, palettes, robust completion and full factorization remain separate. -/
noncomputable section
namespace Overfull.AssignedParts
open Finset Classical
variable {V E : Type*} [Fintype V] [Fintype E] (G : Multigraph V E)

/-- The actual representative supplies the assignment and fiber parity for the
complete joining stage. No quotient admissibility hypothesis is assumed. -/
theorem assignedLabel_joining_decomposition {M : Finset E}
    (hM : G.IsPerfectMatching M) (U₀ U₁ Z : Finset V)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) {h : ℕ}
    (hregular : ∀ v, G.degree v = h)
    (hno : ∀ X : Finset V, ¬ G.IsOverfull h X) :
    ((∀ i, (univ.filter (fun v => assignedLabel G M U₀ U₁ Z v = i)).card % 2 = 0) ∧
      ∃ parts : Finset (Finset E),
        (∀ N ∈ parts, N.Nonempty ∧ G.IsMatching N ∧ N.card ≤ 3) ∧
        (∀ N ∈ parts, ∀ N' ∈ parts, N ≠ N' → Disjoint N N') ∧
        parts.biUnion id = FourOdd.joiningCopies G (assignedLabel G M U₀ U₁ Z)) ∨
    ((∀ i, (univ.filter (fun v => assignedLabel G M U₀ U₁ Z v = i)).card % 2 =
        if i = 0 ∨ i = 1 then 1 else 0) ∧
      Nonempty (FourOdd.TwoOddJoiningDecomposition G (assignedLabel G M U₀ U₁ Z) 0 1 h)) := by
  rcases assignedLabel_parity G hM U₀ U₁ Z h01 h0Z h1Z hcover with heven | hodd
  · exact Or.inl ⟨heven,
      FourOdd.exists_joining_matching_partition_of_even_fibers G
        (assignedLabel G M U₀ U₁ Z) (by decide) hregular hno heven⟩
  · exact Or.inr ⟨hodd,
      FourOdd.exists_twoOddJoining_decomposition G
        (assignedLabel G M U₀ U₁ Z) 0 1 (by decide) h
        (by decide) hregular hno hodd⟩
end Overfull.AssignedParts
