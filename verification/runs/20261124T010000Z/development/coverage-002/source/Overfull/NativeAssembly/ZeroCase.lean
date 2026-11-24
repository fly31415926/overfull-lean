import Overfull.NativeAssembly.BaseClasses
import Overfull.NativeCore.Incidence

/-!
# Native external classes when there are no exceptional vertices

Every reserve copy is then already a joining copy. The actual protected
reserve extension is a complete external matching palette, with the exact
joining union and all original cut certificates.
-/

noncomputable section

namespace Overfull.NativeAssembly

open Finset Classical AssignedParts FourOdd NativeReserve NativeCore

variable {V E J I : Type*} [Fintype V] [Fintype E] [Fintype I]

/-- With no exceptions, the whole native reserve boundary consists only
of actual joining copies for the original representative's assignment. -/
theorem zero_exception_boundary_subset_joining
    (G : Multigraph V E) {M : Finset E} (hM : G.IsPerfectMatching M)
    (U₀ U₁ Z : Finset V) (h01 : Disjoint U₀ U₁)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z) (hZ : Z = ∅)
    (r : ℕ) (R : BoundaryPacking G U₀ U₁ Z M r)
    (N : J → Finset E) (T : Finset J) (i : Fin r) :
    R.residualBoundary N T i ⊆
      joiningCopies (residualGraph G N T) (assignedLabel G M U₀ U₁ Z) := by
  intro e he
  have hs := residualBoundary_subset_joining_exceptional G U₀ U₁ Z hM
    h01 h0Z h1Z r R N T i he
  rcases mem_union.mp hs with hj | hz
  · exact hj
  · obtain ⟨_,hz | hz⟩ := (mem_exceptionalCopies _ univ Z e).mp hz
    · exact (notMem_empty _ (hZ ▸ hz)).elim
    · exact (notMem_empty _ (hZ ▸ hz)).elim

/-- No star insertion is needed when the exceptional set is empty: the
constructed reserve extension already gives the exact external palette. -/
theorem native_zero_exception_extension
    (G : Multigraph V E) {M : Finset E} (hM : G.IsPerfectMatching M)
    (U₀ U₁ Z : Finset V) (h01 : Disjoint U₀ U₁)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z) (hZ : Z = ∅)
    (r : ℕ) (R : BoundaryPacking G U₀ U₁ Z M r)
    (N : J → Finset E) (T : Finset J)
    {h D L : ℕ} {p : Fin 3 → ℕ}
    (C : JoiningPalette (residualGraph G N T) (assignedLabel G M U₀ U₁ Z) h D L p)
    (q : I → Fin r) (f : I → Fin h)
    (P : ReserveExtension C (fun i => R.residualBoundary N T (q i)) f (Z.card+1)) :
    (∀ j, (residualGraph G N T).IsMatching (P.classes j)) ∧
      Pairwise (fun i j => Disjoint (P.classes i) (P.classes j)) ∧
      univ.biUnion P.classes =
        joiningCopies (residualGraph G N T) (assignedLabel G M U₀ U₁ Z) ∧
      (∀ i, P.classes (f i) = R.residualBoundary N T (q i)) ∧
      (∀ j, Z ⊆ (residualGraph G N T).edgeSupport (P.classes j)) ∧
      (∀ j i, (residualGraph G N T).cutOn (P.classes j)
          (labelShore (assignedLabel G M U₀ U₁ Z) {i}) =
        (residualGraph G N T).cutOn (C.classes j)
          (labelShore (assignedLabel G M U₀ U₁ Z) {i})) ∧
      (∀ j, (P.classes j).card ≤ max (3*L) (Z.card+1)) ∧
      (∀ j, ((residualGraph G N T).edgeSupport (P.classes j)).card ≤
        2*max (3*L) (Z.card+1)) := by
  refine ⟨P.matching,P.disjoint,?_,P.prescribed,?_,fun j i => P.cut_eq j {i},
    P.card_le,P.support_card_le⟩
  · ext e
    have hpE : (∃ j, e ∈ P.classes j) ↔
        e ∈ joiningCopies (residualGraph G N T) (assignedLabel G M U₀ U₁ Z) ∨
        ∃ i, e ∈ R.residualBoundary N T (q i) := by
      simpa only [mem_biUnion,mem_univ,true_and,mem_union] using Finset.ext_iff.mp P.cover e
    simp only [mem_biUnion,mem_univ,true_and]
    rw [hpE]
    constructor
    · rintro (he | ⟨i,he⟩)
      · exact he
      · exact zero_exception_boundary_subset_joining G hM U₀ U₁ Z h01 h0Z h1Z hZ
          r R N T (q i) he
    · exact Or.inl
  · intro j v hv
    exact (notMem_empty v (hZ ▸ hv)).elim

end Overfull.NativeAssembly
