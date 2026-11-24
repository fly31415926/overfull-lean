import Overfull.NativeAssembly.BaseClasses

/-!
# Actual native bundle and star separation

Every reserved boundary uses an unpaired exception through its assigned old
core. Its copies are therefore disjoint from the internal exceptional bundle.
The same original assignment partitions the actual residual joining and star
copies without identifying parallel copies.
-/

noncomputable section

namespace Overfull.NativeAssembly

open Finset Classical AssignedParts FourOdd NativeReserve NativeStar

variable {V E K : Type*} [Fintype E] [DecidableEq K]

/-- The actual internal exceptional pool has equal assigned labels at its ends. -/
theorem exceptionInternalPool_internal (H : Multigraph V E) (label : V → K)
    (Z : Finset V) (z : V) :
    ∀ e ∈ exceptionInternalPool H label Z z,
      label (H.firstEnd e) = label (H.secondEnd e) := by
  intro e he
  obtain ⟨hz, _, hs⟩ := (mem_exceptionInternalPool H label Z z e).mp he
  by_contra hn
  exact (joining_iff_otherEnd_label_ne H label z e hz).mp
    ((mem_joiningCopies H label e).mpr hn) hs

/-- A copy to the assigned old core is internal to the assigned label. -/
theorem exceptionCorePool_internal (H : Multigraph V E) (label : V → K)
    (z : V) (U : Finset V) (hlabel : ∀ v ∈ U, label v = label z) :
    ∀ e ∈ exceptionCorePool H z U,
      label (H.firstEnd e) = label (H.secondEnd e) := by
  intro e he
  obtain ⟨_, hz, hu⟩ := mem_filter.mp he
  by_contra hn
  exact (joining_iff_otherEnd_label_ne H label z e hz).mp
    ((mem_joiningCopies H label e).mpr hn) (hlabel _ hu)

variable {J : Type*} [Fintype V]

/-- Native reserved boundaries have no copy in an unpaired exception's
internal exceptional pool. -/
theorem native_internalPool_disjoint_boundary
    (G : Multigraph V E) {M : Finset E} (hM : G.IsPerfectMatching M)
    (U₀ U₁ Z : Finset V) (h01 : Disjoint U₀ U₁)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (σ : Z → Fin 2) (hcode : coarseSignature G M U₀ Z = some σ)
    (r : ℕ) (Q : BoundaryPacking G U₀ U₁ Z M r)
    (N : J → Finset E) (T : Finset J)
    (havoid : ∀ j ∈ T, Disjoint (N j) (removedCopies Q.boundary univ))
    (z : Z) (i : Fin r) :
    Disjoint (exceptionInternalPool (residualGraph G N T)
      (assignedLabel G M U₀ U₁ Z) Z z.val) (Q.residualBoundary N T i) := by
  let H := residualGraph G N T
  apply disjoint_left.mpr
  intro e heI heB
  have hze := ((mem_exceptionInternalPool H _ Z z.val e).mp heI).1
  have heInc : e ∈ (Q.residualBoundary N T i).filter (fun e => z.val ∈ H.edge e) :=
    mem_filter.mpr ⟨heB,hze⟩
  rw [Q.residualBoundary_incidence_eq_assigned_star h0Z h1Z hcover σ hcode
    N T havoid z i] at heInc
  exact disjoint_left.mp
    (assigned_incidence_partition G H hM U₀ U₁ Z h01 h0Z h1Z hcover σ hcode z).2.2.1
    (mem_inter.mp heInc).2 heI

/-- All native assigned-star copies are disjoint from the entire joining set. -/
theorem native_star_disjoint_joining
    (G : Multigraph V E) {M : Finset E} (hM : G.IsPerfectMatching M)
    (U₀ U₁ Z : Finset V) (h01 : Disjoint U₀ U₁)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (σ : Z → Fin 2) (hcode : coarseSignature G M U₀ Z = some σ)
    (N : J → Finset E) (T : Finset J) (z : Z) :
    Disjoint (exceptionCorePool (residualGraph G N T) z.val
      (if σ z = 0 then U₀ else U₁))
      (joiningCopies (residualGraph G N T) (assignedLabel G M U₀ U₁ Z)) := by
  apply internalCopies_disjoint_joining
  apply exceptionCorePool_internal
  exact (unpaired_assignment_fiber_bounds G hM U₀ U₁ Z
    h01 h0Z h1Z hcover σ hcode z).2.1

/-- The original native assignment makes every residual old-core star copy
internal, a property retained by all subsequent color choices. -/
theorem native_star_internal
    (G : Multigraph V E) {M : Finset E} (hM : G.IsPerfectMatching M)
    (U₀ U₁ Z : Finset V) (h01 : Disjoint U₀ U₁)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (σ : Z → Fin 2) (hcode : coarseSignature G M U₀ Z = some σ)
    (N : J → Finset E) (T : Finset J) (z : Z) :
    ∀ e ∈ exceptionCorePool (residualGraph G N T) z.val
      (if σ z = 0 then U₀ else U₁),
      assignedLabel G M U₀ U₁ Z ((residualGraph G N T).firstEnd e) =
        assignedLabel G M U₀ U₁ Z ((residualGraph G N T).secondEnd e) := by
  apply exceptionCorePool_internal
  exact (unpaired_assignment_fiber_bounds G hM U₀ U₁ Z
    h01 h0Z h1Z hcover σ hcode z).2.1

end Overfull.NativeAssembly
