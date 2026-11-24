import Overfull.NativeStar.ReserveInjection
import Overfull.NativeStar.IncidencePartition
import Overfull.NativeStar.CommonPalette

/-!
# Native reserve counts and actual remaining-star balance

The original native reserve supplies the assigned-star injection needed by
the exact incidence partition. Actual joining-used colors, selected reserve
copies, and an injectively colored internal bundle then give balanced
remaining copy and color sets. Protected joining-freeness is derived from
the exact reserve trace, rather than assumed from a cardinality estimate.
-/

noncomputable section

namespace Overfull.NativeStar

open Finset Classical AssignedParts FourOdd NativeReserve

variable {V E J : Type*} [Fintype E]

/-- The actual native unpaired reserve bounds the combined joining and
internal-exceptional incidence without an assumed star-pool cardinality. -/
theorem native_off_core_degree_bound
    (G : Multigraph V E) {M : Finset E} (hM : G.IsPerfectMatching M)
    (U₀ U₁ Z : Finset V) (h01 : Disjoint U₀ U₁)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (σ : Z → Fin 2) (hcode : coarseSignature G M U₀ Z = some σ)
    (r : ℕ) (R : BoundaryPacking G U₀ U₁ Z M r)
    (N : J → Finset E) (T : Finset J)
    (havoid : ∀ j ∈ T, Disjoint (N j) (removedCopies R.boundary univ))
    (z : Z) (h D : ℕ)
    (hdegree : (residualGraph G N T).degree z.val = h) (herror : h-r ≤ D) :
    (residualGraph G N T).degreeOn
        (joiningCopies (residualGraph G N T) (assignedLabel G M U₀ U₁ Z)) z.val +
        (exceptionInternalPool (residualGraph G N T)
          (assignedLabel G M U₀ U₁ Z) Z z.val).card ≤ h-r ∧
      (residualGraph G N T).degreeOn
        (joiningCopies (residualGraph G N T) (assignedLabel G M U₀ U₁ Z)) z.val +
        (exceptionInternalPool (residualGraph G N T)
          (assignedLabel G M U₀ U₁ Z) Z z.val).card ≤ D := by
  exact assigned_off_core_degree_bound G (residualGraph G N T) hM U₀ U₁ Z
    h01 h0Z h1Z hcover σ hcode z h r D hdegree
    (R.reserved_assigned_star_card_le h0Z h1Z hcover σ hcode N T havoid z) herror

section JoiningColors

variable [Fintype V] {K : Type*} [DecidableEq K]
    {H : Multigraph V E} {label : V → K} {h D L : ℕ} {p : K → ℕ}

/-- The colors used at a vertex by the actual original joining classes. -/
def joiningUsedColors (C : JoiningPalette H label h D L p) (z : V) : Finset (Fin h) :=
  univ.filter (fun j => z ∈ H.edgeSupport (C.classes j))

@[simp] theorem mem_joiningUsedColors (C : JoiningPalette H label h D L p)
    (z : V) (j : Fin h) :
    j ∈ joiningUsedColors C z ↔ z ∈ H.edgeSupport (C.classes j) := by
  simp [joiningUsedColors]

/-- Matching and disjointness identify used colors with actual joining incidences. -/
theorem joiningUsedColors_card (C : JoiningPalette H label h D L p) (z : V) :
    (joiningUsedColors C z).card = H.degreeOn (joiningCopies H label) z :=
  C.usedColors_card z

end JoiningColors

variable [Fintype V]

/-- A protected color equal to a native unpaired boundary's joining trace
is free at every exception: that boundary's exceptional copy is in its
assigned-star pool and cannot be a joining copy. -/
theorem protected_joining_color_free_of_reserve_trace
    (G : Multigraph V E) {M : Finset E} (hM : G.IsPerfectMatching M)
    (U₀ U₁ Z : Finset V) (h01 : Disjoint U₀ U₁)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (σ : Z → Fin 2) (hcode : coarseSignature G M U₀ Z = some σ)
    (r : ℕ) (R : BoundaryPacking G U₀ U₁ Z M r)
    (N : J → Finset E) (T : Finset J)
    (havoid : ∀ j ∈ T, Disjoint (N j) (removedCopies R.boundary univ))
    {h D L : ℕ} {p : Fin 3 → ℕ}
    (C : JoiningPalette (residualGraph G N T) (assignedLabel G M U₀ U₁ Z) h D L p)
    (z : Z) (i : Fin r) (j : Fin h)
    (htrace : R.residualBoundary N T i ∩
      joiningCopies (residualGraph G N T) (assignedLabel G M U₀ U₁ Z) = C.classes j) :
    z.val ∉ (residualGraph G N T).edgeSupport (C.classes j) := by
  intro hz
  obtain ⟨e, heC, hze⟩ := ((residualGraph G N T).mem_edgeSupport _ _).mp hz
  rw [← htrace] at heC
  obtain ⟨heB, heJ⟩ := mem_inter.mp heC
  have heInc : e ∈ (R.residualBoundary N T i).filter
      (fun e => z.val ∈ (residualGraph G N T).edge e) := mem_filter.mpr ⟨heB,hze⟩
  rw [R.residualBoundary_incidence_eq_assigned_star h0Z h1Z hcover σ hcode
    N T havoid z i] at heInc
  have hdis := (assigned_incidence_partition G (residualGraph G N T) hM U₀ U₁ Z
    h01 h0Z h1Z hcover σ hcode z).1
  exact disjoint_left.mp hdis
    ((mem_joiningIncidenceCopies _ _ _ _).mpr ⟨hze,heJ⟩) (mem_inter.mp heInc).2

/-- When the two exceptions have the same assigned label, construct an
injective coloring of their entire actual mutual bundle in colors avoiding
the protected labels and the actual joining-used colors at both ends. -/
theorem exists_native_common_bundle_coloring
    (G : Multigraph V E) {M : Finset E} (hM : G.IsPerfectMatching M)
    (U₀ U₁ Z : Finset V) (h01 : Disjoint U₀ U₁)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (σ : Z → Fin 2) (hcode : coarseSignature G M U₀ Z = some σ)
    (r : ℕ) (R : BoundaryPacking G U₀ U₁ Z M r)
    (N : J → Finset E) (T : Finset J)
    (havoid : ∀ j ∈ T, Disjoint (N j) (removedCopies R.boundary univ))
    {h D L : ℕ} {p : Fin 3 → ℕ}
    (C : JoiningPalette (residualGraph G N T) (assignedLabel G M U₀ U₁ Z) h D L p)
    (z₀ z₁ : Z) (hZ : Z = {z₀.val,z₁.val})
    (hsame : assignedLabel G M U₀ U₁ Z z₀.val = assignedLabel G M U₀ U₁ Z z₁.val)
    (hregular : ∀ v, (residualGraph G N T).degree v = h)
    (herror : h-r ≤ D) (hD : 4*D ≤ h)
    (Q : Finset (Fin h)) (hQ : 2*Q.card ≤ h) :
    exceptionInternalPool (residualGraph G N T)
        (assignedLabel G M U₀ U₁ Z) Z z₀.val =
      pairFiberCopies (residualGraph G N T) z₀.val z₁.val ∧
    exceptionInternalPool (residualGraph G N T)
        (assignedLabel G M U₀ U₁ Z) Z z₁.val =
      pairFiberCopies (residualGraph G N T) z₀.val z₁.val ∧
    ∃ c : pairFiberCopies (residualGraph G N T) z₀.val z₁.val → Fin h,
      Function.Injective c ∧
      ∀ e, c e ∉ Q ∧ c e ∉ joiningUsedColors C z₀.val ∧
        c e ∉ joiningUsedColors C z₁.val := by
  let H := residualGraph G N T
  let label := assignedLabel G M U₀ U₁ Z
  have hB₀ : exceptionInternalPool H label Z z₀.val = pairFiberCopies H z₀.val z₁.val := by
    calc
      _ = exceptionInternalPool H label {z₀.val,z₁.val} z₀.val :=
        congrArg (fun X => exceptionInternalPool H label X z₀.val) hZ
      _ = _ := exceptionInternalPool_pair_eq H label z₀.val z₁.val hsame
  have hB₁ : exceptionInternalPool H label Z z₁.val = pairFiberCopies H z₀.val z₁.val := by
    have hswap : ({z₀.val,z₁.val} : Finset V) = {z₁.val,z₀.val} := by
      ext v
      simp only [mem_insert, mem_singleton, or_comm]
    calc
      _ = exceptionInternalPool H label {z₁.val,z₀.val} z₁.val :=
        congrArg (fun X => exceptionInternalPool H label X z₁.val) (hZ.trans hswap)
      _ = pairFiberCopies H z₁.val z₀.val :=
        exceptionInternalPool_pair_eq H label z₁.val z₀.val hsame.symm
      _ = _ := congrArg (H.internalOn univ) hswap.symm
  have h₀ := (native_off_core_degree_bound G hM U₀ U₁ Z h01 h0Z h1Z hcover
    σ hcode r R N T havoid z₀ h D (hregular z₀.val) herror).2
  have h₁ := (native_off_core_degree_bound G hM U₀ U₁ Z h01 h0Z h1Z hcover
    σ hcode r R N T havoid z₁ h D (hregular z₁.val) herror).2
  have hx : (joiningUsedColors C z₀.val).card + (pairFiberCopies H z₀.val z₁.val).card ≤ D := by
    rw [joiningUsedColors_card, ← hB₀]
    exact h₀
  have hy : (joiningUsedColors C z₁.val).card + (pairFiberCopies H z₀.val z₁.val).card ≤ D := by
    rw [joiningUsedColors_card, ← hB₁]
    exact h₁
  exact ⟨hB₀,hB₁,exists_common_bundle_coloring_of_combined_bounds
    (pairFiberCopies H z₀.val z₁.val) Q (joiningUsedColors C z₀.val)
    (joiningUsedColors C z₁.val) hx hy hD hQ⟩

/-- Exact native selected-star balance. The selected protected copies are
the actual reserve intersections, their cardinality is derived from the
reserve injection, and bundle-used colors count distinct actual copies.
The reserve trace derives protected/joining color disjointness. -/
theorem native_remaining_star_balance {I : Type*}
    (G : Multigraph V E) {M : Finset E} (hM : G.IsPerfectMatching M)
    (U₀ U₁ Z : Finset V) (h01 : Disjoint U₀ U₁)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (σ : Z → Fin 2) (hcode : coarseSignature G M U₀ Z = some σ)
    (r : ℕ) (R : BoundaryPacking G U₀ U₁ Z M r)
    (N : J → Finset E) (T : Finset J)
    (havoid : ∀ j ∈ T, Disjoint (N j) (removedCopies R.boundary univ))
    {h D L : ℕ} {p : Fin 3 → ℕ}
    (C : JoiningPalette (residualGraph G N T) (assignedLabel G M U₀ U₁ Z) h D L p)
    (z : Z) (hdegree : (residualGraph G N T).degree z.val = h) (herror : h-r ≤ D)
    (A : Finset I) (q : I → Fin r) (hq : Set.InjOn q A)
    (f : I → Fin h) (hf : Set.InjOn f A)
    (htrace : ∀ i ∈ A, R.residualBoundary N T (q i) ∩
      joiningCopies (residualGraph G N T) (assignedLabel G M U₀ U₁ Z) = C.classes (f i))
    (B : Finset {e : E // e ∉ removedCopies N T})
    (hB : B = exceptionInternalPool (residualGraph G N T)
      (assignedLabel G M U₀ U₁ Z) Z z.val)
    (c : B → Fin h) (hc : Function.Injective c)
    (hcavoid : ∀ e, c e ∉ A.image f ∧ c e ∉ joiningUsedColors C z.val) :
    let S := exceptionCorePool (residualGraph G N T) z.val (if σ z = 0 then U₀ else U₁)
    let P := (A.biUnion (fun i => R.residualBoundary N T (q i))) ∩ S
    let Qcol := A.image f
    let Jcol := joiningUsedColors C z.val
    let Bcol := univ.image c
    P.card = A.card ∧ Qcol.card = A.card ∧ Bcol.card = B.card ∧
      (S \ P).card = h - A.card - Jcol.card - B.card ∧
      (S \ P).card = (remainingStarColors Qcol Jcol Bcol).card ∧
      h - A.card - D ≤ (S \ P).card := by
  let H := residualGraph G N T
  let label := assignedLabel G M U₀ U₁ Z
  let S := exceptionCorePool H z.val (if σ z = 0 then U₀ else U₁)
  let P := (A.biUnion (fun i => R.residualBoundary N T (q i))) ∩ S
  let Qcol := A.image f
  let Jcol := joiningUsedColors C z.val
  let Bcol := univ.image c
  have hP : P.card = A.card :=
    R.selected_residual_assigned_star_card h0Z h1Z hcover σ hcode N T havoid z A q hq
  have hPsub : P ⊆ S := inter_subset_right
  have hQcol : Qcol.card = A.card := card_image_of_injOn hf
  have hBcol : Bcol.card = B.card := by
    rw [card_image_of_injective _ hc, card_univ, Fintype.card_coe]
  have hJcol : Jcol.card = H.degreeOn (joiningCopies H label) z.val := joiningUsedColors_card C z.val
  have hbalance : Jcol.card + S.card + Bcol.card = h := by
    rw [hJcol,hBcol,hB]
    exact (assigned_degree_balance G H hM U₀ U₁ Z h01 h0Z h1Z hcover σ hcode z).trans hdegree
  have hcombined : Jcol.card + Bcol.card ≤ D := by
    rw [hJcol,hBcol,hB]
    exact (native_off_core_degree_bound G hM U₀ U₁ Z h01 h0Z h1Z hcover
      σ hcode r R N T havoid z h D hdegree herror).2
  have hQJ : Disjoint Qcol Jcol := by
    apply disjoint_left.mpr
    intro j hjQ hjJ
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hjQ
    exact (protected_joining_color_free_of_reserve_trace G hM U₀ U₁ Z
      h01 h0Z h1Z hcover σ hcode r R N T havoid C z (q i) (f i) (htrace i hi))
      ((mem_joiningUsedColors C z.val (f i)).mp hjJ)
  have hQB : Disjoint Qcol Bcol := by
    apply disjoint_left.mpr
    intro j hjQ hjB
    obtain ⟨e,_,rfl⟩ := mem_image.mp hjB
    exact (hcavoid e).1 hjQ
  have hJB : Disjoint Jcol Bcol := by
    apply disjoint_left.mpr
    intro j hjJ hjB
    obtain ⟨e,_,rfl⟩ := mem_image.mp hjB
    exact (hcavoid e).2 hjJ
  obtain ⟨hcolors,hlower⟩ := remaining_star_card_eq_colors_and_lower
    S P Qcol Jcol Bcol hPsub (hP.trans hQcol.symm) hbalance hcombined hQJ hQB hJB
  have hexact : (S \ P).card = h - A.card - Jcol.card - B.card := by
    have hsplit := card_sdiff_add_card_eq_card hPsub
    omega
  change P.card = A.card ∧ Qcol.card = A.card ∧ Bcol.card = B.card ∧
    (S \ P).card = h - A.card - Jcol.card - B.card ∧
    (S \ P).card = (remainingStarColors Qcol Jcol Bcol).card ∧
    h - A.card - D ≤ (S \ P).card
  exact ⟨hP,hQcol,hBcol,hexact,hcolors,by simpa only [hQcol] using hlower⟩

end Overfull.NativeStar
