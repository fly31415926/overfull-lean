import Overfull.ExceptionalPalette.ReserveCopies
import Overfull.AssignedParts.ExactPoolWeights

/-!
# Surviving assigned-core reserve copies in the unpaired signature

Each native boundary retains one original copy from an unpaired exception
to its assigned old core. Those copies survive in the actual residual edge
type and are distinct across reserve indices. The resulting injection and
exact selected-family counts keep parallel copies separate.
-/

noncomputable section

namespace Overfull.NativeReserve

open Finset Classical AssignedParts
open scoped BigOperators

variable {V E J : Type*} [Fintype E]

/-- Residual membership in an exceptional-to-core pool is precisely
membership of the surviving original copy in the original pool. -/
@[simp] theorem mem_residual_exceptionCorePool
    (G : Multigraph V E) (N : J → Finset E) (T : Finset J)
    (z : V) (U : Finset V) (e : {e : E // e ∉ removedCopies N T}) :
    e ∈ exceptionCorePool (residualGraph G N T) z U ↔
      e.val ∈ exceptionCorePool G z U := by
  simp only [exceptionCorePool, mem_filter, mem_univ, true_and]
  rfl

namespace BoundaryPacking

variable {G : Multigraph V E} {U₀ U₁ Z : Finset V} {M : Finset E} {r : ℕ}
    (Q : BoundaryPacking G U₀ U₁ Z M r)

/-- The unpaired signature supplies an actual assigned-core copy in every
original reserved boundary. Only the boundaries, not their parents, need
to be pairwise edge-disjoint. -/
theorem boundary_assigned_star_nonempty
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (σ : Z → Fin 2) (hcode : coarseSignature G M U₀ Z = some σ)
    (z : Z) (i : Fin r) :
    (Q.boundary i ∩ exceptionCorePool G z.val (if σ z = 0 then U₀ else U₁)).Nonempty := by
  obtain ⟨e, he⟩ := signature_some_uses_exceptionCorePool G (Q.perfect i)
    U₀ U₁ Z h0Z h1Z hcover σ ((Q.sameSignature i).trans hcode) z
  obtain ⟨heParent, hePool⟩ := mem_inter.mp he
  have heBoundary : e ∈ Q.boundary i := by
    apply compressedBoundary_retains_exceptional G (Q.parent i) U₀ U₁ Z
    exact mem_exceptionalCopies_of_incident G heParent z.property
      (mem_filter.mp hePool).2.1
  exact ⟨e, mem_inter.mpr ⟨heBoundary, hePool⟩⟩

/-- A matching boundary uses exactly one copy from the assigned star pool. -/
theorem boundary_assigned_star_card
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (σ : Z → Fin 2) (hcode : coarseSignature G M U₀ Z = some σ)
    (z : Z) (i : Fin r) :
    (Q.boundary i ∩ exceptionCorePool G z.val (if σ z = 0 then U₀ else U₁)).card = 1 := by
  have hlo := (Q.boundary_assigned_star_nonempty h0Z h1Z hcover σ hcode z i).card_pos
  have hhi := exceptionCorePool_matching_card_le_one G (Q.isMatching i)
    z.val (if σ z = 0 then U₀ else U₁)
  omega

/-- Intersecting a surviving boundary with an exceptional pool and then
forgetting the subtype retains exactly its original pool intersection. -/
theorem residualBoundary_inter_exceptionCorePool_image
    (N : J → Finset E) (T : Finset J)
    (havoid : ∀ j ∈ T, Disjoint (N j) (removedCopies Q.boundary univ))
    (z : V) (U : Finset V) (i : Fin r) :
    ((Q.residualBoundary N T i ∩ exceptionCorePool (residualGraph G N T) z U).image
      Subtype.val) = Q.boundary i ∩ exceptionCorePool G z U := by
  ext e
  constructor
  · intro he
    obtain ⟨f, hf, rfl⟩ := mem_image.mp he
    obtain ⟨hfB, hfP⟩ := mem_inter.mp hf
    exact mem_inter.mpr ⟨(Q.mem_residualBoundary N T i f).mp hfB,
      (mem_residual_exceptionCorePool G N T z U f).mp hfP⟩
  · intro he
    obtain ⟨heB, heP⟩ := mem_inter.mp he
    have hsurvive : e ∉ removedCopies N T := fun hd =>
      disjoint_left.mp (Q.boundary_disjoint_removed N T havoid i) heB hd
    let f : {e : E // e ∉ removedCopies N T} := ⟨e, hsurvive⟩
    exact mem_image.mpr ⟨f, mem_inter.mpr
      ⟨(Q.mem_residualBoundary N T i f).mpr heB,
        (mem_residual_exceptionCorePool G N T z U f).mpr heP⟩, rfl⟩

/-- Exactly one original assigned-core reserve copy survives in each
actual residual boundary. -/
theorem residualBoundary_assigned_star_card
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (σ : Z → Fin 2) (hcode : coarseSignature G M U₀ Z = some σ)
    (N : J → Finset E) (T : Finset J)
    (havoid : ∀ j ∈ T, Disjoint (N j) (removedCopies Q.boundary univ))
    (z : Z) (i : Fin r) :
    (Q.residualBoundary N T i ∩ exceptionCorePool (residualGraph G N T)
      z.val (if σ z = 0 then U₀ else U₁)).card = 1 := by
  rw [← card_image_of_injective _ Subtype.val_injective,
    Q.residualBoundary_inter_exceptionCorePool_image N T havoid]
  exact Q.boundary_assigned_star_card h0Z h1Z hcover σ hcode z i

/-- Each residual boundary contains a member of the exact assigned-core pool. -/
theorem residualBoundary_assigned_star_nonempty
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (σ : Z → Fin 2) (hcode : coarseSignature G M U₀ Z = some σ)
    (N : J → Finset E) (T : Finset J)
    (havoid : ∀ j ∈ T, Disjoint (N j) (removedCopies Q.boundary univ))
    (z : Z) (i : Fin r) :
    (Q.residualBoundary N T i ∩ exceptionCorePool (residualGraph G N T)
      z.val (if σ z = 0 then U₀ else U₁)).Nonempty := by
  apply card_pos.mp
  rw [Q.residualBoundary_assigned_star_card h0Z h1Z hcover σ hcode N T havoid z i]
  decide

/-- Inject the original reserve indices into distinct actual residual
assigned-star copies, retaining the boundary index of every selected copy. -/
theorem exists_residual_assigned_star_injection
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (σ : Z → Fin 2) (hcode : coarseSignature G M U₀ Z = some σ)
    (N : J → Finset E) (T : Finset J)
    (havoid : ∀ j ∈ T, Disjoint (N j) (removedCopies Q.boundary univ)) (z : Z) :
    ∃ f : Fin r → exceptionCorePool (residualGraph G N T)
        z.val (if σ z = 0 then U₀ else U₁),
      Function.Injective f ∧ ∀ i, (f i).val ∈ Q.residualBoundary N T i := by
  have hex (i : Fin r) : ∃ e : exceptionCorePool (residualGraph G N T)
      z.val (if σ z = 0 then U₀ else U₁), e.val ∈ Q.residualBoundary N T i := by
    obtain ⟨e, he⟩ := Q.residualBoundary_assigned_star_nonempty
      h0Z h1Z hcover σ hcode N T havoid z i
    exact ⟨⟨e, (mem_inter.mp he).2⟩, (mem_inter.mp he).1⟩
  choose f hf using hex
  refine ⟨f, ?_, hf⟩
  intro i j hij
  by_contra hne
  have heq : (f i).val = (f j).val := congrArg Subtype.val hij
  exact disjoint_left.mp (Q.residualBoundary_disjoint N T hne)
    (hf i) (heq.symm ▸ hf j)

/-- The surviving assigned-core star pool contains at least all `r`
distinct original reserve incidences. -/
theorem reserved_assigned_star_card_le
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (σ : Z → Fin 2) (hcode : coarseSignature G M U₀ Z = some σ)
    (N : J → Finset E) (T : Finset J)
    (havoid : ∀ j ∈ T, Disjoint (N j) (removedCopies Q.boundary univ)) (z : Z) :
    r ≤ (exceptionCorePool (residualGraph G N T)
      z.val (if σ z = 0 then U₀ else U₁)).card := by
  obtain ⟨f, hf, _⟩ := Q.exists_residual_assigned_star_injection
    h0Z h1Z hcover σ hcode N T havoid z
  simpa only [Fintype.card_fin, Fintype.card_coe] using Fintype.card_le_of_injective f hf

/-- At the exception, the entire residual boundary incidence is exactly
its assigned-core star intersection; no reserved incidence goes to a bundle. -/
theorem residualBoundary_incidence_eq_assigned_star
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (σ : Z → Fin 2) (hcode : coarseSignature G M U₀ Z = some σ)
    (N : J → Finset E) (T : Finset J)
    (havoid : ∀ j ∈ T, Disjoint (N j) (removedCopies Q.boundary univ))
    (z : Z) (i : Fin r) :
    (Q.residualBoundary N T i).filter
        (fun e => z.val ∈ (residualGraph G N T).edge e) =
      Q.residualBoundary N T i ∩ exceptionCorePool (residualGraph G N T)
        z.val (if σ z = 0 then U₀ else U₁) := by
  obtain ⟨f, hf⟩ := Q.residualBoundary_assigned_star_nonempty
    h0Z h1Z hcover σ hcode N T havoid z i
  obtain ⟨hfB, hfP⟩ := mem_inter.mp hf
  ext e
  constructor
  · intro he
    obtain ⟨heB, hez⟩ := mem_filter.mp he
    have hef : e = f := (Q.residualBoundary_matching N T i)
      e heB f hfB z.val hez (mem_filter.mp hfP).2.1
    exact mem_inter.mpr ⟨heB, hef ▸ hfP⟩
  · intro he
    obtain ⟨heB, heP⟩ := mem_inter.mp he
    exact mem_filter.mpr ⟨heB, (mem_filter.mp heP).2.1⟩

/-- An injectively selected reserve family contributes exactly one distinct
assigned-star copy per selected index, in the actual residual copy type. -/
theorem selected_residual_assigned_star_card {I : Type*}
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (σ : Z → Fin 2) (hcode : coarseSignature G M U₀ Z = some σ)
    (N : J → Finset E) (T : Finset J)
    (havoid : ∀ j ∈ T, Disjoint (N j) (removedCopies Q.boundary univ))
    (z : Z) (A : Finset I) (q : I → Fin r) (hq : Set.InjOn q A) :
    ((A.biUnion (fun i => Q.residualBoundary N T (q i))) ∩
      exceptionCorePool (residualGraph G N T)
        z.val (if σ z = 0 then U₀ else U₁)).card = A.card := by
  let S := exceptionCorePool (residualGraph G N T)
    z.val (if σ z = 0 then U₀ else U₁)
  have heq : (A.biUnion (fun i => Q.residualBoundary N T (q i))) ∩ S =
      A.biUnion (fun i => Q.residualBoundary N T (q i) ∩ S) := by
    ext e
    simp only [mem_inter, mem_biUnion]
    constructor
    · rintro ⟨⟨i, hi, he⟩, heS⟩
      exact ⟨i, hi, he, heS⟩
    · rintro ⟨i, hi, he, heS⟩
      exact ⟨⟨i, hi, he⟩, heS⟩
  have hdis : A.toSet.PairwiseDisjoint
      (fun i => Q.residualBoundary N T (q i) ∩ S) := by
    intro i hi j hj hij
    exact (Q.residualBoundary_disjoint N T (fun heq => hij (hq hi hj heq))).mono
      inter_subset_left inter_subset_left
  change ((A.biUnion (fun i => Q.residualBoundary N T (q i))) ∩ S).card = _
  rw [heq, card_biUnion hdis]
  have hcard (i : I) : (Q.residualBoundary N T (q i) ∩ S).card = 1 :=
    Q.residualBoundary_assigned_star_card h0Z h1Z hcover σ hcode N T havoid z (q i)
  simp only [hcard, sum_const, smul_eq_mul, mul_one]

/-- The whole surviving reserve meets the assigned star pool in exactly
`r` distinct original copies. -/
theorem residual_assigned_star_union_card
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (σ : Z → Fin 2) (hcode : coarseSignature G M U₀ Z = some σ)
    (N : J → Finset E) (T : Finset J)
    (havoid : ∀ j ∈ T, Disjoint (N j) (removedCopies Q.boundary univ)) (z : Z) :
    ((univ.biUnion (Q.residualBoundary N T)) ∩
      exceptionCorePool (residualGraph G N T)
        z.val (if σ z = 0 then U₀ else U₁)).card = r := by
  simpa only [card_univ, Fintype.card_fin] using
    Q.selected_residual_assigned_star_card h0Z h1Z hcover σ hcode N T havoid z
      (univ : Finset (Fin r)) id (fun _ _ _ _ heq => heq)

end BoundaryPacking

end Overfull.NativeReserve
