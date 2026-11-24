import Overfull.Patterns.Absorption

/-!
# Forest supply across arbitrary unions of assigned parts

After every exceptional vertex joins its assigned part, the cut of any
union of parts consists of the joining-forest pairs crossing the same
set of labels. The identities use actual enlarged vertex sets.
-/

noncomputable section
namespace Overfull.Patterns
open Finset Classical SimpleGraph Compression MatchingProbability
open scoped BigOperators

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- A set of core labels together with all exceptional vertices assigned
to one of those labels. -/
def Pattern.assignedUnion (P : Pattern E) (L : Finset (Fin 4)) : Finset (E ⊕ Fin 4) :=
  L.image Sum.inr ∪ (univ.filter (fun z => P.assignment z ∈ L)).image Sum.inl

@[simp] theorem Pattern.inl_mem_assignedUnion (P : Pattern E) (L : Finset (Fin 4)) (z : E) :
    Sum.inl z ∈ P.assignedUnion L ↔ P.assignment z ∈ L := by
  simp [Pattern.assignedUnion]

@[simp] theorem Pattern.inr_mem_assignedUnion (P : Pattern E) (L : Finset (Fin 4)) (i : Fin 4) :
    Sum.inr i ∈ P.assignedUnion L ↔ i ∈ L := by
  simp [Pattern.assignedUnion]

/-- The actual finite joining-forest cut on a set of core labels. -/
def Pattern.forestCutCount (P : Pattern E) (L : Finset (Fin 4)) : ℕ :=
  (P.forest.filter (fun p => (p.val.filter (fun i => i ∈ L)).card = 1)).card

/-- Exceptional edges are internal to every union of assigned parts, so
only the forest contributes to its cut count. -/
theorem Pattern.cutCount_assignedUnion (P : Pattern E)
    (hpairs : P.internalPairs = ∅) (L : Finset (Fin 4)) :
    P.cutCount (P.assignedUnion L) = P.forestCutCount L := by
  classical
  let Cross := (univ.filter (fun z => ¬ P.Paired z)).image
    (fun z => ({Sum.inl z,Sum.inr (P.assignment z)} : Finset (E ⊕ Fin 4)))
  let Core := P.forest.image (fun p => p.val.image (Sum.inr : Fin 4 → E ⊕ Fin 4))
  let crosses := fun A : Finset (E ⊕ Fin 4) =>
    (A.filter (fun v => v ∈ P.assignedUnion L)).card = 1
  have hcross : Cross.filter crosses = ∅ := by
    ext b
    simp only [Cross,mem_filter,mem_image,Finset.notMem_empty,iff_false]
    rintro ⟨⟨z,_hz,rfl⟩,hc⟩
    by_cases hzL : P.assignment z ∈ L <;>
      simp [crosses,Finset.filter_insert,Finset.filter_singleton,hzL] at hc
  have hcore : Core.filter crosses =
      (P.forest.filter (fun p => (p.val.filter (fun i => i ∈ L)).card = 1)).image
        (fun p => p.val.image (Sum.inr : Fin 4 → E ⊕ Fin 4)) := by
    dsimp only [Core]
    rw [Finset.filter_image]
    congr 1
    ext p
    simp only [mem_filter]
    apply and_congr_right
    intro _hp
    unfold crosses
    rw [Finset.filter_image,Finset.card_image_of_injective _ Sum.inr_injective]
    simp only [Pattern.inr_mem_assignedUnion]
  have hinj : Function.Injective
      (fun p : LabelPair => p.val.image (Sum.inr : Fin 4 → E ⊕ Fin 4)) := by
    intro p q hpq
    apply Subtype.ext
    exact Finset.image_injective Sum.inr_injective hpq
  unfold Pattern.cutCount Pattern.boundaryEdges
  rw [hpairs,Finset.image_empty,empty_union,Finset.filter_union]
  change (Cross.filter crosses ∪ Core.filter crosses).card = _
  rw [hcross,empty_union,hcore,Finset.card_image_of_injective _ hinj]
  rfl

variable {V I : Type*} [Fintype V]

/-- Unions of actual enlarged core sets are exactly the corresponding
assigned quotient shores. -/
theorem enlarged_union_eq_assignedUnion
    (U : I → Finset V) (Z : Finset V) (code : I ↪ Fin 4)
    (P : Pattern Z) (assignment : V → I)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hUZ : ∀ i, Disjoint (U i) Z)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (hassignment : ∀ z : Z, P.assignment z = code (assignment z.val)) (A : Finset I) :
    A.biUnion (Absorption.enlargedSets U Z assignment) =
      wholeUnion U Z code (P.assignedUnion (A.image code)) := by
  classical
  have heq : A.biUnion (Absorption.enlargedSets U Z assignment) =
      A.biUnion (fun i => wholeUnion U Z code (P.assignedShore (code i))) := by
    apply Finset.biUnion_congr rfl
    intro i _hi
    exact enlargedSets_eq_assigned_shore U Z code P assignment hdisjoint hUZ hcover hassignment i
  rw [heq]
  ext v
  simp only [mem_biUnion,mem_wholeUnion]
  cases hlabel : boundaryLabel U Z code v with
  | inl z =>
    simp only [Pattern.inl_mem_assignedShore,Pattern.inl_mem_assignedUnion,mem_image]
    simp only [eq_comm]
  | inr j =>
    simp only [Pattern.inr_mem_assignedShore,Pattern.inr_mem_assignedUnion,mem_image]
    simp only [eq_comm]

/-- Transport a reserved pattern cut bound to the actual enlarged parts. -/
theorem forest_supply_on_enlarged_parts
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (U : I → Finset V) (Z : Finset V) (code : I ↪ Fin 4)
    (P : Pattern Z) (assignment : V → I) (r : ℕ)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hUZ : ∀ i, Disjoint (U i) Z)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (hpairs : P.internalPairs = ∅)
    (hassignment : ∀ z : Z, P.assignment z = code (assignment z.val))
    (hsupply : ∀ Q : Finset (Z ⊕ Fin 4), r*P.cutCount Q ≤
      cutCount (univ : Finset R.edgeSet) (wholeUnion U Z code Q)) :
    ∀ A : Finset I, r*P.forestCutCount (A.image code) ≤
      cutCount (univ : Finset R.edgeSet) (A.biUnion (Absorption.enlargedSets U Z assignment)) := by
  intro A
  have hh := hsupply (P.assignedUnion (A.image code))
  rw [P.cutCount_assignedUnion hpairs] at hh
  rw [enlarged_union_eq_assignedUnion U Z code P assignment hdisjoint hUZ hcover hassignment A]
  exact hh

end Overfull.Patterns
