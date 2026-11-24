import Overfull.Patterns.WholeCuts
import Overfull.Patterns.Forest

/-!
# Assigned shores and the parity of their joining forest

Putting each exceptional vertex on the same shore as its assigned core
makes every exceptional edge internal. The boundary of an assigned shore
is therefore precisely the incident forest pairs.
-/

noncomputable section
namespace Overfull.Patterns
open Finset Classical SimpleGraph Compression MatchingProbability
open scoped BigOperators

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- One core label together with every exceptional vertex assigned to it. -/
def Pattern.assignedShore (P : Pattern E) (i : Fin 4) : Finset (E ⊕ Fin 4) :=
  insert (Sum.inr i) ((univ.filter (fun z => P.assignment z = i)).image Sum.inl)

@[simp] theorem Pattern.inl_mem_assignedShore (P : Pattern E) (i : Fin 4) (z : E) :
    Sum.inl z ∈ P.assignedShore i ↔ P.assignment z = i := by
  simp [Pattern.assignedShore]

@[simp] theorem Pattern.inr_mem_assignedShore (P : Pattern E) (i j : Fin 4) :
    Sum.inr j ∈ P.assignedShore i ↔ j = i := by
  simp [Pattern.assignedShore]

/-- The cut of an assigned shore counts exactly its incident forest pairs. -/
theorem Pattern.cutCount_assignedShore (P : Pattern E)
    (hpairs : P.internalPairs = ∅) (i : Fin 4) :
    P.cutCount (P.assignedShore i) = pairDegree P.forest i := by
  classical
  let Cross := (univ.filter (fun z => ¬ P.Paired z)).image
    (fun z => ({Sum.inl z,Sum.inr (P.assignment z)} : Finset (E ⊕ Fin 4)))
  let Core := P.forest.image (fun p => p.val.image (Sum.inr : Fin 4 → E ⊕ Fin 4))
  let crosses := fun A : Finset (E ⊕ Fin 4) =>
    (A.filter (fun v => v ∈ P.assignedShore i)).card = 1
  have hcross : Cross.filter crosses = ∅ := by
    ext b
    simp only [Cross,mem_filter,mem_image,Finset.notMem_empty,iff_false]
    rintro ⟨⟨z,_hz,rfl⟩,hc⟩
    by_cases hzi : P.assignment z = i <;>
      simp [crosses,Finset.filter_insert,Finset.filter_singleton,hzi] at hc
  have hcore : Core.filter crosses =
      (P.forest.filter (fun p => i ∈ p.val)).image
        (fun p => p.val.image (Sum.inr : Fin 4 → E ⊕ Fin 4)) := by
    dsimp only [Core]
    rw [Finset.filter_image]
    congr 1
    ext p
    simp only [mem_filter]
    apply and_congr_right
    intro _hp
    have hh : crosses (p.val.image (Sum.inr : Fin 4 → E ⊕ Fin 4)) ↔ i ∈ p.val := by
      unfold crosses
      rw [Finset.filter_image,Finset.card_image_of_injective _ Sum.inr_injective]
      simp only [Pattern.inr_mem_assignedShore]
      rw [Finset.filter_eq']
      by_cases hi : i ∈ p.val <;> simp [hi]
    exact hh
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

variable {V I : Type*} [Fintype V] [Fintype I]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The order of each assigned whole shore has the parity of its forest
degree. This is an actual vertex-cardinality statement. -/
theorem Encodes.assigned_shore_parity
    {U : I → Finset V} {Z : Finset V} {code : I ↪ Fin 4}
    {F : G.Subgraph} {P : Pattern Z} (hP : Encodes G U Z code F P)
    (hdisjoint : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hUZ : ∀ i, Disjoint (U i) Z)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (hparity : ∀ i, Even (((U i : Set V) \ F.verts).ncard))
    (hpairs : P.internalPairs = ∅) (i : Fin 4) :
    (wholeUnion U Z code (P.assignedShore i)).card % 2 = pairDegree P.forest i % 2 := by
  have hh := hP.whole_cut_parity hdisjoint hUZ hcover hparity (P.assignedShore i)
  rw [P.cutCount_assignedShore hpairs i] at hh
  exact hh.symm

/-- Four odd assigned shores force the perfect-matching or star pattern. -/
theorem Encodes.assigned_four_odd_forest
    {U : I → Finset V} {Z : Finset V} {code : I ↪ Fin 4}
    {F : G.Subgraph} {P : Pattern Z} (hP : Encodes G U Z code F P)
    (hdisjoint : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hUZ : ∀ i, Disjoint (U i) Z)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (hparity : ∀ i, Even (((U i : Set V) \ F.verts).ncard))
    (hpairs : P.internalPairs = ∅)
    (hodd : ∀ i : Fin 4, (wholeUnion U Z code (P.assignedShore i)).card % 2 = 1) :
    (P.forest.card = 2 ∧ ∀ i : Fin 4, pairDegree P.forest i = 1) ∨
      ∃ center : Fin 4, P.forest.card = 3 ∧
        ∀ p : LabelPair, p ∈ P.forest ↔ center ∈ p.val := by
  apply four_odd_label_forest P.forest hP.forest
  intro i
  rw [← hP.assigned_shore_parity hdisjoint hUZ hcover hparity hpairs i]
  exact hodd i

end Overfull.Patterns
