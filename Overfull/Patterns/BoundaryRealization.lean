import Overfull.Patterns.Boundary
import Overfull.Patterns.Realization

/-!
# Realization of the accepted boundary patterns

The demand slots are the actual quotient edges of each selected pattern.
A slot is realized by a fresh host edge with exactly those quotient
endpoints.  Thus the output is a family of actual edge-disjoint matchings.
-/

noncomputable section
namespace Overfull.Patterns

open Finset Classical SimpleGraph Compression FractionalMatching MatchingProbability
open PatternRealization
open scoped BigOperators

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- Exceptional labels occurring in one quotient edge. -/
def exceptionalLabels (b : Finset (E ⊕ Fin 4)) : Finset E :=
  univ.filter (fun z => Sum.inl z ∈ b)

/-- A quotient edge uses one core endpoint if it meets the exceptional
set, and at most two otherwise. Accepted patterns have no internal pair. -/
def boundaryArity (b : Finset (E ⊕ Fin 4)) : ℕ :=
  if (exceptionalLabels b).Nonempty then 1 else 2

@[simp] theorem exceptionalLabels_exceptional (z : E) (i : Fin 4) :
    exceptionalLabels {Sum.inl z, Sum.inr i} = {z} := by
  ext w
  simp [exceptionalLabels]

@[simp] theorem boundaryArity_exceptional (z : E) (i : Fin 4) :
    boundaryArity (E := E) {Sum.inl z, Sum.inr i} = 1 := by
  simp [boundaryArity]

@[simp] theorem exceptionalLabels_joining (p : LabelPair) :
    exceptionalLabels (p.val.image (Sum.inr : Fin 4 → E ⊕ Fin 4)) = ∅ := by
  ext z
  simp [exceptionalLabels]

@[simp] theorem boundaryArity_joining (p : LabelPair) :
    boundaryArity (p.val.image (Sum.inr : Fin 4 → E ⊕ Fin 4)) = 2 := by
  simp [boundaryArity]

theorem boundaryEdges_of_no_internal (P : Pattern E) (hP : P.internalPairs = ∅) :
    P.boundaryEdges =
      univ.image (fun z : E => {Sum.inl z,Sum.inr (P.assignment z)}) ∪
      P.forest.image (fun p => p.val.image (Sum.inr : Fin 4 → E ⊕ Fin 4)) := by
  simp [Pattern.boundaryEdges,Pattern.Paired,hP]

theorem boundaryEdge_card (P : Pattern E) (hP : P.internalPairs = ∅)
    (b : Finset (E ⊕ Fin 4)) (hb : b ∈ P.boundaryEdges) : b.card = 2 := by
  rw [boundaryEdges_of_no_internal P hP] at hb
  rcases mem_union.mp hb with hb | hb
  · obtain ⟨z,_hz,rfl⟩ := mem_image.mp hb
    simp
  · obtain ⟨p,_hp,rfl⟩ := mem_image.mp hb
    rw [card_image_of_injective _ Sum.inr_injective,p.property]

/-- Each exceptional label determines its unique edge in an accepted pattern. -/
theorem boundaryEdge_of_exceptional (P : Pattern E) (hP : P.internalPairs = ∅)
    (b : Finset (E ⊕ Fin 4)) (hb : b ∈ P.boundaryEdges) (z : E)
    (hz : Sum.inl z ∈ b) : b = {Sum.inl z,Sum.inr (P.assignment z)} := by
  rw [boundaryEdges_of_no_internal P hP] at hb
  rcases mem_union.mp hb with hb | hb
  · obtain ⟨w,_hw,rfl⟩ := mem_image.mp hb
    have hzw : z = w := by simpa using hz
    subst w
    rfl
  · obtain ⟨p,_hp,rfl⟩ := mem_image.mp hb
    simp at hz

/-- Distinct quotient edges of an accepted pattern share no exceptional label. -/
theorem exceptionalLabels_disjoint (P : Pattern E) (hP : P.internalPairs = ∅)
    (b c : Finset (E ⊕ Fin 4)) (hb : b ∈ P.boundaryEdges) (hc : c ∈ P.boundaryEdges)
    (hne : b ≠ c) : Disjoint (exceptionalLabels b) (exceptionalLabels c) := by
  apply disjoint_left.mpr
  intro z hz hz'
  exact hne ((boundaryEdge_of_exceptional P hP b hb z (mem_filter.mp hz).2).trans
    (boundaryEdge_of_exceptional P hP c hc z (mem_filter.mp hz').2).symm)

/-- Every exceptional label occurs in its assigned boundary edge. -/
theorem assignment_edge_mem (P : Pattern E) (hP : P.internalPairs = ∅) (z : E) :
    {Sum.inl z,Sum.inr (P.assignment z)} ∈ P.boundaryEdges := by
  rw [boundaryEdges_of_no_internal P hP]
  exact mem_union_left _ (mem_image.mpr ⟨z,mem_univ _,rfl⟩)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The finite forest criterion on the four labels bounds its size by three. -/
theorem leafForest_card_le : ∀ F : Finset LabelPair, LeafForest F → F.card ≤ 3 := by
  decide

/-- An accepted pattern has at most one core endpoint per exceptional
vertex and at most six from its joining forest. -/
theorem boundaryArity_sum_le (P : Pattern E) (hP : P.internalPairs = ∅)
    (hforest : LeafForest P.forest) :
    ∑ b ∈ P.boundaryEdges, boundaryArity b ≤ Fintype.card E + 6 := by
  rw [boundaryEdges_of_no_internal P hP]
  have hleft : (∑ b ∈ univ.image (fun z : E => {Sum.inl z,Sum.inr (P.assignment z)}),
      boundaryArity (E := E) b) ≤ Fintype.card E := by
    calc
      _ ≤ ∑ z : E, boundaryArity (E := E) {Sum.inl z,Sum.inr (P.assignment z)} :=
        Finset.sum_image_le_of_nonneg (fun _ _ => Nat.zero_le _)
      _ = Fintype.card E := by simp
  have hright : (∑ b ∈ P.forest.image (fun p =>
      p.val.image (Sum.inr : Fin 4 → E ⊕ Fin 4)), boundaryArity b) ≤ 6 := by
    calc
      _ ≤ ∑ p ∈ P.forest, boundaryArity (p.val.image (Sum.inr : Fin 4 → E ⊕ Fin 4)) :=
        Finset.sum_image_le_of_nonneg (fun _ _ => Nat.zero_le _)
      _ = P.forest.card * 2 := by simp
      _ ≤ 6 := by have h := leafForest_card_le P.forest hforest; omega
  have hunion := Finset.sum_union_inter
    (s₁ := univ.image (fun z : E => ({Sum.inl z,Sum.inr (P.assignment z)} : Finset (E ⊕ Fin 4))))
    (s₂ := P.forest.image (fun p => p.val.image (Sum.inr : Fin 4 → E ⊕ Fin 4)))
    (f := boundaryArity (E := E))
  omega

end Overfull.Patterns
