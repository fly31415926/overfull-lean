import Overfull.CompatibleCircuits.FourTightShorePairing
import Overfull.CompatibleCircuits.FourTightShoreOutsideGeometry

/-!
# Original-copy blocks indexed by the outside contraction

A surviving copy touching the shore selects the unique inside piece
containing it. An exterior copy selects its original singleton. Copies
remain distinct throughout this selection.
-/

noncomputable section

namespace Overfull.FourOdd

open Finset Classical
open Overfull.Multigraph

variable {V E K : Type*} [Fintype E]
    (G : Multigraph V E) (classOf : V → E → K)
    {X : Finset V} {w : V} {k : K}

namespace TightShorePieces

variable (P : TightShorePieces G classOf X w k)

/-- Every original copy touching the shore belongs to an inside piece. -/
theorem exists_part_of_touch {e : E}
    (htouch : G.firstEnd e ∈ X ∨ G.secondEnd e ∈ X) :
    ∃ D ∈ P.parts, e ∈ D := by
  have he : e ∈ univ.filter (fun f => G.firstEnd f ∈ X ∨ G.secondEnd f ∈ X) :=
    mem_filter.mpr ⟨mem_univ _,htouch⟩
  rw [← P.cover] at he
  exact mem_biUnion.mp he

/-- The original-copy block indexed by one surviving outside copy. -/
def outsideBlock (e : joiningCopies G (shoreIntoLabel X w)) : Finset E :=
  if h : ∃ D ∈ P.parts, e.val ∈ D then Classical.choose h else {e.val}

/-- Every block contains the exact surviving copy indexing it. -/
theorem outsideBlock_contains_self (e : joiningCopies G (shoreIntoLabel X w)) :
    e.val ∈ P.outsideBlock G classOf e := by
  unfold outsideBlock
  split_ifs with h
  · exact (Classical.choose_spec h).2
  · exact mem_singleton_self _

/-- When a surviving copy belongs to a piece, that exact piece is its block. -/
theorem outsideBlock_eq_of_mem (e : joiningCopies G (shoreIntoLabel X w))
    {D : Finset E} (hD : D ∈ P.parts) (he : e.val ∈ D) :
    P.outsideBlock G classOf e = D := by
  classical
  have hex : ∃ D ∈ P.parts, e.val ∈ D := ⟨D,hD,he⟩
  rw [outsideBlock,dif_pos hex]
  exact P.part_eq_of_common_copy G classOf
    (Classical.choose_spec hex).1 hD (Classical.choose_spec hex).2 he

/-- Exterior copies select their original singleton, without introducing
an inside copy. -/
theorem outsideBlock_eq_singleton_of_no_touch
    (e : joiningCopies G (shoreIntoLabel X w))
    (htouch : ¬ (G.firstEnd e.val ∈ X ∨ G.secondEnd e.val ∈ X)) :
    P.outsideBlock G classOf e = {e.val} := by
  classical
  have hnone : ¬ ∃ D ∈ P.parts, e.val ∈ D := by
    rintro ⟨D,hD,he⟩
    exact htouch (P.copy_touches G classOf hD he)
  rw [outsideBlock,dif_neg hnone]

/-- Every block is an actual inside piece or an exterior singleton. -/
theorem outsideBlock_cases (e : joiningCopies G (shoreIntoLabel X w)) :
    (P.outsideBlock G classOf e ∈ P.parts ∧
      (G.firstEnd e.val ∈ X ∨ G.secondEnd e.val ∈ X)) ∨
    (P.outsideBlock G classOf e = {e.val} ∧
      ¬ (G.firstEnd e.val ∈ X ∨ G.secondEnd e.val ∈ X)) := by
  classical
  by_cases ht : G.firstEnd e.val ∈ X ∨ G.secondEnd e.val ∈ X
  · obtain ⟨D,hD,he⟩ := P.exists_part_of_touch G classOf ht
    exact Or.inl ⟨(P.outsideBlock_eq_of_mem G classOf e hD he).symm ▸ hD,ht⟩
  · exact Or.inr ⟨P.outsideBlock_eq_singleton_of_no_touch G classOf e ht,ht⟩

/-- The pieces with no surviving outside copy are saved separately. -/
def closedParts : Finset (Finset E) :=
  P.parts.filter (fun D => Disjoint D (joiningCopies G (shoreIntoLabel X w)))

@[simp] theorem mem_closedParts (D : Finset E) :
    D ∈ P.closedParts G classOf ↔
      D ∈ P.parts ∧ Disjoint D (joiningCopies G (shoreIntoLabel X w)) := by
  classical
  simp [closedParts]

/-- Every selected block is nonempty. -/
theorem outsideBlock_nonempty (e : joiningCopies G (shoreIntoLabel X w)) :
    (P.outsideBlock G classOf e).Nonempty :=
  ⟨e.val,P.outsideBlock_contains_self G classOf e⟩

/-- A saved piece is disjoint from every selected outside block. -/
theorem closedPart_disjoint_outsideBlock {D : Finset E}
    (hD : D ∈ P.closedParts G classOf)
    (e : joiningCopies G (shoreIntoLabel X w)) :
    Disjoint D (P.outsideBlock G classOf e) := by
  classical
  obtain ⟨hD,hclosed⟩ := (P.mem_closedParts G classOf D).mp hD
  rcases P.outsideBlock_cases G classOf e with ⟨hblock,_⟩ | ⟨hblock,_⟩
  · apply P.disjoint D hD _ hblock
    intro heq
    apply disjoint_left.mp hclosed
      (heq.symm ▸ P.outsideBlock_contains_self G classOf e)
    exact e.property
  · rw [hblock]
    exact hclosed.mono_left (subset_refl _ ) |>.mono_right (singleton_subset_iff.mpr e.property)

end TightShorePieces

end Overfull.FourOdd
