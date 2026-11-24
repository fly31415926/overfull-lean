import Overfull.CompatibleCircuits.FourTightShoreBlocks
import Overfull.CompatibleCircuits.FourTightShoreExpansion

/-!
# Exact coverage after the two tight-shore partitions

Every original copy either belongs to a block indexed by a surviving
outside copy or to a saved inside piece. These families are disjoint and
their union is the entire original edge-copy set. The final construction
combines their actual compatible-circuit partitions.
-/

noncomputable section

namespace Overfull.FourOdd

open Finset Classical Overfull.Multigraph

variable {V E K : Type*} [Fintype E]
    (G : Multigraph V E) (classOf : V → E → K)
    {X : Finset V} {w : V} {k : K}

namespace TightShorePieces

variable (P : TightShorePieces G classOf X w k)

/-- Copies entirely outside the shore always survive the outside contraction. -/
theorem outside_copy_of_not_touch {e : E}
    (htouch : ¬ (G.firstEnd e ∈ X ∨ G.secondEnd e ∈ X)) :
    e ∈ joiningCopies G (shoreIntoLabel X w) := by
  apply (mem_joiningCopies G (shoreIntoLabel X w) e).mpr
  simpa only [shoreIntoLabel, if_neg (not_or.mp htouch).1,
    if_neg (not_or.mp htouch).2] using G.endpoints_distinct e

/-- The expanded outside blocks and saved inside pieces cover every actual
original edge copy, including copies whose contraction would be a loop. -/
theorem outsideBlock_union_closedParts_cover :
    ((univ : Finset (joiningCopies G (shoreIntoLabel X w))).biUnion
      (P.outsideBlock G classOf)) ∪ (P.closedParts G classOf).biUnion id = univ := by
  apply eq_univ_iff_forall.mpr
  intro e
  by_cases ht : G.firstEnd e ∈ X ∨ G.secondEnd e ∈ X
  · obtain ⟨D, hD, heD⟩ := P.exists_part_of_touch G classOf ht
    by_cases hclosed : Disjoint D (joiningCopies G (shoreIntoLabel X w))
    · apply mem_union_right
      exact mem_biUnion.mpr ⟨D, (P.mem_closedParts G classOf D).mpr ⟨hD, hclosed⟩, heD⟩
    · have hex : ∃ f, f ∈ D ∧ f ∈ joiningCopies G (shoreIntoLabel X w) := by
        by_contra! h
        exact hclosed (disjoint_left.mpr h)
      obtain ⟨f, hfD, hfJ⟩ := hex
      let i : joiningCopies G (shoreIntoLabel X w) := ⟨f, hfJ⟩
      apply mem_union_left
      apply mem_biUnion.mpr
      refine ⟨i, mem_univ _, ?_⟩
      rw [P.outsideBlock_eq_of_mem G classOf i hD hfD]
      exact heD
  · have heJ := outside_copy_of_not_touch G (w := w) ht
    let i : joiningCopies G (shoreIntoLabel X w) := ⟨e, heJ⟩
    apply mem_union_left
    exact mem_biUnion.mpr ⟨i, mem_univ _, P.outsideBlock_contains_self G classOf i⟩

/-- Saved pieces and expanded outside blocks share no original copy. -/
theorem outsideBlock_disjoint_closedParts :
    Disjoint ((univ : Finset (joiningCopies G (shoreIntoLabel X w))).biUnion
      (P.outsideBlock G classOf)) ((P.closedParts G classOf).biUnion id) := by
  apply disjoint_left.mpr
  intro e heB heC
  obtain ⟨i, _, hei⟩ := mem_biUnion.mp heB
  obtain ⟨D, hD, heD⟩ := mem_biUnion.mp heC
  exact disjoint_left.mp (P.closedPart_disjoint_outsideBlock G classOf hD i) heD hei

end TightShorePieces

end Overfull.FourOdd
