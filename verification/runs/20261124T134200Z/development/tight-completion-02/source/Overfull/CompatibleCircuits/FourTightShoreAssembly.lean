import Overfull.CompatibleCircuits.FourTightShoreBlocks
import Overfull.CompatibleCircuits.FourTightShorePieceGeometry
import Overfull.CompatibleCircuits.FourTightShoreExpansion

/-!
# Restoring the actual inside pieces in the outside partition

Every surviving redirected copy selects its unique inside piece. Exact
boundary-pair identities prove that these selected blocks are disjoint,
have the outside graph's degrees and classes, and meet the shore only
through the common designated incidence class at the anchor.
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

/-- A piece contains at most one actual copy surviving the outside
contraction: that copy is its unique complementary boundary incidence. -/
theorem outside_copies_eq_of_mem (hw : w ∉ X) {D : Finset E} (hD : D ∈ P.parts)
    (e f : joiningCopies G (shoreIntoLabel X w)) (he : e.val ∈ D) (hf : f.val ∈ D) :
    e = f := by
  have heB := P.outside_copy_in_complement G classOf hw hD e he
  have hfB := P.outside_copy_in_complement G classOf hw hD f hf
  obtain ⟨a,_,_,_,_,hB⟩ := P.boundary_pair_of_complement G classOf hD heB
  have hfe : f.val = e.val := by rw [hB] at hfB; exact mem_singleton.mp hfB
  exact Subtype.ext hfe.symm

/-- Distinct surviving actual copies select disjoint original blocks. -/
theorem outsideBlock_disjoint (hw : w ∉ X)
    (e f : joiningCopies G (shoreIntoLabel X w)) (hef : e ≠ f) :
    Disjoint (P.outsideBlock G classOf e) (P.outsideBlock G classOf f) := by
  classical
  rcases P.outsideBlock_cases G classOf e with ⟨heP,_⟩ | ⟨heS,heN⟩ <;>
    rcases P.outsideBlock_cases G classOf f with ⟨hfP,_⟩ | ⟨hfS,hfN⟩
  · apply P.disjoint _ heP _ hfP
    intro heq
    exact hef (P.outside_copies_eq_of_mem G classOf hw heP e f
      (P.outsideBlock_contains_self G classOf e)
      (heq.symm ▸ P.outsideBlock_contains_self G classOf f))
  · rw [hfS]
    apply disjoint_left.mpr
    intro a ha haf
    have haf := mem_singleton.mp haf
    subst a
    exact hfN (P.copy_touches G classOf heP ha)
  · rw [heS]
    apply disjoint_left.mpr
    intro a hae ha
    have hae := mem_singleton.mp hae
    subst a
    exact heN (P.copy_touches G classOf hfP ha)
  · rw [heS,hfS]
    apply disjoint_left.mpr
    intro a hae haf
    exact hef (Subtype.ext ((mem_singleton.mp hae).symm.trans (mem_singleton.mp haf)))

/-- Every selected block is compatible in the original graph. -/
theorem outsideBlock_compatible (e : joiningCopies G (shoreIntoLabel X w)) :
    G.Compatible classOf (P.outsideBlock G classOf e) := by
  rcases P.outsideBlock_cases G classOf e with ⟨heP,_⟩ | ⟨heS,_⟩
  · exact P.compatible _ heP
  · rw [heS]
    intro v a ha _ b hb _ _
    exact (mem_singleton.mp ha).trans (mem_singleton.mp hb).symm

/-- The restored original blocks have even degree inside the shore. -/
theorem outsideBlock_inner_even (e : joiningCopies G (shoreIntoLabel X w))
    (v : V) (hv : v ∈ X) : Even (G.degreeOn (P.outsideBlock G classOf e) v) := by
  classical
  rcases P.outsideBlock_cases G classOf e with ⟨heP,_⟩ | ⟨heS,heN⟩
  · exact P.even_inside _ heP v hv
  · have hnot : v ∉ G.edge e.val := by
      intro hve
      apply heN
      rcases (G.incident_iff e.val v).mp hve with h | h
      · exact Or.inl (h.symm ▸ hv)
      · exact Or.inr (h.symm ▸ hv)
    rw [heS]
    simp [degreeOn,hnot]

/-- Outside the shore, each block has precisely the degree of its one
corresponding outside edge copy. -/
theorem outsideBlock_outer_degree (hw : w ∉ X)
    (e : joiningCopies G (shoreIntoLabel X w)) (v : V) (hv : v ∉ X) :
    G.degreeOn (P.outsideBlock G classOf e) v =
      if v ∈ (tightShoreOutsideGraph G X w).edge e then 1 else 0 := by
  classical
  rcases P.outsideBlock_cases G classOf e with ⟨heP,_⟩ | ⟨heS,heN⟩
  · exact P.outside_degree_eq_indicator G classOf hw heP e
      (P.outsideBlock_contains_self G classOf e) v hv
  · rw [heS,tightShoreOutside_edge_of_not_touch G X w e heN]
    simp [degreeOn]

/-- Every outside incidence of a block has the exact original class
recorded at the corresponding contracted copy. -/
theorem outsideBlock_outer_incidence_class (hw : w ∉ X)
    (e : joiningCopies G (shoreIntoLabel X w)) (v : V) (hv : v ∉ X)
    (f : E) (hf : f ∈ P.outsideBlock G classOf e) (hvf : v ∈ G.edge f) :
    v ∈ (tightShoreOutsideGraph G X w).edge e ∧
      tightShoreOutsideClass G classOf X w k v e = classOf v f := by
  rcases P.outsideBlock_cases G classOf e with ⟨heP,_⟩ | ⟨heS,_⟩
  · exact P.outside_incidence_class G classOf hw heP e
      (P.outsideBlock_contains_self G classOf e) v hv f hf hvf
  · rw [heS] at hf
    have hfe := mem_singleton.mp hf
    subst f
    exact tightShoreOutside_original_incidence G classOf X w k e v hv hvf

/-- Any block meeting the shore has the common designated outside class
at the anchor. A compatible outside circuit can use at most one such block. -/
theorem outsideBlock_common_class
    (e : joiningCopies G (shoreIntoLabel X w)) (v : V) (hv : v ∈ X)
    (f : E) (hf : f ∈ P.outsideBlock G classOf e) (hvf : v ∈ G.edge f) :
    w ∈ (tightShoreOutsideGraph G X w).edge e ∧
      tightShoreOutsideClass G classOf X w k w e = k := by
  rcases P.outsideBlock_cases G classOf e with ⟨_,heT⟩ | ⟨heS,heN⟩
  · exact tightShoreOutside_redirected_incidence G classOf X w k e heT
  · rw [heS] at hf
    have hfe := mem_singleton.mp hf
    subst f
    exfalso
    apply heN
    rcases (G.incident_iff e.val v).mp hvf with h | h
    · exact Or.inl (h.symm ▸ hv)
    · exact Or.inr (h.symm ▸ hv)

/-- The exact block-restoration data are constructed from the original
inside partition and the explicit outside contraction. -/
def outsideExpansion (hw : w ∉ X) :
    CompatibleBlockExpansion G (tightShoreOutsideGraph G X w) classOf
      (tightShoreOutsideClass G classOf X w k) univ (P.outsideBlock G classOf)
      X w k where
  disjoint := fun e _ f _ hef => P.outsideBlock_disjoint G classOf hw e f hef
  compatible := fun e _ => P.outsideBlock_compatible G classOf e
  inner_even := fun e _ v hv => P.outsideBlock_inner_even G classOf e v hv
  outer_degree := fun e _ v hv => P.outsideBlock_outer_degree G classOf hw e v hv
  outer_class := by
    intro e _ v hv f hf hvf
    have heinfo := P.outsideBlock_outer_incidence_class G classOf hw e v hv f hf hvf
    refine ⟨heinfo.1,?_⟩
    intro e' _ f' hf' hvf' hclass
    have hfinfo := P.outsideBlock_outer_incidence_class G classOf hw e' v hv f' hf' hvf'
    exact heinfo.2.trans (hclass.trans hfinfo.2.symm)
  common_class := fun e _ v hv f hf hvf =>
    P.outsideBlock_common_class G classOf e v hv f hf hvf

end TightShorePieces

end Overfull.FourOdd
