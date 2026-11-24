import Overfull.CompatibleCircuits.FourTightShoreInside

/-!
# Original-copy pieces of the tight-shore inside partition

The constructed quotient circuits give pairwise disjoint original-copy
pieces. Every piece is compatible in the original graph and has even
degree at every interior vertex. Its boundary is empty, or consists of
one copy of the prescribed tight class and one complementary copy.
-/

noncomputable section

namespace Overfull.FourOdd

open Finset Classical
open Overfull.Multigraph

variable {V E K : Type*} [Fintype V] [Fintype E]
    (G : Multigraph V E) (classOf : V → E → K)

/-- Interior selected degrees are unchanged by the collapse. -/
theorem tightShoreInside_degreeOn_inside (X : Finset V)
    (D : Finset (joiningCopies G (shoreCollapseLabel X))) (x : X) :
    (tightShoreInsideGraph G X).degreeOn D (some x) =
      G.degreeOn (D.image Subtype.val) x.val := by
  classical
  change (joiningQuotient G (shoreCollapseLabel X)).degreeOn D (some x) = _
  rw [joiningQuotient_degreeOn_eq_cut,labelShore_shoreCollapseLabel_inside,
    G.cutOn_singleton_card]

/-- The selected apex degree counts exactly the original boundary copies. -/
theorem tightShoreInside_degreeOn_apex (X : Finset V)
    (D : Finset (joiningCopies G (shoreCollapseLabel X))) :
    (tightShoreInsideGraph G X).degreeOn D none =
      (G.cutOn (D.image Subtype.val) X).card := by
  classical
  change (joiningQuotient G (shoreCollapseLabel X)).degreeOn D none = _
  rw [joiningQuotient_degreeOn_eq_cut,labelShore_shoreCollapseLabel_apex,G.cutOn_compl]

/-- The designated class at the apex counts exactly the original class
copies in the boundary of this selected piece. -/
theorem tightShoreInside_classCutOn_apex (X : Finset V) (w : V) (k : K)
    (hw : w ∉ X) (D : Finset (joiningCopies G (shoreCollapseLabel X))) :
    ((tightShoreInsideGraph G X).classCutOn
      (joiningIncidenceClass G (shoreCollapseLabel X) classOf) D none (w,k) {none}).card =
      (G.classCutOn classOf (D.image Subtype.val) w k X).card := by
  classical
  have h := congrArg Finset.card
    (joiningIncidenceClass_classCutOn_image_on G (shoreCollapseLabel X) classOf
      D none w k {none})
  rw [card_image_of_injective _ Subtype.val_injective,
    if_pos ((shoreCollapseLabel_eq_none X w).mpr hw),
    labelShore_shoreCollapseLabel_apex,G.classCutOn_compl] at h
  exact h

omit [Fintype V] in
/-- Every inside piece is compatible in the original graph, including
at both original outside endpoints of its boundary. -/
theorem tightShoreInside_piece_compatible (X : Finset V) (w : V) (k : K)
    {D : Finset (joiningCopies G (shoreCollapseLabel X))}
    (hcomp : (tightShoreInsideGraph G X).Compatible
      (tightShoreInsideClass G classOf X w k) D) :
    G.Compatible classOf (D.image Subtype.val) := by
  apply joiningIncidenceClass_compatible_image G (shoreCollapseLabel X) classOf
  exact hcomp.of_coarsenTightClassAt (tightShoreInsideGraph G X)
    (joiningIncidenceClass G (shoreCollapseLabel X) classOf) none (w,k)

/-- The interior degrees of each constructed piece are even. -/
theorem tightShoreInside_piece_even_inside (X : Finset V)
    {D : Finset (joiningCopies G (shoreCollapseLabel X))}
    (hD : (tightShoreInsideGraph G X).IsCircuit D) (x : V) (hx : x ∈ X) :
    Even (G.degreeOn (D.image Subtype.val) x) := by
  rw [← tightShoreInside_degreeOn_inside G X D ⟨x,hx⟩]
  exact hD.even_degreeOn _ _

/-- Every piece has no boundary, or exactly one A-copy and one B-copy.
Here A is the original prescribed class cut and B its complement. -/
theorem tightShoreInside_piece_boundary (X : Finset V) (w : V) (k : K)
    (hw : w ∉ X) {D : Finset (joiningCopies G (shoreCollapseLabel X))}
    (hD : (tightShoreInsideGraph G X).IsCircuit D)
    (hcomp : (tightShoreInsideGraph G X).Compatible
      (tightShoreInsideClass G classOf X w k) D) :
    (G.cutOn (D.image Subtype.val) X).card = 0 ∨
      ((G.cutOn (D.image Subtype.val) X).card = 2 ∧
        (G.classCutOn classOf (D.image Subtype.val) w k X).card = 1 ∧
        (G.cutOn (D.image Subtype.val) X \
          G.classCutOn classOf (D.image Subtype.val) w k X).card = 1) := by
  classical
  let H := tightShoreInsideGraph G X
  by_cases hv : none ∈ H.edgeSupport D
  · have hdegree := hD.2.1 none hv
    rw [tightShoreInside_degreeOn_apex] at hdegree
    have hcounts := hD.coarsenTightClassAt_counts H
      (joiningIncidenceClass G (shoreCollapseLabel X) classOf) none (w,k) hcomp hv
    have ha : (G.classCutOn classOf (D.image Subtype.val) w k X).card = 1 := by
      rw [← tightShoreInside_classCutOn_apex G classOf X w k hw D,
        H.classCutOn_singleton_self]
      exact hcounts.1
    have hsub : G.classCutOn classOf (D.image Subtype.val) w k X ⊆
        G.cutOn (D.image Subtype.val) X := filter_subset _ _
    have hsum := card_sdiff_add_card_eq_card hsub
    exact Or.inr ⟨hdegree,ha,by omega⟩
  · apply Or.inl
    rw [← tightShoreInside_degreeOn_apex]
    exact H.degreeOn_eq_zero_of_not_mem hv

/-- A finite exact-copy decomposition suitable for the outside suppression
and restoration construction. -/
structure TightShorePieces (X : Finset V) (w : V) (k : K) where
  parts : Finset (Finset E)
  nonempty : ∀ D ∈ parts, D.Nonempty
  compatible : ∀ D ∈ parts, G.Compatible classOf D
  even_inside : ∀ D ∈ parts, ∀ x ∈ X, Even (G.degreeOn D x)
  boundary : ∀ D ∈ parts,
    (G.cutOn D X).card = 0 ∨
      ((G.cutOn D X).card = 2 ∧ (G.classCutOn classOf D w k X).card = 1 ∧
        (G.cutOn D X \ G.classCutOn classOf D w k X).card = 1)
  card_le : ∀ D ∈ parts, D.card ≤ X.card + 1
  disjoint : ∀ D ∈ parts, ∀ D' ∈ parts, D ≠ D' → Disjoint D D'
  cover : parts.biUnion id =
    univ.filter (fun e => G.firstEnd e ∈ X ∨ G.secondEnd e ∈ X)

/-- Transport the inside partition to exact original-copy pieces. -/
def tightShorePieces_of_partition (X : Finset V) (w : V) (k : K) (hw : w ∉ X)
    (P : (tightShoreInsideGraph G X).CompatibleCircuitPartition
      (tightShoreInsideClass G classOf X w k) univ) :
    TightShorePieces G classOf X w k where
  parts := P.parts.image (fun D => D.image Subtype.val)
  nonempty := by
    intro D hD
    obtain ⟨A,hA,rfl⟩ := mem_image.mp hD
    exact (P.circuit A hA).1.image _
  compatible := by
    intro D hD
    obtain ⟨A,hA,rfl⟩ := mem_image.mp hD
    exact tightShoreInside_piece_compatible G classOf X w k (P.compatible A hA)
  even_inside := by
    intro D hD x hx
    obtain ⟨A,hA,rfl⟩ := mem_image.mp hD
    exact tightShoreInside_piece_even_inside G X (P.circuit A hA) x hx
  boundary := by
    intro D hD
    obtain ⟨A,hA,rfl⟩ := mem_image.mp hD
    exact tightShoreInside_piece_boundary G classOf X w k hw
      (P.circuit A hA) (P.compatible A hA)
  card_le := by
    intro D hD
    obtain ⟨A,hA,rfl⟩ := mem_image.mp hD
    rw [card_image_of_injective _ Subtype.val_injective]
    simpa using (P.circuit A hA).card_le
  disjoint := by
    intro D hD D' hD' hne
    obtain ⟨A,hA,rfl⟩ := mem_image.mp hD
    obtain ⟨B,hB,rfl⟩ := mem_image.mp hD'
    apply disjoint_left.mpr
    intro e he he'
    obtain ⟨a,ha,rfl⟩ := mem_image.mp he
    obtain ⟨b,hb,hab⟩ := mem_image.mp he'
    have hab' : b = a := Subtype.val_injective hab
    apply disjoint_left.mp (P.disjoint A hA B hB (fun h => hne (h ▸ rfl))) ha
    exact hab' ▸ hb
  cover := by
    calc
      _ = (P.parts.biUnion id).image Subtype.val := by
        ext e
        simp
        aesop
      _ = (univ : Finset (joiningCopies G (shoreCollapseLabel X))).image Subtype.val := by
        convert congrArg (Finset.image Subtype.val) P.cover using 1
        ext e
        simp only [mem_image,mem_biUnion,id_eq]
      _ = joiningCopies G (shoreCollapseLabel X) := by ext e; simp
      _ = _ := joiningCopies_shoreCollapseLabel G X

/-- Construct exact original pieces for every tight shore with at most
two vertices, from the original admissibility and degree parity alone. -/
theorem exists_tightShorePieces (X : Finset V) (hX : X.card ≤ 2) (w : V) (k : K)
    (hadmissible : G.AdmissibleOn classOf univ)
    (heven : ∀ v, Even (G.degreeOn univ v)) (hw : w ∉ X)
    (htight : 2 * (G.classCutOn classOf univ w k X).card = (G.cutOn univ X).card) :
    Nonempty (TightShorePieces G classOf X w k) := by
  obtain ⟨P⟩ := exists_tightShoreInside_partition G classOf X hX w k
    hadmissible heven hw htight
  exact ⟨tightShorePieces_of_partition G classOf X w k hw P⟩

end Overfull.FourOdd
