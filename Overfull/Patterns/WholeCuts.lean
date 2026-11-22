import Overfull.Patterns.Boundary
import Overfull.ForceMatching.Family

/-!
# Whole-union cut parity of boundary patterns

The quotient shores are precisely unions of whole cores and selected
exceptional singletons. An encoded compressed matching leaves an even
number of vertices uncovered on each such shore, giving the required
odd-cut lower bound for its finite pattern.
-/

noncomputable section
namespace Overfull.Patterns

open Finset Classical SimpleGraph Compression FractionalMatching MatchingProbability
open scoped BigOperators

variable {V I : Type*} [Fintype V]

/-- A union that is whole on each core is the inverse image of the labels
of its vertices. This does not require all four labels to be occupied. -/
theorem wholeUnion_image_labels (U : I → Finset V) (Z : Finset V)
    (code : I ↪ Fin 4) (X : Finset V)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (hwhole : ∀ i, U i ⊆ X ∨ Disjoint (U i) X) :
    wholeUnion U Z code (X.image (boundaryLabel U Z code)) = X := by
  classical
  ext v
  rw [mem_wholeUnion]
  constructor
  · intro hv
    obtain ⟨w,hw,hlabel⟩ := mem_image.mp hv
    by_cases hvZ : v ∈ Z
    · have hvlabel : boundaryLabel U Z code v = Sum.inl ⟨v,hvZ⟩ := by
        simp [boundaryLabel,hvZ]
      rw [hvlabel] at hlabel
      have hwv := (boundaryLabel_inl_iff U Z code w ⟨v,hvZ⟩).mp hlabel
      change w = v at hwv
      exact hwv ▸ hw
    · obtain ⟨i,hvi⟩ := (hcover v).resolve_left hvZ
      have hwZ : w ∉ Z := by
        intro hwZ
        rw [boundaryLabel_outside U Z code v hvZ] at hlabel
        simp [boundaryLabel,hwZ] at hlabel
      rw [boundaryLabel_outside U Z code w hwZ,
        boundaryLabel_outside U Z code v hvZ,Sum.inr.injEq] at hlabel
      have hwi : w ∈ U i := (coreLabel_eq_iff U Z code hdisjoint hcover hwZ i).mp
        (hlabel.trans (coreLabel_of_mem U code hdisjoint hvi))
      rcases hwhole i with hsub | hdisj
      · exact hsub hvi
      · exact False.elim (disjoint_left.mp hdisj hwi hw)
  · intro hv
    exact mem_image.mpr ⟨v,hv,rfl⟩

variable [Fintype I]

theorem quotient_of_wholeUnions (U : I → Finset V) (Z : Finset V)
    (code : I ↪ Fin 4) (X : Finset V)
    (hdisjoint : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hUZ : ∀ i, Disjoint (U i) Z)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (hX : X ∈ ForceMatching.wholeUnions U Z) :
    ∃ Q : Finset (Z ⊕ Fin 4), X = wholeUnion U Z code Q := by
  classical
  exact ⟨X.image (boundaryLabel U Z code),
    (wholeUnion_image_labels U Z code X (fun i j h => hdisjoint h) hcover
      (ForceMatching.wholeUnions_whole U Z X hdisjoint hUZ hX)).symm⟩

/-- Every quotient shore is an actual union of whole cores and selected
exceptional singletons. -/
theorem wholeUnion_mem_wholeUnions (U : I → Finset V) (Z : Finset V)
    (code : I ↪ Fin 4) (Q : Finset (Z ⊕ Fin 4))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hUZ : ∀ i, Disjoint (U i) Z)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i) :
    wholeUnion U Z code Q ∈ ForceMatching.wholeUnions U Z := by
  classical
  let A : Finset I := univ.filter (fun i => Sum.inr (code i) ∈ Q)
  let B : Finset V := Z.filter (fun v => boundaryLabel U Z code v ∈ Q)
  apply (ForceMatching.mem_wholeUnions U Z _).mpr
  refine ⟨A,B,filter_subset _ _,?_⟩
  ext v
  rw [mem_wholeUnion]
  by_cases hvZ : v ∈ Z
  · have hvA : v ∉ A.biUnion U := by
      intro hv
      obtain ⟨i,_hi,hvi⟩ := mem_biUnion.mp hv
      exact disjoint_left.mp (hUZ i) hvi hvZ
    rw [mem_union]
    simp only [hvA,false_or]
    simp [B,hvZ]
  · obtain ⟨i,hvi⟩ := (hcover v).resolve_left hvZ
    have hlabel : boundaryLabel U Z code v = Sum.inr (code i) :=
      (boundaryLabel_outside U Z code v hvZ).trans
        (congrArg Sum.inr (coreLabel_of_mem U code hdisjoint hvi))
    have hvB : v ∉ B := by simp [B,hvZ]
    rw [hlabel,mem_union]
    simp only [hvB,or_false]
    constructor
    · intro hi
      exact mem_biUnion.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,hi⟩,hvi⟩
    · intro hv
      obtain ⟨j,hj,hvj⟩ := mem_biUnion.mp hv
      have hij : i = j := by
        by_contra hh
        exact disjoint_left.mp (hdisjoint i j hh) hvi hvj
      subst j
      exact (mem_filter.mp hj).2

variable {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
/-- Even uncovered cores and covered exceptional vertices give even
uncovered order on every actual whole union. -/
theorem even_uncovered_wholeUnions (U : I → Finset V) (Z : Finset V)
    (F : G.Subgraph)
    (hdisjoint : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hcovered : (Z : Set V) ⊆ F.verts)
    (hparity : ∀ i, Even (((U i : Set V) \ F.verts).ncard))
    (X : Finset V) (hX : X ∈ ForceMatching.wholeUnions U Z) :
    Even (((X : Set V) \ F.verts).ncard) := by
  classical
  have hdiff (Y : Finset V) : ((Y : Set V) \ F.verts).ncard = (Y \ F.verts.toFinset).card := by
    have hh : (Y : Set V) \ F.verts = ((Y \ F.verts.toFinset : Finset V) : Set V) := by
      ext v
      simp
    rw [hh,Set.ncard_coe_finset]
  obtain ⟨A,B,hB,rfl⟩ := (ForceMatching.mem_wholeUnions U Z X).mp hX
  have heq : (A.biUnion U ∪ B) \ F.verts.toFinset =
      A.biUnion (fun i => U i \ F.verts.toFinset) := by
    ext v
    simp only [mem_sdiff,mem_union,mem_biUnion,Set.mem_toFinset]
    constructor
    · rintro ⟨hA | hvB,hvF⟩
      · obtain ⟨i,hi,hvi⟩ := hA
        exact ⟨i,hi,hvi,hvF⟩
      · exact False.elim (hvF (hcovered (hB hvB)))
    · rintro ⟨i,hi,hvi,hvF⟩
      exact ⟨Or.inl ⟨i,hi,hvi⟩,hvF⟩
  rw [hdiff,heq,Finset.card_biUnion]
  · have heven (i : I) : Even ((U i \ F.verts.toFinset).card) := by
      rw [← hdiff]
      exact hparity i
    clear hX heq
    induction A using Finset.induction_on with
    | empty => simp
    | @insert i A hi ih =>
      rw [sum_insert hi]
      exact (heven i).add ih
  · intro i _hi j _hj hij
    exact (hdisjoint hij).mono sdiff_subset sdiff_subset

/-- The whole-union cut parity used in the weighted residual argument. -/
theorem Encodes.whole_cut_parity
    {U : I → Finset V} {Z : Finset V} {code : I ↪ Fin 4}
    {F : G.Subgraph} {P : Pattern Z} (hP : Encodes G U Z code F P)
    (hdisjoint : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hUZ : ∀ i, Disjoint (U i) Z)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (hparity : ∀ i, Even (((U i : Set V) \ F.verts).ncard))
    (Q : Finset (Z ⊕ Fin 4)) :
    P.cutCount Q % 2 = (wholeUnion U Z code Q).card % 2 := by
  classical
  rw [← hP.whole_cut_count Q]
  apply (matching_uncovered_even_iff_cut_parity F hP.matching _).mp
  exact even_uncovered_wholeUnions U Z F hdisjoint hP.covered hparity _
    (wholeUnion_mem_wholeUnions U Z code Q (fun i j h => hdisjoint h) hUZ hcover)

theorem Encodes.odd_whole_cut_positive
    {U : I → Finset V} {Z : Finset V} {code : I ↪ Fin 4}
    {F : G.Subgraph} {P : Pattern Z} (hP : Encodes G U Z code F P)
    (hdisjoint : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hUZ : ∀ i, Disjoint (U i) Z)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (hparity : ∀ i, Even (((U i : Set V) \ F.verts).ncard))
    (Q : Finset (Z ⊕ Fin 4)) (hodd : (wholeUnion U Z code Q).card % 2 = 1) :
    1 ≤ P.cutCount Q := by
  classical
  have hh := hP.whole_cut_parity hdisjoint hUZ hcover hparity Q
  omega

end Overfull.Patterns
