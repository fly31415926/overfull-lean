import Overfull.Patterns.Boundary

/-!
# Reserved exceptional pairs are distinct actual neighbors

Simplicity identifies an exceptional--core quotient pool with the actual
neighbor set inside that core. No matching or weight assumptions are used
in this graph-level identity.
-/

noncomputable section
namespace Overfull.Patterns
open Finset Classical SimpleGraph Compression FractionalMatching

variable {V I : Type*} [Fintype V] [DecidableEq V]

/-- A core quotient label has exactly the vertices of that actual core
as its inverse image. -/
theorem boundaryLabel_eq_core_iff (U : I → Finset V) (Z : Finset V)
    (code : I ↪ Fin 4)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hUZ : ∀ i, Disjoint (U i) Z)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i) (i : I) (v : V) :
    boundaryLabel U Z code v = Sum.inr (code i) ↔ v ∈ U i := by
  rw [← Finset.mem_singleton,← mem_wholeUnion,
    wholeUnion_single_core U Z code hdisjoint hUZ hcover i]

/-- The exact cardinality of an exceptional--core quotient edge pool. -/
theorem exceptional_pool_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : I → Finset V) (Z : Finset V) (code : I ↪ Fin 4)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hUZ : ∀ i, Disjoint (U i) Z)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i) (z : Z) (i : I) :
    ((univ : Finset G.edgeSet).filter (fun e =>
      labelledEdge G U Z code e = {Sum.inl z,Sum.inr (code i)})).card =
        (G.neighborFinset z.val ∩ U i).card := by
  classical
  let N := G.neighborFinset z.val ∩ U i
  let edge : N → G.edgeSet := fun w =>
    ⟨s(z.val,w.val),(G.mem_neighborFinset z.val w.val).mp (mem_inter.mp w.property).1⟩
  have hinj : Function.Injective edge := by
    intro x y hxy
    have hh := congrArg Subtype.val hxy
    change s(z.val,x.val) = s(z.val,y.val) at hh
    apply Subtype.ext
    rcases Sym2.eq_iff.mp hh with hh | hh
    · exact hh.2
    · exact hh.2.trans hh.1
  have heq : ((univ : Finset G.edgeSet).filter (fun e =>
      labelledEdge G U Z code e = {Sum.inl z,Sum.inr (code i)})) = univ.image edge := by
    ext e
    constructor
    · intro he
      have hlabel := (mem_filter.mp he).2
      have hz : z.val ∈ e.val := (inl_mem_labelledEdge G U Z code e z).mp (by
        rw [hlabel]
        simp)
      obtain ⟨v,hv⟩ := Sym2.mem_iff_exists.mp hz
      have hadj : G.Adj z.val v := by
        change s(z.val,v) ∈ G.edgeSet
        simpa only [hv] using e.property
      have hmem : Sum.inr (code i) ∈ labelledEdge G U Z code e := by
        rw [hlabel]
        simp
      have hcore : boundaryLabel U Z code v = Sum.inr (code i) := by
        have hh : Sum.inr (code i) = boundaryLabel U Z code v := by
          simpa [labelledEdge,hv,Sym2.toFinset_mk_eq] using hmem
        exact hh.symm
      have hvU := (boundaryLabel_eq_core_iff U Z code hdisjoint hUZ hcover i v).mp hcore
      let w : N := ⟨v,mem_inter.mpr ⟨(G.mem_neighborFinset z.val v).mpr hadj,hvU⟩⟩
      refine mem_image.mpr ⟨w,mem_univ _,?_⟩
      apply Subtype.ext
      exact hv.symm
    · intro he
      obtain ⟨w,_hw,rfl⟩ := mem_image.mp he
      refine mem_filter.mpr ⟨mem_univ _,?_⟩
      have hcore := (boundaryLabel_eq_core_iff U Z code hdisjoint hUZ hcover i w.val).mpr
        (mem_inter.mp w.property).2
      simp [labelledEdge,edge,Sym2.toFinset_mk_eq,hcore]
  rw [heq,Finset.card_image_of_injective _ hinj,card_univ,Fintype.card_coe]

/-- Reserving `r` distinct copies of each assigned exceptional pair gives
at least `r` distinct actual neighbors for every absorbed vertex. -/
theorem reserved_pairs_give_neighbors (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : I → Finset V) (Z : Finset V) (code : I ↪ Fin 4)
    (P : Pattern Z) (assignment : V → I) (r : ℕ)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hUZ : ∀ i, Disjoint (U i) Z)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (hassignment : ∀ z : Z, P.assignment z = code (assignment z.val))
    (hreserve : ∀ z : Z, r ≤ ((univ : Finset G.edgeSet).filter (fun e =>
      labelledEdge G U Z code e = {Sum.inl z,Sum.inr (P.assignment z)})).card) :
    ∀ z ∈ Z, r ≤ (G.neighborFinset z ∩ U (assignment z)).card := by
  intro z hz
  have hh := hreserve ⟨z,hz⟩
  rw [hassignment ⟨z,hz⟩,exceptional_pool_card G U Z code hdisjoint hUZ hcover] at hh
  exact hh

end Overfull.Patterns
