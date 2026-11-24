import Overfull.CircuitPatterns.Result
import Overfull.Terminal.PartLabels

/-!
# Transport of the actual frequent-pattern record

The stored code becomes an equivalence when all four labels are used.
The pair pools below contain the same original edge copies, so their
cardinalities and the stored reserve are preserved exactly.
-/

noncomputable section
namespace Overfull.TerminalFour
open Finset Classical SimpleGraph FourOdd Compression CircuitPatterns

/-- Positive regularity and absence of an overfull set force even order. -/
theorem even_order_of_positive_regular {V : Type*} [Fintype V]
    (G : SimpleGraph V) (h : ℕ) (hh : 0 < h)
    (hregular : ∀ v, G.degree v = h)
    (hno : ∀ X : Finset V, ¬ IsOverfull G h X) : Even (Fintype.card V) := by
  apply Nat.even_iff.mpr
  by_contra hn
  have hodd : (univ : Finset V).card % 2 = 1 := by
    simp only [card_univ]
    omega
  obtain ⟨s, hs, _⟩ := MatchingProbability.regular_odd_cut hregular hno univ hodd
  have hz : MatchingProbability.cutCount (univ : Finset G.edgeSet) (univ : Finset V) = 0 := by
    simp [MatchingProbability.cutCount, MatchingProbability.cutEdges, Lovasz.BMatch.cut]
  omega

/-- The actual stored embedding is onto when there are four cores. -/
def fourCodeEquiv {I : Type*} [Fintype I] (code : I ↪ Fin 4)
    (hI : Fintype.card I = 4) : I ≃ Fin 4 := by
  let e := Fintype.equivFinOfCardEq hI
  have hs : Function.Surjective (fun j : Fin 4 => code (e.symm j)) :=
    Finite.surjective_of_injective (fun a b hab => e.symm.injective (code.injective hab))
  exact Equiv.ofBijective code ⟨code.injective, fun j => by
    obtain ⟨i, hi⟩ := hs j
    exact ⟨e.symm i, hi⟩⟩

@[simp] theorem fourCodeEquiv_apply {I : Type*} [Fintype I]
    (code : I ↪ Fin 4) (hI : Fintype.card I = 4) (i : I) :
    fourCodeEquiv code hI i = code i := rfl

/-- Every coded fiber is its original core after the index equivalence. -/
theorem codeEquiv_shore {V I : Type*} [Fintype V] [Fintype I]
    (U : I → Finset V) (code : I ↪ Fin 4) (hI : Fintype.card I = 4)
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hcover : ∀ v, ∃ i, v ∈ U i) (j : Fin 4) :
    labelShore (coreLabel U code) {j} = U ((fourCodeEquiv code hI).symm j) := by
  ext v
  simp only [mem_labelShore, mem_singleton]
  have he : code ((fourCodeEquiv code hI).symm j) = j :=
    (fourCodeEquiv code hI).apply_symm_apply j
  simpa only [he] using coreLabel_eq_iff U ∅ code (fun i j hij => hdisj hij)
    (fun v => Or.inr (hcover v)) (notMem_empty v) ((fourCodeEquiv code hI).symm j)

/-- The quotient pair pool and the manuscript pool are the same original
edge copies under the two subtype-forgetting maps. -/
theorem joining_pairPool_card {V I : Type*} [Fintype V]
    (G : SimpleGraph V) (U : I → Finset V) (code : I ↪ Fin 4) (p : LabelPair) :
    (pairPool (joiningQuotient (Multigraph.ofSimpleGraph G) (coreLabel U code)) p).card =
      (partPairEdges G U code p).card := by
  let M := Multigraph.ofSimpleGraph G
  let label := coreLabel U code
  let Q := joiningQuotient M label
  let f : joiningCopies M label → Sym2 V := fun e => e.val.val
  have hinj : Function.Injective f := fun a b hab =>
    Subtype.ext (Subtype.ext hab)
  have hpairs (s : joiningCopies M label) :
      (s.val.val).toFinset.image label = (Q.edgeLabelPair s).val := by
    dsimp only [Q, joiningQuotient]
    rw [labelQuotient_edgeLabelPair_val (joiningGraph M label) label
      (joiningGraph_join M label)]
    change (M.edge s.val).toFinset.image label =
      {label (M.firstEnd s.val), label (M.secondEnd s.val)}
    rw [← M.edge_eq s.val]
    simp only [Sym2.toFinset_mk_eq, image_insert, image_singleton]
  have himage : (pairPool Q p).image f = partPairEdges G U code p := by
    ext e
    constructor
    · rintro he
      obtain ⟨s, hs, rfl⟩ := mem_image.mp he
      apply (mem_partPairEdges G U code p _).mpr
      exact ⟨s.val.property, (hpairs s).trans
        (congrArg Subtype.val ((mem_pairPool Q p s).mp hs))⟩
    · intro he
      obtain ⟨heG, hep⟩ := (mem_partPairEdges G U code p e).mp he
      let s : G.edgeSet := ⟨e, heG⟩
      have heq : ({label (M.firstEnd s), label (M.secondEnd s)} : Finset (Fin 4)) = p.val := by
        have h := hep
        change (M.edge s).toFinset.image label = p.val at h
        rw [← M.edge_eq s] at h
        simpa only [Sym2.toFinset_mk_eq, image_insert, image_singleton] using h
      have hj : s ∈ joiningCopies M label := by
        apply (mem_joiningCopies M label s).mpr
        intro h
        have hc := p.property
        rw [← heq] at hc
        simp [h] at hc
      let q : joiningCopies M label := ⟨s, hj⟩
      refine mem_image.mpr ⟨q, ?_, rfl⟩
      apply (mem_pairPool Q p q).mpr
      apply Subtype.ext
      exact (hpairs q).symm.trans hep
  rw [← himage, card_image_of_injective _ hinj]

end Overfull.TerminalFour
