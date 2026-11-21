import Overfull.Patterns.Boundary
import Overfull.Patterns.Distribution
import Overfull.Patterns.Cuts

/-!
# Whole unions and the common pattern quotient

The quotient encodes exactly the finite family of unions of complete
cores and exceptional singletons. Every positive-weight pattern has the
correct odd-cut parity because its uncovered part in each core is even.
-/

noncomputable section
namespace Overfull.Patterns

open Finset Classical SimpleGraph Compression MatchingProbability FractionalMatching
open ForceMatching
open scoped BigOperators

variable {V I : Type*} [Fintype V] [Fintype I]

/-- The canonical label shore representing an actual vertex shore. -/
def quotientShore (U : I → Finset V) (Z : Finset V) (code : I ↪ Fin 4)
    (X : Finset V) : Finset (Z ⊕ Fin 4) := X.image (boundaryLabel U Z code)

/-- Every quotient shore pulls back to a union of whole cores and
exceptional singletons, including unused core labels. -/
theorem wholeUnion_mem (U : I → Finset V) (Z : Finset V) (code : I ↪ Fin 4)
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hZ : ∀ i, Disjoint (U i) Z) (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (Q : Finset (Z ⊕ Fin 4)) : wholeUnion U Z code Q ∈ wholeUnions U Z := by
  let A : Finset I := univ.filter (fun i => Sum.inr (code i) ∈ Q)
  let B : Finset V := wholeUnion U Z code Q ∩ Z
  refine (mem_wholeUnions U Z _).mpr ⟨A, B, inter_subset_right, ?_⟩
  ext v
  constructor
  · intro hv
    by_cases hvZ : v ∈ Z
    · exact mem_union_right _ (mem_inter.mpr ⟨hv,hvZ⟩)
    · obtain ⟨i,hvi⟩ := (hcover v).resolve_left hvZ
      apply mem_union_left
      apply mem_biUnion.mpr
      refine ⟨i, ?_, hvi⟩
      apply mem_filter.mpr
      refine ⟨mem_univ _, ?_⟩
      rw [mem_wholeUnion, boundaryLabel_outside U Z code v hvZ,
        coreLabel_of_mem U code (fun i j hij => hdisj hij) hvi] at hv
      exact hv
  · intro hv
    rcases mem_union.mp hv with hvA | hvB
    · obtain ⟨i,hi,hvi⟩ := mem_biUnion.mp hvA
      have hvZ : v ∉ Z := fun hvZ => disjoint_left.mp (hZ i) hvi hvZ
      rw [mem_wholeUnion, boundaryLabel_outside U Z code v hvZ,
        coreLabel_of_mem U code (fun i j hij => hdisj hij) hvi]
      exact (mem_filter.mp hi).2
    · exact (mem_inter.mp hvB).1

/-- The canonical image of a whole union pulls back to exactly that union. -/
theorem wholeUnion_quotientShore (U : I → Finset V) (Z : Finset V) (code : I ↪ Fin 4)
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hZ : ∀ i, Disjoint (U i) Z) (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (X : Finset V) (hX : X ∈ wholeUnions U Z) :
    wholeUnion U Z code (quotientShore U Z code X) = X := by
  ext v
  rw [mem_wholeUnion]
  constructor
  · intro hv
    obtain ⟨u,hu,heq⟩ := mem_image.mp hv
    by_cases hvZ : v ∈ Z
    · have hvlabel : boundaryLabel U Z code v = Sum.inl (⟨v,hvZ⟩ : Z) :=
        boundaryLabel_exceptional U Z code ⟨v,hvZ⟩
      rw [hvlabel] at heq
      have huv := (boundaryLabel_inl_iff U Z code u ⟨v,hvZ⟩).mp heq
      simpa only [huv] using hu
    · have huZ : u ∉ Z := by
        intro huZ
        rw [boundaryLabel_exceptional U Z code ⟨u,huZ⟩,
          boundaryLabel_outside U Z code v hvZ] at heq
        exact Sum.noConfusion heq
      obtain ⟨i,hvi⟩ := (hcover v).resolve_left hvZ
      rw [boundaryLabel_outside U Z code u huZ,
        boundaryLabel_outside U Z code v hvZ] at heq
      have hlabel : coreLabel U code u = code i :=
        (Sum.inr.inj heq).trans (coreLabel_of_mem U code (fun i j hij => hdisj hij) hvi)
      have hui := (coreLabel_eq_iff U Z code (fun i j hij => hdisj hij) hcover huZ i).mp hlabel
      exact (same_core_membership U X (wholeUnions_whole U Z X hdisj hZ hX) hui hvi).mp hu
  · intro hv
    exact mem_image.mpr ⟨v,hv,rfl⟩

variable {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
/-- Cardinality of the actual uncovered vertices, in finset notation. -/
theorem uncovered_card_eq (F : G.Subgraph) (X : Finset V) :
    (((X : Set V) \ F.verts).ncard) = (X \ F.verts.toFinset).card := by
  have heq : (X : Set V) \ F.verts = ((X \ F.verts.toFinset : Finset V) : Set V) := by
    ext v
    simp
  rw [heq, Set.ncard_coe_finset]

omit [DecidableRel G.Adj] in
/-- An exceptional-covering matching with even uncovered core orders has
even uncovered order on every whole union. -/
theorem whole_union_uncovered_even (U : I → Finset V) (Z : Finset V)
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (F : G.Subgraph) (hcoverZ : (Z : Set V) ⊆ F.verts)
    (hparity : ∀ i, Even (((U i : Set V) \ F.verts).ncard))
    (X : Finset V) (hX : X ∈ wholeUnions U Z) :
    Even (((X : Set V) \ F.verts).ncard) := by
  classical
  obtain ⟨A,B,hB,rfl⟩ := (mem_wholeUnions U Z X).mp hX
  rw [uncovered_card_eq]
  have heq : (A.biUnion U ∪ B) \ F.verts.toFinset =
      A.biUnion (fun i => U i \ F.verts.toFinset) := by
    ext v
    simp only [mem_sdiff, mem_union, mem_biUnion]
    constructor
    · rintro ⟨hA | hBv,hFv⟩
      · obtain ⟨i,hi,hvi⟩ := hA
        exact ⟨i,hi,hvi,hFv⟩
      · exact False.elim (hFv (Set.mem_toFinset.mpr (hcoverZ (hB hBv))))
    · rintro ⟨i,hi,hvi,hFv⟩
      exact ⟨Or.inl ⟨i,hi,hvi⟩,hFv⟩
  rw [heq, card_biUnion]
  · have hp (i : I) : Even ((U i \ F.verts.toFinset).card) := by
      simpa only [uncovered_card_eq] using hparity i
    clear hX heq
    induction A using Finset.induction_on with
    | empty => simp
    | @insert i A hi ih =>
      rw [sum_insert hi]
      exact (hp i).add ih
  · intro i _ j _ hij
    exact (hdisj hij).mono sdiff_subset sdiff_subset

/-- The actual compressed cut has the shore's parity on every whole union. -/
theorem whole_union_matching_cut_parity (U : I → Finset V) (Z : Finset V)
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (F : G.Subgraph) (hF : F.IsMatching) (hcoverZ : (Z : Set V) ⊆ F.verts)
    (hparity : ∀ i, Even (((U i : Set V) \ F.verts).ncard))
    (X : Finset V) (hX : X ∈ wholeUnions U Z) :
    cutCount (matchingEdges F) X % 2 = X.card % 2 :=
  (matching_uncovered_even_iff_cut_parity F hF X).mp
    (whole_union_uncovered_even U Z hdisj F hcoverZ hparity X hX)

namespace EncodedDistribution

variable {S : Type*} [Fintype S] {U : I → Finset V} {Z : Finset V}
  {code : I ↪ Fin 4} {k : ℕ} (D : EncodedDistribution G U Z code k S)

/-- Every positive-weight common pattern crosses an odd whole union at
least once. Its parity is inherited from its actual compressed sample. -/
theorem positive_odd_cut (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hZ : ∀ i, Disjoint (U i) Z) (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (Q : Finset (Z ⊕ Fin 4)) (hodd : (wholeUnion U Z code Q).card % 2 = 1)
    (p : Pattern Z) (hp : 0 < D.weight p) : 1 ≤ p.cutCount Q := by
  obtain ⟨s,hs,henc⟩ := D.positive_witness p hp
  have hpar := whole_union_matching_cut_parity U Z hdisj (D.part s)
    henc.matching henc.covered (D.parity s) (wholeUnion U Z code Q)
    (wholeUnion_mem U Z code hdisj hZ hcover Q)
  rw [henc.whole_cut_count Q, hodd] at hpar
  omega

omit [Fintype I] in
/-- Weighted quotient cut capacities are backed by actual host edges. -/
theorem quotient_cut_capacity (hk : 0 < k) (Q : Finset (Z ⊕ Fin 4)) :
    (∑ p, D.weight p * p.cutCount Q) ≤ graphCutCount G (wholeUnion U Z code Q) := by
  rw [← univ_cut_eq_graph]
  exact D.whole_cut_capacity hk (wholeUnion U Z code Q) (fun p => p.cutCount Q)
    (fun s => ((D.encodes s).whole_cut_count Q).symm)

/-- Weighted capacities on the actual finite whole-union family. -/
theorem whole_union_capacity (hk : 0 < k)
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hZ : ∀ i, Disjoint (U i) Z) (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (X : Finset V) (hX : X ∈ wholeUnions U Z) :
    (∑ p, D.weight p * p.cutCount (quotientShore U Z code X)) ≤ graphCutCount G X := by
  have h := D.quotient_cut_capacity hk (quotientShore U Z code X)
  rw [wholeUnion_quotientShore U Z code hdisj hZ hcover X hX] at h
  exact h

end EncodedDistribution
end Overfull.Patterns
