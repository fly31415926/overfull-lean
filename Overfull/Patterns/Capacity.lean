import Overfull.Patterns.BoundaryRealization
import Overfull.Patterns.WholeCuts
import Overfull.Patterns.Selection
import Overfull.Patterns.Cuts

/-!
# Actual pair and whole-cut capacities for the encoded distribution
-/

namespace Overfull.Patterns

open Finset Classical Compression FractionalMatching MatchingProbability
open PatternRealization
open scoped BigOperators

variable {E B : Type*} [DecidableEq E] [DecidableEq B]

omit [DecidableEq E] in
/-- An injective finite image has exactly one representative in every
nonempty fiber. -/
theorem fiber_card_of_injective (A : Finset E) (f : E → B)
    (hinj : Set.InjOn f A) (b : B) :
    (A.filter (fun e => f e = b)).card = if b ∈ A.image f then 1 else 0 := by
  by_cases hb : b ∈ A.image f
  · obtain ⟨e, he, hef⟩ := mem_image.mp hb
    have hs : A.filter (fun a => f a = b) = {e} := by
      ext a
      simp only [mem_filter, mem_singleton]
      constructor
      · rintro ⟨ha, hab⟩
        exact hinj ha he (hab.trans hef.symm)
      · rintro rfl
        exact ⟨he, hef⟩
    simp only [hs, card_singleton, if_pos hb]
  · have hs : A.filter (fun a => f a = b) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro a ha
      obtain ⟨haA, hab⟩ := mem_filter.mp ha
      exact hb (mem_image.mpr ⟨a, haA, hab⟩)
    simp only [hs, card_empty, if_neg hb]

variable {V I S : Type*} [Fintype V] [dV : DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {U : I → Finset V} {Z : Finset V} {code : I ↪ Fin 4}

/-- A boundary pair occurs zero or one times in an encoded matching. -/
theorem Encodes.pool_count {F : G.Subgraph} {P : Pattern Z}
    (hP : Encodes G U Z code F P) (b : Finset (Z ⊕ Fin 4)) :
    (matchingEdges F ∩ boundaryPool G U Z code b).card =
      if b ∈ P.boundaryEdges then 1 else 0 := by
  have heq : matchingEdges F ∩ boundaryPool G U Z code b =
      (matchingEdges F).filter (fun e => labelledEdge G U Z code e = b) := by
    ext e
    simp only [mem_inter, mem_boundaryPool, mem_filter]
  rw [heq]
  have hf := fiber_card_of_injective (matchingEdges F) (labelledEdge G U Z code)
    hP.labelledEdge_injective b
  rw [hP.boundary_edges] at hf
  convert hf using 1

/-- The number of uses of a particular pair by one pattern. -/
noncomputable def pairUse (b : Finset (Z ⊕ Fin 4)) (p : Pattern Z) : ℕ :=
  if b ∈ p.boundaryEdges then 1 else 0

namespace EncodedDistribution

variable [Fintype S] {k : ℕ} (D : EncodedDistribution G U Z code k S)

theorem pair_capacity (hk : 0 < k) (b : Finset (Z ⊕ Fin 4)) :
    (∑ p, D.weight p * (pairUse b p : ℝ)) ≤ (boundaryPool G U Z code b).card := by
  apply D.edge_pool_capacity hk (boundaryPool G U Z code b) (pairUse b)
  intro s
  exact (D.encodes s).pool_count b |>.symm.le

theorem whole_cut_capacity_actual (hk : 0 < k) (Q : Finset (Z ⊕ Fin 4)) :
    (∑ p, D.weight p * (p.cutCount Q : ℝ)) ≤ graphCutCount G (wholeUnion U Z code Q) := by
  have h := D.whole_cut_capacity hk (wholeUnion U Z code Q) (fun p => p.cutCount Q)
    (fun s => ((D.encodes s).whole_cut_count Q).symm)
  simpa only [univ_cut_eq_graph G (wholeUnion U Z code Q)] using h

set_option maxHeartbeats 400000 in
theorem positive_odd_cut [Fintype I]
    (hdisjoint : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hUZ : ∀ i, Disjoint (U i) Z)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (Q : Finset (Z ⊕ Fin 4)) (hodd : (wholeUnion U Z code Q).card % 2 = 1)
    (p : Pattern Z) (hp : 0 < D.weight p) : 1 ≤ p.cutCount Q := by
  have hd : dV = Classical.decEq V := Subsingleton.elim _ _
  subst dV
  obtain ⟨s, _, henc⟩ := D.positive_witness p hp
  exact Encodes.odd_whole_cut_positive (G := G) (U := U) (Z := Z) (code := code)
    (F := D.part s) (P := p) henc hdisjoint hUZ hcover (D.parity s) Q hodd

end EncodedDistribution
end Overfull.Patterns
