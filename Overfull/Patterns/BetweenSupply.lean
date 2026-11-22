import Overfull.Patterns.PoolNeighbors
import Overfull.Patterns.Absorption

/-!
# Reserved forest pairs give actual edges between enlarged parts

Edges are first counted in the residual graph's own edge subtype and then
identified with finite sets of actual unordered vertex pairs. Enlarging
each core preserves every reserved joining edge.
-/

noncomputable section
namespace Overfull.Patterns
open Finset Classical SimpleGraph Compression FractionalMatching

variable {V I : Type*} [Fintype V] [DecidableEq V]

/-- Actual edges joining two supplied vertex sets, counted once each. -/
def edgesBetween (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    Finset G.edgeSet :=
  univ.filter (fun e => (firstEnd e ∈ A ∧ secondEnd e ∈ B) ∨
    (firstEnd e ∈ B ∧ secondEnd e ∈ A))

/-- The same joining edges as actual unordered vertex pairs. -/
def graphEdgesBetween (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    Finset (Sym2 V) := (edgesBetween G A B).image Subtype.val

@[simp] theorem graphEdgesBetween_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) : (graphEdgesBetween G A B).card = (edgesBetween G A B).card := by
  exact Finset.card_image_of_injective _ Subtype.val_injective

theorem edgesBetween_mono (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B A' B' : Finset V) (hA : A ⊆ A') (hB : B ⊆ B') :
    edgesBetween G A B ⊆ edgesBetween G A' B' := by
  intro e he
  refine mem_filter.mpr ⟨mem_univ _,?_⟩
  rcases (mem_filter.mp he).2 with ⟨ha,hb⟩ | ⟨hb,ha⟩
  · exact Or.inl ⟨hA ha,hB hb⟩
  · exact Or.inr ⟨hB hb,hA ha⟩

private theorem finset_pair_eq_iff {α : Type*} [DecidableEq α] (a b c d : α) :
    ({a,b} : Finset α) = {c,d} ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  rw [← Finset.coe_inj]
  simp only [Finset.coe_insert,Finset.coe_singleton,Set.pair_eq_pair_iff]

/-- The quotient pool of two core labels is exactly the set of actual
edges between the two corresponding original cores. -/
theorem core_pair_pool_eq_edgesBetween (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : I → Finset V) (Z : Finset V) (code : I ↪ Fin 4)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hUZ : ∀ i, Disjoint (U i) Z)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i) (i j : I) :
    ((univ : Finset G.edgeSet).filter (fun e =>
      labelledEdge G U Z code e = {Sum.inr (code i),Sum.inr (code j)})) =
        edgesBetween G (U i) (U j) := by
  ext e
  simp only [edgesBetween,mem_filter,mem_univ,true_and,labelledEdge_eq_pair]
  rw [finset_pair_eq_iff]
  simp only [boundaryLabel_eq_core_iff U Z code hdisjoint hUZ hcover]

/-- Every reserved forest-pair edge survives as a joining edge of the
corresponding enlarged parts. The conclusion uses actual Sym2 edges. -/
theorem reserved_forest_pair_enlarged (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : I → Finset V) (Z : Finset V) (code : I ↪ Fin 4)
    (assignment : V → I) (r : ℕ)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hUZ : ∀ i, Disjoint (U i) Z)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (p : LabelPair) (i j : I) (hends : p.val = {code i,code j})
    (hreserve : r ≤ ((univ : Finset G.edgeSet).filter (fun e =>
      labelledEdge G U Z code e = p.val.image (Sum.inr : Fin 4 → Z ⊕ Fin 4))).card) :
    r ≤ (graphEdgesBetween G (Absorption.enlargedSets U Z assignment i)
      (Absorption.enlargedSets U Z assignment j)).card := by
  rw [hends,Finset.image_insert,Finset.image_singleton,
    core_pair_pool_eq_edgesBetween G U Z code hdisjoint hUZ hcover] at hreserve
  rw [graphEdgesBetween_card]
  exact hreserve.trans (card_le_card (edgesBetween_mono G (U i) (U j)
    (Absorption.enlargedSets U Z assignment i) (Absorption.enlargedSets U Z assignment j)
    (Absorption.old_subset_enlarged U Z assignment i)
    (Absorption.old_subset_enlarged U Z assignment j)))

end Overfull.Patterns
