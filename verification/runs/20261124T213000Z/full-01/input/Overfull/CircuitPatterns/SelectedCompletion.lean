import Overfull.CircuitPatterns.Selection
import Overfull.CircuitPatterns.Multiplicity
import Overfull.CircuitPatterns.RealizedFamily
import Overfull.CircuitPatterns.Completion

/-!
# Actual completions of the selected pattern copies

The finite pattern enumeration is first realized by fresh boundary edges.
The proved adaptive core rules then complete those exact boundaries, with
all forbidden-set admissibility derived from the actual boundary family.
-/

noncomputable section
namespace Overfull.CircuitPatterns

open Finset Classical SimpleGraph Compression FractionalMatching MatchingProbability
open ForceMatching ForeignRuleCompletion
open scoped BigOperators

variable {V I S : Type*} [Fintype V] [DecidableEq V] [Fintype S]

theorem copyPattern_pair_count {E : Type*} [Fintype E] [DecidableEq E]
    (m : Pattern E → ℕ) (b : BoundaryPair E) :
    (univ.filter (fun j : Fin (∑ p, m p) =>
      boundaryPairLabels b ∈ (copyPattern m j).boundaryEdges)).card =
        ∑ p, m p*pairIndicator b p := by
  have h := copyPattern_statistic m (pairIndicator b)
  simpa [pairIndicator] using h

def extendBoundary (G : SimpleGraph V) (q : ℕ)
    (F : Fin q → G.Subgraph) (j : ℕ) : G.Subgraph :=
  if h : j < q then F ⟨j,h⟩ else ⊥

omit [Fintype V] [DecidableEq V] in
@[simp] theorem extendBoundary_lt (G : SimpleGraph V) (q : ℕ)
    (F : Fin q → G.Subgraph) (j : ℕ) (hj : j < q) :
    extendBoundary G q F j = F ⟨j,hj⟩ := by
  simp [extendBoundary,hj]

/-- A selected family has actual boundary matchings and actual completed
perfect matchings in the original graph, with the exact prescribed quotient. -/
structure CompletedPatternFamily (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : I → Finset V) (Z : Finset V) (code : I ↪ Fin 4)
    (H : ∀ i, SimpleGraph (U i)) (k t : ℕ)
    (D : EncodedDistribution G U Z code k S) (η a θ σ : ℝ)
    (selection : PatternSelection G U Z code k t D η a) where
  boundary : ℕ → G.Subgraph
  completion : BoundaryCompletion G U H boundary
    (∑ p, selection.multiplicity p) k a θ σ
  boundary_injective : ∀ j < ∑ p, selection.multiplicity p,
    Set.InjOn (labelledEdge G U Z code) (matchingEdges (boundary j))
  boundary_image : ∀ j < ∑ p, selection.multiplicity p,
    (matchingEdges (boundary j)).image (labelledEdge G U Z code) =
      (enumeratedPattern selection.multiplicity selection.frequent j).boundaryEdges

theorem CompletedPatternFamily.boundary_counts
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {U : I → Finset V} {Z : Finset V} {code : I ↪ Fin 4}
    {H : ∀ i, SimpleGraph (U i)} {k t : ℕ}
    {D : EncodedDistribution G U Z code k S} {η a θ σ : ℝ}
    {selection : PatternSelection G U Z code k t D η a}
    (C : CompletedPatternFamily G U Z code H k t D η a θ σ selection)
    (j : ℕ) (hj : j < ∑ p, selection.multiplicity p) (Q : Finset (Z ⊕ Fin 4)) :
    cutCount (matchingEdges (C.boundary j)) (wholeUnion U Z code Q) =
      (enumeratedPattern selection.multiplicity selection.frequent j).cutCount Q :=
  cutCount_eq_pattern_of_boundary U Z code _ _
    (C.boundary_injective j hj) (C.boundary_image j hj) Q

set_option maxHeartbeats 200000 in
/-- No boundary realization or completed matching is assumed: the actual
family is constructed from the selected multiplicities and certified rules. -/
theorem exists_completed_pattern_family (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : I → Finset V) (Z : Finset V) (code : I ↪ Fin 4)
    (H : ∀ i, SimpleGraph (U i)) (k t : ℕ)
    (D : EncodedDistribution G U Z code k S) (η a ε θ σ : ℝ)
    (selection : PatternSelection G U Z code k t D η a)
    (hη : 0 < η) (ha : 0 ≤ a) (ht : Z.card ≤ t)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hUZ : ∀ i, Disjoint (U i) Z)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (hH : ∀ i, H i ≤ G.induce (U i : Set V))
    (hregular : ∀ v, G.degree v = k)
    (hdegree : ∀ i v, (k : ℝ)-a ≤ (H i).degree v)
    (herror : ∀ i, a ≤ ε*(U i).card)
    (hfoot : ∀ i, ((2*t+6 : ℕ) : ℝ) ≤ ε*(U i).card)
    (rule : ∀ i, (s : ℕ) → (Fin s → Finset (U i) × (H i).Subgraph) →
      Finset (U i) → (H i).Subgraph)
    (limit : I → ℕ)
    (hcertificate : ∀ i, RuleCertificate (H i) (limit i) ε θ σ (rule i))
    (hlimit : ∀ i, (∑ p, selection.multiplicity p) ≤ limit i) :
    Nonempty (CompletedPatternFamily G U Z code H k t D η a θ σ selection) := by
  let m := selection.multiplicity
  let q := ∑ p, m p
  let P : Fin q → Pattern Z := copyPattern m
  have hp (j : Fin q) : 0 < m (P j) := copyPattern_positive m j
  obtain ⟨B⟩ := exists_realized_boundary_family_of_slack G U Z code
    hdisjoint hUZ hcover H hH k t a η ha hη ht hregular hdegree P
    (fun j => selection.selected_no_internal (P j) (hp j))
    (fun j => selection.selected_forest (P j) (hp j)) (by
      intro b
      rw [copyPattern_pair_count m b]
      push_cast
      exact selection.pair_demand b) (by
      intro j b hb
      exact selection.sparse_avoided (P j) (hp j) b hb)
  let F := extendBoundary G q B.matching
  have hsource (j : Fin q) : ∃ A : G.Subgraph,
      Encodes G U Z code A (P j) ∧ ∀ i, Even (((U i : Set V) \ A.verts).ncard) := by
    obtain ⟨s,_hs,henc⟩ := D.positive_witness (P j)
      (selection.selected_supported (P j) (hp j))
    exact ⟨D.part s,henc,D.parity s⟩
  have hpar := RealizedBoundaryFamily.even_uncovered G B hdisjoint hUZ hcover hsource
  have hF (j : ℕ) (hj : j < q) : F j = B.matching ⟨j,hj⟩ :=
    extendBoundary_lt G q B.matching j hj
  have hdisj (j : ℕ) (hj : j < q) (l : ℕ) (hl : l < q) (hjl : j ≠ l) :
      Disjoint (F j).spanningCoe (F l).spanningCoe := by
    rw [hF j hj,hF l hl]
    exact B.disjoint _ _ (fun h => hjl (congrArg Fin.val h))
  have hsize (j : ℕ) (hj : j < q) (i : I) :
      ((coveredCore (U i) G (F j)).card : ℝ) ≤ ε*(U i).card := by
    rw [coveredCore_card,hF j hj]
    have hb : ((B.matching ⟨j,hj⟩).verts.toFinset ∩ U i).card ≤ 2*t+6 :=
      (B.footprint _ i).trans (by omega)
    exact (show (((B.matching ⟨j,hj⟩).verts.toFinset ∩ U i).card : ℝ) ≤
      (2*t+6 : ℕ) by exact_mod_cast hb).trans (hfoot i)
  obtain ⟨C⟩ := exists_boundary_completion G U Z H hH F q k a ε θ σ rule limit
    hcertificate hlimit hdisjoint hcover
    (fun j hj => by rw [hF j hj]; exact B.isMatching _)
    (fun j hj => by rw [hF j hj]; exact B.covered _) hdisj
    (fun j hj => by rw [hF j hj]; exact B.no_internal _)
    (by intro v; simpa only [← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hregular v)
    (by intro i v; simpa only [← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hdegree i v) herror
    (fun j hj => by rw [hF j hj]; exact hpar _) hsize
  refine ⟨⟨F,C,?_,?_⟩⟩
  · intro j hj
    rw [hF j hj]
    exact B.boundary_injective _
  · intro j hj
    rw [hF j hj,enumeratedPattern_lt m selection.frequent j hj]
    exact B.boundary_image _

end Overfull.CircuitPatterns
