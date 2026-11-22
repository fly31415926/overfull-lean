import Overfull.Patterns.BoundaryRealization
import Overfull.Patterns.WholeCuts
import Overfull.Patterns.Prefix

/-!
# Cut reserves in the actual completed matching sequence

Completion adds edges inside the original cores. Consequently every
whole-union cut is counted by the prescribed boundary pattern, and the
distinguished pattern's numerical reserve survives as actual cut edges.
-/

namespace Overfull.Patterns

open Finset Classical SimpleGraph MatchingProbability ForceMatching ForeignPhase
open PatternRealization
open scoped BigOperators

variable {V I : Type*} [Fintype V] [Fintype I]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {U : I → Finset V} {Z : Finset V} {code : I ↪ Fin 4}

/-- Internal completion leaves every whole-union pattern cut exact. -/
theorem completed_pattern_whole_cut
    (hdisjoint : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hUZ : ∀ i, Disjoint (U i) Z)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (F N : G.Subgraph) (P : Pattern Z)
    (hF : RealizesPattern G U Z code P F) (hFN : F ≤ N)
    (hadded : ∀ u v, N.Adj u v → F.Adj u v ∨ ∃ i, u ∈ U i ∧ v ∈ U i)
    (Q : Finset (Z ⊕ Fin 4)) :
    cutCount (matchingEdges N) (wholeUnion U Z code Q) = P.cutCount Q := by
  have hwhole := wholeUnions_whole U Z (wholeUnion U Z code Q) hdisjoint hUZ
    (wholeUnion_mem_wholeUnions U Z code Q (fun i j h => hdisjoint h) hUZ hcover)
  have hcut := completed_cutEdges_eq U F N hFN hadded (wholeUnion U Z code Q) hwhole
  change (cutEdges (matchingEdges N) (wholeUnion U Z code Q)).card = _
  rw [hcut]
  exact cutCount_eq_pattern_of_boundary U Z code (matchingEdges F) P
    hF.projection_injective hF.boundary_image Q

omit [Fintype I] in
/-- The protected pattern's cut reserve is an inequality for the actual
residual graph, with all deleted edges subtracted exactly. -/
theorem completed_pattern_cut_reserved
    (N : ℕ → G.Subgraph) (pattern : ℕ → Pattern Z) (s : ℕ)
    (hpresent : ∀ j < s, (N j).spanningCoe ≤ afterDeletions G N j)
    (hcross : ∀ j < s, ∀ Q : Finset (Z ⊕ Fin 4),
      cutCount (matchingEdges (N j)) (wholeUnion U Z code Q) = (pattern j).cutCount Q)
    (w : Pattern Z → ℝ) (p₀ : Pattern Z) (η : ℝ) (r : ℕ)
    (hη₀ : 0 ≤ η) (hη₁ : η ≤ 1) (hw : ∀ p, 0 ≤ w p)
    (hr : (r : ℝ) ≤ w p₀)
    (hn : ∀ p, prefixCount pattern s p ≤ proposedMultiplicity η w p₀ r p)
    (hcap : ∀ Q : Finset (Z ⊕ Fin 4),
      (∑ p, w p * (p.cutCount Q : ℝ)) ≤ graphCutCount G (wholeUnion U Z code Q)) :
    ∀ Q : Finset (Z ⊕ Fin 4),
      r * p₀.cutCount Q ≤ cutCount (univ : Finset (afterDeletions G N s).edgeSet)
        (wholeUnion U Z code Q) := by
  intro Q
  have hreserve := prefix_pair_reserve η w p₀ r (prefixCount pattern s)
    (fun p => p.cutCount Q) (graphCutCount G (wholeUnion U Z code Q) : ℝ)
    hη₀ hη₁ hw hr hn (hcap Q)
  have haccount := prefix_cut_accounting G N pattern s (wholeUnion U Z code Q)
    (fun p => p.cutCount Q) hpresent (fun j hj => hcross j hj Q)
  rw [univ_cut_eq_graph]
  have hh : (r : ℝ) * p₀.cutCount Q ≤
      graphCutCount (afterDeletions G N s) (wholeUnion U Z code Q) := by
    linarith only [hreserve, haccount]
  exact_mod_cast hh

end Overfull.Patterns
