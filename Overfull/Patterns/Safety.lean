import Overfull.Patterns.Plan
import Overfull.Patterns.Prefix
import Overfull.ForeignEdges.Assignment

/-!
# No overfull set at every realized prefix

Odd whole unions use the original weighted cut inequality and exact
subtraction of the realized prefix. A small proposed cut is protected
without changing any original boundary incidence. Large cuts use the
actual exterior-degree bound. The proved small-cut theorem handles all
other shores.
-/

namespace Overfull.Patterns

open Finset Classical MatchingProbability ForeignPhase ForceMatching
open scoped BigOperators

variable {V I S : Type*} [Fintype V] [Fintype I] [Fintype S]
  {G : SimpleGraph V}
  {U : I → Finset V} {Z : Finset V} {code : I ↪ Fin 4} {k : ℕ}

namespace EncodedDistribution

set_option maxHeartbeats 1200000 in
/-- Safety is derived for the actual residual. Its hypotheses supply
the realized pattern counts and actual robust cores, not a safety oracle. -/
theorem completed_prefix_safe (D : EncodedDistribution G U Z code k S)
    (N : ℕ → G.Subgraph) (pattern : ℕ → Pattern Z) (s : ℕ)
    (η a : ℝ) (t : ℕ) (p₀ : Pattern Z) (r : ℕ)
    (hk : 0 < k) (hsk : s ≤ k)
    (hη₀ : 0 < η) (hη₁ : η ≤ 1) (hr : (r : ℝ) ≤ D.weight p₀)
    (hregular : ∀ v, G.degree v = k)
    (hno : ∀ X : Finset V, ¬ IsOverfull G k X)
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hUZ : ∀ i, Disjoint (U i) Z)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (hpresent : ∀ j < s, (N j).spanningCoe ≤ afterDeletions G N j)
    (hcross : ∀ j < s, ∀ Q : Finset (Z ⊕ Fin 4),
      cutCount (matchingEdges (N j)) (wholeUnion U Z code Q) = (pattern j).cutCount Q)
    (hcounts : ∀ p, prefixCount pattern s p ≤ D.plannedMultiplicity η a t p₀ r p)
    (hregularR : ∀ v, (afterDeletions G N s).degree v = k - s)
    (H : ∀ i, SimpleGraph (U i))
    (hH : ∀ i, H i ≤ (afterDeletions G N s).induce (U i : Set V))
    (α c ν τ : ℝ) (hα : 0 < α) (hc : 0 < c) (hν : 0 < ν) (hτ : 0 ≤ τ)
    (hτα : τ ≤ α / 10)
    (hklo : α * Fintype.card V ≤ ((k - s : ℕ) : ℝ))
    (hkhi : ((k - s : ℕ) : ℝ) ≤ 2 * Fintype.card V)
    (ha : a ≤ α * Fintype.card V / 10)
    (hlarge : 3 < ν ^ 2 * c ^ 2 * (Fintype.card V : ℝ))
    (hsize : ∀ i, c * Fintype.card V ≤ ((U i).card : ℝ))
    (hrobust : ∀ i, IsRobustExpander (H i) ν τ)
    (hdegree : ∀ i v, ((k - s : ℕ) : ℝ) - a ≤ ((H i).degree v : ℝ)) :
    ∀ X : Finset V, ¬ IsOverfull (afterDeletions G N s) (k - s) X := by
  classical
  have hcountprop (p : Pattern Z) :
      prefixCount pattern s p ≤ proposedMultiplicity η D.weight p₀ r p :=
    (hcounts p).trans (D.planned_le_proposed η a t p₀ p r)
  have hcountweight (p : Pattern Z) : (prefixCount pattern s p : ℝ) ≤ D.weight p :=
    (show (prefixCount pattern s p : ℝ) ≤ proposedMultiplicity η D.weight p₀ r p
      by exact_mod_cast hcountprop p).trans
      (proposedMultiplicity_le_weight η D.weight p₀ r hη₀.le hη₁ D.weight_nonneg hr p)
  have hwhole : ∀ X ∈ wholeUnions U Z, X.card % 2 = 1 →
      k - s ≤ graphCutCount (afterDeletions G N s) X := by
    intro X hX hodd
    obtain ⟨Q, rfl⟩ := quotient_of_wholeUnions U Z code X hdisj hUZ hcover hX
    apply prefix_odd_cut_safe G N pattern s k (wholeUnion U Z code Q)
      (fun p => p.cutCount Q) D.weight hsk hpresent (fun j hj => hcross j hj Q)
      D.weight_sum hcountweight
    · exact D.positive_odd_cut hdisj hUZ hcover Q hodd
    · exact D.whole_cut_capacity_actual hk Q
  apply no_overfull_of_whole_cut_bounds (afterDeletions G N s) U Z hdisj hUZ hcover
    (k - s) hregularR H hH α c ν τ a hα hc hν hτ hτα hklo hkhi ha hlarge
    hsize hrobust hdegree hwhole
  intro X hX heven v
  obtain ⟨Q, hQX⟩ := quotient_of_wholeUnions U Z code X hdisj hUZ hcover hX
  by_cases hsmall : (graphCutCount G (wholeUnion U Z code Q) : ℝ) -
      (∑ p, (proposedMultiplicity η D.weight p₀ r p : ℝ) * p.cutCount Q) < 2 * a
  · have hzero (j : ℕ) (hj : j < s) : cutCount (matchingEdges (N j)) X = 0 := by
      have hpos : 0 < prefixCount pattern s (pattern j) :=
        card_pos.mpr ⟨j, mem_filter.mpr ⟨mem_range.mpr hj, rfl⟩⟩
      have hmpos : 0 < D.plannedMultiplicity η a t p₀ r (pattern j) :=
        hpos.trans_le (hcounts (pattern j))
      have hz := D.planned_protected_zero η a t p₀ r Q hsmall (pattern j)
      have hc : (pattern j).cutCount Q = 0 := (Nat.mul_eq_zero.mp hz).resolve_left
        (Nat.ne_of_gt hmpos)
      rw [hQX, hcross j hj Q, hc]
    exact toggle_safe_of_preserved_cut G (afterDeletions G N s) k (k - s)
      hregular hregularR hno X heven (afterDeletions_cut_unchanged G N s hpresent X hzero) v
  · by_cases hvZ : v ∈ Z
    · exact hwhole (toggle X v) (wholeUnions_toggle_exceptional U Z X hUZ hX v hvZ)
        (toggle_odd heven v)
    · obtain ⟨i, hvi⟩ := (hcover v).resolve_left hvZ
      have hex := ForeignAssignment.exterior_degree_le_error (afterDeletions G N s)
        (U i) (H i) (hH i) (k - s) a hregularR (hdegree i) ⟨v, hvi⟩
      have hinc := graphCutIncidence_le_exterior (afterDeletions G N s) U X
        (wholeUnions_whole U Z X hdisj hUZ hX) i v hvi
      have hincR : (graphCutIncidence (afterDeletions G N s) X v : ℝ) ≤ a :=
        (show (graphCutIncidence (afterDeletions G N s) X v : ℝ) ≤
          ((afterDeletions G N s).neighborFinset v \ U i).card
          by exact_mod_cast hinc).trans hex
      have hactual := prefix_cut_accounting G N pattern s (wholeUnion U Z code Q)
        (fun p => p.cutCount Q) hpresent (fun j hj => hcross j hj Q)
      have hmono := prefix_cut_mono (proposedMultiplicity η D.weight p₀ r)
        (prefixCount pattern s) (fun p => p.cutCount Q)
        (graphCutCount G (wholeUnion U Z code Q) : ℝ) hcountprop
      have hbig : 2 * a ≤ (graphCutCount (afterDeletions G N s) X : ℝ) := by
        rw [hQX]
        have hn := le_of_not_gt hsmall
        linarith
      apply toggle_safe_of_incidence (afterDeletions G N s) (k - s) hregularR X v
      exact_mod_cast (show (2 : ℝ) * graphCutIncidence (afterDeletions G N s) X v ≤
        graphCutCount (afterDeletions G N s) X by linarith)

end EncodedDistribution
end Overfull.Patterns
