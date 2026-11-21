import Overfull.Patterns.Safety
import Overfull.Patterns.WholeUnions
import Overfull.Patterns.Selection
import Overfull.Patterns.Multiplicity
import Overfull.Patterns.Completion

/-!
# Safe completion of the selected frequent-pattern copies

All original weighted cut and parity hypotheses are supplied by the
actual encoded distribution. Every tested small even cut is protected by
the one common selection, and no residual safety assertion is assumed.
-/

noncomputable section
namespace Overfull.Patterns

open Finset Classical SimpleGraph Compression FractionalMatching MatchingProbability
open ForceMatching ForeignPhase ForeignIncidence
open scoped BigOperators

variable {V I S : Type*} [Fintype V] [Fintype I] [Fintype S]

namespace BoundaryCompletion

set_option maxHeartbeats 1000000 in
/-- Every prefix of the actual completed selected family has no overfull
set. The final retained-degree lower bound suffices for every prefix's
small-cut classification. -/
theorem safe_selected_prefixes (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : I → Finset V) (Z : Finset V) (code : I ↪ Fin 4)
    (H : ∀ i, SimpleGraph (U i)) (k t : ℕ)
    (D : EncodedDistribution G U Z code k S) (η a θ σ : ℝ)
    (selection : PatternSelection G U Z code k t D η a)
    (F : ℕ → G.Subgraph)
    (C : BoundaryCompletion G U H F (∑ p, selection.multiplicity p) k a θ σ)
    (hk : 0 < k) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hZ : ∀ i, Disjoint (U i) Z) (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (hregularG : ∀ v, G.degree v = k)
    (hnoG : ∀ X : Finset V, ¬ IsOverfull G k X)
    (hFcounts : ∀ j < ∑ p, selection.multiplicity p, ∀ Q : Finset (Z ⊕ Fin 4),
      cutCount (matchingEdges (F j)) (wholeUnion U Z code Q) =
        (enumeratedPattern selection.multiplicity selection.frequent j).cutCount Q)
    (α c : ℝ) (hα : 0 < α) (hc : 0 < c) (hθ : 0 < θ) (hσ : 0 ≤ σ)
    (hσα : σ ≤ α / 10)
    (hklo : α * Fintype.card V ≤ ((k-∑ p, selection.multiplicity p : ℕ) : ℝ))
    (hkhi : (k : ℝ) ≤ 2 * Fintype.card V)
    (ha : a ≤ α * Fintype.card V / 10)
    (hlarge : 3 < θ ^ 2 * c ^ 2 * (Fintype.card V : ℝ))
    (hsize : ∀ i, c * Fintype.card V ≤ ((U i).card : ℝ)) :
    ∀ s ≤ ∑ p, selection.multiplicity p, ∀ X : Finset V,
      ¬ IsOverfull (afterDeletions G C.full s) (k-s) X := by
  intro s hs
  have hsk : s ≤ k := hs.trans selection.total_le
  let kind := enumeratedPattern selection.multiplicity selection.frequent
  let crossing := fun X : Finset V => fun p : Pattern Z =>
    p.cutCount (quotientShore U Z code X)
  let proposed := proposedMultiplicity η D.weight selection.frequent selection.reserve
  let K := fun i => remainingCore (U i) (H i) (C.core i) (range s)
  have hn (p : Pattern Z) : prefixMultiplicity kind s p ≤ selection.multiplicity p :=
    enumeratedPattern_prefix_le selection.multiplicity selection.frequent p s hs
  have hweight (p : Pattern Z) : (proposed p : ℝ) ≤ D.weight p :=
    proposedMultiplicity_le_weight η D.weight selection.frequent selection.reserve
      hη hη1 D.weight_nonneg selection.reserve_weight p
  have hdegree (i : I) (v : U i) : ((k-s : ℕ) : ℝ)-a ≤ ((K i).degree v : ℝ) := by
    rw [Nat.cast_sub hsk]
    exact (C.core_degree s hs i v).1
  have hkloS : α * Fintype.card V ≤ ((k-s : ℕ) : ℝ) := by
    exact hklo.trans (by exact_mod_cast Nat.sub_le_sub_left hs k)
  have hkhiS : ((k-s : ℕ) : ℝ) ≤ 2 * Fintype.card V :=
    (show ((k-s : ℕ) : ℝ) ≤ k by exact_mod_cast Nat.sub_le k s).trans hkhi
  apply no_overfull_after_pattern_deletions G U Z hdisj hZ hcover C.full kind s k hsk
    hregularG hnoG (fun j hj => C.present j (hj.trans_le hs))
    (C.residual_regular s hs) K (C.core_embedded s hs)
    α c θ σ a hα hc hθ hσ hσα hkloS hkhiS ha hlarge hsize
    (C.core_robust s hs) hdegree D.weight D.weight_sum proposed selection.multiplicity
    hn selection.proposed_le hweight crossing
  · intro X hX j hj
    rw [completion_whole_cut_count G U Z hdisj hZ (F j) (C.full j)
      (C.contains j (hj.trans_le hs)) (C.added_internal j (hj.trans_le hs)) X hX]
    have hcount := hFcounts j (hj.trans_le hs) (quotientShore U Z code X)
    rw [wholeUnion_quotientShore U Z code hdisj hZ hcover X hX] at hcount
    exact hcount
  · intro X hX hodd p hp
    apply D.positive_odd_cut hdisj hZ hcover (quotientShore U Z code X) _ p hp
    rw [wholeUnion_quotientShore U Z code hdisj hZ hcover X hX]
    exact hodd
  · intro X hX
    exact D.whole_union_capacity hk hdisj hZ hcover X hX
  · intro X hX heven hsmall p
    let Q : EvenLabelCut U Z code := ⟨quotientShore U Z code X, by
      rw [wholeUnion_quotientShore U Z code hdisj hZ hcover X hX]
      exact heven⟩
    have htest : (graphCutCount G (wholeUnion U Z code Q.val) : ℝ)-
        (∑ p, (proposedMultiplicity η D.weight selection.frequent selection.reserve p : ℝ)*
          p.cutCount Q.val) < 2*a := by
      dsimp only [Q]
      rw [wholeUnion_quotientShore U Z code hdisj hZ hcover X hX]
      exact hsmall
    exact selection.protected_cuts Q htest p

end BoundaryCompletion
end Overfull.Patterns
