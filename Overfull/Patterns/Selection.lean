import Overfull.Patterns.Pools
import Overfull.Patterns.Distribution
import Overfull.Patterns.Cuts

/-!
# Choosing and reserving an actual frequent boundary pattern

The capacities are counts of actual host edges. Every discard is tested
against the same original proposal, and the selected multiplicities
retain a linear reserve of one pattern with no exceptional internal edge.
-/

noncomputable section
namespace Overfull.Patterns

open Finset Classical SimpleGraph Compression FractionalMatching MatchingProbability
open scoped BigOperators

theorem patternBound_pos (t : ℕ) : 0 < patternBound t := by
  unfold patternBound
  positivity

instance patternNonempty (E : Type*) [Fintype E] : Nonempty (Pattern E) :=
  ⟨⟨∅,fun _ => 0,∅⟩⟩

def pairIndicator {E : Type*} [Fintype E] [DecidableEq E] (b : BoundaryPair E) (P : Pattern E) : ℕ :=
  if boundaryPairLabels b ∈ P.boundaryEdges then 1 else 0

variable {V I S : Type*} [Fintype V] [DecidableEq V]

/-- Only even whole cuts need protection. Their number is bounded by the
number of all subsets of the exceptional and four core labels. -/
abbrev EvenLabelCut (U : I → Finset V) (Z : Finset V) (code : I ↪ Fin 4) :=
  {Q : Finset (Z ⊕ Fin 4) // (wholeUnion U Z code Q).card % 2 = 0}

theorem card_evenLabelCut_le (U : I → Finset V) (Z : Finset V)
    (code : I ↪ Fin 4) (t : ℕ) (ht : Z.card ≤ t) :
    Fintype.card (EvenLabelCut U Z code) ≤ 2^(t+4) := by
  have hc := Fintype.card_subtype_le (fun Q : Finset (Z ⊕ Fin 4) =>
    (wholeUnion U Z code Q).card % 2 = 0)
  have heq : Fintype.card (Finset (Z ⊕ Fin 4)) = 2^(Z.card+4) := by
    simp
  rw [heq] at hc
  exact hc.trans (Nat.pow_le_pow_right (by omega : 0 < 2) (by omega))

namespace EncodedDistribution

variable [Fintype S] {G : SimpleGraph V} [DecidableRel G.Adj]
  {U : I → Finset V} {Z : Finset V} {code : I ↪ Fin 4} {k : ℕ}
  (D : EncodedDistribution G U Z code k S)

set_option maxHeartbeats 1000000 in
/-- A pattern's pair indicator is backed by a distinct actual compressed
edge. Uniform edge marginals bound the total weight by the pool size. -/
theorem pair_capacity (hk : 0 < k) (b : BoundaryPair Z) :
    (∑ p, D.weight p*(pairIndicator b p : ℝ)) ≤
      (boundaryPool G U Z code b).card := by
  apply D.edge_pool_capacity hk (boundaryPool G U Z code b) (pairIndicator b)
  intro s
  unfold pairIndicator
  split_ifs with hb
  · obtain ⟨e,he,hlabels⟩ := (D.encodes s).boundaryEdge_realized _ hb
    exact Finset.card_pos.mpr ⟨e,mem_inter.mpr
      ⟨he,(mem_boundaryPool G U Z code b e).mpr hlabels⟩⟩
  · exact Nat.zero_le _

/-- The cut capacity is the actual original graph cut, not an assumed
fractional matching distribution in a later residual. -/
theorem label_cut_capacity (hk : 0 < k) (Q : Finset (Z ⊕ Fin 4)) :
    (∑ p, D.weight p*(p.cutCount Q : ℝ)) ≤
      graphCutCount G (wholeUnion U Z code Q) := by
  have h := D.whole_cut_capacity hk (wholeUnion U Z code Q)
    (fun p => p.cutCount Q) (fun s => ((D.encodes s).whole_cut_count Q).symm)
  rw [univ_cut_eq_graph] at h
  exact h

end EncodedDistribution

def discardCoefficient (t : ℕ) : ℕ := (4*t+6)*(t+8)+2^(t+5)

/-- All numerical choices are derived from the actual encoded distribution.
The selected family will be realized by fresh host edges in the next step. -/
structure PatternSelection [Fintype S] (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : I → Finset V) (Z : Finset V) (code : I ↪ Fin 4) (k t : ℕ)
    (D : EncodedDistribution G U Z code k S) (η a : ℝ) where
  frequent : Pattern Z
  reserve : ℕ
  multiplicity : Pattern Z → ℕ
  frequent_lower : (k : ℝ)/patternBound t ≤ D.weight frequent
  frequent_positive : 0 < D.weight frequent
  frequent_no_internal : frequent.internalPairs = ∅
  reserve_lower : (k : ℝ)/(3*patternBound t) ≤ reserve
  reserve_weight : (reserve : ℝ) ≤ D.weight frequent
  total_le : (∑ p, multiplicity p) ≤ k
  retained_lower : reserve ≤ k-∑ p, multiplicity p
  retained_upper : ((k-∑ p, multiplicity p : ℕ) : ℝ) ≤
    reserve+η*k+patternBound t+(discardCoefficient t : ℝ)*a/η
  proposed_le : ∀ p, multiplicity p ≤ proposedMultiplicity η D.weight frequent reserve p
  selected_weight : ∀ p, (multiplicity p : ℝ) ≤ D.weight p
  selected_supported : ∀ p, 0 < multiplicity p → 0 < D.weight p
  selected_no_internal : ∀ p, 0 < multiplicity p → p.internalPairs = ∅
  selected_forest : ∀ p, 0 < multiplicity p → LeafForest p.forest
  sparse_avoided : ∀ p, 0 < multiplicity p → ∀ b : BoundaryPair Z,
    boundaryPairLabels b ∈ p.boundaryEdges →
      ((t : ℝ)+8)*a/η ≤ (boundaryPool G U Z code b).card
  pair_demand : ∀ b : BoundaryPair Z,
    (∑ p, (multiplicity p : ℝ)*pairIndicator b p) ≤
      (1-η)*(boundaryPool G U Z code b).card
  pair_reserved : ∀ b : BoundaryPair Z,
    (reserve : ℝ)*pairIndicator b frequent ≤ (boundaryPool G U Z code b).card -
      ∑ p, (multiplicity p : ℝ)*pairIndicator b p
  protected_cuts : ∀ Q : EvenLabelCut U Z code,
    (graphCutCount G (wholeUnion U Z code Q.val) : ℝ) -
      (∑ p, (proposedMultiplicity η D.weight frequent reserve p : ℝ)*p.cutCount Q.val) < 2*a →
      ∀ p, multiplicity p*p.cutCount Q.val = 0

set_option maxHeartbeats 1000000 in
/-- The maximum-weight pattern, rounding, sparse-pair discards, and even-cut
protection are constructed together with all quantitative bounds. -/
theorem exists_pattern_selection [Fintype S]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : I → Finset V) (Z : Finset V) (code : I ↪ Fin 4) (k t : ℕ)
    (D : EncodedDistribution G U Z code k S) (η a : ℝ)
    (hk : 0 < k) (ht : Z.card ≤ t) (hlarge : (6 : ℝ)*patternBound t ≤ k)
    (hη : 0 < η) (hη1 : η ≤ 1) (ha : 0 ≤ a) :
    Nonempty (PatternSelection G U Z code k t D η a) := by
  let B : ℝ := patternBound t
  have hB : 0 < B := by
    dsimp [B]
    exact_mod_cast patternBound_pos t
  obtain ⟨p₀,hmax,_⟩ := exists_maximum_weight D.weight
  have hcard : (Fintype.card (Pattern Z) : ℝ) ≤ B := by
    dsimp [B]
    exact_mod_cast card_pattern_le Z t (by simpa using ht)
  have hw₀ := maximum_weight_lower_bound D.weight p₀ k B D.weight_nonneg
    hmax D.weight_sum hB hcard
  have hw₀six : (6 : ℝ) ≤ D.weight p₀ :=
    ((le_div_iff₀ hB).mpr (by simpa [B,mul_comm] using hlarge)).trans hw₀
  have hw₀pos : 0 < D.weight p₀ := by linarith only [hw₀six]
  let r : ℕ := ⌊D.weight p₀/2⌋₊
  have hr := reserve_floor_bounds (D.weight p₀) k B hB hlarge hw₀
  change (k : ℝ)/(3*B) ≤ (r : ℝ) ∧ (r : ℝ) ≤ D.weight p₀/2 ∧
    (r : ℝ) ≤ D.weight p₀ at hr
  let pc := fun b : BoundaryPair Z => pairIndicator b
  let pd := fun b : BoundaryPair Z => ((boundaryPool G U Z code b).card : ℝ)
  let cc := fun Q : EvenLabelCut U Z code => fun p : Pattern Z => p.cutCount Q.val
  let cd := fun Q : EvenLabelCut U Z code =>
    (graphCutCount G (wholeUnion U Z code Q.val) : ℝ)
  let proposed := proposedMultiplicity η D.weight p₀ r
  let L := ((t : ℝ)+8)*a/η
  let keep := pairCutKeep pc pd cc cd proposed L a
  let m := acceptedMultiplicity keep proposed
  have hproposed (p) : m p ≤ proposed p := acceptedMultiplicity_le keep proposed p
  have hmweight (p) : (m p : ℝ) ≤ D.weight p :=
    (show (m p : ℝ) ≤ proposed p by exact_mod_cast hproposed p).trans
      (proposedMultiplicity_le_weight η D.weight p₀ r hη.le hη1 D.weight_nonneg hr.2.2 p)
  have hmsupport (p) (hp : 0 < m p) : 0 < D.weight p :=
    (show (0 : ℝ) < m p by exact_mod_cast hp).trans_le (hmweight p)
  have hmkeep (p) (hp : 0 < m p) : keep p := by
    by_contra hn
    have hz : m p = 0 := by simp [m,acceptedMultiplicity,hn]
    omega
  have hpairs := D.pair_capacity hk
  have hcuts (Q : EvenLabelCut U Z code) := D.label_cut_capacity hk Q.val
  have hdiscard := pair_cut_discard_bound η a L D.weight p₀ r pc pd cc cd
    hη hη1 ha (by dsimp [L]; positivity) D.weight_nonneg hr.2.2 hpairs hcuts
  change (∑ p, (proposed p : ℝ)) ≤ (∑ p, (m p : ℝ)) +
    (Fintype.card (BoundaryPair Z) : ℝ)*L +
      (Fintype.card (EvenLabelCut U Z code) : ℝ)*(2*a/η) at hdiscard
  have hJ : Fintype.card (BoundaryPair Z) ≤ 4*t+6 := by
    rw [card_boundaryPair]
    simpa only [Fintype.card_coe] using (show 4*Z.card+6 ≤ 4*t+6 by omega)
  have hcoeff := four_core_discard_coefficient t (Fintype.card (BoundaryPair Z))
    (Fintype.card (EvenLabelCut U Z code)) a η hJ
    (card_evenLabelCut_le U Z code t ht) ha hη
  change (Fintype.card (BoundaryPair Z) : ℝ)*L +
    (Fintype.card (EvenLabelCut U Z code) : ℝ)*(2*a/η) ≤
      (discardCoefficient t : ℝ)*a/η at hcoeff
  have hdiscard' : (∑ p, (proposed p : ℝ)) ≤ (∑ p, (m p : ℝ)) +
      (discardCoefficient t : ℝ)*a/η := by linarith only [hdiscard,hcoeff]
  have hret := accepted_natural_residual_bounds η D.weight p₀ r k
    ((discardCoefficient t : ℝ)*a/η) keep hη.le hη1 D.weight_nonneg hr.2.2
    D.weight_sum hdiscard'
  change (k-∑ p, m p)+(∑ p, m p) = k ∧ r ≤ k-∑ p, m p ∧
    ((k-∑ p, m p : ℕ) : ℝ) ≤
      r+η*k+Fintype.card (Pattern Z)+(discardCoefficient t : ℝ)*a/η at hret
  have htotal : (∑ p, m p) ≤ k := by omega
  refine ⟨⟨p₀,r,m,hw₀,hw₀pos,
    D.internal_pairs_empty_of_weight_gt_one hk p₀ (by linarith only [hw₀six]),
    hr.1,hr.2.2,htotal,hret.2.1,?_,hproposed,hmweight,hmsupport,?_,?_,?_,?_,?_,?_⟩⟩
  · have hh := hret.2.2
    change ((k-∑ p, m p : ℕ) : ℝ) ≤ r+η*k+B+(discardCoefficient t : ℝ)*a/η
    linarith only [hh,hcard]
  · intro p hp
    by_contra hn
    have hz := D.rounded_internal_pattern_zero hk η p₀ p r hη hη1 hr.2.2
      (Finset.nonempty_iff_ne_empty.mpr hn)
    have hmp := hproposed p
    change m p ≤ proposedMultiplicity η D.weight p₀ r p at hmp
    omega
  · intro p hp
    obtain ⟨s,_,henc⟩ := D.positive_witness p (hmsupport p hp)
    exact henc.forest
  · intro p hp b hb
    by_contra hn
    have hz := (hmkeep p hp).1 b (lt_of_not_ge hn)
    change pairIndicator b p = 0 at hz
    simp only [pairIndicator,ite_eq_right_iff,one_ne_zero,imp_false] at hz
    exact hz hb
  · intro b
    have hb := proposed_cut_reserve η D.weight (fun p => (pairIndicator b p : ℝ))
      p₀ r (pd b) hη1 D.weight_nonneg hr.2.2 (fun _ => Nat.cast_nonneg _) (hpairs b)
    have hm : (∑ p, (m p : ℝ)*pairIndicator b p) ≤
        ∑ p, (proposed p : ℝ)*pairIndicator b p := by
      apply sum_le_sum
      intro p _
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hproposed p) (Nat.cast_nonneg _)
    change (∑ p, (m p : ℝ)*pairIndicator b p) ≤ (1-η)*pd b
    change η*pd b ≤ pd b-∑ p, (proposed p : ℝ)*pairIndicator b p at hb
    nlinarith only [hb,hm]
  · intro b
    exact prefix_pair_reserve η D.weight p₀ r m (pc b) (pd b) hη.le hη1
      D.weight_nonneg hr.2.2 hproposed (hpairs b)
  · intro Q hQ p
    exact accepted_zero_on_protected_cut pc pd cc cd proposed L a Q hQ p

end Overfull.Patterns
