import Overfull.Patterns.Capacity

/-!
# One fixed rounding and discard plan

We test all quotient pairs and all quotient shores. This harmless
overcount gives the explicit coefficient `2^(t+4)*(t+10)` in the
manuscript's `O_t(a/η)` term. Every test uses the same proposal.
-/

namespace Overfull.Patterns

open Finset Classical MatchingProbability PatternRealization
open scoped BigOperators

def discardCoefficient (t : ℕ) : ℕ := 2 ^ (t + 4) * (t + 10)

variable {V I S : Type*} [Fintype V] [DecidableEq V] [Fintype S]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {U : I → Finset V} {Z : Finset V} {code : I ↪ Fin 4} {k : ℕ}

namespace EncodedDistribution

variable (D : EncodedDistribution G U Z code k S)

noncomputable def plannedKeep (η a : ℝ) (t : ℕ) (p₀ : Pattern Z) (r : ℕ) : Pattern Z → Prop :=
  pairCutKeep pairUse (fun b => ((boundaryPool G U Z code b).card : ℝ))
    (fun Q p => p.cutCount Q) (fun Q => (graphCutCount G (wholeUnion U Z code Q) : ℝ))
    (proposedMultiplicity η D.weight p₀ r) (((t : ℝ) + 8) * a / η) a

noncomputable def plannedMultiplicity (η a : ℝ) (t : ℕ) (p₀ : Pattern Z) (r : ℕ) : Pattern Z → ℕ :=
  acceptedMultiplicity (D.plannedKeep η a t p₀ r) (proposedMultiplicity η D.weight p₀ r)

theorem planned_le_proposed (η a : ℝ) (t : ℕ) (p₀ p : Pattern Z) (r : ℕ) :
    D.plannedMultiplicity η a t p₀ r p ≤ proposedMultiplicity η D.weight p₀ r p :=
  acceptedMultiplicity_le _ _ p

omit [Fintype V] [DecidableEq V] in
theorem quotient_test_count (t : ℕ) (hZ : Z.card ≤ t) :
    Fintype.card (Finset (Z ⊕ Fin 4)) ≤ 2 ^ (t + 4) := by
  simp only [Fintype.card_finset, Fintype.card_sum, Fintype.card_coe, Fintype.card_fin]
  exact Nat.pow_le_pow_right (by decide) (Nat.add_le_add_right hZ 4)

/-- The discarded colors are charged to one finite family of pair and
cut tests, with no sequential redefinition of a test. -/
theorem planned_discard_bound (hk : 0 < k) (η a : ℝ) (t : ℕ)
    (p₀ : Pattern Z) (r : ℕ) (hη₀ : 0 < η) (hη₁ : η ≤ 1)
    (ha : 0 ≤ a) (hr : (r : ℝ) ≤ D.weight p₀) (hZ : Z.card ≤ t) :
    (∑ p, (proposedMultiplicity η D.weight p₀ r p : ℝ)) ≤
      (∑ p, (D.plannedMultiplicity η a t p₀ r p : ℝ)) +
        (discardCoefficient t : ℝ) * a / η := by
  have h := pair_cut_discard_bound η a (((t : ℝ) + 8) * a / η) D.weight p₀ r
    pairUse (fun b => ((boundaryPool G U Z code b).card : ℝ))
    (fun Q p => p.cutCount Q) (fun Q => (graphCutCount G (wholeUnion U Z code Q) : ℝ))
    hη₀ hη₁ ha (by positivity) D.weight_nonneg hr
    (D.pair_capacity hk) (D.whole_cut_capacity_actual hk)
  change (∑ p, (proposedMultiplicity η D.weight p₀ r p : ℝ)) ≤
    (∑ p, (D.plannedMultiplicity η a t p₀ r p : ℝ)) +
      (Fintype.card (Finset (Z ⊕ Fin 4)) : ℝ) * (((t : ℝ) + 8) * a / η) +
      (Fintype.card (Finset (Z ⊕ Fin 4)) : ℝ) * (2 * a / η) at h
  have hcard : (Fintype.card (Finset (Z ⊕ Fin 4)) : ℝ) ≤ (2 : ℝ) ^ (t + 4) := by
    exact_mod_cast quotient_test_count t hZ
  have h₁ := mul_le_mul_of_nonneg_right hcard
    (show 0 ≤ ((t : ℝ) + 8) * a / η by positivity)
  have h₂ := mul_le_mul_of_nonneg_right hcard (show 0 ≤ 2 * a / η by positivity)
  have hcoef : (2 : ℝ) ^ (t + 4) * (((t : ℝ) + 8) * a / η) +
      (2 : ℝ) ^ (t + 4) * (2 * a / η) = (discardCoefficient t : ℝ) * a / η := by
    unfold discardCoefficient
    push_cast
    ring
  linarith

theorem planned_residual_bounds (hk : 0 < k) (η a : ℝ) (t : ℕ)
    (p₀ : Pattern Z) (r : ℕ) (hη₀ : 0 < η) (hη₁ : η ≤ 1)
    (ha : 0 ≤ a) (hr : (r : ℝ) ≤ D.weight p₀) (hZ : Z.card ≤ t) :
    let m := D.plannedMultiplicity η a t p₀ r
    let h := k - ∑ p, m p
    h + (∑ p, m p) = k ∧ r ≤ h ∧
      (h : ℝ) ≤ r + η * k + patternBound t + (discardCoefficient t : ℝ) * a / η := by
  have hh := accepted_natural_residual_bounds η D.weight p₀ r k
    ((discardCoefficient t : ℝ) * a / η) (D.plannedKeep η a t p₀ r)
    hη₀.le hη₁ D.weight_nonneg hr D.weight_sum
    (D.planned_discard_bound hk η a t p₀ r hη₀ hη₁ ha hr hZ)
  have hcard : (Fintype.card (Pattern Z) : ℝ) ≤ patternBound t := by
    exact_mod_cast card_pattern_le Z t (by simpa using hZ)
  dsimp only at hh ⊢
  change _ ∧ _ ∧ (↑(k - ∑ p, D.plannedMultiplicity η a t p₀ r p) : ℝ) ≤ _ at hh
  exact ⟨hh.1, hh.2.1, by linarith [hh.2.2]⟩

theorem positive_planned_keep (η a : ℝ) (t : ℕ) (p₀ p : Pattern Z) (r : ℕ)
    (hp : 0 < D.plannedMultiplicity η a t p₀ r p) : D.plannedKeep η a t p₀ r p := by
  by_contra hn
  simp only [plannedMultiplicity, acceptedMultiplicity, if_neg hn] at hp
  omega

/-- Every used pair has the original pool size required for endpoint
conflict slack. -/
theorem planned_pool_lower (η a : ℝ) (t : ℕ) (p₀ p : Pattern Z) (r : ℕ)
    (hp : 0 < D.plannedMultiplicity η a t p₀ r p)
    (b : Finset (Z ⊕ Fin 4)) (hb : b ∈ p.boundaryEdges) :
    ((t : ℝ) + 8) * a / η ≤ (boundaryPool G U Z code b).card := by
  have hkeep := D.positive_planned_keep η a t p₀ p r hp
  by_contra hn
  have hh := hkeep.1 b (lt_of_not_ge hn)
  simp only [pairUse, if_pos hb] at hh
  omega

/-- A protected cut loses no edge in any accepted pattern. -/
theorem planned_protected_zero (η a : ℝ) (t : ℕ) (p₀ : Pattern Z) (r : ℕ)
    (Q : Finset (Z ⊕ Fin 4))
    (hQ : (graphCutCount G (wholeUnion U Z code Q) : ℝ) -
      (∑ p, (proposedMultiplicity η D.weight p₀ r p : ℝ) * p.cutCount Q) < 2 * a)
    (p : Pattern Z) : D.plannedMultiplicity η a t p₀ r p * p.cutCount Q = 0 :=
  accepted_zero_on_protected_cut pairUse
    (fun b => ((boundaryPool G U Z code b).card : ℝ))
    (fun Q p => p.cutCount Q) (fun Q => (graphCutCount G (wholeUnion U Z code Q) : ℝ))
    (proposedMultiplicity η D.weight p₀ r) (((t : ℝ) + 8) * a / η) a Q hQ p

theorem planned_pair_demand (hk : 0 < k) (η a : ℝ) (t : ℕ)
    (p₀ : Pattern Z) (r : ℕ) (hη₁ : η ≤ 1)
    (hr : (r : ℝ) ≤ D.weight p₀) (b : Finset (Z ⊕ Fin 4)) :
    (∑ p, (D.plannedMultiplicity η a t p₀ r p : ℝ) * pairUse b p) ≤
      (1 - η) * ((boundaryPool G U Z code b).card - (r : ℝ) * pairUse b p₀) := by
  apply le_trans _ (proposed_demand_le η D.weight (fun p => (pairUse b p : ℝ))
    p₀ r ((boundaryPool G U Z code b).card : ℝ) hη₁ D.weight_nonneg hr
    (fun p => Nat.cast_nonneg _) (D.pair_capacity hk b))
  apply sum_le_sum
  intro p _
  exact mul_le_mul_of_nonneg_right
    (by exact_mod_cast D.planned_le_proposed η a t p₀ p r) (Nat.cast_nonneg _)

end EncodedDistribution
end Overfull.Patterns
