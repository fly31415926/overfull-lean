import Overfull.Patterns.Distribution

/-!
# Choosing the frequent pattern and its integer reserve
-/

namespace Overfull.Patterns

open Finset Classical Compression
open scoped BigOperators

theorem patternBound_pos (t : ℕ) : 0 < patternBound t := by
  unfold patternBound
  positivity

variable {V I S : Type*} [Fintype V] [DecidableEq V] [Fintype S]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {U : I → Finset V} {Z : Finset V} {code : I ↪ Fin 4} {k : ℕ}

namespace EncodedDistribution

/-- The actual matching distribution supplies a frequent pattern, a
linear integer reserve, and an actual assigned core for every exceptional
vertex. -/
theorem exists_frequent_reserve (D : EncodedDistribution G U Z code k S)
    (t : ℕ) (hZ : Z.card ≤ t) (hlarge : 6 * patternBound t ≤ k)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i) :
    ∃ p₀ : Pattern Z, ∃ r : ℕ,
      (∀ p, D.weight p ≤ D.weight p₀) ∧
      (k : ℝ) / patternBound t ≤ D.weight p₀ ∧
      (k : ℝ) / (3 * patternBound t) ≤ r ∧
      (r : ℝ) ≤ D.weight p₀ / 2 ∧
      (r : ℝ) ≤ D.weight p₀ ∧
      0 < D.weight p₀ ∧ p₀.internalPairs = ∅ ∧
      (∀ z : Z, ∃ i, p₀.assignment z = code i) := by
  letI : Nonempty (Pattern Z) := ⟨⟨∅, fun _ => 0, ∅⟩⟩
  obtain ⟨p₀, hmax, _⟩ := exists_maximum_weight D.weight
  have hB : (0 : ℝ) < patternBound t := by exact_mod_cast patternBound_pos t
  have hcard : (Fintype.card (Pattern Z) : ℝ) ≤ patternBound t := by
    exact_mod_cast card_pattern_le Z t (by simpa using hZ)
  have hweight := maximum_weight_lower_bound D.weight p₀ k (patternBound t)
    D.weight_nonneg hmax D.weight_sum hB hcard
  have hlargeR : 6 * (patternBound t : ℝ) ≤ k := by exact_mod_cast hlarge
  have hreserve := reserve_floor_bounds (D.weight p₀) k (patternBound t)
    hB hlargeR hweight
  have hk : 0 < k := (Nat.mul_pos (by decide) (patternBound_pos t)).trans_le hlarge
  have hsix : 6 ≤ D.weight p₀ := by
    have hratio : (6 : ℝ) ≤ (k : ℝ) / patternBound t :=
      (le_div_iff₀ hB).mpr hlargeR
    exact hratio.trans hweight
  have hpos : 0 < D.weight p₀ := by linarith
  have hempty := D.internal_pairs_empty_of_weight_gt_one hk p₀ (by linarith)
  obtain ⟨s, _, henc⟩ := D.positive_witness p₀ hpos
  refine ⟨p₀, ⌊D.weight p₀ / 2⌋₊, hmax, hweight, hreserve.1,
    hreserve.2.1, hreserve.2.2, hpos, hempty, ?_⟩
  intro z
  have hnotpaired : ¬ ∃ w : Z, (D.part s).Adj z.val w.val := by
    intro hp
    obtain ⟨e, he, _⟩ := (henc.paired_iff z).mpr hp
    rw [hempty] at he
    exact notMem_empty e he
  obtain ⟨i, _, hi, _, _⟩ := henc.assignment_represented hdisjoint hcover z hnotpaired
  exact ⟨i, hi⟩

/-- Every positive selected multiplicity comes from an actual compressed
matching and has no internal exceptional edge. -/
theorem selected_pattern_witness (D : EncodedDistribution G U Z code k S)
    (hk : 0 < k) (η : ℝ) (p₀ p : Pattern Z) (r n : ℕ)
    (hη₀ : 0 < η) (hη₁ : η ≤ 1) (hr : (r : ℝ) ≤ D.weight p₀)
    (hn : n ≤ proposedMultiplicity η D.weight p₀ r p) (hpos : 0 < n) :
    p.internalPairs = ∅ ∧ ∃ s, D.pattern s = p ∧
      Encodes G U Z code (D.part s) p ∧
      (∀ i, Even (((U i : Set V) \ (D.part s).verts).ncard)) := by
  have hnp : (n : ℝ) ≤ D.weight p :=
    (show (n : ℝ) ≤ proposedMultiplicity η D.weight p₀ r p by exact_mod_cast hn).trans
      (proposedMultiplicity_le_weight η D.weight p₀ r hη₀.le hη₁ D.weight_nonneg hr p)
  have hw : 0 < D.weight p := (show (0 : ℝ) < n by exact_mod_cast hpos).trans_le hnp
  have hempty : p.internalPairs = ∅ := by
    by_contra h
    have hz := D.rounded_internal_pattern_zero hk η p₀ p r hη₀ hη₁ hr
      (Finset.nonempty_iff_ne_empty.mpr h)
    omega
  obtain ⟨s, hs, he⟩ := D.positive_witness p hw
  exact ⟨hempty, s, hs, he, D.parity s⟩

end EncodedDistribution
end Overfull.Patterns
