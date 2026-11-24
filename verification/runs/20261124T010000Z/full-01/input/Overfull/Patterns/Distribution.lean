import Overfull.Patterns.Encoding
import Overfull.Patterns.Weights
import Overfull.Patterns.Rounding

/-!
# An actual fractional matching distribution with common finite patterns

Every compressed matching is chosen inside its original perfect matching.
Its code uses one fixed embedding of the core labels. The scaled pattern
weights are therefore backed by the actual uniform edge marginals.
-/

namespace Overfull.Patterns

open Finset Classical SimpleGraph Compression FractionalMatching MatchingProbability
open scoped BigOperators

variable {V I S : Type*} [Fintype V] [DecidableEq V]

structure EncodedDistribution (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : I → Finset V) (Z : Finset V) (code : I ↪ Fin 4) (k : ℕ)
    (S : Type*) [Fintype S] where
  original : Distribution G k S
  part : S → G.Subgraph
  pattern : S → Pattern Z
  encodes : ∀ s, Encodes G U Z code (part s) (pattern s)
  contained : ∀ s, part s ≤ original.matching s
  retain_exceptional : ∀ s u v, (original.matching s).Adj u v →
    u ∈ Z ∨ v ∈ Z → (part s).Adj u v
  edge_card : ∀ s, (part s).edgeSet.ncard ≤ Z.card + 3
  vertex_card : ∀ s, (part s).verts.ncard ≤ 2 * Z.card + 6
  footprint : ∀ s i, ((part s).verts.toFinset ∩ U i).card ≤ 2 * Z.card + 6
  parity : ∀ s i, Even (((U i : Set V) \ (part s).verts).ncard)

/-- The checked matching polytope and compression theorems construct all
samples and all patterns; no distribution or compression oracle is given. -/
theorem exists_encoded_distribution (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : I → Finset V) (Z : Finset V) (code : I ↪ Fin 4) (k : ℕ)
    (hk : 0 < k) (hregular : ∀ v, G.degree v = k)
    (hno : ∀ X : Finset V, ¬ IsOverfull G k X)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hUZ : ∀ i, Disjoint (U i) Z)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i) :
    ∃ S : Type, ∃ _ : Fintype S, Nonempty (EncodedDistribution G U Z code k S) := by
  obtain ⟨S, hS, ⟨D⟩⟩ := MatchingProbability.exists_distribution hk hregular hno
  letI := hS
  have hex (s : S) := exists_compressed_encoding G U Z code hdisjoint hUZ hcover
    (D.matching s) (D.perfect s)
  choose F P henc hsub hretain hE hV hfoot hpar using hex
  exact ⟨S, hS, ⟨⟨D, F, P, henc, hsub, hretain, hE, hV, hfoot, hpar⟩⟩⟩

namespace EncodedDistribution

variable [Fintype S] {G : SimpleGraph V} [DecidableRel G.Adj]
  {U : I → Finset V} {Z : Finset V} {code : I ↪ Fin 4} {k : ℕ}
  (D : EncodedDistribution G U Z code k S)

noncomputable def weight (p : Pattern Z) : ℝ :=
  aggregateWeight (scaledWeight D.original) D.pattern p

theorem weight_nonneg (p : Pattern Z) : 0 ≤ D.weight p :=
  aggregateWeight_nonneg _ (scaledWeight_nonneg D.original) _ p

theorem weight_sum : ∑ p, D.weight p = k := by
  change (∑ p, aggregateWeight (scaledWeight D.original) D.pattern p) = k
  rw [aggregateWeight_sum, scaledWeight_sum]

theorem positive_witness (p : Pattern Z) (hp : 0 < D.weight p) :
    ∃ s, D.pattern s = p ∧ Encodes G U Z code (D.part s) p := by
  obtain ⟨s, hs, _⟩ := aggregateWeight_pos_witness _ D.pattern p hp
  exact ⟨s, hs, hs ▸ D.encodes s⟩

theorem internal_pair_weight_le_one (hk : 0 < k) (p : Pattern Z)
    (hp : p.internalPairs.Nonempty) : D.weight p ≤ 1 := by
  by_cases hw : 0 < D.weight p
  · obtain ⟨s₀, _, henc₀⟩ := D.positive_witness p hw
    obtain ⟨pair, hpair⟩ := hp
    obtain ⟨z, w, _, hends⟩ := Finset.card_eq_two.mp pair.property
    have hadj₀ := henc₀.internal_pair_adj pair hpair z w hends
    let e : G.edgeSet := ⟨s(z.val, w.val), (D.part s₀).adj_sub hadj₀⟩
    apply aggregateWeight_le_one_of_edge D.original hk D.pattern p e
    intro s hs
    have henc : Encodes G U Z code (D.part s) p := hs ▸ D.encodes s
    exact (D.contained s).2 (henc.internal_pair_adj pair hpair z w hends)
  · linarith

/-- A pattern whose weight exceeds one assigns every exceptional vertex
to a core; no internal exceptional pair can occur. -/
theorem internal_pairs_empty_of_weight_gt_one (hk : 0 < k)
    (p : Pattern Z) (hp : 1 < D.weight p) : p.internalPairs = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  have h := D.internal_pair_weight_le_one hk p ⟨e, he⟩
  linarith

/-- Flooring removes every possible internal-exceptional-pair pattern. -/
theorem rounded_internal_pattern_zero (hk : 0 < k) (η : ℝ)
    (p₀ p : Pattern Z) (r : ℕ) (hη₀ : 0 < η) (hη₁ : η ≤ 1)
    (hr : (r : ℝ) ≤ D.weight p₀) (hp : p.internalPairs.Nonempty) :
    proposedMultiplicity η D.weight p₀ r p = 0 :=
  proposedMultiplicity_eq_zero_of_weight_le_one η D.weight p₀ r
    hη₀ hη₁ D.weight_nonneg hr p (D.internal_pair_weight_le_one hk p hp)

theorem edge_pool_capacity (hk : 0 < k) (A : Finset G.edgeSet)
    (count : Pattern Z → ℕ)
    (hcount : ∀ s, count (D.pattern s) ≤ (matchingEdges (D.part s) ∩ A).card) :
    (∑ p, D.weight p * (count p : ℝ)) ≤ A.card := by
  apply aggregate_capacity D.original hk D.pattern (fun s => matchingEdges (D.part s))
    (fun s => ForceMatching.matchingEdges_mono _ _ (D.contained s)) A count
  intro s
  convert hcount s using 1
  congr 1
  ext e
  simp only [Finset.mem_inter]

theorem whole_cut_capacity (hk : 0 < k) (X : Finset V)
    (crossing : Pattern Z → ℕ)
    (hcrossing : ∀ s, crossing (D.pattern s) = cutCount (matchingEdges (D.part s)) X) :
    (∑ p, D.weight p * (crossing p : ℝ)) ≤ cutCount (univ : Finset G.edgeSet) X :=
  aggregate_cut_capacity D.original hk D.pattern (fun s => matchingEdges (D.part s))
    (fun s => ForceMatching.matchingEdges_mono _ _ (D.contained s)) X crossing hcrossing

end EncodedDistribution
end Overfull.Patterns
