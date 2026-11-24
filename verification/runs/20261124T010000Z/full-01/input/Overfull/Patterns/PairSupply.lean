import Overfull.Patterns.Capacity
import Overfull.Patterns.Completion
import Overfull.Patterns.PoolNeighbors

/-!
# Actual residual supply in the reserved quotient pairs

The identities count original-host edge copies that survive a present
perfect-matching deletion sequence. Internal completions do not change
the quotient-pair use, so numerical pair reserves become actual residual
edge and neighbor supplies.
-/

noncomputable section
namespace Overfull.Patterns

open Finset Classical SimpleGraph Compression FractionalMatching MatchingProbability
open ForeignPhase PatternRealization
open scoped BigOperators

variable {V I : Type*} [Fintype V] [DecidableEq V]

/-- A deletion partitions each fixed original edge pool exactly. -/
theorem surviving_pool_step (G R : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset G.edgeSet) (N : G.Subgraph) (hpresent : N.spanningCoe ≤ R) :
    (survivingEdges G (R \ N.spanningCoe) A).card +
      (matchingEdges N ∩ A).card = (survivingEdges G R A).card := by
  have hsd : survivingEdges G (R \ N.spanningCoe) A =
      survivingEdges G R A \ matchingEdges N := by
    ext e
    simp only [mem_survivingEdges,mem_sdiff,matchingEdges,mem_filter,mem_univ,true_and,
      SimpleGraph.edgeSet_sdiff,Set.mem_diff]
    tauto
  rw [hsd]
  have heq : survivingEdges G R A ∩ matchingEdges N = matchingEdges N ∩ A := by
    ext e
    simp only [mem_inter,mem_survivingEdges]
    constructor
    · rintro ⟨⟨heA,_heR⟩,heN⟩
      exact ⟨heN,heA⟩
    · rintro ⟨heN,heA⟩
      have heN' : e.val ∈ N.edgeSet := (mem_filter.mp heN).2
      exact ⟨⟨heA,SimpleGraph.edgeSet_mono hpresent heN'⟩,heN⟩
  rw [← heq]
  exact Finset.card_sdiff_add_card_inter (survivingEdges G R A) (matchingEdges N)

/-- Exact pool accounting over every present prefix. -/
theorem afterDeletions_pool_accounting (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset G.edgeSet) (N : ℕ → G.Subgraph) (s : ℕ)
    (hpresent : ∀ j < s, (N j).spanningCoe ≤ afterDeletions G N j) :
    (survivingEdges G (afterDeletions G N s) A).card +
      (∑ j ∈ range s, (matchingEdges (N j) ∩ A).card) = A.card := by
  induction s with
  | zero => simp [survivingEdges]
  | succ s ih =>
    have hh := ih (fun j hj => hpresent j (Nat.lt_succ_of_lt hj))
    have hstep := surviving_pool_step G (afterDeletions G N s) A (N s)
      (hpresent s (Nat.lt_succ_self s))
    rw [← afterDeletions_succ] at hstep
    rw [sum_range_succ]
    omega

/-- Actual surviving original-host copies and residual-host pool copies
have identical cardinalities. -/
theorem surviving_boundaryPool_card (G R : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel R.Adj] (hRG : R ≤ G)
    (U : I → Finset V) (Z : Finset V) (code : I ↪ Fin 4)
    (b : Finset (Z ⊕ Fin 4)) :
    (survivingEdges G R (boundaryPool G U Z code b)).card =
      (boundaryPool R U Z code b).card := by
  apply Finset.card_bij
    (fun e he => (⟨e.val,(mem_survivingEdges G R _ e |>.mp he).2⟩ : R.edgeSet))
  · intro e he
    have hb := (mem_boundaryPool G U Z code b e).mp
      (mem_survivingEdges G R _ e |>.mp he).1
    exact (mem_boundaryPool R U Z code b _).mpr hb
  · intro e he f hf hef
    exact Subtype.ext (congrArg (fun q : R.edgeSet => q.val) hef)
  · intro e he
    let f : G.edgeSet := ⟨e.val,SimpleGraph.edgeSet_mono hRG e.property⟩
    refine ⟨f,?_,rfl⟩
    exact (mem_survivingEdges G R _ f).mpr
      ⟨(mem_boundaryPool G U Z code b f).mpr ((mem_boundaryPool R U Z code b e).mp he),e.property⟩

variable {G : SimpleGraph V} [DecidableRel G.Adj]
    {U : I → Finset V} {Z : Finset V} {code : I ↪ Fin 4}

/-- Raw realized boundaries use each of their prescribed pairs exactly once. -/
theorem RealizesPattern.pool_count {P : Pattern Z} {F : G.Subgraph}
    (hF : RealizesPattern G U Z code P F) (b : Finset (Z ⊕ Fin 4)) :
    (matchingEdges F ∩ boundaryPool G U Z code b).card = pairUse b P := by
  have heq : matchingEdges F ∩ boundaryPool G U Z code b =
      (matchingEdges F).filter (fun e => labelledEdge G U Z code e = b) := by
    ext e
    simp only [mem_inter,mem_boundaryPool,mem_filter]
  rw [heq,fiber_card_of_injective _ _ hF.projection_injective,hF.boundary_image]
  rfl

/-- An internal-core edge has only one quotient label, so it is absent
from every genuine two-label pair pool. -/
theorem boundaryPool_not_internal_of_card
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hUZ : ∀ i, Disjoint (U i) Z)
    (b : Finset (Z ⊕ Fin 4)) (hb : b.card = 2)
    (e : G.edgeSet) (he : e ∈ boundaryPool G U Z code b)
    (i : I) (u v : V) (hu : u ∈ U i) (hv : v ∈ U i) : e.val ≠ s(u,v) := by
  intro heq
  have huZ : u ∉ Z := fun hh => disjoint_left.mp (hUZ i) hu hh
  have hvZ : v ∉ Z := fun hh => disjoint_left.mp (hUZ i) hv hh
  have hlabel : labelledEdge G U Z code e = {Sum.inr (code i)} := by
    rw [labelledEdge,heq,Sym2.toFinset_mk_eq]
    simp [boundaryLabel_outside U Z code u huZ,boundaryLabel_outside U Z code v hvZ,
      coreLabel_of_mem U code hdisjoint hu,coreLabel_of_mem U code hdisjoint hv]
  rw [← (mem_boundaryPool G U Z code b e).mp he,hlabel] at hb
  simp at hb

/-- Adding only internal-core edges preserves every genuine boundary pool. -/
theorem completed_boundaryPool_eq
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hUZ : ∀ i, Disjoint (U i) Z)
    (F N : G.Subgraph) (hFN : F ≤ N)
    (hadded : ∀ u v, N.Adj u v → F.Adj u v ∨ ∃ i, u ∈ U i ∧ v ∈ U i)
    (b : Finset (Z ⊕ Fin 4)) (hb : b.card = 2) :
    matchingEdges N ∩ boundaryPool G U Z code b =
      matchingEdges F ∩ boundaryPool G U Z code b := by
  ext e
  simp only [mem_inter]
  constructor
  · rintro ⟨heN,heB⟩
    have hN : N.Adj (firstEnd e) (secondEnd e) := by
      have h := (mem_filter.mp heN).2
      rw [← edge_eq e] at h
      exact h
    refine ⟨?_,heB⟩
    rcases hadded _ _ hN with hF | ⟨i,hi,hj⟩
    · apply mem_filter.mpr
      refine ⟨mem_univ _,?_⟩
      rw [← edge_eq e]
      exact hF
    · exact (boundaryPool_not_internal_of_card hdisjoint hUZ b hb e heB
        i (firstEnd e) (secondEnd e) hi hj (edge_eq e).symm).elim
  · rintro ⟨heF,heB⟩
    refine ⟨mem_filter.mpr ⟨mem_univ _,?_⟩,heB⟩
    have hF : F.Adj (firstEnd e) (secondEnd e) := by
      have hh := (mem_filter.mp heF).2
      rw [← edge_eq e] at hh
      exact hh
    rw [← edge_eq e]
    exact hFN.2 hF

/-- Exact pattern-use accounting for the completed family at every prefix. -/
theorem completed_pattern_pool_accounting
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hUZ : ∀ i, Disjoint (U i) Z)
    (F N : ℕ → G.Subgraph) (P : ℕ → Pattern Z) (s : ℕ)
    (hpresent : ∀ j < s, (N j).spanningCoe ≤ afterDeletions G N j)
    (hreal : ∀ j < s, RealizesPattern G U Z code (P j) (F j))
    (hcontains : ∀ j < s, F j ≤ N j)
    (hadded : ∀ j < s, ∀ u v, (N j).Adj u v →
      (F j).Adj u v ∨ ∃ i, u ∈ U i ∧ v ∈ U i)
    (b : Finset (Z ⊕ Fin 4)) (hb : b.card = 2) :
    (survivingEdges G (afterDeletions G N s) (boundaryPool G U Z code b)).card +
      (∑ j ∈ range s, pairUse b (P j)) = (boundaryPool G U Z code b).card := by
  have heq (j : ℕ) (hj : j ∈ range s) :
      (matchingEdges (N j) ∩ boundaryPool G U Z code b).card = pairUse b (P j) := by
    rw [completed_boundaryPool_eq hdisjoint hUZ (F j) (N j)
      (hcontains j (mem_range.mp hj)) (hadded j (mem_range.mp hj)) b hb]
    exact (hreal j (mem_range.mp hj)).pool_count b
  simpa only [Finset.sum_congr rfl heq] using
    afterDeletions_pool_accounting G (boundaryPool G U Z code b) N s hpresent

omit [Fintype V] in
/-- Exact actual counts turn the numerical distinguished-pair reserve
into a lower bound for the number of surviving copies. -/
theorem pair_reserve_of_accounting (w : Pattern Z → ℝ) (p₀ : Pattern Z)
    (η : ℝ) (r c d : ℕ) (n : Pattern Z → ℕ) (b : Finset (Z ⊕ Fin 4))
    (hη₀ : 0 ≤ η) (hη₁ : η ≤ 1) (hw : ∀ p, 0 ≤ w p)
    (hr : (r : ℝ) ≤ w p₀) (hn : ∀ p, n p ≤ proposedMultiplicity η w p₀ r p)
    (hcap : (∑ p, w p * (pairUse b p : ℝ)) ≤ d)
    (haccount : c + ∑ p, n p * pairUse b p = d)
    (hb : b ∈ p₀.boundaryEdges) : r ≤ c := by
  have hreserve := prefix_pair_reserve η w p₀ r n (pairUse b) (d : ℝ)
    hη₀ hη₁ hw hr hn hcap
  have haccount' : (c : ℝ) + ∑ p, (n p : ℝ) * (pairUse b p : ℝ) = d := by
    exact_mod_cast haccount
  have hp₀ : pairUse b p₀ = 1 := by simp [pairUse,hb]
  rw [hp₀,Nat.cast_one,mul_one] at hreserve
  have hh : (r : ℝ) ≤ c := by linarith only [hreserve,haccount']
  exact_mod_cast hh

/-- Completed pattern deletions preserve the distinguished pair reserve
in the actual residual graph. -/
theorem completed_pattern_pool_reserved
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hUZ : ∀ i, Disjoint (U i) Z)
    (F N : ℕ → G.Subgraph) (P : ℕ → Pattern Z) (s : ℕ)
    (hpresent : ∀ j < s, (N j).spanningCoe ≤ afterDeletions G N j)
    (hreal : ∀ j < s, RealizesPattern G U Z code (P j) (F j))
    (hcontains : ∀ j < s, F j ≤ N j)
    (hadded : ∀ j < s, ∀ u v, (N j).Adj u v →
      (F j).Adj u v ∨ ∃ i, u ∈ U i ∧ v ∈ U i)
    (w : Pattern Z → ℝ) (p₀ : Pattern Z) (η : ℝ) (r : ℕ) (n : Pattern Z → ℕ)
    (hη₀ : 0 ≤ η) (hη₁ : η ≤ 1) (hw : ∀ p, 0 ≤ w p)
    (hr : (r : ℝ) ≤ w p₀) (hn : ∀ p, n p ≤ proposedMultiplicity η w p₀ r p)
    (b : Finset (Z ⊕ Fin 4)) (hbcard : b.card = 2) (hb : b ∈ p₀.boundaryEdges)
    (hcap : (∑ p, w p * (pairUse b p : ℝ)) ≤ (boundaryPool G U Z code b).card)
    (hcounts : (∑ j ∈ range s, pairUse b (P j)) = ∑ p, n p * pairUse b p) :
    r ≤ (boundaryPool (afterDeletions G N s) U Z code b).card := by
  have haccount := completed_pattern_pool_accounting hdisjoint hUZ F N P s
    hpresent hreal hcontains hadded b hbcard
  rw [hcounts] at haccount
  have hres := pair_reserve_of_accounting w p₀ η r _ _ n b hη₀ hη₁ hw hr hn hcap haccount hb
  rwa [surviving_boundaryPool_card G (afterDeletions G N s) sdiff_le U Z code b] at hres

/-- Reserving every pair of the distinguished pattern supplies its actual
assigned neighbors in the residual host. -/
theorem residual_reserved_neighbors (R : SimpleGraph V) [DecidableRel R.Adj]
    (U : I → Finset V) (Z : Finset V) (code : I ↪ Fin 4)
    (P : Pattern Z) (hP : P.internalPairs = ∅) (assignment : V → I) (r : ℕ)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hUZ : ∀ i, Disjoint (U i) Z)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (hassignment : ∀ z : Z, P.assignment z = code (assignment z.val))
    (hreserve : ∀ b ∈ P.boundaryEdges, r ≤ (boundaryPool R U Z code b).card) :
    ∀ z ∈ Z, r ≤ (R.neighborFinset z ∩ U (assignment z)).card := by
  apply reserved_pairs_give_neighbors R U Z code P assignment r hdisjoint hUZ hcover hassignment
  intro z
  exact hreserve _ (assignment_edge_mem P hP z)

/-- Every joining-forest pair is among the reserved quotient pools. -/
theorem residual_reserved_forest_pairs (R : SimpleGraph V) [DecidableRel R.Adj]
    (U : I → Finset V) (Z : Finset V) (code : I ↪ Fin 4)
    (P : Pattern Z) (r : ℕ)
    (hreserve : ∀ b ∈ P.boundaryEdges, r ≤ (boundaryPool R U Z code b).card) :
    ∀ p ∈ P.forest, r ≤ (boundaryPool R U Z code
      (p.val.image (Sum.inr : Fin 4 → Z ⊕ Fin 4))).card := by
  intro p hp
  exact hreserve _ (mem_union_right _ (mem_image.mpr ⟨p,hp,rfl⟩))

end Overfull.Patterns
