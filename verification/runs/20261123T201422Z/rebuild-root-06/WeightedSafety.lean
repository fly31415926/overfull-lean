import Overfull.NativeReserve.CutSafety

/-!
# Original weighted cut certificates for native residuals

The weights belong to the original decomposition. Exact copy accounting
transfers their inequalities to any finite disjoint realized family; no
fractional decomposition of the residual is postulated.
-/

noncomputable section

namespace Overfull.NativeReserve

open Finset Classical ForceMatching
open scoped BigOperators

variable {V E I J P : Type*} [Fintype P]

def familyMultiplicity (kind : J → P) (T : Finset J) (p : P) : ℕ :=
  (T.filter (fun j => kind j = p)).card

theorem familyMultiplicity_sum (kind : J → P) (T : Finset J) :
    ∑ p, familyMultiplicity kind T p = T.card := by
  simp only [familyMultiplicity, card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  simp

theorem familyMultiplicity_statistic (kind : J → P) (T : Finset J) (c : P → ℕ) :
    (∑ p, familyMultiplicity kind T p * c p) = ∑ j ∈ T, c (kind j) := by
  simp only [familyMultiplicity, card_eq_sum_ones, sum_filter, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  simp [ite_mul, eq_comm]

omit [Fintype P] in
theorem familyMultiplicity_pos (kind : J → P) (T : Finset J) (j : J) (hj : j ∈ T) :
    0 < familyMultiplicity kind T (kind j) := by
  exact card_pos.mpr ⟨j, mem_filter.mpr ⟨hj, rfl⟩⟩

theorem residual_pattern_pool_accounting (N : J → Finset E) (T : Finset J)
    (hdisj : (T : Set J).Pairwise (fun i j => Disjoint (N i) (N j)))
    (kind : J → P) (A : Finset E) (c : P → ℕ)
    (hcount : ∀ j ∈ T, (N j ∩ A).card = c (kind j)) :
    (A \ removedCopies N T).card +
      (∑ p, familyMultiplicity kind T p * c p) = A.card := by
  rw [familyMultiplicity_statistic]
  have heq : (∑ j ∈ T, c (kind j)) = ∑ j ∈ T, (N j ∩ A).card := by
    apply sum_congr rfl
    intro j hj
    exact (hcount j hj).symm
  rw [heq]
  exact residual_pool_accounting N T hdisj A

theorem residual_pattern_pool_lower (N : J → Finset E) (T : Finset J)
    (hdisj : (T : Set J).Pairwise (fun i j => Disjoint (N i) (N j)))
    (kind : J → P) (A : Finset E) (c proposal : P → ℕ)
    (hcount : ∀ j ∈ T, (N j ∩ A).card = c (kind j))
    (hproposal : ∀ p, familyMultiplicity kind T p ≤ proposal p) :
    (A.card : ℝ) - ∑ p, (proposal p : ℝ) * c p ≤
      ((A \ removedCopies N T).card : ℝ) := by
  have hacct := residual_pattern_pool_accounting N T hdisj kind A c hcount
  have hacctR : ((A \ removedCopies N T).card : ℝ) +
      (∑ p, (familyMultiplicity kind T p : ℝ) * c p) = A.card := by exact_mod_cast hacct
  have hsum : (∑ p, (familyMultiplicity kind T p : ℝ) * c p) ≤
      ∑ p, (proposal p : ℝ) * c p := by
    apply sum_le_sum
    intro p _
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hproposal p) (Nat.cast_nonneg _)
  linarith only [hacctR, hsum]

variable [Fintype E]

theorem residual_pattern_cut_accounting (G : Multigraph V E)
    (N : J → Finset E) (T : Finset J)
    (hdisj : (T : Set J).Pairwise (fun i j => Disjoint (N i) (N j)))
    (kind : J → P) (X : Finset V) (c : P → ℕ)
    (hcount : ∀ j ∈ T, (G.cutOn (N j) X).card = c (kind j)) :
    (residualGraph G N T).cutSize X +
      (∑ p, familyMultiplicity kind T p * c p) = G.cutSize X := by
  rw [familyMultiplicity_statistic]
  have heq : (∑ j ∈ T, c (kind j)) = ∑ j ∈ T, (G.cutOn (N j) X).card := by
    apply sum_congr rfl
    intro j hj
    exact (hcount j hj).symm
  rw [heq]
  exact residual_cut_accounting G N T hdisj X

theorem residual_weighted_odd_cut (G : Multigraph V E)
    (N : J → Finset E) (T : Finset J)
    (hdisj : (T : Set J).Pairwise (fun i j => Disjoint (N i) (N j)))
    (kind : J → P) (k : ℕ) (hT : T.card ≤ k)
    (w : P → ℝ) (hsum : ∑ p, w p = k)
    (hn : ∀ p, (familyMultiplicity kind T p : ℝ) ≤ w p)
    (X : Finset V) (c : P → ℕ)
    (hcount : ∀ j ∈ T, (G.cutOn (N j) X).card = c (kind j))
    (hodd : ∀ p, 0 < w p → 1 ≤ c p)
    (hcap : (∑ p, w p * c p) ≤ G.cutSize X) :
    k - T.card ≤ (residualGraph G N T).cutSize X := by
  have hbound := CircuitPatterns.prefix_odd_cut_bound_on_support w
    (familyMultiplicity kind T) c k (G.cutSize X) hsum hn hodd hcap
  have hsumN := familyMultiplicity_sum kind T
  have hsumR : (∑ p, (familyMultiplicity kind T p : ℝ)) = T.card := by exact_mod_cast hsumN
  rw [hsumR] at hbound
  have hacct := residual_pattern_cut_accounting G N T hdisj kind X c hcount
  have hacctR : ((residualGraph G N T).cutSize X : ℝ) +
      (∑ p, (familyMultiplicity kind T p : ℝ) * c p) = G.cutSize X := by exact_mod_cast hacct
  have hresult : ((k - T.card : ℕ) : ℝ) ≤ (residualGraph G N T).cutSize X := by
    rw [Nat.cast_sub hT]
    linarith only [hbound, hacctR]
  exact_mod_cast hresult

theorem residual_proposed_cut_dichotomy (G : Multigraph V E)
    (N : J → Finset E) (T : Finset J)
    (hdisj : (T : Set J).Pairwise (fun i j => Disjoint (N i) (N j)))
    (kind : J → P) (proposal accepted : P → ℕ)
    (hn : ∀ p, familyMultiplicity kind T p ≤ accepted p)
    (hm : ∀ p, accepted p ≤ proposal p)
    (X : Finset V) (c : P → ℕ) (a : ℝ)
    (hcount : ∀ j ∈ T, (G.cutOn (N j) X).card = c (kind j))
    (hprotected : (G.cutSize X : ℝ) - (∑ p, (proposal p : ℝ) * c p) < 2 * a →
      ∀ p, accepted p * c p = 0) :
    2 * a ≤ ((residualGraph G N T).cutSize X : ℝ) ∨
      G.cutEdges X \ removedCopies N T = G.cutEdges X := by
  by_cases hsmall : (G.cutSize X : ℝ) - (∑ p, (proposal p : ℝ) * c p) < 2 * a
  · apply Or.inr
    apply residual_cut_pool_unchanged G N T X
    intro j hj
    rw [hcount j hj]
    have hpos : 0 < accepted (kind j) := (familyMultiplicity_pos kind T j hj).trans_le (hn _)
    have hzero := hprotected hsmall (kind j)
    rcases Nat.mul_eq_zero.mp hzero with hz | hz
    · omega
    · exact hz
  · apply Or.inl
    have hacct := residual_pattern_cut_accounting G N T hdisj kind X c hcount
    have hacctR : ((residualGraph G N T).cutSize X : ℝ) +
        (∑ p, (familyMultiplicity kind T p : ℝ) * c p) = G.cutSize X := by exact_mod_cast hacct
    have hmon := CircuitPatterns.prefix_cut_mono proposal (familyMultiplicity kind T) c
      (G.cutSize X) (fun p => (hn p).trans (hm p))
    linarith only [hacctR, hmon, not_lt.mp hsmall]

variable [Fintype V] [Fintype I]

theorem residual_no_overfull_of_pattern_counts (G : Multigraph V E)
    (N : J → Finset E) (T : Finset J)
    (hNdisj : (T : Set J).Pairwise (fun i j => Disjoint (N i) (N j)))
    (hperfect : ∀ j ∈ T, G.IsPerfectMatching (N j))
    (U : I → Finset V) (Z : Finset V)
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hZ : ∀ i, Disjoint (U i) Z) (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (kind : J → P) (k : ℕ) (hT : T.card ≤ k)
    (hregularG : ∀ v, G.degree v = k) (hnoG : ∀ X, ¬ G.IsOverfull k X)
    (C : ∀ i, SmallCuts.Core (residualGraph G N T) (U i))
    (α c ν τ a : ℝ)
    (hα : 0 < α) (hc : 0 < c) (hν : 0 < ν) (hτ : 0 ≤ τ) (hτα : τ ≤ α / 10)
    (hklo : α * Fintype.card V ≤ ((k - T.card : ℕ) : ℝ))
    (hkhi : ((k - T.card : ℕ) : ℝ) ≤ 2 * Fintype.card V)
    (ha : a ≤ α * Fintype.card V / 10)
    (hlarge : 3 < ν ^ 2 * c ^ 2 * (Fintype.card V : ℝ))
    (hsize : ∀ i, c * Fintype.card V ≤ ((U i).card : ℝ))
    (hrobust : ∀ i, IsRobustExpander (C i).graph ν τ)
    (hdegree : ∀ i v, ((k - T.card : ℕ) : ℝ) - a ≤ ((C i).graph.degree v : ℝ))
    (w : P → ℝ) (hsum : ∑ p, w p = k) (proposal accepted : P → ℕ)
    (hn : ∀ p, familyMultiplicity kind T p ≤ accepted p)
    (hm : ∀ p, accepted p ≤ proposal p) (hweight : ∀ p, (proposal p : ℝ) ≤ w p)
    (crossing : Finset V → P → ℕ)
    (hcounts : ∀ X ∈ wholeUnions U Z, ∀ j ∈ T, (G.cutOn (N j) X).card = crossing X (kind j))
    (hodd : ∀ X ∈ wholeUnions U Z, X.card % 2 = 1 → ∀ p, 0 < w p → 1 ≤ crossing X p)
    (hcap : ∀ X ∈ wholeUnions U Z, (∑ p, w p * crossing X p) ≤ G.cutSize X)
    (hprotected : ∀ X ∈ wholeUnions U Z, X.card % 2 = 0 →
      (G.cutSize X : ℝ) - (∑ p, (proposal p : ℝ) * crossing X p) < 2 * a →
        ∀ p, accepted p * crossing X p = 0) :
    ∀ X, ¬ (residualGraph G N T).IsOverfull (k - T.card) X := by
  have hnweight (p : P) : (familyMultiplicity kind T p : ℝ) ≤ w p := by
    exact (show (familyMultiplicity kind T p : ℝ) ≤ proposal p from
      by exact_mod_cast (hn p).trans (hm p)).trans (hweight p)
  apply residual_no_overfull G N T hNdisj hperfect U Z hdisj hZ hcover k
    hregularG hnoG C α c ν τ a hα hc hν hτ hτα hklo hkhi ha hlarge hsize hrobust hdegree
  · intro X hX hXodd
    exact residual_weighted_odd_cut G N T hNdisj kind k hT w hsum hnweight X
      (crossing X) (hcounts X hX) (hodd X hX hXodd) (hcap X hX)
  · intro X hX heven
    exact residual_proposed_cut_dichotomy G N T hNdisj kind proposal accepted hn hm
      X (crossing X) a (hcounts X hX) (hprotected X hX heven)

end Overfull.NativeReserve
