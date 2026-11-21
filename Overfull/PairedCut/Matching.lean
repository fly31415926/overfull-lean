import Overfull.PairedCut.Full
import Overfull.MatchingPairing
import Overfull.RandomReserveDegrees

/-!
# A robust bipartite cut retaining a matching

The matching's actual edges are extended to a complete pairing. The
paired-cut theorem then puts every matching edge between its two sides.
-/

namespace Overfull.PairedCut

open Finset Classical SimpleGraph

/-- A uniform paired cut of the reserve, with every edge of the given
ambient matching crossing the cut. -/
theorem exists_matching_cut (α ν τ : ℝ) (hα : 0 < α) (hν : 0 < ν)
    (hντ : ν ≤ τ) (hτ : τ ≤ 1 / 8) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∃ n₀ : ℕ,
      ∀ (V : Type*) [Fintype V] [DecidableEq V]
        (G P : SimpleGraph V) [DecidableRel P.Adj] (M : G.Subgraph),
        M.IsMatching → Even (Fintype.card V) → n₀ ≤ Fintype.card V →
        (∀ v, α * Fintype.card V ≤ (P.degree v : ℝ)) → IsRobustExpander P ν τ →
        ∃ A B : Finset V, ∃ e : A ⊕ B ≃ V, ∃ Q : SimpleGraph (A ⊕ B),
          Fintype.card A = Fintype.card B ∧
          (∀ a a', ¬ M.Adj (e (.inl a)) (e (.inl a'))) ∧
          (∀ b b', ¬ M.Adj (e (.inr b)) (e (.inr b'))) ∧
          Q ≤ P.comap e ∧
          (∀ a, (2 * α / 3) * Fintype.card A ≤ ((rightNeighbors Q a).card : ℝ)) ∧
          (∀ b, (2 * α / 3) * Fintype.card A ≤ ((leftNeighbors Q b).card : ℝ)) ∧
          IsBipartiteRobustExpander Q ξ (4 * τ) := by
  obtain ⟨ξ,hξ,n₀,hn₀⟩ := paired_cut α ν τ hα hν hντ hτ
  refine ⟨ξ,hξ,n₀,?_⟩
  intro V _ _ G P _ M hM heven hn hdegree hP
  obtain ⟨f,hf⟩ := MatchingPairing.exists_pairing M hM heven
  obtain ⟨A,B,hAB,hunion,hAcard,hBcard,hpair,hcut,hrob⟩ :=
    hn₀ V _ P f hn hdegree hP
  let e := cutSidesEquiv A B hAB hunion
  let Q := cutSidesGraph P A B
  have hcross (v w : V) (hvw : M.Adj v w) :
      (v ∈ A ∧ w ∈ B) ∨ (v ∈ B ∧ w ∈ A) := by
    obtain ⟨i,hi⟩ := hf v w hvw
    have hs := hpair i
    rcases Sym2.eq_iff.mp hi with ⟨hv,hw⟩ | ⟨hw,hv⟩
    · rw [hv,hw] at hs
      tauto
    · rw [hw,hv] at hs
      tauto
  have hleft : ∀ a a', ¬ M.Adj (e (.inl a)) (e (.inl a')) := by
    intro a a' h
    change M.Adj a.val a'.val at h
    rcases hcross a.val a'.val h with h | h
    · exact Finset.disjoint_left.mp hAB a'.property h.2
    · exact Finset.disjoint_left.mp hAB a.property h.1
  have hright : ∀ b b', ¬ M.Adj (e (.inr b)) (e (.inr b')) := by
    intro b b' h
    change M.Adj b.val b'.val at h
    rcases hcross b.val b'.val h with h | h
    · exact Finset.disjoint_left.mp hAB h.1 b.property
    · exact Finset.disjoint_left.mp hAB h.2 b'.property
  have hQbip : Q.IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr) := by
    refine ⟨?_,?_⟩
    · apply Set.disjoint_left.mpr
      rintro v ⟨a,rfl⟩ ⟨b,h⟩
      cases h
    · intro x y hxy
      rcases x with a | b <;> rcases y with a' | b'
      · simp [Q,cutSidesGraph,crossingGraph,a.property,a'.property] at hxy
      · exact Or.inl ⟨⟨a,rfl⟩,⟨b',rfl⟩⟩
      · exact Or.inr ⟨⟨b,rfl⟩,⟨a',rfl⟩⟩
      · have hb : b.val ∉ A := fun h => Finset.disjoint_left.mp hAB h b.property
        have hb' : b'.val ∉ A := fun h => Finset.disjoint_left.mp hAB h b'.property
        simp [Q,cutSidesGraph,crossingGraph,hb,hb'] at hxy
  have hQmin (v : A ⊕ B) : α * Fintype.card V / 3 ≤ (Q.degree v : ℝ) := by
    change α * Fintype.card V / 3 ≤ ((cutSidesGraph P A B).degree v : ℝ)
    rw [cutSidesGraph_degree P A B hAB hunion]
    exact hcut (Sum.elim Subtype.val Subtype.val v)
  have hbalance : Fintype.card A = Fintype.card B := by
    simpa only [Fintype.card_coe] using hAcard.trans hBcard.symm
  have horder : (Fintype.card V : ℝ) = 2 * Fintype.card A := by
    have hsum : A.card + B.card = Fintype.card V := by
      rw [← Finset.card_union_of_disjoint hAB,hunion,Finset.card_univ]
    have hsumR : (A.card : ℝ) + B.card = Fintype.card V := by exact_mod_cast hsum
    have hcard : A.card = B.card := hAcard.trans hBcard.symm
    rw [← hcard] at hsumR
    rw [Fintype.card_coe]
    linarith
  refine ⟨A,B,e,Q,hbalance,hleft,hright,?_,?_,?_,hrob⟩
  · intro x y hxy
    exact hxy.1
  · intro a
    have hdeg : (rightNeighbors Q a).card = Q.degree (.inl a) :=
      RandomReserve.crossingDegree_eq_degree Q hQbip (.inl a)
    rw [hdeg]
    have h := hQmin (.inl a)
    rw [horder] at h
    nlinarith only [h]
  · intro b
    have hdeg : (leftNeighbors Q b).card = Q.degree (.inr b) :=
      RandomReserve.crossingDegree_eq_degree Q hQbip (.inr b)
    rw [hdeg]
    have h := hQmin (.inr b)
    rw [horder] at h
    nlinarith only [h]

end Overfull.PairedCut
