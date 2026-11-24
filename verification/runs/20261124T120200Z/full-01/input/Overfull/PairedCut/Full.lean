import Overfull.PairedCut.FromClusters
import Overfull.PairedCut.Regularity

/-!
# The prescribed-pair cut lemma

This is the full paired-cut statement. It obtains actual regular clusters
from the graph, samples independent pair orientations, and proves robust
expansion of the resulting actual bipartite crossing graph. All constants
are chosen before the finite graph and the prescribed pairing.
-/

namespace Overfull.PairedCut

open Finset Classical

/-- Every sufficiently large robust expander of positive linear minimum
degree has a balanced bipartite robust cut splitting any prescribed pairing.
The pairing is represented exactly by `I × Bool ≃ V`. -/
theorem paired_cut (α ν τ : ℝ) (hα : 0 < α) (hν : 0 < ν)
    (hντ : ν ≤ τ) (hτ : τ ≤ 1 / 8) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∃ n₀ : ℕ,
      ∀ (V I : Type*) [Fintype V] [Fintype I] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj] (e : I × Bool ≃ V),
        n₀ ≤ Fintype.card V →
        (∀ v, α * Fintype.card V ≤ (G.degree v : ℝ)) →
        IsRobustExpander G ν τ →
        ∃ A B : Finset V,
          Disjoint A B ∧ A ∪ B = univ ∧ A.card = Fintype.card I ∧ B.card = Fintype.card I ∧
          (∀ i, (e (i,false) ∈ A ∧ e (i,true) ∈ B) ∨
            (e (i,true) ∈ A ∧ e (i,false) ∈ B)) ∧
          (∀ v, α * Fintype.card V / 3 ≤ ((crossingGraph G A).degree v : ℝ)) ∧
          IsBipartiteRobustExpander (cutSidesGraph G A B) ξ (4 * τ) := by
  let γ := ν / 4
  let ε := γ / 200
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεγ : ε ≤ γ / 100 := by dsimp [ε]; linarith
  have hγτ : γ ≤ τ := by dsimp [γ]; linarith
  have hν1 : ν ≤ 1 := by linarith
  have hτ0 : 0 ≤ τ := hν.le.trans hντ
  obtain ⟨K,hK,d,hd,hd1,nReg,hReg⟩ := exists_robust_regular_clusters ν τ ε hν hν1 hτ0 hε
  let β := 1 / (2 * (K : ℝ))
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hβ : 0 < β := by dsimp [β]; positivity
  obtain ⟨nCut,hCut⟩ := exists_prescribed_pair_cut_from_clusters α ε β d γ τ K
    hα hε hεγ hβ hd hd1 hγ hγτ hτ
  refine ⟨d * γ ^ 2 / 100,by positivity,max nReg nCut,?_⟩
  intro V I _ _ _ G _ e hn hdegree hG
  obtain ⟨P,w,C,R,hK',ht,hw,hsize,hdisjoint,hexception,hlarge,hR,hregular⟩ :=
    hReg V G ((le_max_left nReg nCut).trans hn) hG
  apply hCut V I P.parts G e R C w
  · simpa only [Fintype.card_coe] using hK'
  · exact (le_max_right nReg nCut).trans hn
  · exact hdegree
  · intro j
    rw [hsize j]
    exact hlarge
  · exact hw
  · simpa only [γ,Fintype.card_coe] using ht
  · have heq : 2 * γ = ν / 2 := by dsimp [γ]; ring
    simpa only [heq] using hR
  · exact hdisjoint
  · exact hsize
  · simpa only [Finset.compl_eq_univ_sdiff] using hexception
  · exact hregular

end Overfull.PairedCut
