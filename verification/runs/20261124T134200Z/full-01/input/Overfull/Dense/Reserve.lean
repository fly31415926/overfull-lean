import Overfull.Dense.Reserve.Flow

/-!
# Balancing a reserve on six directed bipartite pairs

This is Lemma 5.10 (`dense:reserve`) of the manuscript, with the explicit
constant `12 / (2*c-1)` and a positive threshold depending only on `c`.
All degrees and pair sizes count the edges of the actual directed graph.
Probabilities vanish on nonedges and lie strictly between zero and one
on every edge. The six row and column equalities give exact balance at
every vertex, since addition by one permutes the six classes.
-/

namespace Overfull.Dense

open Classical

noncomputable def reserveConstant (c : ℝ) : ℝ := 12/(2*c-1)

noncomputable def reserveThreshold (c : ℝ) : ℝ := min (1/4) (1/(4*reserveConstant c))

theorem reserve_constants (c : ℝ) (hc : 1/2 < c) :
    0 < reserveConstant c ∧ 0 < reserveThreshold c ∧
      reserveConstant c * reserveThreshold c ≤ 1/4 ∧ reserveThreshold c ≤ 1/4 := by
  have hden : 0 < 2*c-1 := by linarith
  have hC : 0 < reserveConstant c := div_pos (by norm_num) hden
  have hT : 0 < reserveThreshold c := lt_min (by norm_num) (by positivity)
  have hbound := mul_le_mul_of_nonneg_left
    (min_le_right (1/4 : ℝ) (1/(4*reserveConstant c))) hC.le
  have hcancel : reserveConstant c * (1/(4*reserveConstant c)) = 1/4 := by
    field_simp
  rw [hcancel] at hbound
  exact ⟨hC,hT,hbound,min_le_left _ _⟩

end Overfull.Dense

namespace Overfull

open Finset Classical Dense

/-- The six-pair reserve lemma with explicit constants and threshold. -/
theorem dense_reserve_explicit {V : Type*} [Fintype V] (G : SixCycleGraph V)
    (c e θ μ : ℝ) (hc : 1/2 < c) (he : 0 < e)
    (hθ : 0 < θ) (hθsmall : θ ≤ reserveThreshold c) (hμ : 0 < μ) (hμsmall : μ < 1/4)
    (hcounts : ∀ j, (1-θ)*e ≤ (G.edgeCount j : ℝ) ∧
      (G.edgeCount j : ℝ) ≤ (1+θ)*e)
    (himbalance : ∀ v, |(G.outDegree v : ℝ)-(G.inDegree v : ℝ)| ≤
      θ * min (G.outDegree v : ℝ) (G.inDegree v : ℝ))
    (hleft : ∀ j (u : G.Part j),
      c*Fintype.card (G.Part (j+1)) ≤ (G.outDegree u.val : ℝ))
    (hright : ∀ j (v : G.Part (j+1)),
      c*Fintype.card (G.Part j) ≤ (G.inDegree v.val : ℝ)) :
    reserveConstant c * θ < 1/2 ∧
    ∃ p : ∀ j, G.Part j → G.Part (j+1) → ℝ,
      (∀ j u v, ¬ G.adj u.val v.val → p j u v = 0) ∧
      (∀ j (v : G.Part (j+1)), (∑ w, p (j+1) v w) = ∑ u, p j u v) ∧
      ∀ j u v, G.adj u.val v.val →
        0 < p j u v ∧ p j u v < 1 ∧ |p j u v-μ| ≤ reserveConstant c*μ*θ := by
  obtain ⟨hC,_,hCT,hT⟩ := reserve_constants c hc
  have hquarter : θ ≤ 1/4 := hθsmall.trans hT
  have hCθ : reserveConstant c*θ ≤ 1/4 :=
    (mul_le_mul_of_nonneg_left hθsmall hC.le).trans hCT
  have hhalf : reserveConstant c*θ < 1/2 := by linarith
  obtain ⟨p,hp0,hbalance,hbound⟩ :=
    G.exists_balanced_weights c e θ μ hc he hθ.le hquarter hμ.le
      hcounts himbalance hleft hright
  refine ⟨hhalf,p,hp0,hbalance,?_⟩
  intro j u v huv
  have hb : |p j u v-μ| ≤ reserveConstant c*μ*θ := hbound j u v huv
  have hscaled := mul_le_mul_of_nonneg_left hCθ hμ.le
  have hab := abs_le.mp hb
  exact ⟨by nlinarith,by nlinarith,hb⟩

/-- Full Lemma 5.10. The constants depend only on `c`; the vertex classes,
their sizes, and the graph are arbitrary finite data. -/
theorem dense_reserve (c : ℝ) (hc : 1/2 < c) :
    ∃ c₁ θ₀ : ℝ, 0 < c₁ ∧ 0 < θ₀ ∧ c₁*θ₀ < 1/2 ∧
      ∀ (V : Type*) [Fintype V] (G : SixCycleGraph V) (e θ μ : ℝ),
        0 < e → 0 < θ → θ ≤ θ₀ → 0 < μ → μ < 1/4 →
        (∀ j, (1-θ)*e ≤ (G.edgeCount j : ℝ) ∧ (G.edgeCount j : ℝ) ≤ (1+θ)*e) →
        (∀ v, |(G.outDegree v : ℝ)-(G.inDegree v : ℝ)| ≤
          θ * min (G.outDegree v : ℝ) (G.inDegree v : ℝ)) →
        (∀ j (u : G.Part j), c*Fintype.card (G.Part (j+1)) ≤ (G.outDegree u.val : ℝ)) →
        (∀ j (v : G.Part (j+1)), c*Fintype.card (G.Part j) ≤ (G.inDegree v.val : ℝ)) →
        ∃ p : ∀ j, G.Part j → G.Part (j+1) → ℝ,
          (∀ j u v, ¬ G.adj u.val v.val → p j u v = 0) ∧
          (∀ j (v : G.Part (j+1)), (∑ w, p (j+1) v w) = ∑ u, p j u v) ∧
          ∀ j u v, G.adj u.val v.val →
            0 < p j u v ∧ p j u v < 1 ∧ |p j u v-μ| ≤ c₁*μ*θ := by
  obtain ⟨hC,hT,hCT,_⟩ := reserve_constants c hc
  refine ⟨reserveConstant c,reserveThreshold c,hC,hT,by linarith,?_⟩
  intro V _ G e θ μ he hθ hθsmall hμ hμsmall hcounts himbalance hleft hright
  exact (dense_reserve_explicit G c e θ μ hc he hθ hθsmall hμ hμsmall
    hcounts himbalance hleft hright).2

end Overfull
