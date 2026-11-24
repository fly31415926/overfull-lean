import Overfull.Dense.Reserve.Estimates

/-!
# Correcting all six directed pairs to common vertex demands
-/

namespace Overfull.Dense.SixCycleGraph

open Finset Classical

variable {V : Type*} [Fintype V] (G : SixCycleGraph V)

theorem initial_row_sum (μ : ℝ) (j : ZMod 6) (u : G.Part j) :
    (∑ v : G.Part (j+1), if G.adj u.val v.val then μ else 0) = μ*G.outDegree u.val := by
  calc
    _ = ∑ _v ∈ rightNeighbors (G.pairGraph j) u, μ := by
      simp only [rightNeighbors, pairGraph, Finset.sum_filter]
    _ = (rightNeighbors (G.pairGraph j) u).card * μ := by simp
    _ = _ := by rw [G.pair_rightNeighbors_card]; ring

theorem initial_column_sum (μ : ℝ) (j : ZMod 6) (v : G.Part (j+1)) :
    (∑ u : G.Part j, if G.adj u.val v.val then μ else 0) = μ*G.inDegree v.val := by
  calc
    _ = ∑ _u ∈ leftNeighbors (G.pairGraph j) v, μ := by
      simp only [leftNeighbors, pairGraph, Finset.sum_filter]
    _ = (leftNeighbors (G.pairGraph j) v).card * μ := by simp
    _ = _ := by rw [G.pair_leftNeighbors_card]; ring

theorem exists_pair_weights (c e θ μ : ℝ) (hc : 1/2 < c) (he : 0 < e)
    (hθ : 0 ≤ θ) (hθsmall : θ ≤ 1/4) (hμ : 0 ≤ μ)
    (hcounts : ∀ j, (1-θ)*e ≤ (G.edgeCount j : ℝ) ∧
      (G.edgeCount j : ℝ) ≤ (1+θ)*e)
    (himbalance : ∀ v, |(G.outDegree v : ℝ)-(G.inDegree v : ℝ)| ≤
      θ * min (G.outDegree v : ℝ) (G.inDegree v : ℝ))
    (j : ZMod 6)
    (hleft : ∀ u : G.Part j, c*Fintype.card (G.Part (j+1)) ≤ (G.outDegree u.val : ℝ))
    (hright : ∀ v : G.Part (j+1), c*Fintype.card (G.Part j) ≤ (G.inDegree v.val : ℝ)) :
    ∃ p : G.Part j → G.Part (j+1) → ℝ,
      (∀ u v, ¬ G.adj u.val v.val → p u v = 0) ∧
      (∀ u, ∑ v, p u v = G.reserveDemand μ u.val) ∧
      (∀ v, ∑ u, p u v = G.reserveDemand μ v.val) ∧
      ∀ u v, G.adj u.val v.val → |p u v-μ| ≤ (12/(2*c-1))*μ*θ := by
  let r : G.Part j → ℝ := fun u => G.reserveDemand μ u.val-μ*G.outDegree u.val
  let s : G.Part (j+1) → ℝ := fun v => G.reserveDemand μ v.val-μ*G.inDegree v.val
  have hr (u : G.Part j) : |r u| ≤ (4*μ*θ)*Fintype.card (G.Part (j+1)) := by
    calc
      _ ≤ (4*μ*θ)*G.outDegree u.val :=
        G.reserveDemand_out_error e θ μ he hθ hθsmall hμ hcounts himbalance u.val
      _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast G.outDegree_le_part_card j u)
        (by positivity)
  have hs (v : G.Part (j+1)) : |s v| ≤ (4*μ*θ)*Fintype.card (G.Part j) := by
    calc
      _ ≤ (4*μ*θ)*G.inDegree v.val :=
        G.reserveDemand_in_error e θ μ he hθ hθsmall hμ hcounts himbalance v.val
      _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast G.inDegree_le_part_card j v)
        (by positivity)
  have htotal : ∑ u, r u = ∑ v, s v := by
    simp only [r,s,Finset.sum_sub_distrib,← Finset.mul_sum,
      G.sum_reserveDemand e θ μ he hθsmall (fun j => (hcounts j).1),
      G.sum_outDegree_real, G.sum_inDegree_real]
  obtain ⟨z,hz0,hzr,hzs,hz⟩ := dense_unequal_flow (G.pairGraph j) c (4*μ*θ) hc
    (fun u => by simpa only [G.pair_rightNeighbors_card] using hleft u)
    (fun v => by simpa only [G.pair_leftNeighbors_card] using hright v) r s hr hs htotal
  let p : G.Part j → G.Part (j+1) → ℝ :=
    fun u v => (if G.adj u.val v.val then μ else 0)+z u v
  refine ⟨p,?_,?_,?_,?_⟩
  · intro u v huv
    have hzuv := hz0 u v huv
    simp only [p,if_neg huv,hzuv,add_zero]
  · intro u
    simp only [p,Finset.sum_add_distrib,G.initial_row_sum,hzr,r]
    ring
  · intro v
    simp only [p,Finset.sum_add_distrib,G.initial_column_sum,hzs,s]
    ring
  · intro u v huv
    have h := hz u v
    have hbound : 3*(4*μ*θ)/(2*c-1) = (12/(2*c-1))*μ*θ := by ring
    simpa only [p,if_pos huv,add_sub_cancel_left,hbound] using h

/-- All six pairs have the same prescribed vertex demand at their common
class, so their corrected edge weights have equal incoming and outgoing sums. -/
theorem exists_balanced_weights (c e θ μ : ℝ) (hc : 1/2 < c) (he : 0 < e)
    (hθ : 0 ≤ θ) (hθsmall : θ ≤ 1/4) (hμ : 0 ≤ μ)
    (hcounts : ∀ j, (1-θ)*e ≤ (G.edgeCount j : ℝ) ∧
      (G.edgeCount j : ℝ) ≤ (1+θ)*e)
    (himbalance : ∀ v, |(G.outDegree v : ℝ)-(G.inDegree v : ℝ)| ≤
      θ * min (G.outDegree v : ℝ) (G.inDegree v : ℝ))
    (hleft : ∀ j (u : G.Part j),
      c*Fintype.card (G.Part (j+1)) ≤ (G.outDegree u.val : ℝ))
    (hright : ∀ j (v : G.Part (j+1)),
      c*Fintype.card (G.Part j) ≤ (G.inDegree v.val : ℝ)) :
    ∃ p : ∀ j, G.Part j → G.Part (j+1) → ℝ,
      (∀ j u v, ¬ G.adj u.val v.val → p j u v = 0) ∧
      (∀ j (v : G.Part (j+1)), (∑ w, p (j+1) v w) = ∑ u, p j u v) ∧
      ∀ j u v, G.adj u.val v.val → |p j u v-μ| ≤ (12/(2*c-1))*μ*θ := by
  choose p hp0 hpr hpc hpb using
    fun j => G.exists_pair_weights c e θ μ hc he hθ hθsmall hμ hcounts himbalance
      j (hleft j) (hright j)
  refine ⟨p,hp0,?_,hpb⟩
  intro j v
  rw [hpr,hpc]

end Overfull.Dense.SixCycleGraph
