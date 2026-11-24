import Overfull.RobustRealization.Blocks
import Overfull.RobustRealization.CyclePower

/-!
# Consecutive blocks in a cycle power

All blocks except the last have exactly `q` vertices. The last absorbs the
remainder. Its size is controlled by the division inequalities on `n`.
-/

namespace Overfull.RobustRealization

open Finset Classical SimpleGraph

def intervalBlock (n l q : ℕ) (hl : 0 < l) (v : Fin n) : Fin l :=
  ⟨min (v.val / q) (l-1), by omega⟩

theorem intervalBlock_bounds (n l q : ℕ) (hl : 0 < l) (hq : 0 < q)
    (hn : n < l * q + l) (v : Fin n) :
    (intervalBlock n l q hl v).val * q ≤ v.val ∧
      v.val < ((intervalBlock n l q hl v).val + 1) * q + l := by
  constructor
  · exact (Nat.mul_le_mul_right q (min_le_left _ _)).trans (Nat.div_mul_le_self _ _)
  · by_cases hv : v.val / q ≤ l-1
    · have hf : (intervalBlock n l q hl v).val = v.val / q := min_eq_left hv
      rw [hf]
      have := Nat.lt_mul_div_succ v.val hq
      nlinarith
    · have hf : (intervalBlock n l q hl v).val = l-1 := min_eq_right (by omega)
      rw [hf]
      have hvn := v.isLt
      have hlast : l-1+1 = l := by omega
      rw [hlast]
      omega

theorem intervalBlock_card_ge (n l q : ℕ) (hl : 0 < l) (hq : 0 < q)
    (hn : l * q ≤ n) (i : Fin l) :
    q ≤ (block (intervalBlock n l q hl) i).card := by
  let g : Fin q → Fin n := fun j => ⟨i.val * q + j.val, by
    have h₁ : i.val * q + j.val < (i.val+1)*q := by nlinarith [j.isLt]
    have h₂ : (i.val+1)*q ≤ l*q := Nat.mul_le_mul_right q i.isLt
    exact lt_of_lt_of_le h₁ (h₂.trans hn)⟩
  have hg : Function.Injective g := by
    intro j k hjk
    have h := congrArg Fin.val hjk
    apply Fin.ext
    dsimp [g] at h
    omega
  have hmem : ∀ j : Fin q, g j ∈ block (intervalBlock n l q hl) i := by
    intro j
    rw [mem_block]
    apply Fin.ext
    change min ((i.val*q+j.val)/q) (l-1) = i.val
    have hdiv : (i.val*q+j.val)/q = i.val := by
      rw [Nat.add_comm, Nat.mul_comm i.val q, Nat.add_mul_div_left _ _ hq,
        Nat.div_eq_of_lt j.isLt, Nat.zero_add]
    rw [hdiv]
    exact min_eq_left (by omega)
  have hc := Finset.card_le_card_of_injOn g (s := (univ : Finset (Fin q)))
    (t := block (intervalBlock n l q hl) i) (fun j _ => hmem j)
    (fun j _ k _ h => hg h)
  simpa using hc

theorem intervalBlock_close (n l q : ℕ) (hl : 0 < l) (hq : 0 < q)
    (hn : n < l*q+l) (u v : Fin n)
    (h : intervalBlock n l q hl u = intervalBlock n l q hl v ∨
      (pathGraph l).Adj (intervalBlock n l q hl u) (intervalBlock n l q hl v)) :
    u.val ≤ v.val + (2*q+l) ∧ v.val ≤ u.val + (2*q+l) := by
  have hu := intervalBlock_bounds n l q hl hq hn u
  have hv := intervalBlock_bounds n l q hl hq hn v
  have hindices : (intervalBlock n l q hl u).val ≤ (intervalBlock n l q hl v).val + 1 ∧
      (intervalBlock n l q hl v).val ≤ (intervalBlock n l q hl u).val + 1 := by
    rcases h with h | h
    · rw [h]
      omega
    · rw [pathGraph_adj] at h
      omega
  constructor <;> nlinarith [Nat.mul_le_mul_right q hindices.1,
    Nat.mul_le_mul_right q hindices.2]

/-- A cycle power remains robust after a graph of maximum degree one is
removed. The conclusion concerns any graph containing the surviving edges. -/
theorem robust_of_cyclePower (n l q r : ℕ) [NeZero n]
    (hl : 0 < l) (hq : 0 < q) (hn₁ : l*q ≤ n) (hn₂ : n < l*q+l)
    (hr : 2*q+l ≤ r)
    (G M : SimpleGraph (Fin n))
    (hcover : cyclePower n r ≤ G ⊔ M) (hM : ∀ v, M.degree v ≤ 1)
    (ν τ β : ℝ) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hlarge : 1 ≤ ν * n) (hsmall : 3*ν*l < τ)
    (hgap : 3*ν*l+ν ≤ β) (hsize : β*n ≤ q) :
    IsRobustExpander G ν τ := by
  let f := intervalBlock n l q hl
  apply robust_of_blocks G (pathGraph l) (pathGraph_preconnected l) f ν τ β hν hντ
      (by simpa using hlarge) (by simpa using hsmall) (by simpa using hgap)
  · intro i
    have hc : (q : ℝ) ≤ (block f i).card := by
      exact_mod_cast intervalBlock_card_ge n l q hl hq hn₁ i
    simpa using hsize.trans hc
  · intro v i hi
    have hsub : block f i \ G.neighborFinset v ⊆ insert v (M.neighborFinset v) := by
      intro w hw
      obtain ⟨hwi, hwG⟩ := Finset.mem_sdiff.mp hw
      by_cases hvw : v = w
      · subst w
        exact Finset.mem_insert_self _ _
      have hwi' : f w = i := (mem_block f i w).mp hwi
      have hrel : f v = f w ∨ (pathGraph l).Adj (f v) (f w) := by
        simpa only [hwi'] using hi
      have hc := intervalBlock_close n l q hl hq hn₂ v w hrel
      have he := hcover (cyclePower_adj_of_distance n r v w hvw
        (by omega) (by omega))
      rcases he with he | he
      · exact (hwG (by simpa using he)).elim
      · exact Finset.mem_insert_of_mem (by simpa using he)
    have hcard := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
    have hm := hM v
    rw [card_neighborFinset_eq_degree] at hcard
    omega

end Overfull.RobustRealization
