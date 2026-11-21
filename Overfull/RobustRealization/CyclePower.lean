import Overfull.Basic
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Order.Interval.Finset.Fin

/-!
# Cycle powers and their exact degrees

Vertices are the actual labels `Fin n`; adjacency uses modular differences.
-/

namespace Overfull.RobustRealization

open Finset Classical SimpleGraph

def cyclePower (n r : ℕ) [NeZero n] : SimpleGraph (Fin n) :=
  SimpleGraph.circulantGraph {x : Fin n | 0 < x.val ∧ x.val ≤ r}

theorem cyclePower_adj (n r : ℕ) [NeZero n] (u v : Fin n) :
    (cyclePower n r).Adj u v ↔ u ≠ v ∧
      ((0 < (u - v).val ∧ (u - v).val ≤ r) ∨
       (0 < (v - u).val ∧ (v - u).val ≤ r)) := by
  rfl

theorem cyclePower_adj_translate (n r : ℕ) [NeZero n] (u v d : Fin n) :
    (cyclePower n r).Adj (u + d) (v + d) ↔ (cyclePower n r).Adj u v := by
  exact SimpleGraph.circulantGraph_adj_translate

theorem cyclePower_adj_of_lt (n r : ℕ) [NeZero n] (u v : Fin n)
    (huv : u.val < v.val) (hd : v.val - u.val ≤ r) :
    (cyclePower n r).Adj u v := by
  rw [cyclePower_adj]
  refine ⟨by intro h; have := congrArg Fin.val h; omega, Or.inr ?_⟩
  rw [Fin.sub_val_of_le (show u ≤ v from huv.le)]
  exact ⟨Nat.sub_pos_of_lt huv, hd⟩

theorem cyclePower_adj_of_distance (n r : ℕ) [NeZero n] (u v : Fin n)
    (hne : u ≠ v) (h₁ : u.val ≤ v.val + r) (h₂ : v.val ≤ u.val + r) :
    (cyclePower n r).Adj u v := by
  by_cases huv : u.val < v.val
  · exact cyclePower_adj_of_lt n r u v huv (by omega)
  · have hval : u.val ≠ v.val := fun h => hne (Fin.ext h)
    exact (cyclePower_adj_of_lt n r v u (by omega) (by omega)).symm

theorem cyclePower_neighbor_zero (n r : ℕ) [NeZero n]
    (hr : 0 < r) (hrn : 2 * r < n) :
    (cyclePower n r).neighborFinset 0 =
      Ioc 0 (⟨r, by omega⟩ : Fin n) ∪ Ici (⟨n-r, by omega⟩ : Fin n) := by
  ext v
  simp only [mem_neighborFinset, cyclePower_adj, zero_sub, sub_zero,
    mem_union, mem_Ioc, mem_Ici, Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val,
    Fin.val_zero]
  by_cases hv : v = 0
  · subst v
    simp
    omega
  · have hv0 : 0 < v.val := by
      have : v.val ≠ 0 := fun h => hv (Fin.ext h)
      omega
    rw [Fin.val_neg, if_neg hv]
    have hvn := v.isLt
    have h0v : (0 : Fin n) ≠ v := Ne.symm hv
    omega

theorem cyclePower_neighbor_translate (n r : ℕ) [NeZero n] (v : Fin n) :
    (cyclePower n r).neighborFinset v =
      ((cyclePower n r).neighborFinset 0).image (fun w => w + v) := by
  ext w
  simp only [mem_neighborFinset, mem_image]
  constructor
  · intro h
    refine ⟨w - v, ?_, sub_add_cancel w v⟩
    have ht := cyclePower_adj_translate n r 0 (w-v) v
    apply ht.mp
    simpa only [zero_add, sub_add_cancel] using h
  · rintro ⟨z, hz, rfl⟩
    have ht := (cyclePower_adj_translate n r 0 z v).mpr hz
    simpa only [zero_add] using ht

/-- For a radius strictly below half the order, the cycle power is exactly
`2r`-regular. -/
theorem cyclePower_degree (n r : ℕ) [NeZero n]
    (hr : 0 < r) (hrn : 2 * r < n) (v : Fin n) :
    (cyclePower n r).degree v = 2 * r := by
  rw [← card_neighborFinset_eq_degree, cyclePower_neighbor_translate,
    Finset.card_image_of_injective _ (fun _ _ h => add_right_cancel h),
    cyclePower_neighbor_zero n r hr hrn]
  have hd : Disjoint (Ioc 0 (⟨r, by omega⟩ : Fin n))
      (Ici (⟨n-r, by omega⟩ : Fin n)) := by
    apply Finset.disjoint_left.mpr
    intro w hw₁ hw₂
    have h₁ := (Finset.mem_Ioc.mp hw₁).2
    have h₂ := Finset.mem_Ici.mp hw₂
    change w.val ≤ r at h₁
    change n-r ≤ w.val at h₂
    omega
  rw [Finset.card_union_of_disjoint hd, Fin.card_Ioc, Fin.card_Ici]
  simp only [Fin.val_zero, Nat.sub_zero]
  omega

end Overfull.RobustRealization
