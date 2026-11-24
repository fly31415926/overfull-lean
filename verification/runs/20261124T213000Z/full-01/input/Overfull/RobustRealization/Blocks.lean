import Overfull.RobustExpansion
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Robust expansion from consecutive dense blocks

The criterion counts the actual graph neighbors in each block. It permits
the loss of the vertex itself and one further edge, as required when a
matching is deleted from a cycle power.
-/

namespace Overfull.RobustRealization

open Finset SimpleGraph
open scoped BigOperators

variable {V I : Type*} [Fintype V] [Fintype I]

noncomputable def block (f : V → I) (i : I) : Finset V := by
  classical
  exact univ.filter (fun v => f v = i)

omit [Fintype I] in
@[simp] theorem mem_block (f : V → I) (i : I) (v : V) :
    v ∈ block f i ↔ f v = i := by
  classical
  simp [block]

theorem sum_inter_block_card [DecidableEq V] (f : V → I) (S : Finset V) :
    (∑ i : I, (S ∩ block f i).card) = S.card := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise (s := S) (t := (univ : Finset I))
    (f := f) (fun _ _ => Finset.mem_univ _)
  calc
    _ = ∑ i : I, (S.filter (fun v => f v = i)).card := by
      apply Finset.sum_congr rfl
      intro i _
      apply congrArg Finset.card
      ext v
      simp
    _ = _ := h.symm

theorem exists_boundary_edge (H : SimpleGraph I) (hH : H.Preconnected)
    (T : Finset I) (hT : T.Nonempty) (hT' : T ≠ univ) :
    ∃ i ∈ T, ∃ j ∉ T, H.Adj i j := by
  classical
  by_contra! hnone
  obtain ⟨i, hi⟩ := hT
  have hclosed : ∀ {i j}, i ∈ T → H.Adj i j → j ∈ T := by
    intro i j hi hij
    by_contra hj
    exact hnone i hi j hj hij
  have hall : ∀ j, j ∈ T := by
    intro j
    obtain ⟨p⟩ := hH i j
    induction p with
    | nil => exact hi
    | @cons u v w huv p ih => exact ih (hclosed hi huv)
  exact hT' (Finset.eq_univ_iff_forall.mpr hall)

omit [Fintype I] in
theorem neighbors_in_heavy_block
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : V → I) (S : Finset V) (i : I) (v : V) (ν : ℝ)
    (hlarge : 1 ≤ ν * Fintype.card V)
    (hheavy : 3 * ν * Fintype.card V ≤ ((S ∩ block f i).card : ℝ))
    (hmissing : (block f i \ G.neighborFinset v).card ≤ 2) :
    v ∈ robustNeighbors G ν S := by
  classical
  rw [mem_robustNeighbors]
  have hsub : S ∩ block f i ⊆
      (G.neighborFinset v ∩ S) ∪ (block f i \ G.neighborFinset v) := by
    intro w hw
    obtain ⟨hwS, hwi⟩ := Finset.mem_inter.mp hw
    by_cases hwN : w ∈ G.neighborFinset v
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hwN, hwS⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hwi, hwN⟩)
  have hcount : (S ∩ block f i).card ≤ (G.neighborFinset v ∩ S).card + 2 :=
    (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_left hmissing _))
  have hreal : ((S ∩ block f i).card : ℝ) ≤ (G.neighborFinset v ∩ S).card + 2 := by
    exact_mod_cast hcount
  linarith

/-- A connected arrangement of linear-sized blocks is robust when each
vertex misses at most two vertices of its own and each neighboring block. -/
theorem robust_of_blocks [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph I) (hH : H.Preconnected) (f : V → I)
    (ν τ β : ℝ) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hlarge : 1 ≤ ν * Fintype.card V)
    (hsmall : 3 * ν * Fintype.card I < τ)
    (hgap : 3 * ν * Fintype.card I + ν ≤ β)
    (hsize : ∀ i, β * Fintype.card V ≤ ((block f i).card : ℝ))
    (hmissing : ∀ v i, f v = i ∨ H.Adj (f v) i →
      (block f i \ G.neighborFinset v).card ≤ 2) :
    IsRobustExpander G ν τ := by
  classical
  intro S hSlow hShigh
  let T : Finset I := univ.filter
    (fun i => 3 * ν * Fintype.card V ≤ ((S ∩ block f i).card : ℝ))
  let A : Finset V := univ.filter (fun v => f v ∈ T)
  have hTmem (i : I) : i ∈ T ↔
      3 * ν * Fintype.card V ≤ ((S ∩ block f i).card : ℝ) := by simp [T]
  have hAmem (v : V) : v ∈ A ↔ f v ∈ T := by simp [A]
  have hm : 0 < (Fintype.card V : ℝ) := by
    by_contra! hm
    have := mul_nonpos_of_nonneg_of_nonpos hν.le hm
    linarith
  have hSbound : (S.card : ℝ) ≤ A.card +
      3 * ν * Fintype.card V * Fintype.card I := by
    have hpart : (S \ A).card + (S ∩ A).card = S.card :=
      Finset.card_sdiff_add_card_inter S A
    have hsum : ((S \ A).card : ℝ) =
        ∑ i : I, (((S \ A) ∩ block f i).card : ℝ) := by
      exact_mod_cast (sum_inter_block_card f (S \ A)).symm
    have hbound : ((S \ A).card : ℝ) ≤
        3 * ν * Fintype.card V * Fintype.card I := by
      rw [hsum]
      calc
        _ ≤ ∑ _i : I, 3 * ν * Fintype.card V := by
          apply Finset.sum_le_sum
          intro i _
          by_cases hi : i ∈ T
          · have hempty : (S \ A) ∩ block f i = ∅ := by
              apply Finset.eq_empty_iff_forall_notMem.mpr
              intro v hv
              obtain ⟨hvSA, hvi⟩ := Finset.mem_inter.mp hv
              have hvA : v ∈ A := (hAmem v).mpr ((mem_block f i v).mp hvi ▸ hi)
              exact (Finset.mem_sdiff.mp hvSA).2 hvA
            rw [hempty, Finset.card_empty, Nat.cast_zero]
            positivity
          · have hi' := lt_of_not_ge ((hTmem i).not.mp hi)
            have hsub : (S \ A) ∩ block f i ⊆ S ∩ block f i := by
              intro v hv
              obtain ⟨hvSA, hvi⟩ := Finset.mem_inter.mp hv
              exact Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hvSA).1, hvi⟩
            have hc : ((((S \ A) ∩ block f i).card : ℝ)) ≤
                ((S ∩ block f i).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
            exact hc.trans hi'.le
        _ = _ := by simp; ring
    have hcap : ((S ∩ A).card : ℝ) ≤ A.card := by
      exact_mod_cast Finset.card_le_card (Finset.inter_subset_right : S ∩ A ⊆ A)
    have hpart' : ((S \ A).card : ℝ) + (S ∩ A).card = S.card := by
      exact_mod_cast hpart
    linarith
  have hTne : T.Nonempty := by
    by_contra! hT0
    have hA0 : A = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv
      have := (hAmem v).mp hv
      exact hT0 ⟨f v, this⟩
    have hstrict := mul_lt_mul_of_pos_right hsmall hm
    rw [hA0, Finset.card_empty, Nat.cast_zero, zero_add] at hSbound
    nlinarith
  have hAR : A ⊆ robustNeighbors G ν S := by
    intro v hv
    exact neighbors_in_heavy_block G f S (f v) v ν hlarge
      ((hTmem _).mp ((hAmem v).mp hv)) (hmissing v (f v) (Or.inl rfl))
  by_cases hTall : T = univ
  · have hAall : A = univ := by ext v; simp [A, hTall]
    have hRall : robustNeighbors G ν S = univ :=
      Finset.Subset.antisymm (Finset.subset_univ _) (hAall ▸ hAR)
    rw [hRall, Finset.card_univ]
    have hmul := mul_le_mul_of_nonneg_right hντ hm.le
    nlinarith
  · obtain ⟨i, hi, j, hj, hij⟩ := exists_boundary_edge H hH T hTne hTall
    have hBR : block f j ⊆ robustNeighbors G ν S := by
      intro v hv
      have hvj := (mem_block f j v).mp hv
      exact neighbors_in_heavy_block G f S i v ν hlarge ((hTmem i).mp hi)
        (hmissing v i (Or.inr (hvj ▸ hij.symm)))
    have hdisj : Disjoint A (block f j) := by
      apply Finset.disjoint_left.mpr
      intro v hvA hvj
      exact hj ((mem_block f j v).mp hvj ▸ (hAmem v).mp hvA)
    have hcard : A.card + (block f j).card ≤ (robustNeighbors G ν S).card := by
      rw [← Finset.card_union_of_disjoint hdisj]
      exact Finset.card_le_card (Finset.union_subset hAR hBR)
    have hcard' : (A.card : ℝ) + (block f j).card ≤ (robustNeighbors G ν S).card := by
      exact_mod_cast hcard
    have hsz := hsize j
    have hgap' := mul_le_mul_of_nonneg_right hgap hm.le
    nlinarith

end Overfull.RobustRealization
