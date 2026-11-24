import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Group.Int.Even
import Mathlib.Tactic

/-!
# Selecting at most two balanced integer vectors

These are the possible endpoint contributions of a component in the union
of two matchings. The argument retains the indices of the chosen components.
-/

namespace Overfull.BalancedVectors

open Finset Classical

def Allowed (x y : ℤ) : Prop :=
  (x = 0 ∧ y = 0) ∨ (x = 2 ∧ y = 0) ∨ (x = -2 ∧ y = 0) ∨
  (x = 0 ∧ y = 2) ∨ (x = 0 ∧ y = -2) ∨
  (x = 1 ∧ y = 1) ∨ (x = -1 ∧ y = -1) ∨
  (x = 1 ∧ y = -1) ∨ (x = -1 ∧ y = 1)

theorem allowed_iff (x y : ℤ) :
    Allowed x y ↔ |x| + |y| ≤ 2 ∧ Even (x + y) := by
  constructor
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ |
      ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) <;>
      norm_num [Int.even_iff]
  · rintro ⟨habs,heven⟩
    have hx : -2 ≤ x ∧ x ≤ 2 := by
      have := abs_nonneg y
      have := le_abs_self x
      have := neg_le_abs x
      omega
    have hy : -2 ≤ y ∧ y ≤ 2 := by
      have := abs_nonneg x
      have := le_abs_self y
      have := neg_le_abs y
      omega
    obtain ⟨hxl,hxu⟩ := hx
    obtain ⟨hyl,hyu⟩ := hy
    interval_cases x <;> interval_cases y <;>
      norm_num [Allowed, Int.even_iff] at *

variable {I : Type*} [Fintype I]

theorem exists_difference_two (a b : I → ℤ) (hallowed : ∀ i, Allowed (a i) (b i))
    (hpositive : 0 < ∑ i, (a i - b i)) :
    ∃ i, a i - b i = 2 := by
  by_contra! hnone
  have hnonpos : ∑ i, (a i - b i) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i _
    have h := hallowed i
    have hn := hnone i
    rcases h with h | h | h | h | h | h | h | h | h <;> omega
  omega

theorem exists_balanced_subset (a b : I → ℤ) (hallowed : ∀ i, Allowed (a i) (b i))
    (ha : 0 < ∑ i, a i) (hb : 0 < ∑ i, b i) :
    ∃ S : Finset I, S.card ≤ 2 ∧ ∃ p : ℤ, (p = 1 ∨ p = 2) ∧
      (∑ i ∈ S, a i) = p ∧ (∑ i ∈ S, b i) = p := by
  by_cases hdiag : ∃ i, a i = 1 ∧ b i = 1
  · obtain ⟨i,hai,hbi⟩ := hdiag
    exact ⟨{i}, by simp, 1, Or.inl rfl, by simp [hai], by simp [hbi]⟩
  have hdiag' : ∀ i, ¬ (a i = 1 ∧ b i = 1) := by simpa using hdiag
  have haxis : ∃ i, (a i = 2 ∧ b i = 0) ∨ (a i = 0 ∧ b i = 2) := by
    by_contra! hn
    have hs : ∑ i, (a i + b i) ≤ 0 := by
      apply Finset.sum_nonpos
      intro i _
      have h := hallowed i
      have hni := hn i
      have hdi := hdiag' i
      rcases h with h | h | h | h | h | h | h | h | h <;> omega
    rw [Finset.sum_add_distrib] at hs
    omega
  have hapos : ∃ i, 0 < a i := by
    by_contra! hn
    have hs : ∑ i, a i ≤ 0 := Finset.sum_nonpos (fun i _ => hn i)
    omega
  have hbpos : ∃ i, 0 < b i := by
    by_contra! hn
    have hs : ∑ i, b i ≤ 0 := Finset.sum_nonpos (fun i _ => hn i)
    omega
  obtain ⟨i,hi | hi⟩ := haxis
  · obtain ⟨j,hbj⟩ := hbpos
    have hj : (a j = 0 ∧ b j = 2) ∨ (a j = -1 ∧ b j = 1) := by
      have h := hallowed j
      have hd := hdiag' j
      rcases h with h | h | h | h | h | h | h | h | h <;> omega
    have hij : i ≠ j := by intro h; subst j; omega
    rcases hj with hj | hj
    · exact ⟨{i,j}, by simp [hij], 2, Or.inr rfl,
        by simp [hij,hi.1,hj.1], by simp [hij,hi.2,hj.2]⟩
    · exact ⟨{i,j}, by simp [hij], 1, Or.inl rfl,
        by simp [hij,hi.1,hj.1], by simp [hij,hi.2,hj.2]⟩
  · obtain ⟨j,haj⟩ := hapos
    have hj : (a j = 2 ∧ b j = 0) ∨ (a j = 1 ∧ b j = -1) := by
      have h := hallowed j
      have hd := hdiag' j
      rcases h with h | h | h | h | h | h | h | h | h <;> omega
    have hij : i ≠ j := by intro h; subst j; omega
    rcases hj with hj | hj
    · exact ⟨{i,j}, by simp [hij], 2, Or.inr rfl,
        by simp [hij,hi.1,hj.1], by simp [hij,hi.2,hj.2]⟩
    · exact ⟨{i,j}, by simp [hij], 1, Or.inl rfl,
        by simp [hij,hi.1,hj.1], by simp [hij,hi.2,hj.2]⟩

end Overfull.BalancedVectors
