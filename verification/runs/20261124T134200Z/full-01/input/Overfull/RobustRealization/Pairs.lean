import Overfull.Basic

/-!
# Graphs consisting of specified disjoint pairs

The degree formulas concern the constructed simple graph itself. They are
used to add long chords or delete consecutive pairs from a cycle power.
-/

namespace Overfull.RobustRealization

open Finset Classical SimpleGraph

variable {V I : Type*} [Fintype V] [Fintype I] [DecidableEq V]

def pairGraph (a b : I → V) (hab : ∀ i j, a i ≠ b j) : SimpleGraph V where
  Adj x y := ∃ i, (x = a i ∧ y = b i) ∨ (x = b i ∧ y = a i)
  symm := by
    rintro x y ⟨i, h | h⟩
    · exact ⟨i, Or.inr ⟨h.2, h.1⟩⟩
    · exact ⟨i, Or.inl ⟨h.2, h.1⟩⟩
  loopless := by
    rintro x ⟨i, h | h⟩
    · exact hab i i (h.1.symm.trans h.2)
    · exact hab i i (h.2.symm.trans h.1)

omit [Fintype V] [Fintype I] [DecidableEq V] in
theorem pairGraph_adj (a b : I → V) (hab : ∀ i j, a i ≠ b j) (x y : V) :
    (pairGraph a b hab).Adj x y ↔
      ∃ i, (x = a i ∧ y = b i) ∨ (x = b i ∧ y = a i) := Iff.rfl

omit [Fintype I] [DecidableEq V] in
theorem pairGraph_neighborFinset_left (a b : I → V)
    (ha : Function.Injective a) (hab : ∀ i j, a i ≠ b j) (i : I) :
    (pairGraph a b hab).neighborFinset (a i) = {b i} := by
  ext v
  simp only [mem_neighborFinset, pairGraph_adj, Finset.mem_singleton]
  constructor
  · rintro ⟨j, h | h⟩
    · have hij := ha h.1
      simpa only [← hij] using h.2
    · exact (hab i j h.1).elim
  · rintro rfl
    exact ⟨i, Or.inl ⟨rfl, rfl⟩⟩

omit [Fintype I] [DecidableEq V] in
theorem pairGraph_neighborFinset_right (a b : I → V)
    (hb : Function.Injective b) (hab : ∀ i j, a i ≠ b j) (i : I) :
    (pairGraph a b hab).neighborFinset (b i) = {a i} := by
  ext v
  simp only [mem_neighborFinset, pairGraph_adj, Finset.mem_singleton]
  constructor
  · rintro ⟨j, h | h⟩
    · exact (hab j i h.1.symm).elim
    · have hij := hb h.1
      simpa only [← hij] using h.2
  · rintro rfl
    exact ⟨i, Or.inr ⟨rfl, rfl⟩⟩

omit [Fintype I] [DecidableEq V] in
theorem pairGraph_degree_left (a b : I → V)
    (ha : Function.Injective a) (hab : ∀ i j, a i ≠ b j) (i : I) :
    (pairGraph a b hab).degree (a i) = 1 := by
  rw [← card_neighborFinset_eq_degree, pairGraph_neighborFinset_left a b ha hab i]
  simp

omit [Fintype I] [DecidableEq V] in
theorem pairGraph_degree_right (a b : I → V)
    (hb : Function.Injective b) (hab : ∀ i j, a i ≠ b j) (i : I) :
    (pairGraph a b hab).degree (b i) = 1 := by
  rw [← card_neighborFinset_eq_degree, pairGraph_neighborFinset_right a b hb hab i]
  simp

theorem pairGraph_degree (a b : I → V)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (hab : ∀ i j, a i ≠ b j) (v : V) :
    (pairGraph a b hab).degree v =
      if v ∈ (univ.image a ∪ univ.image b) then 1 else 0 := by
  by_cases hv : v ∈ (univ.image a ∪ univ.image b)
  · rw [if_pos hv]
    rcases Finset.mem_union.mp hv with hv | hv
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
      exact pairGraph_degree_left a b ha hab i
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
      exact pairGraph_degree_right a b hb hab i
  · rw [if_neg hv, degree_eq_zero_iff_notMem_support]
    rintro ⟨w, i, hi | hi⟩
    · exact hv (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, mem_univ _, hi.1.symm⟩))
    · exact hv (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, mem_univ _, hi.1.symm⟩))

theorem pairGraph_degree_le_one (a b : I → V)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (hab : ∀ i j, a i ≠ b j) (v : V) :
    (pairGraph a b hab).degree v ≤ 1 := by
  rw [pairGraph_degree a b ha hb hab]
  split <;> omega

omit [Fintype V] in
theorem pairGraph_covered_card (a b : I → V)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (hab : ∀ i j, a i ≠ b j) :
    (univ.image a ∪ univ.image b).card = 2 * Fintype.card I := by
  have hd : Disjoint (univ.image a) (univ.image b) := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hv
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hw
    exact hab i j (hi.trans hj.symm)
  rw [Finset.card_union_of_disjoint hd, Finset.card_image_of_injective _ ha,
    Finset.card_image_of_injective _ hb, Finset.card_univ]
  omega

omit [Fintype V] [Fintype I] [DecidableEq V] in
theorem pairGraph_le (G : SimpleGraph V) (a b : I → V)
    (hab : ∀ i j, a i ≠ b j) (hG : ∀ i, G.Adj (a i) (b i)) :
    pairGraph a b hab ≤ G := by
  rintro v w ⟨i, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · exact hG i
  · exact (hG i).symm

end Overfull.RobustRealization
