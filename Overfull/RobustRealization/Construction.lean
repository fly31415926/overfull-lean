import Overfull.RobustRealization.CyclePower
import Overfull.RobustRealization.Pairs
import Overfull.BipartitePackingAccounting

/-!
# Realizing an almost constant degree multiset

Even base degrees are realized by a cycle power with disjoint long chords
added. Odd base degrees are realized by a cycle power with consecutive
pairs removed. The complete-graph endpoint is included separately.
-/

namespace Overfull.RobustRealization

open Finset Classical SimpleGraph

theorem exists_chord_matching (n r h : ℕ) [NeZero n]
    (hh : 2*h ≤ n) (hr : r < n/2) :
    ∃ (M : SimpleGraph (Fin n)) (Z : Finset (Fin n)),
      Z.card = 2*h ∧ (∀ v, M.degree v = if v ∈ Z then 1 else 0) ∧
      M ≤ (cyclePower n r)ᶜ := by
  let a : Fin h → Fin n := fun i => ⟨i.val, by omega⟩
  let b : Fin h → Fin n := fun i => ⟨i.val+n/2, by omega⟩
  have ha : Function.Injective a := by
    intro i j hij
    apply Fin.ext
    have hv := congrArg Fin.val hij
    exact hv
  have hb : Function.Injective b := by
    intro i j hij
    have hv := congrArg Fin.val hij
    apply Fin.ext
    dsimp [b] at hv
    omega
  have hab : ∀ i j, a i ≠ b j := by
    intro i j hij
    have hv := congrArg Fin.val hij
    dsimp [a, b] at hv
    have hi := i.isLt
    omega
  refine ⟨pairGraph a b hab, univ.image a ∪ univ.image b,
    by simpa using pairGraph_covered_card a b ha hb hab,
    pairGraph_degree a b ha hb hab, ?_⟩
  apply pairGraph_le _ a b hab
  intro i
  rw [SimpleGraph.compl_adj]
  refine ⟨hab i i, ?_⟩
  have hlt : a i < b i := by change i.val < i.val+n/2; omega
  have hdiff₁ : (b i-a i).val = n/2 := by
    rw [Fin.sub_val_of_le hlt.le]
    dsimp [a, b]
    omega
  have hdiff₂ : (a i-b i).val = n-n/2 := by
    rw [Fin.coe_sub_iff_lt.mpr hlt]
    dsimp [a, b]
    omega
  rw [cyclePower_adj, hdiff₁, hdiff₂]
  rintro ⟨_, h | h⟩ <;> omega

theorem exists_consecutive_matching (n r h : ℕ) [NeZero n]
    (hh : 2*h ≤ n) (hr : 0 < r) :
    ∃ (M : SimpleGraph (Fin n)) (Z : Finset (Fin n)),
      Z.card = 2*h ∧ (∀ v, M.degree v = if v ∈ Z then 1 else 0) ∧
      M ≤ cyclePower n r := by
  let a : Fin h → Fin n := fun i => ⟨2*i.val, by omega⟩
  let b : Fin h → Fin n := fun i => ⟨2*i.val+1, by omega⟩
  have ha : Function.Injective a := by
    intro i j hij
    have hv := congrArg Fin.val hij
    apply Fin.ext
    dsimp [a] at hv
    omega
  have hb : Function.Injective b := by
    intro i j hij
    have hv := congrArg Fin.val hij
    apply Fin.ext
    dsimp [b] at hv
    omega
  have hab : ∀ i j, a i ≠ b j := by
    intro i j hij
    have hv := congrArg Fin.val hij
    dsimp [a, b] at hv
    omega
  refine ⟨pairGraph a b hab, univ.image a ∪ univ.image b,
    by simpa using pairGraph_covered_card a b ha hb hab,
    pairGraph_degree a b ha hb hab, ?_⟩
  apply pairGraph_le _ a b hab
  intro i
  apply cyclePower_adj_of_lt
  · change 2*i.val < 2*i.val+1
    omega
  · change (2*i.val+1)-2*i.val ≤ r
    omega

set_option maxHeartbeats 800000 in
/-- The graph realizes `h` entries equal to `d+1` and all remaining entries
equal to `d`. It contains the required cycle power after adding back a
graph of maximum degree one. -/
theorem exists_degree_multiset (n d h : ℕ) [NeZero n]
    (hd : 2 ≤ d) (hdn : d < n) (hh : h ≤ n)
    (hmax : 0 < h → d+1 < n) (heven : Even (n*d+h)) :
    ∃ (G M : SimpleGraph (Fin n)) (r : ℕ) (Z : Finset (Fin n)),
      Z.card = h ∧ (∀ v, G.degree v = if v ∈ Z then d+1 else d) ∧
      (d : ℝ)/3 ≤ r ∧ cyclePower n r ≤ G ⊔ M ∧ (∀ v, M.degree v ≤ 1) := by
  by_cases hfull : d+1 = n
  · have hh0 : h = 0 := by
      by_contra hn
      have := hmax (Nat.pos_of_ne_zero hn)
      omega
    refine ⟨⊤, ⊥, n, ∅, by simp [hh0], ?_, ?_, ?_, ?_⟩
    · intro v
      have htop : (⊤ : SimpleGraph (Fin n)).degree v = n-1 := by
        simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card,
          Nat.card_fin] using (SimpleGraph.complete_graph_degree v)
      simp only [Finset.notMem_empty, if_false]
      have hd' : n-1 = d := by omega
      simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        using (htop.trans hd')
    · have hdr : (d : ℝ) < n := by exact_mod_cast hdn
      linarith
    · simp
    · intro v
      simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        using (show (⊥ : SimpleGraph (Fin n)).degree v ≤ 1 by simp)
  have hd1 : d+1 < n := by omega
  by_cases hdEven : Even d
  · obtain ⟨r, hr⟩ := hdEven
    have hr2 : 2*r = d := by omega
    have hrpos : 0 < r := by omega
    have hrn : 2*r < n := by omega
    have hEven : Even h := by
      rw [Nat.even_iff] at heven ⊢
      have hdm : d % 2 = 0 := by omega
      rw [Nat.add_mod, Nat.mul_mod, hdm] at heven
      simp only [Nat.mul_zero, Nat.zero_mod, Nat.zero_add, Nat.mod_mod] at heven
      exact heven
    obtain ⟨k, hk⟩ := hEven
    have hk2 : 2*k = h := by omega
    obtain ⟨M, Z, hZ, hMdeg, hMc⟩ := exists_chord_matching n r k (by omega) (by omega)
    have hInf : cyclePower n r ⊓ M = ⊥ := by
      ext v w
      simp only [SimpleGraph.inf_adj, SimpleGraph.bot_adj, iff_false, not_and]
      intro hp hm
      exact (hMc hm).2 hp
    have hdegree (v : Fin n) :
        (cyclePower n r ⊔ M).degree v = if v ∈ Z then d+1 else d := by
      have hdeg := BipartitePackingAccounting.degree_sup_add_degree_inf (cyclePower n r) M v
      have hzero : (cyclePower n r ⊓ M).degree v = 0 := by
        simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        rw [hInf]
        simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
          using (SimpleGraph.bot_degree v)
      rw [hzero, Nat.add_zero, cyclePower_degree n r hrpos hrn v, hMdeg v] at hdeg
      simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        at hdeg ⊢
      by_cases hv : v ∈ Z
      · simp only [if_pos hv] at hdeg ⊢
        omega
      · simp only [if_neg hv] at hdeg ⊢
        omega
    refine ⟨cyclePower n r ⊔ M, ⊥, r, Z, by omega, ?_, ?_, ?_, ?_⟩
    · simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        using hdegree
    · have hrR : (2 : ℝ)*r = d := by exact_mod_cast hr2
      have := Nat.cast_nonneg r (α := ℝ)
      linarith
    · exact le_trans le_sup_left le_sup_left
    · intro v
      simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        using (show (⊥ : SimpleGraph (Fin n)).degree v ≤ 1 by simp)
  · have hdmod : d % 2 = 1 := by
      rw [Nat.even_iff] at hdEven
      omega
    have hEven : Even (n-h) := by
      rw [Nat.even_iff] at heven ⊢
      rw [Nat.add_mod, Nat.mul_mod, hdmod, Nat.mul_one] at heven
      simp only [Nat.mod_mod] at heven
      omega
    obtain ⟨k, hk⟩ := hEven
    have hk2 : 2*k = n-h := by omega
    let r := (d+1)/2
    have hr2 : 2*r = d+1 := by dsimp [r]; omega
    have hrpos : 0 < r := by omega
    have hrn : 2*r < n := by omega
    obtain ⟨M, Z, hZ, hMdeg, hMc⟩ := exists_consecutive_matching n r k (by omega) hrpos
    have hdegree (v : Fin n) :
        (cyclePower n r \ M).degree v = if v ∈ univ \ Z then d+1 else d := by
      have hdeg := BipartitePackingAccounting.degree_sdiff_add_of_le (cyclePower n r) M hMc v
      rw [cyclePower_degree n r hrpos hrn v, hMdeg v] at hdeg
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
      by_cases hv : v ∈ Z
      · simp only [hv, if_pos, not_true_eq_false, if_false] at hdeg ⊢
        omega
      · simp only [hv, if_neg, not_false_eq_true, if_true] at hdeg ⊢
        omega
    refine ⟨cyclePower n r \ M, M, r, univ \ Z, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Finset.card_sdiff_of_subset (Finset.subset_univ Z), Finset.card_univ,
        Fintype.card_fin, hZ]
      omega
    · simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        using hdegree
    · have hrR : (2 : ℝ)*r = d+1 := by exact_mod_cast hr2
      have := Nat.cast_nonneg r (α := ℝ)
      linarith
    · intro v w hvw
      by_cases hm : M.Adj v w
      · exact Or.inr hm
      · exact Or.inl ⟨hvw, hm⟩
    · intro v
      rw [hMdeg v]
      split <;> omega

end Overfull.RobustRealization
