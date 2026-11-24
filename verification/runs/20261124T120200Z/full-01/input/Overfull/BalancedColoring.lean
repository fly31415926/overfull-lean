import Overfull.ColorCoverage
import Overfull.TwoColorEndpoints
import Overfull.BalancedVectors

/-!
# Balanced colorings

Actual two-color component interchanges first balance the two sides in each
class and then reduce the spread of their common coverage counts.
-/

namespace Overfull.Multigraph.EdgeColoring

open Finset Classical
open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E]
variable {G : Multigraph V E} {q : ℕ}

omit [Fintype E] in
theorem transfer_eq_endpoint_sum (c : G.EdgeColoring q) (i j : Fin q)
    (A : Finset V) (C : (c.twoColorGraph i j).ConnectedComponent) :
    c.transfer i j A (c.componentVertices i j C) =
      ∑ v ∈ c.componentEndpoints i j C,
        if v ∈ A then c.coverIndicator i v - c.coverIndicator j v else 0 := by
  rw [c.transfer_eq_sum, componentEndpoints, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hi : c.Covers i v <;> by_cases hj : c.Covers j v <;>
    simp [coverIndicator, hi, hj]

theorem component_transfers_allowed (c : G.EdgeColoring q) (i j : Fin q) (hij : i ≠ j)
    (A B Z : Finset V) (hAB : Disjoint A B) (hpartition : (A ∪ B) ∪ Z = univ)
    (hZ : ∀ v ∈ Z, G.degree v = q)
    (C : (c.twoColorGraph i j).ConnectedComponent) :
    BalancedVectors.Allowed
      (c.transfer i j A (c.componentVertices i j C))
      (c.transfer i j B (c.componentVertices i j C)) := by
  have hside (v : V) (hv : v ∈ c.componentEndpoints i j C) :
      (v ∈ A ∧ v ∉ B) ∨ (v ∈ B ∧ v ∉ A) := by
    have hsign := (Finset.mem_filter.mp hv).2
    have hvZ : v ∉ Z := by
      intro hz
      have hi := c.covers_of_degree_eq v (hZ v hz) i
      have hj := c.covers_of_degree_eq v (hZ v hz) j
      tauto
    have hvall : v ∈ (A ∪ B) ∪ Z := by rw [hpartition]; simp
    have hvAB : v ∈ A ∨ v ∈ B := by
      simpa only [Finset.mem_union, hvZ, or_false] using hvall
    have hd : ¬ (v ∈ A ∧ v ∈ B) := by
      rintro ⟨ha, hb⟩
      exact Finset.disjoint_left.mp hAB ha hb
    tauto
  obtain ⟨hcard, heven⟩ := c.componentEndpoints_card i j hij C
  by_cases hzero : (c.componentEndpoints i j C).card = 0
  · have hP := Finset.card_eq_zero.mp hzero
    simp [c.transfer_eq_endpoint_sum, hP, BalancedVectors.Allowed]
  · have htwo : (c.componentEndpoints i j C).card = 2 := by
      rw [Nat.even_iff] at heven
      omega
    obtain ⟨x, y, hxy, hP⟩ := Finset.card_eq_two.mp htwo
    have hx : x ∈ c.componentEndpoints i j C := by rw [hP]; simp
    have hy : y ∈ c.componentEndpoints i j C := by rw [hP]; simp
    have hsx := hside x hx
    have hsy := hside y hy
    have hcx := (Finset.mem_filter.mp hx).2
    have hcy := (Finset.mem_filter.mp hy).2
    rw [c.transfer_eq_endpoint_sum, c.transfer_eq_endpoint_sum, hP,
      Finset.sum_pair hxy, Finset.sum_pair hxy]
    rcases hsx with ⟨hAx, hBx⟩ | ⟨hBx, hAx⟩ <;>
      rcases hsy with ⟨hAy, hBy⟩ | ⟨hBy, hAy⟩ <;>
      rcases hcx with ⟨hix, hjx⟩ | ⟨hjx, hix⟩ <;>
      rcases hcy with ⟨hiy, hjy⟩ | ⟨hjy, hiy⟩ <;>
      simp [coverIndicator, hAx, hBx, hAy, hBy, hix, hjx, hiy, hjy, BalancedVectors.Allowed]

noncomputable def imbalance (c : G.EdgeColoring q) (A B : Finset V) (i : Fin q) : ℤ :=
  c.coveredCount A i - c.coveredCount B i

theorem imbalance_even (c : G.EdgeColoring q) (A B Z : Finset V)
    (hAB : Disjoint A B) (hUZ : Disjoint (A ∪ B) Z)
    (hpartition : (A ∪ B) ∪ Z = univ) (hZeven : Even Z.card)
    (hZ : ∀ v ∈ Z, G.degree v = q) (i : Fin q) : Even (c.imbalance A B i) := by
  have hz : c.coveredCount Z i = (Z.card : ℤ) :=
    c.coveredCount_of_covers Z i (fun v hv => c.covers_of_degree_eq v (hZ v hv) i)
  have hcount := c.coveredCount_union (A ∪ B) Z i hUZ
  rw [hpartition, c.coveredCount_univ, c.coveredCount_union A B i hAB, hz] at hcount
  have heven : Even ((c.coveredVertices i).card : ℤ) :=
    (Int.even_coe_nat _).mpr (c.coveredVertices_even i)
  have hevenZ : Even (Z.card : ℤ) := (Int.even_coe_nat _).mpr hZeven
  have hs : Even (c.coveredCount A i + c.coveredCount B i) := by
    convert heven.sub hevenZ using 1
    omega
  convert hs.sub (even_two_mul (c.coveredCount B i)) using 1
  unfold imbalance
  ring

theorem sum_imbalance_zero (c : G.EdgeColoring q) (A B : Finset V)
    (hdegree : (∑ v ∈ A, G.degree v) = ∑ v ∈ B, G.degree v) :
    ∑ i : Fin q, c.imbalance A B i = 0 := by
  simp only [imbalance, Finset.sum_sub_distrib, c.sum_coveredCount]
  have h : (∑ v ∈ A, (G.degree v : ℤ)) = ∑ v ∈ B, (G.degree v : ℤ) := by
    exact_mod_cast hdegree
  rw [h, sub_self]

omit [Fintype E] in
theorem swapOn_imbalance (c : G.EdgeColoring q) (i j : Fin q)
    (X : Finset V) (hX : c.TwoColorClosed i j X) (A B : Finset V) :
    (c.swapOn i j X hX).imbalance A B i =
      c.imbalance A B i - (c.transfer i j A X - c.transfer i j B X) := by
  simp only [imbalance, c.swapOn_coveredCount]
  ring

omit [Fintype E] in
theorem swapOn_imbalance_right (c : G.EdgeColoring q) (i j : Fin q)
    (X : Finset V) (hX : c.TwoColorClosed i j X) (A B : Finset V) :
    (c.swapOn i j X hX).imbalance A B j =
      c.imbalance A B j + (c.transfer i j A X - c.transfer i j B X) := by
  simp only [imbalance, c.swapOn_coveredCount_right]
  ring

omit [Fintype E] in
theorem swapOn_imbalance_other (c : G.EdgeColoring q) (i j r : Fin q)
    (X : Finset V) (hX : c.TwoColorClosed i j X) (A B : Finset V)
    (hri : r ≠ i) (hrj : r ≠ j) :
    (c.swapOn i j X hX).imbalance A B r = c.imbalance A B r := by
  simp only [imbalance, c.swapOn_coveredCount_other i j r X hX _ hri hrj]

private theorem sum_change_two {I : Type*} [Fintype I] (a b : I → ℤ)
    (i j : I) (hij : i ≠ j) (hother : ∀ r, r ≠ i → r ≠ j → a r = b r) :
    (∑ r, a r) = (∑ r, b r) + (a i - b i) + (a j - b j) := by
  have hpoint (r : I) : a r = b r +
      (if r = i then a i - b i else 0) + (if r = j then a j - b j else 0) := by
    by_cases hri : r = i
    · subst r
      simp [hij]
    · by_cases hrj : r = j
      · subst r
        simp [hri]
      · rw [hother r hri hrj]
        simp [hri, hrj]
  calc
    _ = ∑ r : I, (b r + (if r = i then a i - b i else 0) +
        (if r = j then a j - b j else 0)) := Finset.sum_congr rfl (fun r _ => hpoint r)
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

def IsBalanced (c : G.EdgeColoring q) (A B : Finset V) : Prop :=
  ∀ i, c.coveredCount A i = c.coveredCount B i

/-- The first finite minimum eliminates every nonzero side imbalance. -/
theorem exists_balanced (c₀ : G.EdgeColoring q) (A B Z : Finset V)
    (hAB : Disjoint A B) (hUZ : Disjoint (A ∪ B) Z)
    (hpartition : (A ∪ B) ∪ Z = univ) (hZeven : Even Z.card)
    (hZ : ∀ v ∈ Z, G.degree v = q)
    (hdegree : (∑ v ∈ A, G.degree v) = ∑ v ∈ B, G.degree v) :
    ∃ c : G.EdgeColoring q, c.IsBalanced A B := by
  obtain ⟨c, _, hmin⟩ := Finset.exists_min_image (univ : Finset (G.EdgeColoring q))
    (fun c => ∑ i : Fin q, (c.imbalance A B i) ^ 2) ⟨c₀, Finset.mem_univ c₀⟩
  have hsum := c.sum_imbalance_zero A B hdegree
  have hnonpos (i : Fin q) : c.imbalance A B i ≤ 0 := by
    by_contra hn
    have hi : 0 < c.imbalance A B i := lt_of_not_ge hn
    have hnegative : ∃ j, c.imbalance A B j < 0 := by
      by_contra hnot
      push_neg at hnot
      have hall := (Finset.sum_eq_zero_iff_of_nonneg
        (fun r (_ : r ∈ (univ : Finset (Fin q))) => hnot r)).mp hsum
      have hiz := hall i (Finset.mem_univ i)
      omega
    obtain ⟨j, hj⟩ := hnegative
    have hij : i ≠ j := by intro h; subst j; omega
    have hei := c.imbalance_even A B Z hAB hUZ hpartition hZeven hZ i
    have hej := c.imbalance_even A B Z hAB hUZ hpartition hZeven hZ j
    rw [Int.even_iff] at hei hej
    have hi₂ : 2 ≤ c.imbalance A B i := by omega
    have hj₂ : c.imbalance A B j ≤ -2 := by omega
    have hsumcomp :
        (∑ C : (c.twoColorGraph i j).ConnectedComponent,
          (c.transfer i j A (c.componentVertices i j C) -
            c.transfer i j B (c.componentVertices i j C))) =
          c.imbalance A B i - c.imbalance A B j := by
      rw [Finset.sum_sub_distrib, c.sum_transfer_components, c.sum_transfer_components]
      unfold imbalance
      ring
    obtain ⟨C, hC⟩ := BalancedVectors.exists_difference_two
      (fun C => c.transfer i j A (c.componentVertices i j C))
      (fun C => c.transfer i j B (c.componentVertices i j C))
      (fun C => c.component_transfers_allowed i j hij A B Z hAB hpartition hZ C)
      (by rw [hsumcomp]; omega)
    let X := c.componentVertices i j C
    let c' := c.swapOn i j X (c.component_closed i j C)
    have hci : c'.imbalance A B i = c.imbalance A B i - 2 := by
      simpa only [c', X, hC] using c.swapOn_imbalance i j X (c.component_closed i j C) A B
    have hcj : c'.imbalance A B j = c.imbalance A B j + 2 := by
      simpa only [c', X, hC] using c.swapOn_imbalance_right i j X (c.component_closed i j C) A B
    have henergy := sum_change_two
      (fun r => (c'.imbalance A B r) ^ 2) (fun r => (c.imbalance A B r) ^ 2)
      i j hij (by
        intro r hri hrj
        exact congrArg (fun x : ℤ => x ^ 2)
          (c.swapOn_imbalance_other i j r X (c.component_closed i j C) A B hri hrj))
    simp only [hci, hcj] at henergy
    have hminimal := hmin c' (Finset.mem_univ c')
    rw [henergy] at hminimal
    nlinarith
  refine ⟨c, ?_⟩
  intro i
  have hi := (Finset.sum_eq_zero_iff_of_nonpos
    (fun r (_ : r ∈ (univ : Finset (Fin q))) => hnonpos r)).mp hsum i (Finset.mem_univ i)
  exact sub_eq_zero.mp hi

omit [Fintype E] in
theorem swapOn_isBalanced (c : G.EdgeColoring q) (A B : Finset V)
    (hc : c.IsBalanced A B) (i j : Fin q) (X : Finset V)
    (hX : c.TwoColorClosed i j X)
    (htransfer : c.transfer i j A X = c.transfer i j B X) :
    (c.swapOn i j X hX).IsBalanced A B := by
  intro r
  by_cases hri : r = i
  · subst r
    rw [c.swapOn_coveredCount, c.swapOn_coveredCount, htransfer, hc i]
  · by_cases hrj : r = j
    · subst r
      rw [c.swapOn_coveredCount_right, c.swapOn_coveredCount_right, htransfer, hc j]
    · rw [c.swapOn_coveredCount_other i j r X hX A hri hrj,
        c.swapOn_coveredCount_other i j r X hX B hri hrj, hc r]

/-- The second finite minimum makes the balanced coverage counts differ by at most two. -/
theorem exists_balanced_spread (c₀ : G.EdgeColoring q) (A B Z : Finset V)
    (hAB : Disjoint A B) (hUZ : Disjoint (A ∪ B) Z)
    (hpartition : (A ∪ B) ∪ Z = univ) (hZeven : Even Z.card)
    (hZ : ∀ v ∈ Z, G.degree v = q)
    (hdegree : (∑ v ∈ A, G.degree v) = ∑ v ∈ B, G.degree v) :
    ∃ c : G.EdgeColoring q, c.IsBalanced A B ∧
      ∀ i j, |c.coveredCount A i - c.coveredCount A j| ≤ 2 := by
  obtain ⟨c₁, hc₁⟩ := c₀.exists_balanced A B Z hAB hUZ hpartition hZeven hZ hdegree
  let S : Finset (G.EdgeColoring q) := univ.filter (fun c => c.IsBalanced A B)
  have hS : S.Nonempty := ⟨c₁, Finset.mem_filter.mpr ⟨Finset.mem_univ c₁, hc₁⟩⟩
  obtain ⟨c, hcS, hmin⟩ := Finset.exists_min_image S
    (fun c => ∑ i : Fin q, (c.coveredCount A i) ^ 2) hS
  have hc : c.IsBalanced A B := (Finset.mem_filter.mp hcS).2
  have hle (i j : Fin q) : c.coveredCount A i - c.coveredCount A j ≤ 2 := by
    by_contra hn
    have hdelta : 3 ≤ c.coveredCount A i - c.coveredCount A j := by omega
    have hij : i ≠ j := by intro h; subst j; omega
    have hsumA : 0 < ∑ C : (c.twoColorGraph i j).ConnectedComponent,
        c.transfer i j A (c.componentVertices i j C) := by
      rw [c.sum_transfer_components]
      omega
    have hsumB : 0 < ∑ C : (c.twoColorGraph i j).ConnectedComponent,
        c.transfer i j B (c.componentVertices i j C) := by
      rw [c.sum_transfer_components, ← hc i, ← hc j]
      omega
    obtain ⟨T, _, p, hp, hA, hB⟩ := BalancedVectors.exists_balanced_subset
      (fun C => c.transfer i j A (c.componentVertices i j C))
      (fun C => c.transfer i j B (c.componentVertices i j C))
      (fun C => c.component_transfers_allowed i j hij A B Z hAB hpartition hZ C)
      hsumA hsumB
    let X := c.componentUnion i j T
    have hX := c.componentUnion_closed i j T
    have hXA : c.transfer i j A X = p := by
      rw [c.transfer_componentUnion]
      exact hA
    have hXB : c.transfer i j B X = p := by
      rw [c.transfer_componentUnion]
      exact hB
    let c' := c.swapOn i j X hX
    have hc' : c'.IsBalanced A B :=
      c.swapOn_isBalanced A B hc i j X hX (hXA.trans hXB.symm)
    have hc'S : c' ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ c', hc'⟩
    have hci : c'.coveredCount A i = c.coveredCount A i - p := by
      simpa only [c', hXA] using c.swapOn_coveredCount i j X hX A
    have hcj : c'.coveredCount A j = c.coveredCount A j + p := by
      simpa only [c', hXA] using c.swapOn_coveredCount_right i j X hX A
    have henergy := sum_change_two
      (fun r => (c'.coveredCount A r) ^ 2) (fun r => (c.coveredCount A r) ^ 2)
      i j hij (by
        intro r hri hrj
        exact congrArg (fun x : ℤ => x ^ 2)
          (c.swapOn_coveredCount_other i j r X hX A hri hrj))
    simp only [hci, hcj] at henergy
    have hminimal := hmin c' hc'S
    rw [henergy] at hminimal
    rcases hp with rfl | rfl <;> nlinarith
  refine ⟨c, hc, ?_⟩
  intro i j
  apply abs_le.mpr
  exact ⟨by have := hle j i; omega, hle i j⟩

theorem balanced_footprint_bound (c : G.EdgeColoring q) (hq : 0 < q)
    (A B : Finset V) (hAB : Disjoint A B) (hc : c.IsBalanced A B)
    (hspread : ∀ i j, |c.coveredCount A i - c.coveredCount A j| ≤ 2) (i : Fin q) :
    (((A ∪ B) ∩ c.coveredVertices i).card : ℝ) ≤
      (∑ v ∈ A ∪ B, (G.degree v : ℝ)) / q + 4 := by
  have hcount (j : Fin q) : c.coveredCount (A ∪ B) j = 2 * c.coveredCount A j := by
    rw [c.coveredCount_union A B j hAB, ← hc j]
    ring
  have hle (j : Fin q) :
      (c.coveredCount (A ∪ B) i : ℝ) ≤ (c.coveredCount (A ∪ B) j : ℝ) + 4 := by
    have h := (abs_le.mp (hspread i j)).2
    have hz : c.coveredCount (A ∪ B) i ≤ c.coveredCount (A ∪ B) j + 4 := by
      rw [hcount i, hcount j]
      omega
    exact_mod_cast hz
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ (univ : Finset (Fin q))) => hle j)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hsum
  have hdegreeSum : (∑ j : Fin q, (c.coveredCount (A ∪ B) j : ℝ)) =
      ∑ v ∈ A ∪ B, (G.degree v : ℝ) := by
    exact_mod_cast c.sum_coveredCount (A ∪ B)
  rw [hdegreeSum] at hsum
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hbound : (c.coveredCount (A ∪ B) i : ℝ) - 4 ≤
      (∑ v ∈ A ∪ B, (G.degree v : ℝ)) / q := by
    apply (le_div_iff₀ hqR).mpr
    nlinarith
  have hbound' : (c.coveredCount (A ∪ B) i : ℝ) ≤
      (∑ v ∈ A ∪ B, (G.degree v : ℝ)) / q + 4 := by linarith
  simpa only [coveredCount, Int.cast_natCast] using hbound'

theorem balanced_footprint_bound_of_degree_bound (c : G.EdgeColoring q) (hq : 0 < q)
    (A B : Finset V) (hAB : Disjoint A B) (hcard : A.card = B.card)
    (hc : c.IsBalanced A B)
    (hspread : ∀ i j, |c.coveredCount A i - c.coveredCount A j| ≤ 2)
    (a : ℝ) (hdegree : ∀ v ∈ A ∪ B, (G.degree v : ℝ) ≤ a) (i : Fin q) :
    (((A ∪ B) ∩ c.coveredVertices i).card : ℝ) ≤ 2 * A.card * a / q + 4 := by
  have hsize : ((A ∪ B).card : ℝ) = 2 * A.card := by
    rw [Finset.card_union_of_disjoint hAB, ← hcard]
    push_cast
    ring
  have hsum : (∑ v ∈ A ∪ B, (G.degree v : ℝ)) ≤ 2 * A.card * a := by
    calc
      _ ≤ ∑ _v ∈ A ∪ B, a := Finset.sum_le_sum hdegree
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, hsize]
  exact (c.balanced_footprint_bound hq A B hAB hc hspread i).trans
    (add_le_add_right (div_le_div_of_nonneg_right hsum (Nat.cast_nonneg q)) 4)

end Overfull.Multigraph.EdgeColoring

namespace Overfull.Multigraph

open Finset Classical
open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E]

/-- Lemma 2.10, including exceptional coverage, balance, spread, exact
per-vertex incidence, and both footprint estimates. All color classes consist
of actual multigraph edge copies. -/
theorem balanced_edgeColoring (G : Multigraph V E) (q : ℕ) (hq : 0 < q)
    (A B Z : Finset V) (hAB : Disjoint A B) (hUZ : Disjoint (A ∪ B) Z)
    (hpartition : (A ∪ B) ∪ Z = univ) (hcard : A.card = B.card)
    (hZeven : Even Z.card) (hZ : ∀ v ∈ Z, G.degree v = q)
    (hdegree : (∑ v ∈ A, G.degree v) = ∑ v ∈ B, G.degree v)
    (hcolor : Nonempty (G.EdgeColoring q)) :
    ∃ c : G.EdgeColoring q,
      (∀ i, Z ⊆ c.coveredVertices i) ∧
      (∀ i, (A ∩ c.coveredVertices i).card = (B ∩ c.coveredVertices i).card) ∧
      (∀ i j, |((A ∩ c.coveredVertices i).card : ℤ) -
        (A ∩ c.coveredVertices j).card| ≤ 2) ∧
      (∀ v ∈ A ∪ B, (univ.filter (fun i : Fin q => v ∈ c.coveredVertices i)).card =
        G.degree v) ∧
      (∀ i, (((A ∪ B) ∩ c.coveredVertices i).card : ℝ) ≤
        (∑ v ∈ A ∪ B, (G.degree v : ℝ)) / q + 4) ∧
      (∀ a : ℝ, (∀ v ∈ A ∪ B, (G.degree v : ℝ) ≤ a) →
        ∀ i, (((A ∪ B) ∩ c.coveredVertices i).card : ℝ) ≤ 2 * A.card * a / q + 4) := by
  obtain ⟨c₀⟩ := hcolor
  obtain ⟨c, hc, hspread⟩ :=
    c₀.exists_balanced_spread A B Z hAB hUZ hpartition hZeven hZ hdegree
  refine ⟨c, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i v hv
    exact (c.mem_coveredVertices i v).mpr (c.covers_of_degree_eq v (hZ v hv) i)
  · intro i
    have h := hc i
    unfold EdgeColoring.coveredCount at h
    exact_mod_cast h
  · intro i j
    exact hspread i j
  · intro v _
    simpa only [c.mem_coveredVertices] using c.coveredColors_card v
  · exact c.balanced_footprint_bound hq A B hAB hc hspread
  · intro a ha
    exact c.balanced_footprint_bound_of_degree_bound hq A B hAB hcard hc hspread a ha

end Overfull.Multigraph
