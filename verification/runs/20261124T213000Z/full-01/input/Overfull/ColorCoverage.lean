import Overfull.TwoColorSwitch

/-!
# Counting color coverage

Every incident edge has its own color. These identities relate coverage
counts to degrees and record the exact effect of an interchange.
-/

namespace Overfull.Multigraph.EdgeColoring

open Finset Classical
open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E]
variable {G : Multigraph V E} {q : ℕ}

omit [Fintype V] in
theorem coveredColors_card (c : G.EdgeColoring q) (v : V) :
    (univ.filter (fun i : Fin q => c.Covers i v)).card = G.degree v := by
  have heq : univ.filter (fun i : Fin q => c.Covers i v) =
      (G.incidenceEdges v).image c.color := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      G.mem_incidenceEdges, Covers]
    aesop
  rw [heq]
  change _ = (G.incidenceEdges v).card
  apply Finset.card_image_of_injOn
  intro e he f hf hef
  exact c.proper hef ((G.mem_incidenceEdges v e).mp he) ((G.mem_incidenceEdges v f).mp hf)

omit [Fintype V] in
theorem covers_of_degree_eq (c : G.EdgeColoring q) (v : V) (hv : G.degree v = q)
    (i : Fin q) : c.Covers i v := by
  have heq : univ.filter (fun i : Fin q => c.Covers i v) = univ :=
    Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by
      rw [c.coveredColors_card v, hv, Finset.card_univ, Fintype.card_fin])
  have hi : i ∈ univ.filter (fun i : Fin q => c.Covers i v) := by rw [heq]; simp
  exact (Finset.mem_filter.mp hi).2

theorem coveredVertices_eq_biUnion (c : G.EdgeColoring q) (i : Fin q) :
    c.coveredVertices i = (c.colorClass i).biUnion (fun e => (G.edge e).toFinset) := by
  ext v
  simp only [mem_coveredVertices, Covers, Finset.mem_biUnion, colorClass,
    Finset.mem_filter, Finset.mem_univ, true_and, Sym2.mem_toFinset]

omit [Fintype V] in
theorem colorClass_pairwise_disjoint (c : G.EdgeColoring q) (i : Fin q) :
    (↑(c.colorClass i) : Set E).PairwiseDisjoint (fun e => (G.edge e).toFinset) := by
  intro e he f hf hne
  apply Finset.disjoint_left.mpr
  intro v hv hv'
  apply hne
  exact c.proper ((Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp hf).2.symm)
    (by simpa only [Sym2.mem_toFinset] using hv)
    (by simpa only [Sym2.mem_toFinset] using hv')

theorem coveredVertices_card (c : G.EdgeColoring q) (i : Fin q) :
    (c.coveredVertices i).card = 2 * (c.colorClass i).card := by
  rw [c.coveredVertices_eq_biUnion, Finset.card_biUnion (c.colorClass_pairwise_disjoint i)]
  have h : ∑ e ∈ c.colorClass i, (G.edge e).toFinset.card =
      ∑ _e ∈ c.colorClass i, (2 : ℕ) := by
    apply Finset.sum_congr rfl
    intro e _
    exact Sym2.card_toFinset_of_not_isDiag _ (G.loopless e)
  rw [h]
  simp [Nat.mul_comm]

theorem coveredVertices_even (c : G.EdgeColoring q) (i : Fin q) :
    Even (c.coveredVertices i).card := by
  rw [c.coveredVertices_card]
  exact even_two_mul _

/-- Integer-valued coverage counts make the signed interchanges explicit. -/
noncomputable def coveredCount (c : G.EdgeColoring q) (X : Finset V) (i : Fin q) : ℤ :=
  (X ∩ c.coveredVertices i).card

noncomputable def coverIndicator (c : G.EdgeColoring q) (i : Fin q) (v : V) : ℤ :=
  if c.Covers i v then 1 else 0

omit [Fintype E] in
theorem coveredCount_eq_sum (c : G.EdgeColoring q) (X : Finset V) (i : Fin q) :
    c.coveredCount X i = ∑ v ∈ X, c.coverIndicator i v := by
  simp [coveredCount, coveredVertices, coverIndicator, Finset.inter_filter,
    Finset.sum_boole]

omit [Fintype E] in
theorem coveredCount_nonneg (c : G.EdgeColoring q) (X : Finset V) (i : Fin q) :
    0 ≤ c.coveredCount X i := Int.natCast_nonneg _

theorem sum_coveredCount (c : G.EdgeColoring q) (X : Finset V) :
    (∑ i : Fin q, c.coveredCount X i) = ∑ v ∈ X, (G.degree v : ℤ) := by
  simp only [coveredCount_eq_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  simp only [coverIndicator, Finset.sum_boole]
  rw [c.coveredColors_card]

omit [Fintype E] in
theorem coveredCount_union (c : G.EdgeColoring q) (X Y : Finset V) (i : Fin q)
    (hXY : Disjoint X Y) :
    c.coveredCount (X ∪ Y) i = c.coveredCount X i + c.coveredCount Y i := by
  simp only [coveredCount_eq_sum]
  exact Finset.sum_union hXY

/-- Difference between the two coverage counts inside the selected set. -/
noncomputable def transfer (c : G.EdgeColoring q) (i j : Fin q)
    (A X : Finset V) : ℤ := c.coveredCount (A ∩ X) i - c.coveredCount (A ∩ X) j

omit [Fintype E] in
theorem transfer_eq_sum (c : G.EdgeColoring q) (i j : Fin q) (A X : Finset V) :
    c.transfer i j A X =
      ∑ v ∈ X, if v ∈ A then c.coverIndicator i v - c.coverIndicator j v else 0 := by
  rw [transfer, coveredCount_eq_sum, coveredCount_eq_sum, ← Finset.sum_sub_distrib]
  rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.sum_filter]

omit [Fintype E] in
theorem swapOn_coveredCount (c : G.EdgeColoring q) (i j : Fin q)
    (X : Finset V) (hX : c.TwoColorClosed i j X) (A : Finset V) :
    (c.swapOn i j X hX).coveredCount A i = c.coveredCount A i - c.transfer i j A X := by
  simp only [transfer, coveredCount_eq_sum, ← Finset.filter_mem_eq_inter, Finset.sum_filter]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro v _
  simp only [coverIndicator, c.swapOn_covers i j i X hX v, Equiv.swap_apply_left]
  by_cases hv : v ∈ X <;> by_cases hi : c.Covers i v <;>
    by_cases hj : c.Covers j v <;> simp [hv, hi, hj]

omit [Fintype E] in
theorem swapOn_coveredCount_other (c : G.EdgeColoring q) (i j r : Fin q)
    (X : Finset V) (hX : c.TwoColorClosed i j X) (A : Finset V)
    (hri : r ≠ i) (hrj : r ≠ j) :
    (c.swapOn i j X hX).coveredCount A r = c.coveredCount A r := by
  simp only [coveredCount_eq_sum, coverIndicator,
    c.swapOn_covers i j r X hX, Equiv.swap_apply_of_ne_of_ne hri hrj, ite_self]

omit [Fintype E] in
theorem swapOn_coveredCount_right (c : G.EdgeColoring q) (i j : Fin q)
    (X : Finset V) (hX : c.TwoColorClosed i j X) (A : Finset V) :
    (c.swapOn i j X hX).coveredCount A j = c.coveredCount A j + c.transfer i j A X := by
  simp only [transfer, coveredCount_eq_sum, ← Finset.filter_mem_eq_inter, Finset.sum_filter]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  simp only [coverIndicator, c.swapOn_covers i j j X hX v, Equiv.swap_apply_right]
  by_cases hv : v ∈ X <;> by_cases hi : c.Covers i v <;>
    by_cases hj : c.Covers j v <;> simp [hv, hi, hj]

omit [Fintype E] in
theorem coveredCount_univ (c : G.EdgeColoring q) (i : Fin q) :
    c.coveredCount univ i = (c.coveredVertices i).card := by
  simp [coveredCount]

omit [Fintype E] in
theorem coveredCount_of_covers (c : G.EdgeColoring q) (X : Finset V) (i : Fin q)
    (hX : ∀ v ∈ X, c.Covers i v) : c.coveredCount X i = X.card := by
  unfold coveredCount
  rw [Finset.inter_eq_left.mpr (fun v hv => (c.mem_coveredVertices i v).mpr (hX v hv))]

/-- There are finitely many actual proper colorings on a finite edge type. -/
noncomputable instance coloringFintype : Fintype (G.EdgeColoring q) :=
  Fintype.ofInjective (fun c => c.color) (by
    intro c d h
    cases c
    cases d
    congr)

omit [Fintype E] in
theorem transfer_union (c : G.EdgeColoring q) (i j : Fin q) (A X Y : Finset V)
    (hXY : Disjoint X Y) :
    c.transfer i j A (X ∪ Y) = c.transfer i j A X + c.transfer i j A Y := by
  simp only [transfer_eq_sum]
  exact Finset.sum_union hXY

noncomputable def componentUnion (c : G.EdgeColoring q) (i j : Fin q)
    (S : Finset (c.twoColorGraph i j).ConnectedComponent) : Finset V :=
  S.biUnion (c.componentVertices i j)

omit [Fintype E] in
theorem componentUnion_closed (c : G.EdgeColoring q) (i j : Fin q)
    (S : Finset (c.twoColorGraph i j).ConnectedComponent) :
    c.TwoColorClosed i j (c.componentUnion i j S) := by
  induction S using Finset.induction_on with
  | empty => intro e _; simp [componentUnion]
  | @insert C S _ ih =>
    simpa only [componentUnion, Finset.biUnion_insert] using
      c.closed_union (c.component_closed i j C) ih

omit [Fintype E] in
theorem transfer_componentUnion (c : G.EdgeColoring q) (i j : Fin q)
    (A : Finset V) (S : Finset (c.twoColorGraph i j).ConnectedComponent) :
    c.transfer i j A (c.componentUnion i j S) =
      ∑ C ∈ S, c.transfer i j A (c.componentVertices i j C) := by
  simp only [transfer_eq_sum, componentUnion]
  apply Finset.sum_biUnion
  intro C _ D _ hCD
  exact c.componentVertices_disjoint i j hCD

omit [Fintype E] in
theorem sum_transfer_components (c : G.EdgeColoring q) (i j : Fin q) (A : Finset V) :
    (∑ C : (c.twoColorGraph i j).ConnectedComponent,
      c.transfer i j A (c.componentVertices i j C)) =
        c.coveredCount A i - c.coveredCount A j := by
  have hcomponent (C : (c.twoColorGraph i j).ConnectedComponent) :
      c.componentVertices i j C =
        univ.filter (fun v => (c.twoColorGraph i j).connectedComponentMk v = C) := by
    ext v
    simp [SimpleGraph.ConnectedComponent.mem_supp_iff]
  simp only [transfer_eq_sum, hcomponent]
  rw [Finset.sum_fiberwise (univ : Finset V)
    (c.twoColorGraph i j).connectedComponentMk
    (fun v => if v ∈ A then c.coverIndicator i v - c.coverIndicator j v else 0)]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [Finset.sum_sub_distrib, ← c.coveredCount_eq_sum, ← c.coveredCount_eq_sum]

end Overfull.Multigraph.EdgeColoring
