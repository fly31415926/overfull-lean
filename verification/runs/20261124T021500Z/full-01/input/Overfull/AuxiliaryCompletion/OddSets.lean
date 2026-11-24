import Overfull.AuxiliaryCompletion.Graph
import Overfull.AuxiliaryCompletion.BalancedIncidence

/-!
# Odd sets in the auxiliary completion

The restriction on neighbors of vertices of deficiency one is used for
shores containing one new vertex. Shores containing no new vertex retain
the original odd-set inequality. All remaining shores are controlled by
actual cuts of the auxiliary graph.
-/

namespace Overfull.AuxiliaryCompletion

open Finset Classical
open scoped BigOperators

variable {V U E : Type*} [Fintype V] [Fintype U] [Fintype E]

omit [Fintype V] in
theorem internal_empty_empty (G : Multigraph V E) :
    G.internalEdges ∅ = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  have h := (G.mem_internalEdges ∅ e).mp he
  simp only [Finset.notMem_empty, false_and] at h

omit [Fintype V] in
theorem internal_singleton_empty (G : Multigraph V E) (v : V) :
    G.internalEdges {v} = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨h₁, h₂⟩ := (G.mem_internalEdges {v} e).mp he
  simp only [Finset.mem_singleton] at h₁ h₂
  exact G.endpoints_distinct e (h₁.trans h₂.symm)

omit [Fintype V] in
theorem deficiency_sum_bound (G : Multigraph V E) (k : ℕ)
    (hdegree : ∀ v, G.degree v ≤ k) (S : Finset V) :
    2 * (G.internalEdges S).card + (∑ v ∈ S, (k - G.degree v)) ≤ k * S.card := by
  have hsum : (∑ v ∈ S, G.degree v) + (∑ v ∈ S, (k - G.degree v)) =
      k * S.card := by
    rw [← Finset.sum_add_distrib]
    simp only [Nat.add_sub_of_le (hdegree _)]
    simp [Nat.mul_comm]
  have hcount := G.degree_sum_on S
  omega

omit [Fintype V] [Fintype U] in
theorem crossingCount_singleton (N : V → Finset U) (S : Finset V) (u : U) :
    crossingCount N S {u} = (S.filter (fun v => u ∈ N v)).card := by
  classical
  unfold crossingCount
  conv_rhs => rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hu : u ∈ N v <;> simp [hu]

omit [Fintype V] in
theorem regular_degree_sum (G : Multigraph V E) (k : ℕ)
    (hregular : ∀ v, G.degree v = k) (S : Finset V) :
    k * S.card = 2 * (G.internalEdges S).card + G.cutSize S := by
  have h := G.degree_sum_on S
  simpa [hregular, Nat.mul_comm] using h

theorem cut_ge_zero_aux (G : Multigraph V E) (N : V → Finset U)
    (H : SimpleGraph U) (k : ℕ)
    (hregular : ∀ v, (graph G N H).degree v = k)
    (hno : ∀ S : Finset V, ¬ G.IsOverfull k S)
    (S : Finset V) (hodd : S.card % 2 = 1) :
    k ≤ (graph G N H).cutSize (S.disjSum ∅) := by
  classical
  have hinside : ((graph G N H).internalEdges (S.disjSum ∅)).card =
      (G.internalEdges S).card := by
    rw [internal_card_disjSum]
    rw [internal_empty_empty]
    simp [crossingCount]
  have hcount := regular_degree_sum (graph G N H) k hregular (S.disjSum ∅)
  simp only [Finset.card_disjSum, Finset.card_empty, Nat.add_zero, hinside] at hcount
  have hbound := Nat.not_lt.mp (hno S)
  change (G.internalEdges S).card ≤ k * (S.card / 2) at hbound
  have hcard : S.card = 2 * (S.card / 2) + 1 := by omega
  rw [hcard] at hcount
  nlinarith

theorem cut_ge_one_aux (G : Multigraph V E) (N : V → Finset U)
    (H : SimpleGraph U) (k : ℕ)
    (hdegree : ∀ v, G.degree v ≤ k)
    (hN : ValidIncidences (fun v => k - G.degree v) N)
    (hregular : ∀ v, (graph G N H).degree v = k)
    (S : Finset V) (u : U) (heven : S.card % 2 = 0) :
    k ≤ (graph G N H).cutSize (S.disjSum {u}) := by
  classical
  have hinside := internal_card_disjSum G N H S {u}
  rw [internal_singleton_empty, Finset.card_empty, Nat.add_zero,
    crossingCount_singleton] at hinside
  have hdef := deficiency_sum_bound G k hdegree S
  have hinc := twice_incidence_card_le_deficiency_sum_add_one
    (fun v => k - G.degree v) N hN S u
  have hcard : S.card = 2 * (S.card / 2) := by omega
  have hbound : 2 * ((graph G N H).internalEdges (S.disjSum {u})).card ≤
      k * S.card := by
    rw [hcard] at hdef ⊢
    have hround :
        2 * ((graph G N H).internalEdges (S.disjSum {u})).card ≤
          2 * (k * (S.card / 2)) + 1 := by nlinarith
    have hround' : ((graph G N H).internalEdges (S.disjSum {u})).card ≤
        k * (S.card / 2) := by omega
    nlinarith
  have hcount := regular_degree_sum (graph G N H) k hregular (S.disjSum {u})
  simp only [Finset.card_disjSum, Finset.card_singleton] at hcount
  nlinarith

theorem cut_ge_small_aux (G : Multigraph V E) (N : V → Finset U)
    (H : SimpleGraph U) (k : ℕ)
    (hdegree : ∀ v, G.degree v ≤ k)
    (hN : ValidIncidences (fun v => k - G.degree v) N)
    (hregular : ∀ v, (graph G N H).degree v = k)
    (hno : ∀ S : Finset V, ¬ G.IsOverfull k S)
    (S : Finset V) (T : Finset U) (hT : T.card ≤ 1)
    (hodd : (S.disjSum T).card % 2 = 1) :
    k ≤ (graph G N H).cutSize (S.disjSum T) := by
  classical
  by_cases hT0 : T.card = 0
  · have hTempty : T = ∅ := Finset.card_eq_zero.mp hT0
    subst T
    exact cut_ge_zero_aux G N H k hregular hno S (by simpa using hodd)
  · have hT1 : T.card = 1 := by omega
    obtain ⟨u, rfl⟩ := Finset.card_eq_one.mp hT1
    apply cut_ge_one_aux G N H k hdegree hN hregular S u
    simp only [Finset.card_disjSum, Finset.card_singleton] at hodd
    omega

omit [Fintype V] in
theorem not_overfull_of_regular_cuts (G : Multigraph V E) (k : ℕ)
    (hregular : ∀ v, G.degree v = k)
    (hcuts : ∀ S : Finset V, S.card % 2 = 1 → k ≤ G.cutSize S) :
    ∀ S : Finset V, ¬ G.IsOverfull k S := by
  intro S
  apply Nat.not_lt.mpr
  have hcount := regular_degree_sum G k hregular S
  by_cases heven : S.card % 2 = 0
  · have hcard : S.card = 2 * (S.card / 2) := by omega
    rw [hcard] at hcount
    change (G.internalEdges S).card ≤ k * (S.card / 2)
    nlinarith
  · have hodd : S.card % 2 = 1 := by omega
    have hcut := hcuts S hodd
    have hcard : S.card = 2 * (S.card / 2) + 1 := by omega
    rw [hcard] at hcount
    change (G.internalEdges S).card ≤ k * (S.card / 2)
    nlinarith

/-- The actual auxiliary completion retains every odd-set inequality. -/
theorem no_overfull (G : Multigraph V E) (N : V → Finset U)
    (H : SimpleGraph U) (k : ℕ)
    (hdegree : ∀ v, G.degree v ≤ k)
    (hN : ValidIncidences (fun v => k - G.degree v) N)
    (hregular : ∀ v, (graph G N H).degree v = k)
    (heven : (Fintype.card V + Fintype.card U) % 2 = 0)
    (hno : ∀ S : Finset V, ¬ G.IsOverfull k S)
    (haux : ∀ T : Finset U, 2 ≤ T.card → 2 ≤ Tᶜ.card →
      k < (Multigraph.ofSimpleGraph H).cutSize T) :
    ∀ X : Finset (V ⊕ U), ¬ (graph G N H).IsOverfull k X := by
  classical
  apply not_overfull_of_regular_cuts (graph G N H) k hregular
  intro X hodd
  let S := X.toLeft
  let T := X.toRight
  have hX : S.disjSum T = X := Finset.toLeft_disjSum_toRight
  by_cases hT : T.card ≤ 1
  · rw [← hX]
    exact cut_ge_small_aux G N H k hdegree hN hregular hno S T hT (hX ▸ hodd)
  · by_cases hTc : Tᶜ.card ≤ 1
    · have hcompl : Sᶜ.disjSum Tᶜ = Xᶜ := by
        rw [← hX]
        ext v
        cases v <;> simp
      have hoddcomp : Xᶜ.card % 2 = 1 := by
        have hcard := Finset.card_add_card_compl X
        simp only [Fintype.card_sum] at hcard
        omega
      have hcut := cut_ge_small_aux G N H k hdegree hN hregular hno
        Sᶜ Tᶜ hTc (hcompl ▸ hoddcomp)
      rw [hcompl, Multigraph.cutSize_compl] at hcut
      exact hcut
    · have hcore := haux T (by omega) (by omega)
      have hhost := auxiliary_cut_le G N H S T
      rw [hX] at hhost
      omega

end Overfull.AuxiliaryCompletion
