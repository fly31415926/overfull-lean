import Overfull.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
Degree counting on a vertex set, including the contribution of a clique
which meets both sides of the cut. All counts refer to actual graph edges.
-/

namespace Overfull

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

private def insideGraph (X : Finset V) : SimpleGraph V where
  Adj v w := G.Adj v w ∧ v ∈ X ∧ w ∈ X
  symm := by
    intro v w h
    exact ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless := by
    intro v h
    exact G.loopless v h.1

theorem internal_degree_sum [DecidableRel G.Adj] (X : Finset V) :
    2 * (internalEdges G X).card =
      ∑ v ∈ X, ((G.neighborFinset v) ∩ X).card := by
  classical
  let H := insideGraph G X
  letI : DecidableRel H.Adj := Classical.decRel _
  have hmap : (internalEdges G X).image Subtype.val = H.edgeFinset := by
    ext e
    obtain ⟨v, w⟩ := e
    change s(v, w) ∈ (internalEdges G X).image Subtype.val ↔ s(v, w) ∈ H.edgeFinset
    simp [internalEdges, H, insideGraph, Sym2.toFinset_mk_eq, Finset.insert_subset_iff, Finset.singleton_subset_iff, and_comm]
  have hcard : (internalEdges G X).card = H.edgeFinset.card := by
    rw [← hmap, Finset.card_image_of_injective _ Subtype.val_injective]
  have hN (v : V) : H.neighborFinset v =
      if v ∈ X then G.neighborFinset v ∩ X else ∅ := by
    ext w
    by_cases hv : v ∈ X <;> simp [H, insideGraph, hv]
  have hsum : ∑ v : V, H.degree v = ∑ v ∈ X, H.degree v := by
    symm
    apply Finset.sum_subset (Finset.subset_univ X)
    intro v _ hv
    simp [SimpleGraph.degree, hN, hv]
  rw [hcard, ← H.sum_degrees_eq_twice_card_edges, hsum]
  apply Finset.sum_congr rfl
  intro v hv
  simp [SimpleGraph.degree, hN, hv]

theorem internal_edges_add_boundary [DecidableRel G.Adj] (X : Finset V) :
    2 * (internalEdges G X).card +
      (∑ v ∈ X, (G.neighborFinset v \ X).card) = ∑ v ∈ X, G.degree v := by
  classical
  rw [internal_degree_sum G, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  exact Finset.card_inter_add_card_sdiff (G.neighborFinset v) X

/-- Counting neighbors inside a clique gives its exact internal-edge count. -/
theorem clique_internal_edge_count [DecidableRel G.Adj] (X : Finset V)
    (hclique : ∀ v ∈ X, ∀ w ∈ X, v ≠ w → G.Adj v w) :
    2 * (internalEdges G X).card = X.card * (X.card - 1) := by
  classical
  rw [internal_degree_sum G X]
  have hN (v : V) (hv : v ∈ X) : G.neighborFinset v ∩ X = X.erase v := by
    ext w
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
      Finset.mem_erase]
    constructor
    · rintro ⟨hadj, hw⟩
      exact ⟨hadj.ne.symm, hw⟩
    · rintro ⟨hne, hw⟩
      exact ⟨hclique v hv w hw hne.symm, hw⟩
  calc
    (∑ v ∈ X, (G.neighborFinset v ∩ X).card) =
        ∑ _v ∈ X, (X.card - 1) := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [hN v hv, Finset.card_erase_of_mem hv]
    _ = _ := by simp

/-- An odd clique on `k` vertices attains the internal-edge bound for `k`
colors. The statement concerns the actual internal-edge finset. -/
theorem saturated_odd_clique [DecidableRel G.Adj] (X : Finset V) (k : ℕ)
    (hX : X.card = k) (hodd : k % 2 = 1)
    (hclique : ∀ v ∈ X, ∀ w ∈ X, v ≠ w → G.Adj v w) :
    (internalEdges G X).card = k * (X.card / 2) := by
  have h := clique_internal_edge_count G X hclique
  have hsub : X.card - 1 = 2 * (X.card / 2) := by omega
  rw [hsub, hX] at h
  rw [hX]
  nlinarith

theorem internal_edges_le_degree_bound [DecidableRel G.Adj] (X : Finset V)
    (Δ : ℕ) (hdegree : ∀ v, G.degree v ≤ Δ) :
    2 * (internalEdges G X).card ≤ Δ * X.card := by
  classical
  have hsum : (∑ v ∈ X, G.degree v) ≤ Δ * X.card := by
    calc
      _ ≤ ∑ _v ∈ X, Δ := Finset.sum_le_sum (fun v _ => hdegree v)
      _ = _ := by simp [Nat.mul_comm]
  have h := internal_edges_add_boundary G X
  omega

theorem not_overfull_of_even_card [DecidableRel G.Adj] (X : Finset V)
    (Δ : ℕ) (hdegree : ∀ v, G.degree v ≤ Δ) (heven : X.card % 2 = 0) :
    ¬ IsOverfull G Δ X := by
  have h := internal_edges_le_degree_bound G X Δ hdegree
  have hc : X.card = 2 * (X.card / 2) := by omega
  unfold IsOverfull
  rw [hc] at h
  nlinarith

/-- The deficiency identity counts internal and crossing edges of the actual
graph. Each crossing edge occurs at its unique endpoint in `X`. -/
theorem deficiency_identity [DecidableRel G.Adj] (X : Finset V)
    (Δ : ℕ) (hdegree : ∀ v, G.degree v ≤ Δ) :
    2 * (internalEdges G X).card +
      (∑ v ∈ X, (Δ - G.degree v)) +
      (∑ v ∈ X, (G.neighborFinset v \ X).card) = Δ * X.card := by
  classical
  have hsum : (∑ v ∈ X, (Δ - G.degree v)) +
      (∑ v ∈ X, G.degree v) = Δ * X.card := by
    rw [← Finset.sum_add_distrib]
    simp [Nat.sub_add_cancel (hdegree _), Nat.mul_comm]
  have h := internal_edges_add_boundary G X
  omega

/-- For an odd set, overfullness is equivalent to deficiency plus the cut
being smaller than the number of colors. -/
theorem overfull_iff_odd_deficiency [DecidableRel G.Adj] (X : Finset V)
    (Δ : ℕ) (hdegree : ∀ v, G.degree v ≤ Δ) (hodd : X.card % 2 = 1) :
    IsOverfull G Δ X ↔
      (∑ v ∈ X, (Δ - G.degree v)) +
        (∑ v ∈ X, (G.neighborFinset v \ X).card) < Δ := by
  have h := deficiency_identity G X Δ hdegree
  have hc : X.card = 2 * (X.card / 2) + 1 := by omega
  rw [hc, Nat.mul_add, Nat.mul_one] at h
  unfold IsOverfull
  constructor <;> intro hlt <;> nlinarith

/-- Even sets satisfy the edge bound automatically, so checking the odd-set
deficiency inequalities is equivalent to excluding every overfull set. -/
theorem no_overfull_iff_odd_deficiency [DecidableRel G.Adj]
    (Δ : ℕ) (hdegree : ∀ v, G.degree v ≤ Δ) :
    (∀ X : Finset V, ¬ IsOverfull G Δ X) ↔
      ∀ X : Finset V, X.card % 2 = 1 →
        Δ ≤ (∑ v ∈ X, (Δ - G.degree v)) +
          (∑ v ∈ X, (G.neighborFinset v \ X).card) := by
  constructor
  · intro h X hodd
    exact Nat.not_lt.mp (fun hlt =>
      h X ((overfull_iff_odd_deficiency G X Δ hdegree hodd).mpr hlt))
  · intro h X
    by_cases hodd : X.card % 2 = 1
    · rw [overfull_iff_odd_deficiency G X Δ hdegree hodd]
      exact Nat.not_lt.mpr (h X hodd)
    · exact not_overfull_of_even_card G X Δ hdegree (by omega)

theorem clique_cut_bound [DecidableRel G.Adj] (X U : Finset V)
    (Δ : ℕ) (hdegree : ∀ v, G.degree v ≤ Δ) (hU : U.card = Δ)
    (hclique : ∀ v ∈ U, ∀ w ∈ U, v ≠ w → G.Adj v w) :
    2 * (internalEdges G X).card +
      (X ∩ U).card * (Δ - (X ∩ U).card) ≤ Δ * X.card := by
  classical
  have hcard : (U \ X).card = Δ - (X ∩ U).card := by
    rw [Finset.card_sdiff, hU, Finset.inter_comm]
  have hneighbor (v : V) (hv : v ∈ X ∩ U) :
      (U \ X).card ≤ (G.neighborFinset v \ X).card := by
    apply Finset.card_le_card
    intro w hw
    rcases Finset.mem_inter.mp hv with ⟨hvX, hvU⟩
    rcases Finset.mem_sdiff.mp hw with ⟨hwU, hwX⟩
    refine Finset.mem_sdiff.mpr ⟨?_, hwX⟩
    rw [SimpleGraph.mem_neighborFinset]
    apply hclique v hvU w hwU
    intro h
    exact hwX (h ▸ hvX)
  have hboundary : (X ∩ U).card * (Δ - (X ∩ U).card) ≤
      ∑ v ∈ X, (G.neighborFinset v \ X).card := by
    calc
      _ = ∑ _v ∈ X ∩ U, (U \ X).card := by simp [hcard]
      _ ≤ ∑ v ∈ X ∩ U, (G.neighborFinset v \ X).card :=
        Finset.sum_le_sum hneighbor
      _ ≤ ∑ v ∈ X, (G.neighborFinset v \ X).card :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_left (by
          intro v _ _
          exact Nat.zero_le _)
  have hsum : (∑ v ∈ X, G.degree v) ≤ Δ * X.card := by
    calc
      _ ≤ ∑ _v ∈ X, Δ := Finset.sum_le_sum (fun v _ => hdegree v)
      _ = _ := by simp [Nat.mul_comm]
  have h := internal_edges_add_boundary G X
  omega

end Overfull
