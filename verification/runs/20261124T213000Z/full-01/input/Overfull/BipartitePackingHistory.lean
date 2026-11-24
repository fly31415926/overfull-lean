import Overfull.BipartitePackingAccounting
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Appending one matching to a finite history

The history of `s` completed rounds is indexed by `Fin s`. Appending the
next matching preserves all old entries and gives the exact graph and
load identities used by the online induction.
-/

namespace Overfull.BipartitePackingHistory

open Finset Classical SimpleGraph
open scoped BigOperators
open BipartitePackingAccounting

variable {V : Type*} [Fintype V] {s : ℕ}
variable (G R : SimpleGraph V) (M : Fin s → G.Subgraph) (N : G.Subgraph)

omit [Fintype V] in
@[simp] theorem edgeUnion_zero (M₀ : Fin 0 → G.Subgraph) :
    edgeUnion (fun i => (M₀ i).spanningCoe) univ = ⊥ := by
  have h : (univ : Finset (Fin 0)) = ∅ := by simp
  rw [h, edgeUnion_empty]

omit [Fintype V] in
@[simp] theorem missingCount_zero (M₀ : Fin 0 → G.Subgraph) (v : V) :
    missingCount G M₀ univ v = 0 := by
  simp [missingCount]

@[simp] theorem reserveLoad_zero (M₀ : Fin 0 → G.Subgraph) (v : V) :
    reserveLoad G R M₀ univ v = 0 := by
  have h : (univ : Finset (Fin 0)) = ∅ := by simp
  rw [h, reserveLoad_empty]

omit [Fintype V] in
theorem edgeUnion_snoc :
    edgeUnion (fun i => (Fin.snoc (α := fun _ => G.Subgraph) M N i).spanningCoe) univ =
      edgeUnion (fun i => (M i).spanningCoe) univ ⊔ N.spanningCoe := by
  ext v w
  simp only [edgeUnion_adj, Finset.mem_univ, true_and, SimpleGraph.sup_adj]
  constructor
  · rintro ⟨i, hi⟩
    induction i using Fin.lastCases with
    | last => exact Or.inr (by simpa using hi)
    | cast i => exact Or.inl ⟨i, by simpa using hi⟩
  · rintro (⟨i, hi⟩ | hi)
    · exact ⟨i.castSucc, by simpa using hi⟩
    · exact ⟨Fin.last s, by simpa using hi⟩

omit [Fintype V] in
theorem matching_snoc (hM : ∀ i, (M i).IsMatching) (hN : N.IsMatching) :
    ∀ i, (Fin.snoc (α := fun _ => G.Subgraph) M N i).IsMatching := by
  intro i
  induction i using Fin.lastCases with
  | last => simpa using hN
  | cast i => simpa using hM i

omit [Fintype V] in
theorem pairwise_disjoint_snoc
    (hM : Pairwise (fun i j => Disjoint (M i).spanningCoe (M j).spanningCoe))
    (hN : Disjoint N.spanningCoe (edgeUnion (fun i => (M i).spanningCoe) univ)) :
    Pairwise (fun i j => Disjoint (Fin.snoc (α := fun _ => G.Subgraph) M N i).spanningCoe (Fin.snoc (α := fun _ => G.Subgraph) M N j).spanningCoe) := by
  have hsub : ∀ i, (M i).spanningCoe ≤ edgeUnion (fun i => (M i).spanningCoe) univ := by
    intro i v w hvw
    exact ⟨i, Finset.mem_univ _, hvw⟩
  intro i j hij
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => exact (hij rfl).elim
    | cast j => simpa using hN.mono_right (hsub j)
  | cast i =>
    induction j using Fin.lastCases with
    | last => simpa using (hN.mono_right (hsub i)).symm
    | cast j =>
      have hij' : i ≠ j := by intro h; subst j; exact hij rfl
      simpa using hM hij'

omit [Fintype V] in
theorem missingCount_snoc (v : V) :
    missingCount G (Fin.snoc (α := fun _ => G.Subgraph) M N) univ v =
      missingCount G M univ v + if v ∉ N.verts then 1 else 0 := by
  unfold missingCount
  calc
    _ = ∑ i : Fin (s + 1), if v ∉ (Fin.snoc (α := fun _ => G.Subgraph) M N i).verts then 1 else 0 := by
      simp only [Finset.sum_boole, Nat.cast_id]
    _ = _ := by
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, Finset.sum_boole, Nat.cast_id]

/-- Appending a matching gives the actual union graph used by the one-round result. -/
theorem reserveLoad_snoc_graph (v : V) :
    reserveLoad G R (Fin.snoc (α := fun _ => G.Subgraph) M N) univ v =
      (R ⊓ (edgeUnion (fun i => (M i).spanningCoe) univ ⊔ N.spanningCoe)).degree v := by
  unfold reserveLoad
  apply congrArg Finset.card
  ext w
  simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.inf_adj, edgeUnion_snoc]

/-- Pairwise edge-disjointness makes the old and new reserve contributions add. -/
theorem reserveLoad_snoc
    (hM : Pairwise (fun i j => Disjoint (M i).spanningCoe (M j).spanningCoe))
    (hN : Disjoint N.spanningCoe (edgeUnion (fun i => (M i).spanningCoe) univ)) (v : V) :
    reserveLoad G R (Fin.snoc (α := fun _ => G.Subgraph) M N) univ v =
      reserveLoad G R M univ v + (R ⊓ N.spanningCoe).degree v := by
  have hnew := pairwise_disjoint_snoc G M N hM hN
  rw [reserveLoad_eq_sum G R (Fin.snoc (α := fun _ => G.Subgraph) M N) univ (fun i _ j _ hij => hnew hij),
    Fin.sum_univ_castSucc, reserveLoad_eq_sum G R M univ (fun i _ j _ hij => hM hij)]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    apply congrArg Finset.card
    ext w
    simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.inf_adj,
      Subgraph.spanningCoe_adj, Fin.snoc_castSucc]
  · apply congrArg Finset.card
    ext w
    simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.inf_adj,
      Subgraph.spanningCoe_adj, Fin.snoc_last]

theorem total_reserveLoad_snoc
    (hM : Pairwise (fun i j => Disjoint (M i).spanningCoe (M j).spanningCoe))
    (hN : Disjoint N.spanningCoe (edgeUnion (fun i => (M i).spanningCoe) univ)) :
    (∑ v, reserveLoad G R (Fin.snoc (α := fun _ => G.Subgraph) M N) univ v) =
      (∑ v, reserveLoad G R M univ v) + ∑ v, (R ⊓ N.spanningCoe).degree v := by
  simp_rw [reserveLoad_snoc G R M N hM hN]
  exact Finset.sum_add_distrib

end Overfull.BipartitePackingHistory
