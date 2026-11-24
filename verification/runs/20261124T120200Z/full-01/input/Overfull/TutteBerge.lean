import Overfull.TutteBerge.Graph
import Overfull.TutteBerge.Matching

/-!
# The Tutte–Berge formula for finite simple graphs

The maximum deficiency is the maximum of the actual integer differences
`o(G − X) − |X|`. A matching attaining that deficiency is constructed from
Tutte's theorem. Maximum matchings are compared by their actual unordered
edge counts, including the empty graph.
-/

namespace Overfull.TutteBerge

open Finset Classical SimpleGraph

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

/-- Every actual matching leaves at least the deficiency of every vertex set
uncovered. Pairing its uncovered vertices to new universal vertices reduces
this assertion to the necessity direction of Tutte's theorem. -/
theorem oddCount_le_add_uncovered (M : G.Subgraph) (hM : M.IsMatching)
    (X : Set V) :
    oddCount G X ≤ X.ncard + M.vertsᶜ.ncard := by
  obtain ⟨N, hN⟩ := exists_perfectMatching_augmented_uncovered G M hM
  have h := SimpleGraph.not_isTutteViolator_of_isPerfectMatching hN
    (deletionSet {v : V // v ∉ M.verts} X)
  change ¬ (deletionSet {v : V // v ∉ M.verts} X).ncard <
    oddCount (augmented G {v : V // v ∉ M.verts})
      (deletionSet {v : V // v ∉ M.verts} X) at h
  rw [oddCount_deletionSet, deletionSet_ncard] at h
  simpa only [Nat.card_coe_set_eq] using Nat.le_of_not_lt h

theorem deficiency_le_uncovered (M : G.Subgraph) (hM : M.IsMatching) :
    deficiency G ≤ M.vertsᶜ.ncard :=
  deficiency_le_of_bounds G _ (oddCount_le_add_uncovered G M hM)

/-- There exists an actual matching with exactly the maximum deficiency
many uncovered vertices. -/
theorem exists_matching_attaining_deficiency :
    ∃ M : G.Subgraph, M.IsMatching ∧ M.vertsᶜ.ncard = deficiency G := by
  obtain ⟨N, hN⟩ := augmented_has_perfectMatching (D := Fin (deficiency G)) G
    (by simpa using deficiency_order_even G)
    (by simpa using oddCount_le_add_deficiency G)
  obtain ⟨M, hM, hmiss⟩ := exists_matching_of_perfect_augmented G N hN
  have hle : M.vertsᶜ.ncard ≤ deficiency G := by simpa using hmiss
  exact ⟨M, hM, le_antisymm hle (deficiency_le_uncovered G M hM)⟩

/-- Maximum is measured by the number of actual unordered matching edges. -/
noncomputable def IsMaximumMatching (M : G.Subgraph) : Prop :=
  M.IsMatching ∧ ∀ N : G.Subgraph, N.IsMatching →
    N.spanningCoe.edgeFinset.card ≤ M.spanningCoe.edgeFinset.card

/-- A matching is maximum exactly when its number of uncovered vertices
is the maximum Tutte deficiency. -/
theorem isMaximumMatching_iff_deficiency (M : G.Subgraph) (hM : M.IsMatching) :
    IsMaximumMatching G M ↔ M.vertsᶜ.ncard = deficiency G := by
  constructor
  · intro hmax
    obtain ⟨N, hN, hNmiss⟩ := exists_matching_attaining_deficiency G
    have hedge := hmax.2 N hN
    have hm := matching_uncovered_add_twice_edges G M hM
    have hn := matching_uncovered_add_twice_edges G N hN
    have hbound := deficiency_le_uncovered G M hM
    omega
  · intro hmiss
    refine ⟨hM, ?_⟩
    intro N hN
    have hm := matching_uncovered_add_twice_edges G M hM
    have hn := matching_uncovered_add_twice_edges G N hN
    have hbound := deficiency_le_uncovered G N hN
    omega

theorem exists_maximum_matching :
    ∃ M : G.Subgraph, IsMaximumMatching G M ∧ M.vertsᶜ.ncard = deficiency G := by
  obtain ⟨M, hM, hmiss⟩ := exists_matching_attaining_deficiency G
  exact ⟨M, (isMaximumMatching_iff_deficiency G M hM).mpr hmiss, hmiss⟩

/-- **Tutte–Berge formula (manuscript Theorem 2.5).** A maximum matching
misses exactly the maximum of `o(G − X) − |X|`. The accompanying integer
maximum theorem states this without truncated subtraction. -/
theorem tutte_berge (M : G.Subgraph) (hM : IsMaximumMatching G M) :
    M.vertsᶜ.ncard = deficiency G :=
  (isMaximumMatching_iff_deficiency G M hM.1).mp hM

/-- The integer differences in the displayed Tutte–Berge formula are all
bounded by the number of unmatched vertices of a maximum matching, and
one actual vertex set attains equality. -/
theorem tutte_berge_integer_maximum (M : G.Subgraph) (hM : IsMaximumMatching G M) :
    (∀ X : Set V, (oddCount G X : ℤ) - X.ncard ≤ (M.vertsᶜ.ncard : ℤ)) ∧
      ∃ X : Set V, (oddCount G X : ℤ) - X.ncard = (M.vertsᶜ.ncard : ℤ) := by
  rw [tutte_berge G M hM]
  exact ⟨deficiency_integer_bound G, deficiency_integer_attained G⟩

end Overfull.TutteBerge

