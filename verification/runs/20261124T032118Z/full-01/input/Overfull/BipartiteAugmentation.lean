import Overfull.BipartiteAugment
import Overfull.TutteBerge.Matching

/-!
# Switching along a bipartite augmenting path

The replacement is an actual matching subgraph. Its edges outside the path
are unchanged, and its covered vertices are exactly the original covered
vertices together with the two previously uncovered ends.
-/

namespace Overfull

open Finset Classical SimpleGraph

namespace MatchingSwitch

variable {V : Type*} {G : SimpleGraph V}

/-- Replace the edges incident with `N.verts` by the edges of `N`. -/
def replacement (M N : G.Subgraph) : G.Subgraph :=
  M.deleteVerts N.verts ⊔ N

theorem deleteVerts_adj_iff (M : G.Subgraph) (S : Set V) (v w : V) :
    (M.deleteVerts S).Adj v w ↔ M.Adj v w ∧ v ∉ S ∧ w ∉ S := by
  rw [Subgraph.deleteVerts_adj]
  constructor
  · rintro ⟨_, hv, _, hw, h⟩
    exact ⟨h, hv, hw⟩
  · rintro ⟨h, hv, hw⟩
    exact ⟨M.edge_vert h, hv, M.edge_vert (M.symm h), hw, h⟩

/-- Deleting a set closed under matching partners leaves a matching. -/
theorem deleteVerts_isMatching (M : G.Subgraph) (hM : M.IsMatching)
    (S : Set V) (hclosed : ∀ v w, v ∈ S → M.Adj v w → w ∈ S) :
    (M.deleteVerts S).IsMatching := by
  intro v hv
  obtain ⟨w, hvw, huniq⟩ := hM hv.1
  refine ⟨w, (deleteVerts_adj_iff M S v w).mpr ⟨hvw, hv.2, ?_⟩, ?_⟩
  · intro hw
    exact hv.2 (hclosed w v hw (M.symm hvw))
  · intro w' hw'
    exact huniq w' ((deleteVerts_adj_iff M S v w').mp hw').1

/-- A matching can be replaced on a partner-closed vertex set by another
matching covering that set. -/
theorem replacement_isMatching (M N : G.Subgraph)
    (hM : M.IsMatching) (hN : N.IsMatching)
    (hclosed : ∀ v w, v ∈ N.verts → M.Adj v w → w ∈ N.verts) :
    (replacement M N).IsMatching := by
  apply (deleteVerts_isMatching M hM N.verts hclosed).sup hN
  rw [Set.disjoint_left]
  intro v hv hw
  exact ((M.deleteVerts N.verts).support_subset_verts hv).2
    (N.support_subset_verts hw)

/-- Replacement retains every previously covered vertex. -/
theorem replacement_verts (M N : G.Subgraph) :
    (replacement M N).verts = M.verts ∪ N.verts := by
  ext v
  simp [replacement]

/-- The exact adjacency relation after replacement. -/
theorem replacement_adj (M N : G.Subgraph) (v w : V) :
    (replacement M N).Adj v w ↔
      (M.Adj v w ∧ v ∉ N.verts ∧ w ∉ N.verts) ∨ N.Adj v w := by
  rw [replacement, Subgraph.sup_adj, deleteVerts_adj_iff]

/-- Edges not incident with the replacement set are unchanged. -/
theorem replacement_adj_off (M N : G.Subgraph) {v w : V}
    (hv : v ∉ N.verts) (hw : w ∉ N.verts) :
    (replacement M N).Adj v w ↔ M.Adj v w := by
  rw [replacement_adj]
  constructor
  · rintro (⟨h, _, _⟩ | h)
    · exact h
    · exact (hv (N.edge_vert h)).elim
  · exact fun h => Or.inl ⟨h, hv, hw⟩

/-- Every new edge belongs to the replacement matching. -/
theorem replacement_new_edge (M N : G.Subgraph) {v w : V}
    (h : (replacement M N).Adj v w) (hold : ¬M.Adj v w) : N.Adj v w := by
  rcases (replacement_adj M N v w).mp h with h | h
  · exact (hold h.1).elim
  · exact h

/-- If the original matching avoids a graph and all replacement edges lie
in it, the resulting intersection is exactly the replacement matching. -/
theorem replacement_intersection (M N : G.Subgraph) (R : SimpleGraph V)
    (hM : ∀ v w, M.Adj v w → ¬R.Adj v w)
    (hN : ∀ v w, N.Adj v w → R.Adj v w) :
    (replacement M N).spanningCoe ⊓ R = N.spanningCoe := by
  ext v w
  constructor
  · rintro ⟨h, hR⟩
    rcases (replacement_adj M N v w).mp h with h | h
    · exact (hM v w h.1 hR).elim
    · exact h
  · intro h
    exact ⟨(replacement_adj M N v w).mpr (Or.inr h), hN v w h⟩

end MatchingSwitch

namespace BipartiteAugmentingPath

variable {A B : Type*} {G : SimpleGraph (A ⊕ B)}
variable {M : (⊤ : SimpleGraph (A ⊕ B)).Subgraph}
variable {W : Finset (A ⊕ B)} {x : A} {y : B}
variable (p : BipartiteAugmentingPath G M W x y)

/-- The actual vertices of the path. -/
def vertexSet : Set (A ⊕ B) :=
  Set.range (fun i => Sum.inl (p.left i)) ∪
    Set.range (fun i => Sum.inr (p.right i))

@[simp] theorem inl_mem_vertexSet (a : A) :
    (.inl a : A ⊕ B) ∈ p.vertexSet ↔ ∃ i, p.left i = a := by
  simp [vertexSet]

@[simp] theorem inr_mem_vertexSet (b : B) :
    (.inr b : A ⊕ B) ∈ p.vertexSet ↔ ∃ i, p.right i = b := by
  simp [vertexSet]

theorem left_mem_vertexSet (i : Fin (p.length + 1)) :
    (.inl (p.left i) : A ⊕ B) ∈ p.vertexSet :=
  (p.inl_mem_vertexSet _).mpr ⟨i, rfl⟩

theorem right_mem_vertexSet (i : Fin (p.length + 1)) :
    (.inr (p.right i) : A ⊕ B) ∈ p.vertexSet :=
  (p.inr_mem_vertexSet _).mpr ⟨i, rfl⟩

theorem start_mem_vertexSet : (.inl x : A ⊕ B) ∈ p.vertexSet :=
  (p.inl_mem_vertexSet _).mpr ⟨0, p.start⟩

theorem finish_mem_vertexSet : (.inr y : A ⊕ B) ∈ p.vertexSet :=
  (p.inr_mem_vertexSet _).mpr ⟨Fin.last p.length, p.finish⟩

/-- All path vertices avoid the forbidden set. -/
theorem vertexSet_avoids {v : A ⊕ B} (hv : v ∈ p.vertexSet) : v ∉ W := by
  rcases hv with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · exact p.left_avoids i
  · exact p.right_avoids i

/-- Each vertex of the path other than its two ends is covered by `M`. -/
theorem vertexSet_subset_covered :
    p.vertexSet ⊆ M.verts ∪ {(.inl x : A ⊕ B), .inr y} := by
  rintro v (⟨i, rfl⟩ | ⟨i, rfl⟩)
  · induction i using Fin.cases with
    | zero => exact Or.inr (by simp [p.start])
    | succ i => exact Or.inl (M.edge_vert (p.matching_edges i))
  · induction i using Fin.lastCases with
    | last => exact Or.inr (by simp [p.finish])
    | cast i => exact Or.inl (M.edge_vert (M.symm (p.matching_edges i)))

/-- The vertices of an augmenting path are closed under the partners in the
original matching, including when that matching is not contained in `G`. -/
theorem vertexSet_partner_closed (hM : M.IsMatching)
    (hxM : (.inl x : A ⊕ B) ∉ M.verts)
    (hyM : (.inr y : A ⊕ B) ∉ M.verts) :
    ∀ v w, v ∈ p.vertexSet → M.Adj v w → w ∈ p.vertexSet := by
  rintro v w (⟨i, rfl⟩ | ⟨i, rfl⟩) hvw
  · induction i using Fin.cases with
    | zero => exact (hxM (p.start ▸ M.edge_vert hvw)).elim
    | succ i =>
      have hw := hM.eq_of_adj_left hvw (p.matching_edges i)
      rw [hw]
      exact p.right_mem_vertexSet i.castSucc
  · induction i using Fin.lastCases with
    | last => exact (hyM (p.finish ▸ M.edge_vert hvw)).elim
    | cast i =>
      have hw := hM.eq_of_adj_left hvw (M.symm (p.matching_edges i))
      rw [hw]
      exact p.left_mem_vertexSet i.succ

/-- Pair the corresponding left and right vertices of the path. -/
def forwardMatching : (⊤ : SimpleGraph (A ⊕ B)).Subgraph where
  verts := p.vertexSet
  Adj v w := ∃ i : Fin (p.length + 1),
    (v = .inl (p.left i) ∧ w = .inr (p.right i)) ∨
    (v = .inr (p.right i) ∧ w = .inl (p.left i))
  adj_sub := by
    rintro v w ⟨i, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ <;> simp
  edge_vert := by
    rintro v w ⟨i, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
    · exact p.left_mem_vertexSet i
    · exact p.right_mem_vertexSet i
  symm := by
    rintro v w ⟨i, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
    · exact ⟨i, Or.inr ⟨rfl, rfl⟩⟩
    · exact ⟨i, Or.inl ⟨rfl, rfl⟩⟩

@[simp] theorem forwardMatching_verts : p.forwardMatching.verts = p.vertexSet := rfl

/-- The forward edges form a matching on all vertices of the path. -/
theorem forwardMatching_isMatching : p.forwardMatching.IsMatching := by
  rintro v (⟨i, rfl⟩ | ⟨i, rfl⟩)
  · refine ⟨.inr (p.right i), ⟨i, Or.inl ⟨rfl, rfl⟩⟩, ?_⟩
    rintro w ⟨j, (⟨hij, hw⟩ | ⟨hij, hw⟩)⟩
    · have hij' := p.left_injective (Sum.inl.inj hij)
      simpa only [← hij'] using hw
    · exact (Sum.noConfusion hij)
  · refine ⟨.inl (p.left i), ⟨i, Or.inr ⟨rfl, rfl⟩⟩, ?_⟩
    rintro w ⟨j, (⟨hij, hw⟩ | ⟨hij, hw⟩)⟩
    · exact (Sum.noConfusion hij)
    · have hij' := p.right_injective (Sum.inr.inj hij)
      simpa only [← hij'] using hw

/-- Every forward edge is an edge of the supplied graph. -/
theorem forwardMatching_adj_graph {v w : A ⊕ B}
    (h : p.forwardMatching.Adj v w) : G.Adj v w := by
  rcases h with ⟨i, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
  · exact p.graph_edges i
  · exact G.symm (p.graph_edges i)

/-- The matching obtained by switching along the path. -/
def augmented : (⊤ : SimpleGraph (A ⊕ B)).Subgraph :=
  MatchingSwitch.replacement M p.forwardMatching

/-- Switching yields an actual matching. -/
theorem augmented_isMatching (hM : M.IsMatching)
    (hxM : (.inl x : A ⊕ B) ∉ M.verts)
    (hyM : (.inr y : A ⊕ B) ∉ M.verts) : p.augmented.IsMatching :=
  MatchingSwitch.replacement_isMatching M p.forwardMatching hM
    p.forwardMatching_isMatching (p.vertexSet_partner_closed hM hxM hyM)

/-- Exactly the two ends become covered. -/
theorem augmented_verts :
    p.augmented.verts = M.verts ∪ {(.inl x : A ⊕ B), .inr y} := by
  rw [augmented, MatchingSwitch.replacement_verts, forwardMatching_verts]
  apply Set.Subset.antisymm
  · exact Set.union_subset (Set.subset_union_left) p.vertexSet_subset_covered
  · apply Set.union_subset Set.subset_union_left
    intro v hv
    rcases Set.mem_insert_iff.mp hv with rfl | hv
    · exact Or.inr p.start_mem_vertexSet
    · have h : v = .inr y := Set.mem_singleton_iff.mp hv
      subst v
      exact Or.inr p.finish_mem_vertexSet

/-- All previously covered vertices remain covered. -/
theorem augmented_covers_original : M.verts ⊆ p.augmented.verts := by
  rw [p.augmented_verts]
  exact Set.subset_union_left

/-- Edges away from the path are unchanged. -/
theorem augmented_adj_off {v w : A ⊕ B}
    (hv : v ∉ p.vertexSet) (hw : w ∉ p.vertexSet) :
    p.augmented.Adj v w ↔ M.Adj v w :=
  MatchingSwitch.replacement_adj_off M p.forwardMatching hv hw

/-- Every new edge is a forward graph edge and has both ends on the path. -/
theorem augmented_new_edge {v w : A ⊕ B}
    (h : p.augmented.Adj v w) (hold : ¬M.Adj v w) :
    G.Adj v w ∧ v ∈ p.vertexSet ∧ w ∈ p.vertexSet := by
  have hf := MatchingSwitch.replacement_new_edge M p.forwardMatching h hold
  exact ⟨p.forwardMatching_adj_graph hf, p.forwardMatching.edge_vert hf,
    p.forwardMatching.edge_vert (p.forwardMatching.symm hf)⟩

/-- Switching preserves the fact that every edge crosses the bipartition. -/
theorem augmented_isCrossingMatching (hM : IsCrossingMatching M)
    (hxM : (.inl x : A ⊕ B) ∉ M.verts)
    (hyM : (.inr y : A ⊕ B) ∉ M.verts) : IsCrossingMatching p.augmented := by
  refine ⟨p.augmented_isMatching hM.1 hxM hyM, ?_, ?_⟩
  · intro a a' h
    rcases (MatchingSwitch.replacement_adj M p.forwardMatching _ _).mp h with
      h | ⟨i, (⟨h, hw⟩ | ⟨h, hw⟩)⟩
    · exact hM.2.1 a a' h.1
    · cases hw
    · cases h
  · intro b b' h
    rcases (MatchingSwitch.replacement_adj M p.forwardMatching _ _).mp h with
      h | ⟨i, (⟨h, hw⟩ | ⟨h, hw⟩)⟩
    · exact hM.2.2 b b' h.1
    · cases h
    · cases hw

/-- The path contains exactly two vertices for each forward edge. -/
theorem vertexSet_ncard : p.vertexSet.ncard = 2 * (p.length + 1) := by
  have hd : Disjoint (Set.range (fun i => (Sum.inl (p.left i) : A ⊕ B)))
      (Set.range (fun i => (Sum.inr (p.right i) : A ⊕ B))) := by
    rw [Set.disjoint_left]
    rintro v ⟨i, rfl⟩ ⟨j, h⟩
    exact Sum.noConfusion h
  have hl : Function.Injective (fun i => (Sum.inl (p.left i) : A ⊕ B)) :=
    Sum.inl_injective.comp p.left_injective
  have hr : Function.Injective (fun i => (Sum.inr (p.right i) : A ⊕ B)) :=
    Sum.inr_injective.comp p.right_injective
  rw [vertexSet, Set.ncard_union_eq hd,
    Set.ncard_range_of_injective hl, Set.ncard_range_of_injective hr]
  simp [two_mul]

variable [Fintype A] [Fintype B]

/-- There is exactly one new forward edge for each pair of path vertices. -/
theorem forwardMatching_edge_card :
    p.forwardMatching.spanningCoe.edgeFinset.card = p.length + 1 := by
  have h := TutteBerge.matching_vertices_card (⊤ : SimpleGraph (A ⊕ B))
    p.forwardMatching p.forwardMatching_isMatching
  rw [p.forwardMatching_verts, p.vertexSet_ncard] at h
  omega

/-- An augmentation increases the actual unordered edge count by one. -/
theorem augmented_edge_card (hM : M.IsMatching)
    (hxM : (.inl x : A ⊕ B) ∉ M.verts)
    (hyM : (.inr y : A ⊕ B) ∉ M.verts) :
    p.augmented.spanningCoe.edgeFinset.card = M.spanningCoe.edgeFinset.card + 1 := by
  have hd : Disjoint M.verts {(.inl x : A ⊕ B), .inr y} := by
    rw [Set.disjoint_left]
    intro v hv hend
    rcases Set.mem_insert_iff.mp hend with rfl | hend
    · exact hxM hv
    · have h : v = .inr y := Set.mem_singleton_iff.mp hend
      subst v
      exact hyM hv
  have hMcard := TutteBerge.matching_vertices_card (⊤ : SimpleGraph (A ⊕ B)) M hM
  have hNcard := TutteBerge.matching_vertices_card (⊤ : SimpleGraph (A ⊕ B))
    p.augmented (p.augmented_isMatching hM hxM hyM)
  rw [p.augmented_verts, Set.ncard_union_eq hd,
    Set.ncard_pair (by simp : (Sum.inl x : A ⊕ B) ≠ Sum.inr y)] at hNcard
  omega

omit [Fintype A] [Fintype B] in
/-- When the original matching avoids `G`, the reserve edges of the
augmented matching are precisely the forward edges. -/
theorem augmented_reserve_graph
    (hdisjoint : ∀ v w, M.Adj v w → ¬G.Adj v w) :
    p.augmented.spanningCoe ⊓ G = p.forwardMatching.spanningCoe := by
  ext v w
  constructor
  · rintro ⟨h, hG⟩
    rcases (MatchingSwitch.replacement_adj M p.forwardMatching v w).mp h with h | h
    · exact (hdisjoint v w h.1 hG).elim
    · exact h
  · intro h
    exact ⟨(MatchingSwitch.replacement_adj M p.forwardMatching v w).mpr (Or.inr h),
      p.forwardMatching_adj_graph h⟩

/-- The exact number of reserve edges introduced by one path. -/
theorem augmented_reserve_edge_card
    (hdisjoint : ∀ v w, M.Adj v w → ¬G.Adj v w) :
    (p.augmented.spanningCoe ⊓ G).edgeFinset.card = p.length + 1 := by
  have heq := SimpleGraph.edgeFinset_inj.mpr (p.augmented_reserve_graph hdisjoint)
  exact (congrArg Finset.card heq).trans p.forwardMatching_edge_card

/-- Each path vertex receives one reserve edge and every other vertex
receives none. -/
theorem augmented_reserve_degree
    (hdisjoint : ∀ v w, M.Adj v w → ¬G.Adj v w) (v : A ⊕ B) :
    (p.augmented.spanningCoe ⊓ G).degree v = if v ∈ p.vertexSet then 1 else 0 := by
  have hn : (p.augmented.spanningCoe ⊓ G).neighborFinset v =
      p.forwardMatching.spanningCoe.neighborFinset v := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset]
    exact iff_of_eq (congrArg (fun H : SimpleGraph (A ⊕ B) => H.Adj v w)
      (p.augmented_reserve_graph hdisjoint))
  change ((p.augmented.spanningCoe ⊓ G).neighborFinset v).card = _
  rw [hn, SimpleGraph.card_neighborFinset_eq_degree]
  by_cases hv : v ∈ p.vertexSet
  · rw [if_pos hv, Subgraph.degree_spanningCoe]
    exact Subgraph.isMatching_iff_forall_degree.mp p.forwardMatching_isMatching v hv
  · rw [if_neg hv]
    apply (p.forwardMatching.spanningCoe.degree_eq_zero_iff_notMem_support v).mpr
    rintro ⟨w, hw⟩
    exact hv (p.forwardMatching.edge_vert hw)

/-- No reserve edge is introduced at a forbidden vertex. -/
theorem augmented_reserve_degree_zero
    (hdisjoint : ∀ v w, M.Adj v w → ¬G.Adj v w) {v : A ⊕ B} (hv : v ∈ W) :
    (p.augmented.spanningCoe ⊓ G).degree v = 0 := by
  rw [p.augmented_reserve_degree hdisjoint]
  exact if_neg (fun h => p.vertexSet_avoids h hv)

end BipartiteAugmentingPath
end Overfull
