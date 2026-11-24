import Overfull.BipartiteAugmentation

/-!
# Simultaneous augmentation along disjoint bipartite paths

All paths are alternating with respect to the same original matching. Their
forward edges form a matching because their vertex sets are disjoint. The
single replacement below therefore carries out all augmentations at once.
-/

namespace Overfull.BipartitePathFamily

open Finset Classical SimpleGraph
open scoped BigOperators

variable {I A B : Type*} {G : SimpleGraph (A ⊕ B)}
variable {M : (⊤ : SimpleGraph (A ⊕ B)).Subgraph}
variable {W : I → Finset (A ⊕ B)} {x : I → A} {y : I → B}
variable (p : ∀ i, BipartiteAugmentingPath G M (W i) (x i) (y i))

/-- The forward edges of all paths, retained as actual graph edges. -/
noncomputable def forwardMatching : (⊤ : SimpleGraph (A ⊕ B)).Subgraph :=
  ⨆ i, (p i).forwardMatching

@[simp] theorem forwardMatching_verts :
    (forwardMatching p).verts = ⋃ i, (p i).vertexSet := by
  simp [forwardMatching, Subgraph.verts_iSup]

/-- Disjoint path vertex sets make the union of forward edges a matching. -/
theorem forwardMatching_isMatching
    (hdisjoint : Pairwise fun i j => Disjoint (p i).vertexSet (p j).vertexSet) :
    (forwardMatching p).IsMatching := by
  apply Subgraph.IsMatching.iSup (fun i => (p i).forwardMatching_isMatching)
  intro i j hij
  exact (hdisjoint hij).mono (p i).forwardMatching.support_subset_verts
    (p j).forwardMatching.support_subset_verts

/-- Every edge added by the family belongs to the supplied graph. -/
theorem forwardMatching_adj_graph {v w : A ⊕ B}
    (h : (forwardMatching p).Adj v w) : G.Adj v w := by
  obtain ⟨i, hi⟩ := Subgraph.iSup_adj.mp h
  exact (p i).forwardMatching_adj_graph hi

/-- The combined path vertex set is closed under original matching partners. -/
theorem forwardMatching_partner_closed (hM : M.IsMatching)
    (hxM : ∀ i, (.inl (x i) : A ⊕ B) ∉ M.verts)
    (hyM : ∀ i, (.inr (y i) : A ⊕ B) ∉ M.verts) :
    ∀ v w, v ∈ (forwardMatching p).verts → M.Adj v w →
      w ∈ (forwardMatching p).verts := by
  intro v w hv hvw
  rw [forwardMatching_verts] at hv ⊢
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hv
  exact Set.mem_iUnion.mpr ⟨i,
    (p i).vertexSet_partner_closed hM (hxM i) (hyM i) v w hi hvw⟩

/-- Simultaneously switch along all paths. -/
noncomputable def augmented : (⊤ : SimpleGraph (A ⊕ B)).Subgraph :=
  MatchingSwitch.replacement M (forwardMatching p)

/-- The simultaneous switch is an actual matching. -/
theorem augmented_isMatching (hM : M.IsMatching)
    (hxM : ∀ i, (.inl (x i) : A ⊕ B) ∉ M.verts)
    (hyM : ∀ i, (.inr (y i) : A ⊕ B) ∉ M.verts)
    (hdisjoint : Pairwise fun i j => Disjoint (p i).vertexSet (p j).vertexSet) :
    (augmented p).IsMatching :=
  MatchingSwitch.replacement_isMatching M (forwardMatching p) hM
    (forwardMatching_isMatching p hdisjoint)
    (forwardMatching_partner_closed p hM hxM hyM)

/-- Simultaneous augmentation retains a matching whose edges cross the
given bipartition. -/
theorem augmented_isCrossingMatching (hM : IsCrossingMatching M)
    (hxM : ∀ i, (.inl (x i) : A ⊕ B) ∉ M.verts)
    (hyM : ∀ i, (.inr (y i) : A ⊕ B) ∉ M.verts)
    (hdisjoint : Pairwise fun i j => Disjoint (p i).vertexSet (p j).vertexSet) :
    IsCrossingMatching (augmented p) := by
  refine ⟨augmented_isMatching p hM.1 hxM hyM hdisjoint, ?_, ?_⟩
  · intro a a' h
    rcases (MatchingSwitch.replacement_adj M (forwardMatching p) _ _).mp h with h | h
    · exact hM.2.1 a a' h.1
    · obtain ⟨i, hi⟩ := Subgraph.iSup_adj.mp h
      rcases hi with ⟨j, (⟨h, hw⟩ | ⟨h, hw⟩)⟩
      · cases hw
      · cases h
  · intro b b' h
    rcases (MatchingSwitch.replacement_adj M (forwardMatching p) _ _).mp h with h | h
    · exact hM.2.2 b b' h.1
    · obtain ⟨i, hi⟩ := Subgraph.iSup_adj.mp h
      rcases hi with ⟨j, (⟨h, hw⟩ | ⟨h, hw⟩)⟩
      · cases h
      · cases hw

/-- Exactly the ends of the paths are added to the covered set. -/
theorem augmented_verts :
    (augmented p).verts = M.verts ∪ ⋃ i, {(.inl (x i) : A ⊕ B), .inr (y i)} := by
  rw [augmented, MatchingSwitch.replacement_verts, forwardMatching_verts]
  apply Set.Subset.antisymm
  · rintro v (hv | hv)
    · exact Or.inl hv
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hv
      rcases (p i).vertexSet_subset_covered hi with hM | hend
      · exact Or.inl hM
      · exact Or.inr (Set.mem_iUnion.mpr ⟨i, hend⟩)
  · rintro v (hv | hv)
    · exact Or.inl hv
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hv
      apply Or.inr
      apply Set.mem_iUnion.mpr
      refine ⟨i, ?_⟩
      rcases Set.mem_insert_iff.mp hi with rfl | hi
      · exact (p i).start_mem_vertexSet
      · have h : v = .inr (y i) := Set.mem_singleton_iff.mp hi
        subst v
        exact (p i).finish_mem_vertexSet

/-- Every previously covered vertex stays covered. -/
theorem augmented_covers_original : M.verts ⊆ (augmented p).verts := by
  rw [augmented_verts]
  exact Set.subset_union_left

/-- Edges away from all paths stay unchanged. -/
theorem augmented_adj_off {v w : A ⊕ B}
    (hv : ∀ i, v ∉ (p i).vertexSet) (hw : ∀ i, w ∉ (p i).vertexSet) :
    (augmented p).Adj v w ↔ M.Adj v w := by
  apply MatchingSwitch.replacement_adj_off
  · simpa only [forwardMatching_verts, Set.mem_iUnion, not_exists] using hv
  · simpa only [forwardMatching_verts, Set.mem_iUnion, not_exists] using hw

/-- Every augmented edge is an original matching edge or an edge of `G`. -/
theorem augmented_adj_subset {v w : A ⊕ B} (h : (augmented p).Adj v w) :
    M.Adj v w ∨ G.Adj v w := by
  rcases (MatchingSwitch.replacement_adj M (forwardMatching p) v w).mp h with h | h
  · exact Or.inl h.1
  · exact Or.inr (forwardMatching_adj_graph p h)

/-- Regard the switched matching as a subgraph of any graph containing
the original matching and the edges available to the paths. -/
noncomputable def augmentedInGraph (H : SimpleGraph (A ⊕ B))
    (hM : ∀ v w, M.Adj v w → H.Adj v w) (hG : G ≤ H) : H.Subgraph where
  verts := (augmented p).verts
  Adj := (augmented p).Adj
  adj_sub := by
    intro v w h
    rcases augmented_adj_subset p h with h | h
    · exact hM v w h
    · exact hG h
  edge_vert := (augmented p).edge_vert
  symm := (augmented p).symm

@[simp] theorem augmentedInGraph_verts (H : SimpleGraph (A ⊕ B))
    (hM : ∀ v w, M.Adj v w → H.Adj v w) (hG : G ≤ H) :
    (augmentedInGraph p H hM hG).verts = (augmented p).verts := rfl

@[simp] theorem augmentedInGraph_spanningCoe (H : SimpleGraph (A ⊕ B))
    (hM : ∀ v w, M.Adj v w → H.Adj v w) (hG : G ≤ H) :
    (augmentedInGraph p H hM hG).spanningCoe = (augmented p).spanningCoe := rfl

/-- The ambient-graph version is again an actual matching. -/
theorem augmentedInGraph_isMatching (H : SimpleGraph (A ⊕ B))
    (hMH : ∀ v w, M.Adj v w → H.Adj v w) (hGH : G ≤ H)
    (hM : M.IsMatching)
    (hxM : ∀ i, (.inl (x i) : A ⊕ B) ∉ M.verts)
    (hyM : ∀ i, (.inr (y i) : A ⊕ B) ∉ M.verts)
    (hdisjoint : Pairwise fun i j => Disjoint (p i).vertexSet (p j).vertexSet) :
    (augmentedInGraph p H hMH hGH).IsMatching :=
  augmented_isMatching p hM hxM hyM hdisjoint

/-- In particular, the simultaneous augmentation uses no edge of a graph
avoided by both the original matching and the supplied graph. -/
theorem augmented_avoids_graph (H : SimpleGraph (A ⊕ B))
    (hM : ∀ v w, M.Adj v w → ¬H.Adj v w)
    (hG : ∀ v w, G.Adj v w → ¬H.Adj v w) :
    ∀ v w, (augmented p).Adj v w → ¬H.Adj v w := by
  intro v w h
  rcases augmented_adj_subset p h with h | h
  · exact hM v w h
  · exact hG v w h

/-- If the paths join all uncovered vertices outside `S`, the resulting
matching covers exactly the complement of `S`. -/
theorem augmented_verts_eq_compl (S : Set (A ⊕ B))
    (hcovered : M.verts ∪ ⋃ i, {(.inl (x i) : A ⊕ B), .inr (y i)} = Sᶜ) :
    (augmented p).verts = Sᶜ := by
  rw [augmented_verts, hcovered]

/-- When the original matching is disjoint from `G`, its newly used edges
of `G` are precisely the forward edges of the paths. -/
theorem augmented_reserve_graph
    (hdisjoint : ∀ v w, M.Adj v w → ¬G.Adj v w) :
    (augmented p).spanningCoe ⊓ G = (forwardMatching p).spanningCoe := by
  ext v w
  constructor
  · rintro ⟨h, hG⟩
    rcases (MatchingSwitch.replacement_adj M (forwardMatching p) v w).mp h with h | h
    · exact (hdisjoint v w h.1 hG).elim
    · exact h
  · intro h
    exact ⟨(MatchingSwitch.replacement_adj M (forwardMatching p) v w).mpr (Or.inr h),
      forwardMatching_adj_graph p h⟩

/-- The same identity applies to a larger reserve containing the supplied
graph. This accounts for load in the original reserve when paths use only
its still unused edges. -/
theorem augmented_reserve_graph_of_le (R : SimpleGraph (A ⊕ B))
    (hGR : G ≤ R) (hdisjoint : ∀ v w, M.Adj v w → ¬R.Adj v w) :
    (augmented p).spanningCoe ⊓ R = (forwardMatching p).spanningCoe :=
  MatchingSwitch.replacement_intersection M (forwardMatching p) R hdisjoint
    (fun _ _ h => hGR (forwardMatching_adj_graph p h))

variable [Fintype A] [Fintype B]

/-- The edge set of the forward matching is the union of the actual forward
edge sets of the individual paths. -/
theorem forwardMatching_edgeFinset [Fintype I] :
    (forwardMatching p).spanningCoe.edgeFinset =
      univ.biUnion (fun i => (p i).forwardMatching.spanningCoe.edgeFinset) := by
  ext e
  induction e using Sym2.ind with
  | h v w =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, Subgraph.spanningCoe_adj,
      forwardMatching, Subgraph.iSup_adj, Finset.mem_biUnion, Finset.mem_univ, true_and]

/-- Pairwise disjoint paths contribute exactly the sum of their forward
edge counts. -/
theorem forwardMatching_edge_card [Fintype I]
    (hdisjoint : Pairwise fun i j => Disjoint (p i).vertexSet (p j).vertexSet) :
    (forwardMatching p).spanningCoe.edgeFinset.card = ∑ i, ((p i).length + 1) := by
  rw [forwardMatching_edgeFinset, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro i _
    exact (p i).forwardMatching_edge_card
  · intro i _ j _ hij
    change Disjoint (p i).forwardMatching.spanningCoe.edgeFinset
      (p j).forwardMatching.spanningCoe.edgeFinset
    rw [Finset.disjoint_left]
    intro e hei hej
    induction e using Sym2.ind with
    | h v w =>
      have hi : (p i).forwardMatching.Adj v w := SimpleGraph.mem_edgeFinset.mp hei
      have hj : (p j).forwardMatching.Adj v w := SimpleGraph.mem_edgeFinset.mp hej
      exact (Set.disjoint_left.mp (hdisjoint hij))
        ((p i).forwardMatching.edge_vert hi) ((p j).forwardMatching.edge_vert hj)

/-- The exact total number of reserve edges used by simultaneous augmentation. -/
theorem augmented_reserve_edge_card [Fintype I]
    (hpaths : Pairwise fun i j => Disjoint (p i).vertexSet (p j).vertexSet)
    (hdisjoint : ∀ v w, M.Adj v w → ¬G.Adj v w) :
    ((augmented p).spanningCoe ⊓ G).edgeFinset.card = ∑ i, ((p i).length + 1) := by
  have heq := SimpleGraph.edgeFinset_inj.mpr (augmented_reserve_graph p hdisjoint)
  simpa only [SimpleGraph.edgeFinset, Set.toFinset_card, ← Nat.card_eq_fintype_card]
    using (congrArg Finset.card heq).trans (forwardMatching_edge_card p hpaths)

/-- If each path uses at most `ℓ` reserve edges, all paths together use at
most `ℓ` times their number. -/
theorem augmented_reserve_edge_card_le [Fintype I]
    (hpaths : Pairwise fun i j => Disjoint (p i).vertexSet (p j).vertexSet)
    (hdisjoint : ∀ v w, M.Adj v w → ¬G.Adj v w)
    (ℓ : ℕ) (hℓ : ∀ i, (p i).length + 1 ≤ ℓ) :
    ((augmented p).spanningCoe ⊓ G).edgeFinset.card ≤ ℓ * Fintype.card I := by
  rw [augmented_reserve_edge_card p hpaths hdisjoint]
  calc
    ∑ i, ((p i).length + 1) ≤ ∑ _i : I, ℓ := Finset.sum_le_sum (fun i _ => hℓ i)
    _ = ℓ * Fintype.card I := by simp [Nat.mul_comm]

/-- A path vertex uses exactly one new reserve edge. Every other vertex
uses none, even when several paths are augmented at once. -/
theorem augmented_reserve_degree
    (hpaths : Pairwise fun i j => Disjoint (p i).vertexSet (p j).vertexSet)
    (hdisjoint : ∀ v w, M.Adj v w → ¬G.Adj v w) (v : A ⊕ B) :
    ((augmented p).spanningCoe ⊓ G).degree v =
      if ∃ i, v ∈ (p i).vertexSet then 1 else 0 := by
  have hn : ((augmented p).spanningCoe ⊓ G).neighborFinset v =
      (forwardMatching p).spanningCoe.neighborFinset v := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset]
    exact iff_of_eq (congrArg (fun H : SimpleGraph (A ⊕ B) => H.Adj v w)
      (augmented_reserve_graph p hdisjoint))
  change (((augmented p).spanningCoe ⊓ G).neighborFinset v).card = _
  rw [hn, SimpleGraph.card_neighborFinset_eq_degree]
  have hM := forwardMatching_isMatching p hpaths
  by_cases hv : ∃ i, v ∈ (p i).vertexSet
  · rw [if_pos hv, Subgraph.degree_spanningCoe]
    apply Subgraph.isMatching_iff_forall_degree.mp hM v
    rwa [forwardMatching_verts, Set.mem_iUnion]
  · rw [if_neg hv]
    apply ((forwardMatching p).spanningCoe.degree_eq_zero_iff_notMem_support v).mpr
    rintro ⟨w, hw⟩
    have h := (forwardMatching p).edge_vert hw
    rw [forwardMatching_verts, Set.mem_iUnion] at h
    exact hv h

/-- A vertex forbidden to every path receives no reserve edge. -/
theorem augmented_reserve_degree_zero
    (hpaths : Pairwise fun i j => Disjoint (p i).vertexSet (p j).vertexSet)
    (hdisjoint : ∀ v w, M.Adj v w → ¬G.Adj v w)
    {v : A ⊕ B} (hv : ∀ i, v ∈ W i) :
    ((augmented p).spanningCoe ⊓ G).degree v = 0 := by
  rw [augmented_reserve_degree p hpaths hdisjoint]
  apply if_neg
  rintro ⟨i, hi⟩
  exact (p i).vertexSet_avoids hi (hv i)

/-- The original reserve receives exactly the forward edges, even when
the augmenting paths use a proper subgraph of that reserve. -/
theorem augmented_reserve_edge_card_of_le [Fintype I] (R : SimpleGraph (A ⊕ B))
    (hGR : G ≤ R)
    (hpaths : Pairwise fun i j => Disjoint (p i).vertexSet (p j).vertexSet)
    (hdisjoint : ∀ v w, M.Adj v w → ¬R.Adj v w) :
    ((augmented p).spanningCoe ⊓ R).edgeFinset.card = ∑ i, ((p i).length + 1) := by
  have heq := SimpleGraph.edgeFinset_inj.mpr (augmented_reserve_graph_of_le p R hGR hdisjoint)
  simpa only [SimpleGraph.edgeFinset, Set.toFinset_card, ← Nat.card_eq_fintype_card]
    using (congrArg Finset.card heq).trans (forwardMatching_edge_card p hpaths)

/-- The total increase of reserve degree is twice the number of new
reserve edges. -/
theorem augmented_reserve_degree_sum [Fintype I] (R : SimpleGraph (A ⊕ B))
    (hGR : G ≤ R)
    (hpaths : Pairwise fun i j => Disjoint (p i).vertexSet (p j).vertexSet)
    (hdisjoint : ∀ v w, M.Adj v w → ¬R.Adj v w) :
    ∑ v, ((augmented p).spanningCoe ⊓ R).degree v =
      2 * ∑ i, ((p i).length + 1) := by
  have hsum := ((augmented p).spanningCoe ⊓ R).sum_degrees_eq_twice_card_edges
  have hcard := augmented_reserve_edge_card_of_le p R hGR hpaths hdisjoint
  simp only [SimpleGraph.edgeFinset, Set.toFinset_card, ← Nat.card_eq_fintype_card] at hsum hcard
  rw [hcard] at hsum
  exact hsum

/-- The degree load added by all paths is at most `2 * ℓ * |I|`. -/
theorem augmented_reserve_degree_sum_le [Fintype I] (R : SimpleGraph (A ⊕ B))
    (hGR : G ≤ R)
    (hpaths : Pairwise fun i j => Disjoint (p i).vertexSet (p j).vertexSet)
    (hdisjoint : ∀ v w, M.Adj v w → ¬R.Adj v w)
    (ℓ : ℕ) (hℓ : ∀ i, (p i).length + 1 ≤ ℓ) :
    ∑ v, ((augmented p).spanningCoe ⊓ R).degree v ≤
      2 * ℓ * Fintype.card I := by
  rw [augmented_reserve_degree_sum p R hGR hpaths hdisjoint]
  have hsum : ∑ i, ((p i).length + 1) ≤ ℓ * Fintype.card I := by
    calc
      ∑ i, ((p i).length + 1) ≤ ∑ _i : I, ℓ := Finset.sum_le_sum (fun i _ => hℓ i)
      _ = ℓ * Fintype.card I := by simp [Nat.mul_comm]
  nlinarith

/-- Exact reserve load at a vertex, measured in a reserve containing the
supplied graph. -/
theorem augmented_reserve_degree_of_le (R : SimpleGraph (A ⊕ B))
    (hGR : G ≤ R)
    (hpaths : Pairwise fun i j => Disjoint (p i).vertexSet (p j).vertexSet)
    (hdisjoint : ∀ v w, M.Adj v w → ¬R.Adj v w) (v : A ⊕ B) :
    ((augmented p).spanningCoe ⊓ R).degree v =
      if ∃ i, v ∈ (p i).vertexSet then 1 else 0 := by
  have hMdisjoint : ∀ v w, M.Adj v w → ¬G.Adj v w :=
    fun v w hvw hG => hdisjoint v w hvw (hGR hG)
  have hg : (augmented p).spanningCoe ⊓ R = (augmented p).spanningCoe ⊓ G :=
    (augmented_reserve_graph_of_le p R hGR hdisjoint).trans
      (augmented_reserve_graph p hMdisjoint).symm
  have hn : ((augmented p).spanningCoe ⊓ R).neighborFinset v =
      ((augmented p).spanningCoe ⊓ G).neighborFinset v := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset]
    exact iff_of_eq (congrArg (fun H : SimpleGraph (A ⊕ B) => H.Adj v w) hg)
  exact (congrArg Finset.card hn).trans (augmented_reserve_degree p hpaths hMdisjoint v)

end Overfull.BipartitePathFamily
