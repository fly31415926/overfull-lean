import Overfull.CircuitPatterns.Completion
import Overfull.NativeReserve.Residual

/-!
# Simple residuals and the original edge copies

Deleting a prefix of actual simple subgraphs deletes precisely the corresponding
finite sets of original host copies. The resulting edge types are explicitly
equivalent, with unchanged unordered endpoints. No coloring is used here.
-/

noncomputable section

namespace Overfull.Terminal

open Finset Classical SimpleGraph MatchingProbability ForeignPhase NativeReserve
open BipartitePackingAccounting

variable {V : Type*} [Fintype V]

theorem matchingEdges_isMatching (G : SimpleGraph V) (M : G.Subgraph)
    (hM : M.IsMatching) :
    (Multigraph.ofSimpleGraph G).IsMatching (matchingEdges M) := by
  intro e he f hf v hev hfv
  obtain ⟨x, hx⟩ := Sym2.mem_iff_exists.mp hev
  obtain ⟨y, hy⟩ := Sym2.mem_iff_exists.mp hfv
  change e.val = s(v, x) at hx
  change f.val = s(v, y) at hy
  have hex : M.Adj v x := by simpa only [hx] using (mem_filter.mp he).2
  have hfy : M.Adj v y := by simpa only [hy] using (mem_filter.mp hf).2
  have hxy := hM.eq_of_adj_left hex hfy
  apply Subtype.ext
  rw [hx, hy, hxy]

theorem matchingEdges_isPerfectMatching (G : SimpleGraph V) (M : G.Subgraph)
    (hM : M.IsPerfectMatching) :
    (Multigraph.ofSimpleGraph G).IsPerfectMatching (matchingEdges M) := by
  apply (Multigraph.ofSimpleGraph G).isPerfectMatching_iff.mpr
  refine ⟨matchingEdges_isMatching G M hM.1, ?_⟩
  intro v
  obtain ⟨w, hvw, _⟩ := SimpleGraph.Subgraph.isPerfectMatching_iff.mp hM v
  refine ⟨⟨s(v, w), M.adj_sub hvw⟩, mem_filter.mpr ⟨mem_univ _, hvw⟩, ?_⟩
  simp [Multigraph.ofSimpleGraph]

/-- The first `q` simple matchings, as actual original host edge copies. -/
def matchingFamilyCopies (G : SimpleGraph V) (N : ℕ → G.Subgraph) (q : ℕ) :
    Fin q → Finset G.edgeSet := fun j => matchingEdges (N j.val)

@[simp] theorem mem_matchingFamilyCopies (G : SimpleGraph V)
    (N : ℕ → G.Subgraph) (q : ℕ) (j : Fin q) (e : G.edgeSet) :
    e ∈ matchingFamilyCopies G N q j ↔ e.val ∈ (N j.val).edgeSet := by
  simp [matchingFamilyCopies, matchingEdges]

@[simp] theorem mem_removedFamilyCopies (G : SimpleGraph V)
    (N : ℕ → G.Subgraph) (q : ℕ) (e : G.edgeSet) :
    e ∈ removedCopies (matchingFamilyCopies G N q) univ ↔
      ∃ j < q, e.val ∈ (N j).edgeSet := by
  simp only [mem_removedCopies, mem_univ, true_and, mem_matchingFamilyCopies]
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨j.val, j.isLt, hj⟩
  · rintro ⟨j, hj, he⟩
    exact ⟨⟨j, hj⟩, he⟩

theorem removedFamilyCopies_eq_range (G : SimpleGraph V)
    (N : ℕ → G.Subgraph) (q : ℕ) :
    removedCopies (matchingFamilyCopies G N q) univ =
      (range q).biUnion (fun j => matchingEdges (N j)) := by
  ext e
  simp [matchingEdges]

omit [Fintype V] in
@[simp] theorem spanningCoe_mem_edgeSet (G : SimpleGraph V) (M : G.Subgraph)
    (e : Sym2 V) : e ∈ M.spanningCoe.edgeSet ↔ e ∈ M.edgeSet := by
  rcases e with ⟨u, v⟩
  rfl

omit [Fintype V] in
theorem edgeUnion_mem_edgeSet {J : Type*} (H : J → SimpleGraph V)
    (T : Finset J) (e : Sym2 V) :
    e ∈ (edgeUnion H T).edgeSet ↔ ∃ j ∈ T, e ∈ (H j).edgeSet := by
  rcases e with ⟨u, v⟩
  rfl

/-- This equivalence records the exact original copies removed, including
the empty-prefix case and families that have not yet been shown disjoint. -/
theorem mem_residual_iff_not_removed (G : SimpleGraph V)
    (N : ℕ → G.Subgraph) (q : ℕ) (e : G.edgeSet) :
    e.val ∈ (afterDeletions G N q).edgeSet ↔
      e ∉ removedCopies (matchingFamilyCopies G N q) univ := by
  simp only [afterDeletions, edgeSet_sdiff, Set.mem_diff, e.property, true_and,
    edgeUnion_mem_edgeSet, mem_range, spanningCoe_mem_edgeSet,
    mem_removedFamilyCopies]

private theorem matchingEdges_disjoint_of_present (G : SimpleGraph V)
    (N : ℕ → G.Subgraph) {i j : ℕ} (hij : i < j)
    (hj : (N j).spanningCoe ≤ afterDeletions G N j) :
    Disjoint (matchingEdges (N i)) (matchingEdges (N j)) := by
  apply disjoint_left.mpr
  intro e hei hej
  have heR := SimpleGraph.edgeSet_mono hj
    ((spanningCoe_mem_edgeSet G (N j) e.val).mpr (mem_filter.mp hej).2)
  have hn := (mem_residual_iff_not_removed G N j e).mp heR
  exact hn ((mem_removedFamilyCopies G N j e).mpr ⟨i, hij, (mem_filter.mp hei).2⟩)

theorem matchingFamilyCopies_pairwise_disjoint (G : SimpleGraph V)
    (N : ℕ → G.Subgraph) (q : ℕ)
    (hpresent : ∀ j < q, (N j).spanningCoe ≤ afterDeletions G N j) :
    Pairwise (fun i j => Disjoint (matchingFamilyCopies G N q i)
      (matchingFamilyCopies G N q j)) := by
  intro i j hij
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact matchingEdges_disjoint_of_present G N hlt (hpresent j.val j.isLt)
  · exact (matchingEdges_disjoint_of_present G N hgt (hpresent i.val i.isLt)).symm

theorem matchingFamilyCopies_perfect (G : SimpleGraph V)
    (N : ℕ → G.Subgraph) (q : ℕ)
    (hperfect : ∀ j < q, (N j).IsPerfectMatching) :
    ∀ j, (Multigraph.ofSimpleGraph G).IsPerfectMatching (matchingFamilyCopies G N q j) := by
  intro j
  exact matchingEdges_isPerfectMatching G (N j.val) (hperfect j.val j.isLt)

/-- A simple residual edge is the same original host copy, with no endpoint
change or choice of a replacement copy. -/
def residualEdgeEmbedding (G : SimpleGraph V) (N : ℕ → G.Subgraph) (q : ℕ) :
    (afterDeletions G N q).edgeSet ↪ G.edgeSet where
  toFun e := ⟨e.val, SimpleGraph.edgeSet_mono sdiff_le e.property⟩
  inj' := by
    intro e f h
    exact Subtype.ext (congrArg Subtype.val h)

@[simp] theorem residualEdgeEmbedding_val (G : SimpleGraph V)
    (N : ℕ → G.Subgraph) (q : ℕ) (e : (afterDeletions G N q).edgeSet) :
    (residualEdgeEmbedding G N q e).val = e.val := rfl

@[simp] theorem residualEdgeEmbedding_edge (G : SimpleGraph V)
    (N : ℕ → G.Subgraph) (q : ℕ) (e : (afterDeletions G N q).edgeSet) :
    (Multigraph.ofSimpleGraph G).edge (residualEdgeEmbedding G N q e) =
      (Multigraph.ofSimpleGraph (afterDeletions G N q)).edge e := rfl

@[simp] theorem residualEdgeEmbedding_firstEnd (G : SimpleGraph V)
    (N : ℕ → G.Subgraph) (q : ℕ) (e : (afterDeletions G N q).edgeSet) :
    (Multigraph.ofSimpleGraph G).firstEnd (residualEdgeEmbedding G N q e) =
      (Multigraph.ofSimpleGraph (afterDeletions G N q)).firstEnd e := rfl

@[simp] theorem residualEdgeEmbedding_secondEnd (G : SimpleGraph V)
    (N : ℕ → G.Subgraph) (q : ℕ) (e : (afterDeletions G N q).edgeSet) :
    (Multigraph.ofSimpleGraph G).secondEnd (residualEdgeEmbedding G N q e) =
      (Multigraph.ofSimpleGraph (afterDeletions G N q)).secondEnd e := rfl

/-- An explicit equivalence between residual original copies and the edge
subtype of the actual simple residual. Both maps preserve the same `Sym2`. -/
def residualEdgeEquiv (G : SimpleGraph V) (N : ℕ → G.Subgraph) (q : ℕ) :
    {e : G.edgeSet // e ∉ removedCopies (matchingFamilyCopies G N q) univ} ≃
      (afterDeletions G N q).edgeSet where
  toFun e := ⟨e.val.val, (mem_residual_iff_not_removed G N q e.val).mpr e.property⟩
  invFun e := ⟨residualEdgeEmbedding G N q e,
    (mem_residual_iff_not_removed G N q _).mp e.property⟩
  left_inv _ := by rfl
  right_inv _ := by rfl

@[simp] theorem residualEdgeEquiv_edge (G : SimpleGraph V)
    (N : ℕ → G.Subgraph) (q : ℕ)
    (e : {e : G.edgeSet // e ∉ removedCopies (matchingFamilyCopies G N q) univ}) :
    (Multigraph.ofSimpleGraph (afterDeletions G N q)).edge (residualEdgeEquiv G N q e) =
      (residualGraph (Multigraph.ofSimpleGraph G) (matchingFamilyCopies G N q) univ).edge e :=
  rfl

@[simp] theorem residualEdgeEquiv_embedding (G : SimpleGraph V)
    (N : ℕ → G.Subgraph) (q : ℕ)
    (e : {e : G.edgeSet // e ∉ removedCopies (matchingFamilyCopies G N q) univ}) :
    residualEdgeEmbedding G N q (residualEdgeEquiv G N q e) = e.val := rfl

theorem residualEdgeEmbedding_image_univ (G : SimpleGraph V)
    (N : ℕ → G.Subgraph) (q : ℕ) :
    (univ : Finset (afterDeletions G N q).edgeSet).image (residualEdgeEmbedding G N q) =
      univ \ removedCopies (matchingFamilyCopies G N q) univ := by
  ext e
  simp only [mem_image, mem_univ, true_and, mem_sdiff]
  constructor
  · rintro ⟨f, rfl⟩
    exact (mem_residual_iff_not_removed G N q _).mp f.property
  · intro he
    exact ⟨residualEdgeEquiv G N q ⟨e, he⟩, rfl⟩

/-- Every original edge pool has exactly its surviving original copies in
the simple residual. This applies in particular to joining and cut pools. -/
theorem residualEdgeEmbedding_image_filter (G : SimpleGraph V)
    (N : ℕ → G.Subgraph) (q : ℕ) (A : Finset G.edgeSet) :
    (univ.filter (fun e : (afterDeletions G N q).edgeSet =>
      residualEdgeEmbedding G N q e ∈ A)).image (residualEdgeEmbedding G N q) =
      A \ removedCopies (matchingFamilyCopies G N q) univ := by
  ext e
  simp only [mem_image, mem_filter, mem_univ, true_and, mem_sdiff]
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨hf, (mem_residual_iff_not_removed G N q _).mp f.property⟩
  · rintro ⟨heA, he⟩
    exact ⟨residualEdgeEquiv G N q ⟨e, he⟩, heA, rfl⟩

end Overfull.Terminal
