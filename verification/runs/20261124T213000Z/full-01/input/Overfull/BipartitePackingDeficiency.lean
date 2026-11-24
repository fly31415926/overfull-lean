import Overfull.HallDefect

/-!
# The deficiency bound in bipartite packing

A maximum matching supplies its own Hall witness. Counting the actual edges
between that witness and its neighborhood bounds the number of uncovered
vertices in terms of the degree error and the total nonnegative load.
-/

namespace Overfull.BipartitePackingDeficiency

open Finset Classical SimpleGraph
open scoped BigOperators

variable {A B : Type*} [Fintype A] [Fintype B]
variable (G : SimpleGraph (A ⊕ B))

private theorem matching_degree (M : G.Subgraph) (hM : M.IsMatching)
    (v : A ⊕ B) : M.spanningCoe.degree v = if v ∈ M.verts then 1 else 0 := by
  by_cases hv : v ∈ M.verts
  · rw [if_pos hv, Subgraph.degree_spanningCoe]
    exact Subgraph.isMatching_iff_forall_degree.mp hM v hv
  · rw [if_neg hv]
    apply (M.spanningCoe.degree_eq_zero_iff_notMem_support v).mpr
    rintro ⟨w, hw⟩
    exact hv (M.edge_vert hw)

private theorem matching_bipartite
    (hbip : G.IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr))
    (M : G.Subgraph) : M.spanningCoe.IsBipartiteWith
      ((univ : Finset A).image (Sum.inl : A → A ⊕ B))
      ((univ : Finset B).image (Sum.inr : B → A ⊕ B)) where
  disjoint := by simpa using hbip.disjoint
  mem_of_adj := by
    intro v w hvw
    simpa using hbip.mem_of_adj (M.adj_sub hvw)

/-- Every edge of a bipartite matching covers exactly one vertex of the
left side. The edge count is the actual unordered edge count. -/
theorem matching_left_card
    (hbip : G.IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr))
    (M : G.Subgraph) (hM : M.IsMatching) :
    (univ.filter (fun a : A => (.inl a : A ⊕ B) ∈ M.verts)).card =
      M.spanningCoe.edgeFinset.card := by
  have h := SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges
    (matching_bipartite G hbip M)
  rw [Finset.sum_image (fun a _ a' _ h => Sum.inl.inj h)] at h
  simpa only [matching_degree G M hM, Finset.sum_boole, Nat.cast_id] using h

/-- The matching edges and the uncovered left vertices partition the left
side, in cardinality. -/
theorem matching_edge_card_add_uncoveredLeft
    (hbip : G.IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr))
    (M : G.Subgraph) (hM : M.IsMatching) :
    M.spanningCoe.edgeFinset.card + (uncoveredLeft M).card = Fintype.card A := by
  rw [← matching_left_card G hbip M hM]
  simpa only [uncoveredLeft, Finset.card_univ] using
    Finset.filter_card_add_filter_neg_card_eq_card
      (s := (univ : Finset A)) (fun a => (.inl a : A ⊕ B) ∈ M.verts)

/-- The corresponding exact identity on the right side. -/
theorem matching_edge_card_add_uncoveredRight
    (hbip : G.IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr))
    (M : G.Subgraph) (hM : M.IsMatching) :
    M.spanningCoe.edgeFinset.card +
      (univ.filter (fun b : B => (.inr b : A ⊕ B) ∉ M.verts)).card = Fintype.card B := by
  have h := SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges'
    (matching_bipartite G hbip M)
  rw [Finset.sum_image (fun b _ b' _ h => Sum.inr.inj h)] at h
  have hcard : (univ.filter (fun b : B => (.inr b : A ⊕ B) ∈ M.verts)).card =
      M.spanningCoe.edgeFinset.card := by
    simpa only [matching_degree G M hM, Finset.sum_boole, Nat.cast_id] using h
  rw [← hcard]
  exact Finset.filter_card_add_filter_neg_card_eq_card
    (s := (univ : Finset B)) (fun b => (.inr b : A ⊕ B) ∈ M.verts)

/-- A matching in a balanced bipartite graph misses equally many vertices
of its two sides. -/
theorem matching_uncovered_sides_eq
    (hbip : G.IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr))
    (hbalance : Fintype.card A = Fintype.card B)
    (M : G.Subgraph) (hM : M.IsMatching) :
    (uncoveredLeft M).card =
      (univ.filter (fun b : B => (.inr b : A ⊕ B) ∉ M.verts)).card := by
  have hleft := matching_edge_card_add_uncoveredLeft G hbip M hM
  have hright := matching_edge_card_add_uncoveredRight G hbip M hM
  omega

variable [DecidableEq A] [DecidableEq B] [DecidableRel G.Adj]

/-- A maximum matching has an actual Hall witness with deficiency at least
the number of its uncovered left vertices. -/
theorem maximum_matching_hall_witness
    (hbip : G.IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr))
    (M : G.Subgraph) (hM : M.IsMatching)
    (hmax : ∀ N : G.Subgraph, N.IsMatching →
      N.spanningCoe.edgeFinset.card ≤ M.spanningCoe.edgeFinset.card) :
    ∃ X : Finset A,
      (X.biUnion (rightNeighbors G)).card + (uncoveredLeft M).card ≤ X.card := by
  by_cases hzero : (uncoveredLeft M).card = 0
  · exact ⟨∅, by simp [hzero]⟩
  by_contra hnot
  push_neg at hnot
  have hHall : ∀ X : Finset A,
      X.card - ((uncoveredLeft M).card - 1) ≤ (X.biUnion (rightNeighbors G)).card := by
    intro X
    have h := hnot X
    omega
  obtain ⟨N, hN, hmiss⟩ := bipartite_hall_defect G ((uncoveredLeft M).card - 1) hHall
  have hcardM := matching_edge_card_add_uncoveredLeft G hbip M hM
  have hcardN := matching_edge_card_add_uncoveredLeft G hbip N hN
  have hsize := hmax N hN
  omega

private theorem rightNeighbors_card_eq_degree
    (hbip : G.IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr)) (a : A) :
    (rightNeighbors G a).card = G.degree (.inl a) := by
  have himage : (rightNeighbors G a).image Sum.inr = G.neighborFinset (.inl a) := by
    ext v
    cases v with
    | inl a' =>
      have hnot : ¬G.Adj (.inl a) (.inl a') := by
        intro h
        simpa using hbip.mem_of_adj h
      simp [rightNeighbors, hnot]
    | inr b => simp [rightNeighbors]
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← himage,
    Finset.card_image_of_injective _ Sum.inr_injective]

private theorem leftNeighbors_card_eq_degree
    (hbip : G.IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr)) (b : B) :
    (leftNeighbors G b).card = G.degree (.inr b) := by
  have himage : (leftNeighbors G b).image Sum.inl = G.neighborFinset (.inr b) := by
    ext v
    cases v with
    | inl a => simp [leftNeighbors, G.adj_comm]
    | inr b' =>
      have hnot : ¬G.Adj (.inr b) (.inr b') := by
        intro h
        simpa using hbip.mem_of_adj h
      simp [leftNeighbors, hnot]
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← himage,
    Finset.card_image_of_injective _ Sum.inl_injective]

/-- Double-counting actual crossing edges: the degree sum on a left set
does not exceed the degree sum on its actual neighborhood. -/
theorem degree_sum_le_neighbor_sum
    (hbip : G.IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr)) (X : Finset A) :
    ∑ a ∈ X, G.degree (.inl a) ≤
      ∑ b ∈ X.biUnion (rightNeighbors G), G.degree (.inr b) := by
  let N := X.biUnion (rightNeighbors G)
  let r : A → B → Prop := fun a b => G.Adj (.inl a) (.inr b)
  have hleft : ∀ a ∈ X, rightNeighbors G a = Finset.bipartiteAbove r N a := by
    intro a ha
    ext b
    simp only [rightNeighbors, Finset.bipartiteAbove, Finset.mem_filter,
      Finset.mem_univ, true_and, r]
    constructor
    · intro hab
      exact ⟨Finset.mem_biUnion.mpr ⟨a, ha, by simpa [rightNeighbors] using hab⟩, hab⟩
    · exact fun h => h.2
  calc
    _ = ∑ a ∈ X, (Finset.bipartiteAbove r N a).card := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [← hleft a ha, rightNeighbors_card_eq_degree G hbip]
    _ = ∑ b ∈ N, (Finset.bipartiteBelow r X b).card :=
      Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow r
    _ ≤ ∑ b ∈ N, (leftNeighbors G b).card := by
      apply Finset.sum_le_sum
      intro b _
      apply Finset.card_le_card
      intro a ha
      simpa only [leftNeighbors, Finset.mem_filter, Finset.mem_univ, true_and]
        using (Finset.mem_filter.mp ha).2
    _ = _ := by simp only [leftNeighbors_card_eq_degree G hbip, N]

/-- The degree-error estimate in Step 2 of the packing proof. The Hall
witness is derived from maximum size, and the load is summed over
the actual vertex set. Equal side sizes are not needed for this bound. -/
theorem maximum_matching_deficiency
    (hbip : G.IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr))
    (M : G.Subgraph) (hM : M.IsMatching)
    (hmax : ∀ N : G.Subgraph, N.IsMatching →
      N.spanningCoe.edgeFinset.card ≤ M.spanningCoe.edgeFinset.card)
    (m : ℕ) (d a t : ℝ) (u : A ⊕ B → ℝ)
    (hd : 0 < d) (ha : 0 ≤ a) (hu : ∀ v, 0 ≤ u v)
    (hA : Fintype.card A ≤ m) (hB : Fintype.card B ≤ m)
    (hlower : ∀ v, d - a ≤ (G.degree v : ℝ))
    (hupper : ∀ v, (G.degree v : ℝ) ≤ d + a + u v)
    (hload : ∑ v, u v ≤ t) :
    ((uncoveredLeft M).card : ℝ) ≤ (2 * a * m + t) / d := by
  obtain ⟨X, hX⟩ := maximum_matching_hall_witness G hbip M hM hmax
  let N := X.biUnion (rightNeighbors G)
  have hdef : (N.card : ℝ) + (uncoveredLeft M).card ≤ X.card := by
    exact_mod_cast hX
  have hXsize : (X.card : ℝ) ≤ m := by
    exact_mod_cast (Finset.card_le_univ X).trans hA
  have hNsize : (N.card : ℝ) ≤ m := by
    exact_mod_cast (Finset.card_le_univ N).trans hB
  have hcount : ∑ x ∈ X, (G.degree (.inl x) : ℝ) ≤
      ∑ b ∈ N, (G.degree (.inr b) : ℝ) := by
    exact_mod_cast degree_sum_le_neighbor_sum G hbip X
  have hloadN : ∑ b ∈ N, u (.inr b) ≤ t := by
    calc
      _ ≤ ∑ b : B, u (.inr b) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ N)
          (by intro b _ _; exact hu _)
      _ ≤ ∑ v : A ⊕ B, u v := by
        rw [Fintype.sum_sum_type]
        exact le_add_of_nonneg_left (Finset.sum_nonneg (fun v _ => hu _))
      _ ≤ t := hload
  have hlowerX : (d - a) * X.card ≤ ∑ x ∈ X, (G.degree (.inl x) : ℝ) := by
    calc
      _ = ∑ _x ∈ X, (d - a) := by simp [mul_comm, sub_mul]
      _ ≤ _ := Finset.sum_le_sum (fun x _ => hlower (.inl x))
  have hupperN : ∑ b ∈ N, (G.degree (.inr b) : ℝ) ≤ (d + a) * N.card + t := by
    calc
      _ ≤ ∑ b ∈ N, (d + a + u (.inr b)) :=
        Finset.sum_le_sum (fun b _ => hupper (.inr b))
      _ = (d + a) * N.card + ∑ b ∈ N, u (.inr b) := by
        rw [Finset.sum_add_distrib]
        simp [mul_comm, add_mul]
      _ ≤ _ := add_le_add_left hloadN _
  apply (le_div_iff₀ hd).mpr
  have hdegrees := hlowerX.trans (hcount.trans hupperN)
  have hdh := mul_le_mul_of_nonneg_left hdef hd.le
  have haX := mul_le_mul_of_nonneg_left hXsize ha
  have haN := mul_le_mul_of_nonneg_left hNsize ha
  nlinarith

end Overfull.BipartitePackingDeficiency
