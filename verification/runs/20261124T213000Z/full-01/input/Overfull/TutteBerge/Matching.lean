import Overfull.TutteBerge.Graph

/-!
# Matchings and universal augmentation

An original matching becomes perfect after one universal dummy vertex is
added for each uncovered vertex. Conversely, restricting a perfect matching
of the augmented graph loses at most as many original vertices as there are
dummy vertices. All matchings here are actual mathlib graph subgraphs.
-/

namespace Overfull.TutteBerge

open Finset Classical SimpleGraph

variable {V D : Type*} (G : SimpleGraph V)

/-- Keep the original matching and pair each uncovered vertex with its own
dummy vertex. -/
def extendedMatching (M : G.Subgraph) : (augmented G {v : V // v ∉ M.verts}).Subgraph where
  verts := Set.univ
  Adj x y := match x, y with
    | .inl v, .inl w => M.Adj v w
    | .inl v, .inr d => v = d.val
    | .inr d, .inl v => v = d.val
    | .inr _, .inr _ => False
  adj_sub := by
    rintro (v | d) (w | e) h
    · exact M.adj_sub h
    · trivial
    · trivial
    · exact h.elim
  edge_vert := by intro _ _ _; trivial
  symm := by
    rintro (v | d) (w | e) h
    · exact M.symm h
    · exact h
    · exact h
    · exact h

/-- Pairing the uncovered vertices with their copies gives a perfect matching
of the actual augmented graph. No finiteness assumption is needed here. -/
theorem extendedMatching_isPerfectMatching (M : G.Subgraph) (hM : M.IsMatching) :
    (extendedMatching G M).IsPerfectMatching := by
  rw [Subgraph.isPerfectMatching_iff]
  intro x
  cases x with
  | inl v =>
    by_cases hv : v ∈ M.verts
    · obtain ⟨w, hvw, huniq⟩ := hM hv
      refine ⟨.inl w, hvw, ?_⟩
      intro y hy
      cases y with
      | inl w' => exact congrArg Sum.inl (huniq w' hy)
      | inr d =>
        change v = d.val at hy
        exact (d.property (hy ▸ hv)).elim
    · refine ⟨.inr ⟨v, hv⟩, rfl, ?_⟩
      intro y hy
      cases y with
      | inl w => exact (hv (M.edge_vert hy)).elim
      | inr d =>
        change v = d.val at hy
        exact congrArg Sum.inr (Subtype.ext hy.symm)
  | inr d =>
    refine ⟨.inl d.val, rfl, ?_⟩
    intro y hy
    cases y with
    | inl v => exact congrArg Sum.inl hy
    | inr e => exact hy.elim

/-- A matching extends to a perfect matching after adding one universal
vertex for every vertex it misses. -/
theorem exists_perfectMatching_augmented_uncovered
    (M : G.Subgraph) (hM : M.IsMatching) :
    ∃ N : (augmented G {v : V // v ∉ M.verts}).Subgraph, N.IsPerfectMatching :=
  ⟨extendedMatching G M, extendedMatching_isPerfectMatching G M hM⟩

/-- Retain exactly the original-original edges of an augmented matching.
The vertex set is their actual support, so no isolated vertices are retained. -/
def originalMatching (N : (augmented G D).Subgraph) : G.Subgraph where
  verts v := ∃ w : V, N.Adj (.inl v) (.inl w)
  Adj v w := N.Adj (.inl v) (.inl w)
  adj_sub := by intro v w h; exact N.adj_sub h
  edge_vert := by intro v w h; exact ⟨w, h⟩
  symm := by intro v w h; exact N.symm h

/-- Restricting a matching to edges between original vertices is a matching. -/
theorem originalMatching_isMatching (N : (augmented G D).Subgraph)
    (hN : N.IsMatching) : (originalMatching G N).IsMatching := by
  intro v hv
  obtain ⟨w, hvw⟩ := hv
  refine ⟨w, hvw, ?_⟩
  intro w' hvw'
  exact Sum.inl.inj (hN.eq_of_adj_left hvw' hvw)

/-- Every original vertex uncovered by the restriction is matched to a dummy
vertex in the perfect augmented matching. -/
theorem uncovered_has_dummy_partner (N : (augmented G D).Subgraph)
    (hN : N.IsPerfectMatching) (v : {v : V // v ∉ (originalMatching G N).verts}) :
    ∃ d : D, N.Adj (.inl v.val) (.inr d) := by
  obtain ⟨w, hvw, _⟩ := Subgraph.isPerfectMatching_iff.mp hN (.inl v.val)
  cases w with
  | inl w => exact (v.property ⟨w, hvw⟩).elim
  | inr d => exact ⟨d, hvw⟩

/-- Different uncovered original vertices have different dummy partners. -/
theorem uncovered_injection_to_dummies (N : (augmented G D).Subgraph)
    (hN : N.IsPerfectMatching) :
    ∃ f : {v : V // v ∉ (originalMatching G N).verts} → D, Function.Injective f := by
  choose f hf using uncovered_has_dummy_partner G N hN
  refine ⟨f, ?_⟩
  intro v w hvw
  apply Subtype.ext
  have hw : N.Adj (.inl w.val) (.inr (f v)) := by rw [hvw]; exact hf w
  exact Sum.inl.inj (hN.1.eq_of_adj_right (hf v) hw)

/-- Restriction of a perfect augmented matching misses at most one original
vertex per dummy vertex. -/
theorem originalMatching_uncovered_card_le [Finite D]
    (N : (augmented G D).Subgraph) (hN : N.IsPerfectMatching) :
    (originalMatching G N).vertsᶜ.ncard ≤ Nat.card D := by
  obtain ⟨f, hf⟩ := uncovered_injection_to_dummies G N hN
  have h := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_coe_set_eq] using h

/-- The backward adapter from a perfect matching of a universal augmentation
to an actual matching of the original graph. -/
theorem exists_matching_of_perfect_augmented [Finite D]
    (N : (augmented G D).Subgraph) (hN : N.IsPerfectMatching) :
    ∃ M : G.Subgraph, M.IsMatching ∧ M.vertsᶜ.ncard ≤ Nat.card D :=
  ⟨originalMatching G N, originalMatching_isMatching G N hN.1,
    originalMatching_uncovered_card_le G N hN⟩

/-- A finite matching covers exactly twice as many vertices as it has
unordered edges. The spanning coercion retains precisely its actual edges. -/
theorem matching_vertices_card [Fintype V]
    (M : G.Subgraph) (hM : M.IsMatching) :
    M.verts.ncard = 2 * M.spanningCoe.edgeFinset.card := by
  have hdegree : ∀ v : V, M.spanningCoe.degree v = if v ∈ M.verts then 1 else 0 := by
    intro v
    by_cases hv : v ∈ M.verts
    · rw [if_pos hv, Subgraph.degree_spanningCoe]
      exact Subgraph.isMatching_iff_forall_degree.mp hM v hv
    · rw [if_neg hv]
      apply (M.spanningCoe.degree_eq_zero_iff_notMem_support v).mpr
      rintro ⟨w, hw⟩
      exact hv (M.edge_vert hw)
  have h := M.spanningCoe.sum_degrees_eq_twice_card_edges
  simp only [hdegree, Finset.sum_boole, Nat.cast_id] at h
  have hfilter : (Finset.univ.filter (fun v => v ∈ M.verts)) = M.verts.toFinset := by
    ext v
    simp
  rw [hfilter] at h
  simpa only [Set.toFinset_card, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] using h

/-- The numbers of uncovered vertices and covered pairs account for the
entire vertex set. -/
theorem matching_uncovered_add_twice_edges [Fintype V]
    (M : G.Subgraph) (hM : M.IsMatching) :
    M.vertsᶜ.ncard + 2 * M.spanningCoe.edgeFinset.card = Nat.card V := by
  have h := Set.ncard_add_ncard_compl M.verts
  rw [matching_vertices_card G M hM] at h
  omega

end Overfull.TutteBerge
