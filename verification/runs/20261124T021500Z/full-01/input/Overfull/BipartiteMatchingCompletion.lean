import Overfull.BipartitePathFamily
import Overfull.BipartitePathPacking

/-!
# Completing a matching through a robust reserve

The forbidden set and the disjoint augmenting paths are constructed from the
graph and matching. No paths or perfect matching are assumed. A specified
set of already covered vertices is protected from all new reserve edges.
-/

namespace Overfull.BipartiteMatchingCompletion

open Finset Classical SimpleGraph
open scoped BigOperators

/-- Add the matching partners of `Z` to `S ∪ Z`. The resulting set is closed
under matching partners, and no more than `|Z|` vertices have been added. -/
theorem exists_partner_closed_set {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (M : G.Subgraph) (hM : M.IsMatching)
    (S Z : Finset V) (hS : ∀ v ∈ S, v ∉ M.verts)
    (hZ : ∀ v ∈ Z, v ∈ M.verts) :
    ∃ W : Finset V,
      S ∪ Z ⊆ W ∧ W.card ≤ S.card + 2 * Z.card ∧
      (∀ v ∈ W, v ∈ S ∨ v ∈ M.verts) ∧
      (∀ v w, v ∈ W → M.Adj v w → w ∈ W) := by
  classical
  let f : Z → V := fun z => (hM (hZ z.val z.property)).choose
  have hf (z : Z) : M.Adj z.val (f z) := (hM (hZ z.val z.property)).choose_spec.1
  let P : Finset V := univ.image f
  let W := S ∪ Z ∪ P
  have hPcard : P.card ≤ Z.card := by
    calc
      P.card ≤ (univ : Finset Z).card := Finset.card_image_le
      _ = Z.card := by simp
  have hSZ : S ∪ Z ⊆ W := Finset.subset_union_left
  refine ⟨W, hSZ, ?_, ?_, ?_⟩
  · have h₁ := Finset.card_union_le (S ∪ Z) P
    have h₂ := Finset.card_union_le S Z
    dsimp [W]
    omega
  · intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · rcases Finset.mem_union.mp hv with hv | hv
      · exact Or.inl hv
      · exact Or.inr (hZ v hv)
    · obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hv
      exact Or.inr (M.edge_vert (M.symm (hf z)))
  · intro v w hv hvw
    rcases Finset.mem_union.mp hv with hv | hv
    · rcases Finset.mem_union.mp hv with hv | hv
      · exact (hS v hv (M.edge_vert hvw)).elim
      · have hw : w = f ⟨v, hv⟩ := hM.eq_of_adj_left hvw (hf ⟨v, hv⟩)
        apply Finset.mem_union_right
        apply Finset.mem_image.mpr
        exact ⟨⟨v, hv⟩, Finset.mem_univ _, hw.symm⟩
    · obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hv
      have hw : w = z.val := hM.eq_of_adj_left hvw (M.symm (hf z))
      rw [hw]
      exact hSZ (Finset.mem_union_right _ z.property)

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- Left vertices outside `S` that the matching misses. -/
noncomputable def uncoveredLeftOutside
    (M : (⊤ : SimpleGraph (A ⊕ B)).Subgraph) (S : Finset (A ⊕ B)) : Finset A :=
  univ.filter (fun a => (.inl a : A ⊕ B) ∉ S ∧ (.inl a : A ⊕ B) ∉ M.verts)

/-- Right vertices outside `S` that the matching misses. -/
noncomputable def uncoveredRightOutside
    (M : (⊤ : SimpleGraph (A ⊕ B)).Subgraph) (S : Finset (A ⊕ B)) : Finset B :=
  univ.filter (fun b => (.inr b : A ⊕ B) ∉ S ∧ (.inr b : A ⊕ B) ∉ M.verts)

/-- A robust reserve completes an actual crossing matching. The set `Z`
is covered using only original matching edges. Reserve degree increases by
at most one at each vertex, by zero on `S ∪ Z`, and by at most `2 * ℓ * h`
in total, where `h` is the actual uncovered count on either side.

The path graph `G` may be a proper subgraph of the reserve `R`; thus load is
measured in the original reserve even when only its unused edges remain
available for augmentation.
-/
theorem exists_completion
    (G R : SimpleGraph (A ⊕ B)) [DecidableRel G.Adj]
    (hGR : G ≤ R)
    (M : (⊤ : SimpleGraph (A ⊕ B)).Subgraph) (hM : IsCrossingMatching M)
    (hMR : ∀ v w, M.Adj v w → ¬R.Adj v w)
    (S Z : Finset (A ⊕ B)) (hS : ∀ v ∈ S, v ∉ M.verts)
    (hZ : ∀ v ∈ Z, v ∈ M.verts)
    (hbalance : (uncoveredLeftOutside M S).card = (uncoveredRightOutside M S).card)
    (θ τ δ : ℝ) (hθ : 0 < θ) (hτ : 0 < τ) (hδ : 2 * τ ≤ δ)
    (hleft : ∀ a, δ * Fintype.card A ≤ ((rightNeighbors G a).card : ℝ))
    (hright : ∀ b, δ * Fintype.card A ≤ ((leftNeighbors G b).card : ℝ))
    (hexpand : IsBipartiteRobustExpander G θ τ)
    (ℓ : ℕ) (hℓ : Nat.ceil (2 / θ) + 2 ≤ ℓ)
    (hbudget : (S.card : ℝ) + 2 * Z.card + 2 * ℓ * (uncoveredLeftOutside M S).card ≤
      min θ δ * Fintype.card A / 2 - 1) :
    ∃ N : (⊤ : SimpleGraph (A ⊕ B)).Subgraph,
      IsCrossingMatching N ∧ N.verts = (S : Set (A ⊕ B))ᶜ ∧
      M.verts ⊆ N.verts ∧
      (∀ v w, N.Adj v w → M.Adj v w ∨ G.Adj v w) ∧
      (∀ v ∈ S ∪ Z, (N.spanningCoe ⊓ R).degree v = 0) ∧
      (∀ v, (N.spanningCoe ⊓ R).degree v ≤ 1) ∧
      (∑ v, (N.spanningCoe ⊓ R).degree v ≤
        2 * ℓ * (uncoveredLeftOutside M S).card) := by
  classical
  obtain ⟨W, hSW, hWcard, hWsub, hclosed⟩ :=
    exists_partner_closed_set (⊤ : SimpleGraph (A ⊕ B)) M hM.1 S Z hS hZ
  let U := uncoveredLeftOutside M S
  let V := uncoveredRightOutside M S
  let eA : Fin U.card ≃ U := (Fintype.equivFinOfCardEq (Fintype.card_coe U)).symm
  let eB : Fin U.card ≃ V :=
    (Fintype.equivFinOfCardEq ((Fintype.card_coe V).trans hbalance.symm)).symm
  let x : Fin U.card → A := fun i => (eA i).val
  let y : Fin U.card → B := fun i => (eB i).val
  have hxin : Function.Injective x := Subtype.val_injective.comp eA.injective
  have hyin : Function.Injective y := Subtype.val_injective.comp eB.injective
  have hx (i : Fin U.card) : (.inl (x i) : A ⊕ B) ∉ S ∧
      (.inl (x i) : A ⊕ B) ∉ M.verts := (Finset.mem_filter.mp (eA i).property).2
  have hy (i : Fin U.card) : (.inr (y i) : A ⊕ B) ∉ S ∧
      (.inr (y i) : A ⊕ B) ∉ M.verts := (Finset.mem_filter.mp (eB i).property).2
  have hxW (i : Fin U.card) : (.inl (x i) : A ⊕ B) ∉ W := by
    intro hi
    rcases hWsub _ hi with hs | hm
    · exact (hx i).1 hs
    · exact (hx i).2 hm
  have hyW (i : Fin U.card) : (.inr (y i) : A ⊕ B) ∉ W := by
    intro hi
    rcases hWsub _ hi with hs | hm
    · exact (hy i).1 hs
    · exact (hy i).2 hm
  have hxall (a : A) (haS : (.inl a : A ⊕ B) ∉ S)
      (haM : (.inl a : A ⊕ B) ∉ M.verts) : ∃ i, x i = a := by
    have ha : a ∈ U := Finset.mem_filter.mpr ⟨Finset.mem_univ _, haS, haM⟩
    obtain ⟨i, hi⟩ := eA.surjective ⟨a, ha⟩
    exact ⟨i, congrArg Subtype.val hi⟩
  have hyall (b : B) (hbS : (.inr b : A ⊕ B) ∉ S)
      (hbM : (.inr b : A ⊕ B) ∉ M.verts) : ∃ i, y i = b := by
    have hb : b ∈ V := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbS, hbM⟩
    obtain ⟨i, hi⟩ := eB.surjective ⟨b, hb⟩
    exact ⟨i, congrArg Subtype.val hi⟩
  have hends : ∀ v : A ⊕ B, v ∉ W → v ∉ M.verts →
      (∃ i, v = .inl (x i)) ∨ ∃ i, v = .inr (y i) := by
    intro v hv hvm
    have hvS : v ∉ S := fun hs => hv (hSW (Finset.mem_union_left _ hs))
    cases v with
    | inl a =>
      obtain ⟨i, hi⟩ := hxall a hvS hvm
      exact Or.inl ⟨i, congrArg Sum.inl hi.symm⟩
    | inr b =>
      obtain ⟨i, hi⟩ := hyall b hvS hvm
      exact Or.inr ⟨i, congrArg Sum.inr hi.symm⟩
  have hbudgetW : (W.card : ℝ) + 2 * ℓ * U.card ≤
      min θ δ * Fintype.card A / 2 - 1 := by
    have hcard : (W.card : ℝ) ≤ S.card + 2 * Z.card := by exact_mod_cast hWcard
    dsimp [U]
    linarith
  obtain ⟨p, hlen, hpaths⟩ := BipartitePathPacking.exists_disjoint_paths G M hM
    θ τ δ hθ hτ hδ hleft hright hexpand ℓ hℓ U.card W x y hxin hyin
    (fun i => (hx i).2) (fun i => (hy i).2) hxW hyW hclosed hends hbudgetW
  let N := BipartitePathFamily.augmented p
  have hNverts : N.verts = (S : Set (A ⊕ B))ᶜ := by
    rw [BipartitePathFamily.augmented_verts]
    ext v
    constructor
    · rintro (hv | hv) hvS
      · exact hS v hvS hv
      · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hv
        rcases Set.mem_insert_iff.mp hi with rfl | hi
        · exact (hx i).1 hvS
        · have heq : v = .inr (y i) := Set.mem_singleton_iff.mp hi
          subst v
          exact (hy i).1 hvS
    · intro hvS
      by_cases hvM : v ∈ M.verts
      · exact Or.inl hvM
      · have hvW : v ∉ W := by
          intro hv
          rcases hWsub v hv with hs | hm
          · exact hvS hs
          · exact hvM hm
        rcases hends v hvW hvM with ⟨i, rfl⟩ | ⟨i, rfl⟩
        · exact Or.inr (Set.mem_iUnion.mpr ⟨i, by simp⟩)
        · exact Or.inr (Set.mem_iUnion.mpr ⟨i, by simp⟩)
  refine ⟨N, BipartitePathFamily.augmented_isCrossingMatching p hM
    (fun i => (hx i).2) (fun i => (hy i).2) hpaths, hNverts,
    BipartitePathFamily.augmented_covers_original p,
    (fun _ _ h => BipartitePathFamily.augmented_adj_subset p h), ?_, ?_, ?_⟩
  · intro v hv
    have hvW := hSW hv
    have hd := BipartitePathFamily.augmented_reserve_degree_of_le p R hGR hpaths hMR v
    have hvnot : ¬∃ i, v ∈ (p i).vertexSet := by
      rintro ⟨i, hi⟩
      exact (p i).vertexSet_avoids hi hvW
    simpa only [if_neg hvnot] using hd
  · intro v
    have hd := BipartitePathFamily.augmented_reserve_degree_of_le p R hGR hpaths hMR v
    rw [hd]
    split_ifs <;> omega
  · simpa only [Fintype.card_fin] using
      BipartitePathFamily.augmented_reserve_degree_sum_le p R hGR hpaths hMR ℓ hlen

/-- The completion is an actual subgraph of any ambient graph containing
the original matching and the available reserve edges. The explicit edge
condition also preserves disjointness from every previously used edge set
avoided by these two inputs. -/
theorem exists_completion_in_graph
    (G R H : SimpleGraph (A ⊕ B)) [DecidableRel G.Adj]
    (hGR : G ≤ R) (hGH : G ≤ H)
    (M : (⊤ : SimpleGraph (A ⊕ B)).Subgraph) (hM : IsCrossingMatching M)
    (hMH : ∀ v w, M.Adj v w → H.Adj v w)
    (hMR : ∀ v w, M.Adj v w → ¬R.Adj v w)
    (S Z : Finset (A ⊕ B)) (hS : ∀ v ∈ S, v ∉ M.verts)
    (hZ : ∀ v ∈ Z, v ∈ M.verts)
    (hbalance : (uncoveredLeftOutside M S).card = (uncoveredRightOutside M S).card)
    (θ τ δ : ℝ) (hθ : 0 < θ) (hτ : 0 < τ) (hδ : 2 * τ ≤ δ)
    (hleft : ∀ a, δ * Fintype.card A ≤ ((rightNeighbors G a).card : ℝ))
    (hright : ∀ b, δ * Fintype.card A ≤ ((leftNeighbors G b).card : ℝ))
    (hexpand : IsBipartiteRobustExpander G θ τ)
    (ℓ : ℕ) (hℓ : Nat.ceil (2 / θ) + 2 ≤ ℓ)
    (hbudget : (S.card : ℝ) + 2 * Z.card + 2 * ℓ * (uncoveredLeftOutside M S).card ≤
      min θ δ * Fintype.card A / 2 - 1) :
    ∃ N : H.Subgraph,
      N.IsMatching ∧ N.verts = (S : Set (A ⊕ B))ᶜ ∧
      M.verts ⊆ N.verts ∧
      (∀ v w, N.Adj v w → M.Adj v w ∨ G.Adj v w) ∧
      (∀ v ∈ S ∪ Z, (N.spanningCoe ⊓ R).degree v = 0) ∧
      (∀ v, (N.spanningCoe ⊓ R).degree v ≤ 1) ∧
      (∑ v, (N.spanningCoe ⊓ R).degree v ≤
        2 * ℓ * (uncoveredLeftOutside M S).card) := by
  obtain ⟨N, hN, hverts, hcover, hedges, hzero, hdegree, htotal⟩ :=
    exists_completion G R hGR M hM hMR S Z hS hZ hbalance
      θ τ δ hθ hτ hδ hleft hright hexpand ℓ hℓ hbudget
  let N' : H.Subgraph := {
    verts := N.verts
    Adj := N.Adj
    adj_sub := by
      intro v w h
      rcases hedges v w h with h | h
      · exact hMH v w h
      · exact hGH h
    edge_vert := N.edge_vert
    symm := N.symm
  }
  exact ⟨N', hN.1, hverts, hcover, hedges, hzero, hdegree, htotal⟩

omit [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] in
/-- Every completion using only old matching edges and available graph
edges avoids any graph avoided by both inputs. -/
theorem completion_avoids_graph
    (G H : SimpleGraph (A ⊕ B))
    (M N : (⊤ : SimpleGraph (A ⊕ B)).Subgraph)
    (hedges : ∀ v w, N.Adj v w → M.Adj v w ∨ G.Adj v w)
    (hM : ∀ v w, M.Adj v w → ¬H.Adj v w)
    (hG : ∀ v w, G.Adj v w → ¬H.Adj v w) :
    ∀ v w, N.Adj v w → ¬H.Adj v w := by
  intro v w h
  rcases hedges v w h with h | h
  · exact hM v w h
  · exact hG v w h

end Overfull.BipartiteMatchingCompletion
