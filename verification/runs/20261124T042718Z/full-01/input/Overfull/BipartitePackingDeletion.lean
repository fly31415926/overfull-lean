import Overfull.BipartitePackingAccounting
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-!
# Vertex deletion in the two sides of a bipartite graph

Deleting vertices leaves a graph on the sum of the two remaining sides.
This description is isomorphic to the literal induced subgraph, and the
maps below preserve degrees and actual matching edges.
-/

set_option maxHeartbeats 800000

namespace Overfull.BipartitePackingDeletion

open Finset Classical SimpleGraph
open scoped BigOperators

variable {A B : Type*}

abbrev RemainingLeft (S : Finset (A ⊕ B)) := {a : A // (Sum.inl a : A ⊕ B) ∉ S}

abbrev RemainingRight (S : Finset (A ⊕ B)) := {b : B // (Sum.inr b : A ⊕ B) ∉ S}

/-- Forget the two subtype proofs while retaining which side contains the vertex. -/
def remainingVertex (S : Finset (A ⊕ B)) :
    RemainingLeft S ⊕ RemainingRight S ↪ A ⊕ B where
  toFun
    | .inl a => .inl a.val
    | .inr b => .inr b.val
  inj' := by
    rintro (a | b) (a' | b') h
    · exact congrArg Sum.inl (Subtype.ext (Sum.inl.inj h))
    · cases h
    · cases h
    · exact congrArg Sum.inr (Subtype.ext (Sum.inr.inj h))

@[simp] theorem remainingVertex_inl (S : Finset (A ⊕ B)) (a : RemainingLeft S) :
    remainingVertex S (.inl a) = .inl a.val := rfl

@[simp] theorem remainingVertex_inr (S : Finset (A ⊕ B)) (b : RemainingRight S) :
    remainingVertex S (.inr b) = .inr b.val := rfl

theorem remainingVertex_not_mem (S : Finset (A ⊕ B))
    (v : RemainingLeft S ⊕ RemainingRight S) : remainingVertex S v ∉ S := by
  cases v with
  | inl a => exact a.property
  | inr b => exact b.property

/-- The sum of the side complements is the complement in the sum. -/
def sideDeletionEquiv (S : Finset (A ⊕ B)) :
    RemainingLeft S ⊕ RemainingRight S ≃ ↥((↑S : Set (A ⊕ B))ᶜ) where
  toFun v := ⟨remainingVertex S v, remainingVertex_not_mem S v⟩
  invFun v := match v with
    | ⟨.inl a, ha⟩ => .inl ⟨a, ha⟩
    | ⟨.inr b, hb⟩ => .inr ⟨b, hb⟩
  left_inv := by rintro (a | b) <;> rfl
  right_inv := by rintro ⟨a | b, h⟩ <;> rfl

@[simp] theorem sideDeletionEquiv_val (S : Finset (A ⊕ B))
    (v : RemainingLeft S ⊕ RemainingRight S) :
    (sideDeletionEquiv S v).val = remainingVertex S v := rfl

def deletedGraph (G : SimpleGraph (A ⊕ B)) (S : Finset (A ⊕ B)) :
    SimpleGraph (RemainingLeft S ⊕ RemainingRight S) := G.comap (remainingVertex S)

@[simp] theorem deletedGraph_adj (G : SimpleGraph (A ⊕ B)) (S : Finset (A ⊕ B))
    (v w : RemainingLeft S ⊕ RemainingRight S) :
    (deletedGraph G S).Adj v w ↔ G.Adj (remainingVertex S v) (remainingVertex S w) := Iff.rfl

def deletedGraphIso (G : SimpleGraph (A ⊕ B)) (S : Finset (A ⊕ B)) :
    deletedGraph G S ≃g G.induce (↑S : Set (A ⊕ B))ᶜ where
  toEquiv := sideDeletionEquiv S
  map_rel_iff' := Iff.rfl

theorem deletedGraph_bipartite (G : SimpleGraph (A ⊕ B)) (S : Finset (A ⊕ B))
    (hbip : G.IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr)) :
    (deletedGraph G S).IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr) := by
  constructor
  · rw [Set.disjoint_left]
    rintro _ ⟨a, rfl⟩ ⟨b, h⟩
    cases h
  · rintro (a | b) (a' | b') hadj
    · exfalso
      simpa using hbip.mem_of_adj hadj
    · exact Or.inl ⟨⟨a, rfl⟩, ⟨b', rfl⟩⟩
    · exact Or.inr ⟨⟨b, rfl⟩, ⟨a', rfl⟩⟩
    · exfalso
      simpa using hbip.mem_of_adj hadj

variable [Fintype A] [Fintype B]

theorem deletedGraph_degree (G : SimpleGraph (A ⊕ B)) (S : Finset (A ⊕ B))
    (v : RemainingLeft S ⊕ RemainingRight S) :
    (deletedGraph G S).degree v =
      (G.induce (↑S : Set (A ⊕ B))ᶜ).degree (sideDeletionEquiv S v) := by
  rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
  exact Fintype.card_congr ((deletedGraphIso G S).mapNeighborSet v)

omit [Fintype B] in
theorem remainingLeft_card_le (S : Finset (A ⊕ B)) :
    Fintype.card (RemainingLeft S) ≤ Fintype.card A := Fintype.card_subtype_le _

omit [Fintype A] in
theorem remainingRight_card_le (S : Finset (A ⊕ B)) :
    Fintype.card (RemainingRight S) ≤ Fintype.card B := Fintype.card_subtype_le _

/-- Balanced deletion preserves equality of the side sizes. -/
theorem remaining_sides_balanced (S : Finset (A ⊕ B))
    (hAB : Fintype.card A = Fintype.card B)
    (hS : (univ.filter (fun a : A => (Sum.inl a : A ⊕ B) ∈ S)).card =
      (univ.filter (fun b : B => (Sum.inr b : A ⊕ B) ∈ S)).card) :
    Fintype.card (RemainingLeft S) = Fintype.card (RemainingRight S) := by
  unfold RemainingLeft RemainingRight
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl,
    Fintype.card_subtype, Fintype.card_subtype, hAB, hS]

omit [Fintype A] [Fintype B] in
def liftMatching (G : SimpleGraph (A ⊕ B)) (S : Finset (A ⊕ B))
    (M : (deletedGraph G S).Subgraph) : G.Subgraph :=
  M.map (SimpleGraph.Embedding.comap (remainingVertex S) G).toHom

omit [Fintype A] [Fintype B] in
theorem liftMatching_isMatching (G : SimpleGraph (A ⊕ B)) (S : Finset (A ⊕ B))
    (M : (deletedGraph G S).Subgraph) (hM : M.IsMatching) :
    (liftMatching G S M).IsMatching :=
  hM.map _ (remainingVertex S).injective

omit [Fintype A] [Fintype B] in
theorem liftMatching_verts (G : SimpleGraph (A ⊕ B)) (S : Finset (A ⊕ B))
    (M : (deletedGraph G S).Subgraph) :
    (liftMatching G S M).verts = remainingVertex S '' M.verts := rfl

omit [Fintype A] [Fintype B] in
theorem liftMatching_adj (G : SimpleGraph (A ⊕ B)) (S : Finset (A ⊕ B))
    (M : (deletedGraph G S).Subgraph) (v w : RemainingLeft S ⊕ RemainingRight S) :
    (liftMatching G S M).Adj (remainingVertex S v) (remainingVertex S w) ↔ M.Adj v w := by
  constructor
  · rintro ⟨x, y, hxy, hx, hy⟩
    have hx' : x = v := (remainingVertex S).injective hx
    have hy' : y = w := (remainingVertex S).injective hy
    simpa only [hx', hy'] using hxy
  · intro hvw
    exact ⟨v, w, hvw, rfl, rfl⟩

omit [Fintype A] [Fintype B] in
theorem liftMatching_verts_subset (G : SimpleGraph (A ⊕ B)) (S : Finset (A ⊕ B))
    (M : (deletedGraph G S).Subgraph) :
    (liftMatching G S M).verts ⊆ (↑S : Set (A ⊕ B))ᶜ := by
  rintro v ⟨w, _, rfl⟩
  exact remainingVertex_not_mem S w

omit [Fintype A] [Fintype B] in
theorem liftMatching_perfect_verts (G : SimpleGraph (A ⊕ B)) (S : Finset (A ⊕ B))
    (M : (deletedGraph G S).Subgraph) (hM : M.IsPerfectMatching) :
    (liftMatching G S M).verts = (↑S : Set (A ⊕ B))ᶜ := by
  apply Set.Subset.antisymm (liftMatching_verts_subset G S M)
  intro v hv
  obtain ⟨w, hw⟩ := (sideDeletionEquiv S).surjective ⟨v, hv⟩
  refine ⟨w, ?_, ?_⟩
  · exact hM.2 w
  · exact congrArg Subtype.val hw

omit [Fintype A] [Fintype B] in
theorem liftMatching_mem_verts (G : SimpleGraph (A ⊕ B)) (S : Finset (A ⊕ B))
    (M : (deletedGraph G S).Subgraph) (v : RemainingLeft S ⊕ RemainingRight S) :
    remainingVertex S v ∈ (liftMatching G S M).verts ↔ v ∈ M.verts := by
  constructor
  · rintro ⟨w, hw, hwv⟩
    have : w = v := (remainingVertex S).injective hwv
    simpa only [this] using hw
  · intro hv
    exact ⟨v, hv, rfl⟩

omit [Fintype B] in
theorem liftMatching_uncoveredLeft_card (G : SimpleGraph (A ⊕ B)) (S : Finset (A ⊕ B))
    (M : (deletedGraph G S).Subgraph) :
    (univ.filter (fun a : A => (.inl a : A ⊕ B) ∉ S ∧
      (.inl a : A ⊕ B) ∉ (liftMatching G S M).verts)).card =
      (univ.filter (fun a : RemainingLeft S =>
        (.inl a : RemainingLeft S ⊕ RemainingRight S) ∉ M.verts)).card := by
  symm
  apply Finset.card_bij (fun (a : RemainingLeft S) _ => a.val)
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    refine ⟨a.property, ?_⟩
    intro hv
    exact ha ((liftMatching_mem_verts G S M (.inl a)).mp hv)
  · intro a _ a' _ haa'
    exact Subtype.ext haa'
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    refine ⟨⟨a, ha.1⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro hM
    exact ha.2 ((liftMatching_mem_verts G S M (.inl ⟨a, ha.1⟩)).mpr hM)

omit [Fintype A] in
theorem liftMatching_uncoveredRight_card (G : SimpleGraph (A ⊕ B)) (S : Finset (A ⊕ B))
    (M : (deletedGraph G S).Subgraph) :
    (univ.filter (fun b : B => (.inr b : A ⊕ B) ∉ S ∧
      (.inr b : A ⊕ B) ∉ (liftMatching G S M).verts)).card =
      (univ.filter (fun b : RemainingRight S =>
        (.inr b : RemainingLeft S ⊕ RemainingRight S) ∉ M.verts)).card := by
  symm
  apply Finset.card_bij (fun (b : RemainingRight S) _ => b.val)
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    refine ⟨b.property, ?_⟩
    intro hv
    exact hb ((liftMatching_mem_verts G S M (.inr b)).mp hv)
  · intro b _ b' _ hbb'
    exact Subtype.ext hbb'
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    refine ⟨⟨b, hb.1⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro hM
    exact hb.2 ((liftMatching_mem_verts G S M (.inr ⟨b, hb.1⟩)).mpr hM)

end Overfull.BipartitePackingDeletion
