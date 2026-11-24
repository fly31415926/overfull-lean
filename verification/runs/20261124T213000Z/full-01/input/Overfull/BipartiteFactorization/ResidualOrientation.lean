import Overfull.Konig
import Overfull.ColorClasses
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-!
# Balanced orientations of actual bipartite residual graphs

An even-regular bipartite simple graph is split into two regular spanning
subgraphs by the proved König coloring theorem. Orienting the first from the
left side to the right side and the second in the opposite direction gives
an actual orientation with equal prescribed indegrees and outdegrees. This
is a construction on the bipartite residual only, not a factorization of an
ambient multigraph containing that residual.
-/

noncomputable section

namespace Overfull.BipartiteFactorization

open Finset Classical

variable {V A B : Type*}

/-- The spanning simple graph consisting of the colors in an actual palette. -/
def paletteGraph {G : SimpleGraph V} {k : ℕ} (c : Overfull.EdgeColoring G k)
    (I : Finset (Fin k)) : SimpleGraph V where
  Adj u v := ∃ h : G.Adj u v, c.color (⟨s(u, v), h⟩ : G.edgeSet) ∈ I
  symm := by
    intro u v h
    obtain ⟨huv, hc⟩ := h
    refine ⟨huv.symm, ?_⟩
    have he : (⟨s(v, u), huv.symm⟩ : G.edgeSet) = ⟨s(u, v), huv⟩ :=
      Subtype.ext Sym2.eq_swap
    rwa [he]
  loopless := by
    intro v h
    exact G.loopless v h.choose

theorem paletteGraph_le {G : SimpleGraph V} {k : ℕ}
    (c : Overfull.EdgeColoring G k) (I : Finset (Fin k)) : paletteGraph c I ≤ G := by
  intro u v h
  exact h.choose

/-- Complementary palettes partition exactly the edges of the original graph. -/
theorem paletteGraph_union {G : SimpleGraph V} {k : ℕ}
    (c : Overfull.EdgeColoring G k) (I : Finset (Fin k)) :
    paletteGraph c I ⊔ paletteGraph c Iᶜ = G := by
  ext u v
  constructor
  · rintro (h | h)
    · exact h.choose
    · exact h.choose
  · intro h
    by_cases hc : c.color (⟨s(u, v), h⟩ : G.edgeSet) ∈ I
    · exact Or.inl ⟨h, hc⟩
    · exact Or.inr ⟨h, mem_compl.mpr hc⟩

/-- No original edge appears in the two complementary palette subgraphs. -/
theorem paletteGraph_disjoint {G : SimpleGraph V} {k : ℕ}
    (c : Overfull.EdgeColoring G k) (I : Finset (Fin k)) :
    Disjoint (paletteGraph c I) (paletteGraph c Iᶜ) := by
  apply disjoint_iff.mpr
  ext u v
  simp only [SimpleGraph.inf_adj, SimpleGraph.bot_adj, iff_false]
  rintro ⟨⟨h, hi⟩, ⟨h', hj⟩⟩
  exact (mem_compl.mp hj) hi

/-- At a saturated vertex each palette contributes exactly its cardinality. -/
theorem paletteGraph_degree [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {k : ℕ} (c : Overfull.EdgeColoring G k)
    (I : Finset (Fin k)) (v : V) (hv : G.degree v = k) :
    (paletteGraph c I).degree v = I.card := by
  let f : (paletteGraph c I).neighborSet v → I := fun u =>
    ⟨c.color ⟨s(v, u.val), u.property.choose⟩, u.property.choose_spec⟩
  have hbij := c.neighborColor_bijective_of_degree_eq v hv
  have hf : Function.Bijective f := by
    constructor
    · intro u w h
      have hc := congrArg Subtype.val h
      have he := hbij.1 (a₁ := ⟨u.val, u.property.choose⟩)
        (a₂ := ⟨w.val, w.property.choose⟩) hc
      exact Subtype.ext (congrArg (fun z : G.neighborSet v => z.val) he)
    · intro i
      obtain ⟨u, hu⟩ := hbij.2 i.val
      dsimp only at hu
      have hi : c.color (⟨s(v, u.val), u.property⟩ : G.edgeSet) ∈ I := by
        rw [hu]
        exact i.property
      refine ⟨⟨u.val, ⟨u.property, hi⟩⟩, ?_⟩
      exact Subtype.ext hu
  have hc := Fintype.card_congr (Equiv.ofBijective f hf)
  simpa only [SimpleGraph.card_neighborSet_eq_degree, Fintype.card_coe] using hc

/-- The unordered-edge model of a graph with specified bipartite sides is
bipartite in the finite multigraph interface used by König's theorem. -/
theorem ofSimpleGraph_bipartite (G : SimpleGraph (A ⊕ B))
    (hG : G.IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr)) :
    (Multigraph.ofSimpleGraph G).IsBipartite := by
  let M := Multigraph.ofSimpleGraph G
  refine ⟨fun v => v.isLeft, ?_⟩
  intro e
  have he : G.Adj (M.firstEnd e) (M.secondEnd e) := by
    have h := e.property
    change M.edge e ∈ G.edgeSet at h
    rw [← M.edge_eq e] at h
    exact h
  rcases hG.mem_of_adj he with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ | ⟨⟨b, hb⟩, ⟨a, ha⟩⟩
  · rw [← ha, ← hb]
    simp
  · rw [← hb, ← ha]
    simp

/-- Two actual regular spanning graphs specify opposite directions for each
edge of the even-regular bipartite residual. -/
structure ResidualOrientation [Fintype A] [Fintype B]
    (G : SimpleGraph (A ⊕ B)) (r : ℕ) where
  forward : SimpleGraph (A ⊕ B)
  backward : SimpleGraph (A ⊕ B)
  forward_le : forward ≤ G
  backward_le : backward ≤ G
  union_eq : forward ⊔ backward = G
  disjoint : Disjoint forward backward
  forward_degree : ∀ v, forward.degree v = r
  backward_degree : ∀ v, backward.degree v = r
  bipartite : G.IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr)

/-- The proved König theorem splits every even-regular bipartite residual
into two actual `r`-regular spanning graphs. The zero-degree case is included. -/
theorem exists_regular_bipartite_orientation [Fintype A] [Fintype B]
    (G : SimpleGraph (A ⊕ B)) [DecidableRel G.Adj] (r : ℕ)
    (hG : G.IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr))
    (hdegree : ∀ v, G.degree v = 2 * r) :
    Nonempty (ResidualOrientation G r) := by
  obtain ⟨cM⟩ := (Multigraph.ofSimpleGraph G).exists_edgeColoring_of_bipartite
    (ofSimpleGraph_bipartite G hG) (2 * r) (by
      intro v
      simpa only [Multigraph.ofSimpleGraph_degree, hdegree] using (le_refl (2 * r)))
  let c : Overfull.EdgeColoring G (2 * r) :=
    ⟨cM.color, fun he hf hc => cM.proper hc he hf⟩
  obtain ⟨I, _, hI⟩ := (univ : Finset (Fin (2 * r))).exists_subset_card_eq
    (show r ≤ (univ : Finset (Fin (2 * r))).card by simp; omega)
  have hIc : Iᶜ.card = r := by
    have h := card_compl_add_card I
    simp only [Fintype.card_fin] at h
    omega
  exact ⟨{
    forward := paletteGraph c I
    backward := paletteGraph c Iᶜ
    forward_le := paletteGraph_le c I
    backward_le := paletteGraph_le c Iᶜ
    union_eq := paletteGraph_union c I
    disjoint := paletteGraph_disjoint c I
    forward_degree := fun v => (paletteGraph_degree c I v (hdegree v)).trans hI
    backward_degree := fun v => (paletteGraph_degree c Iᶜ v (hdegree v)).trans hIc
    bipartite := hG }⟩


namespace ResidualOrientation

variable [Fintype A] [Fintype B] {G : SimpleGraph (A ⊕ B)} {r : ℕ}
variable (D : ResidualOrientation G r)

/-- An actual directed arc, with one direction chosen for each residual edge. -/
def arc : (A ⊕ B) → (A ⊕ B) → Prop
  | .inl a, .inr b => D.forward.Adj (.inl a) (.inr b)
  | .inr b, .inl a => D.backward.Adj (.inr b) (.inl a)
  | _, _ => False

/-- Actual outgoing neighbors in the constructed orientation. -/
def outNeighbors (v : A ⊕ B) : Finset (A ⊕ B) := univ.filter (D.arc v)

/-- Actual incoming neighbors in the constructed orientation. -/
def inNeighbors (v : A ⊕ B) : Finset (A ⊕ B) := univ.filter (fun u => D.arc u v)

def outDegree (v : A ⊕ B) : ℕ := (D.outNeighbors v).card

def inDegree (v : A ⊕ B) : ℕ := (D.inNeighbors v).card

include D in
private theorem no_left (a a' : A) : ¬ G.Adj (.inl a) (.inl a') := by
  intro h
  have ht := D.bipartite.mem_of_mem_adj (show (.inl a : A ⊕ B) ∈ Set.range Sum.inl
    from ⟨a, rfl⟩) h
  rcases ht with ⟨b, hb⟩
  cases hb

include D in
private theorem no_right (b b' : B) : ¬ G.Adj (.inr b) (.inr b') := by
  intro h
  have ht := D.bipartite.symm.mem_of_mem_adj
    (show (.inr b : A ⊕ B) ∈ Set.range Sum.inr from ⟨b, rfl⟩) h
  rcases ht with ⟨a, ha⟩
  cases ha

/-- Arcs out of a left vertex are exactly its forward-subgraph edges. -/
theorem arc_from_left (a : A) (v : A ⊕ B) :
    D.arc (.inl a) v ↔ D.forward.Adj (.inl a) v := by
  cases v with
  | inl a' =>
      exact iff_of_false id (fun h => D.no_left a a' (D.forward_le h))
  | inr b => rfl

/-- Arcs into a left vertex are exactly its backward-subgraph edges. -/
theorem arc_to_left (a : A) (v : A ⊕ B) :
    D.arc v (.inl a) ↔ D.backward.Adj (.inl a) v := by
  cases v with
  | inl a' =>
      exact iff_of_false id (fun h => D.no_left a a' (D.backward_le h))
  | inr b => exact ⟨fun h => h.symm, fun h => h.symm⟩

/-- Arcs out of a right vertex are exactly its backward-subgraph edges. -/
theorem arc_from_right (b : B) (v : A ⊕ B) :
    D.arc (.inr b) v ↔ D.backward.Adj (.inr b) v := by
  cases v with
  | inl a => rfl
  | inr b' =>
      exact iff_of_false id (fun h => D.no_right b b' (D.backward_le h))

/-- Arcs into a right vertex are exactly its forward-subgraph edges. -/
theorem arc_to_right (b : B) (v : A ⊕ B) :
    D.arc v (.inr b) ↔ D.forward.Adj (.inr b) v := by
  cases v with
  | inl a => exact ⟨fun h => h.symm, fun h => h.symm⟩
  | inr b' =>
      exact iff_of_false id (fun h => D.no_right b b' (D.forward_le h))

/-- Every arc comes from an actual edge of the original residual. -/
theorem arc_subgraph {u v : A ⊕ B} (h : D.arc u v) : G.Adj u v := by
  cases u with
  | inl a => exact D.forward_le ((D.arc_from_left a v).mp h)
  | inr b => exact D.backward_le ((D.arc_from_right b v).mp h)

/-- Every original edge is oriented, and no nonedge is introduced. -/
theorem edge_iff_arc (u v : A ⊕ B) :
    G.Adj u v ↔ D.arc u v ∨ D.arc v u := by
  constructor
  · intro h
    have hh : D.forward.Adj u v ∨ D.backward.Adj u v := by
      change (D.forward ⊔ D.backward).Adj u v
      rwa [D.union_eq]
    cases u with
    | inl a =>
        rcases hh with hf | hb
        · exact Or.inl ((D.arc_from_left a v).mpr hf)
        · exact Or.inr ((D.arc_to_left a v).mpr hb)
    | inr b =>
        rcases hh with hf | hb
        · exact Or.inr ((D.arc_to_right b v).mpr hf)
        · exact Or.inl ((D.arc_from_right b v).mpr hb)
  · rintro (h | h)
    · exact D.arc_subgraph h
    · exact (D.arc_subgraph h).symm

/-- The two possible orientations of an edge cannot both occur. -/
theorem arc_asymm {u v : A ⊕ B} (h : D.arc u v) : ¬ D.arc v u := by
  intro h'
  have hnot (x y : A ⊕ B) : ¬ (D.forward.Adj x y ∧ D.backward.Adj x y) := by
    intro hh
    have hi : (D.forward ⊓ D.backward).Adj x y := hh
    rw [disjoint_iff.mp D.disjoint] at hi
    exact hi
  cases u with
  | inl a =>
      exact hnot (.inl a) v
        ⟨(D.arc_from_left a v).mp h, (D.arc_to_left a v).mp h'⟩
  | inr b =>
      exact hnot (.inr b) v
        ⟨(D.arc_to_right b v).mp h', (D.arc_from_right b v).mp h⟩

theorem arc_irrefl (v : A ⊕ B) : ¬ D.arc v v := by
  intro h
  exact G.loopless v (D.arc_subgraph h)

theorem outNeighbors_left (a : A) :
    D.outNeighbors (.inl a) = D.forward.neighborFinset (.inl a) := by
  ext v
  simp only [outNeighbors, mem_filter, mem_univ, true_and, SimpleGraph.mem_neighborFinset]
  exact D.arc_from_left a v

theorem inNeighbors_left (a : A) :
    D.inNeighbors (.inl a) = D.backward.neighborFinset (.inl a) := by
  ext v
  simp only [inNeighbors, mem_filter, mem_univ, true_and, SimpleGraph.mem_neighborFinset]
  exact D.arc_to_left a v

theorem outNeighbors_right (b : B) :
    D.outNeighbors (.inr b) = D.backward.neighborFinset (.inr b) := by
  ext v
  simp only [outNeighbors, mem_filter, mem_univ, true_and, SimpleGraph.mem_neighborFinset]
  exact D.arc_from_right b v

theorem inNeighbors_right (b : B) :
    D.inNeighbors (.inr b) = D.forward.neighborFinset (.inr b) := by
  ext v
  simp only [inNeighbors, mem_filter, mem_univ, true_and, SimpleGraph.mem_neighborFinset]
  exact D.arc_to_right b v

/-- The outgoing degree counts actual arcs and is exactly half the
undirected degree at every vertex. -/
theorem outDegree_eq (v : A ⊕ B) : D.outDegree v = r := by
  cases v with
  | inl a =>
      rw [outDegree, D.outNeighbors_left, SimpleGraph.card_neighborFinset_eq_degree]
      exact D.forward_degree _
  | inr b =>
      rw [outDegree, D.outNeighbors_right, SimpleGraph.card_neighborFinset_eq_degree]
      exact D.backward_degree _

/-- The incoming degree counts actual arcs and is exactly half the
undirected degree at every vertex. -/
theorem inDegree_eq (v : A ⊕ B) : D.inDegree v = r := by
  cases v with
  | inl a =>
      rw [inDegree, D.inNeighbors_left, SimpleGraph.card_neighborFinset_eq_degree]
      exact D.backward_degree _
  | inr b =>
      rw [inDegree, D.inNeighbors_right, SimpleGraph.card_neighborFinset_eq_degree]
      exact D.forward_degree _

end ResidualOrientation

end Overfull.BipartiteFactorization
