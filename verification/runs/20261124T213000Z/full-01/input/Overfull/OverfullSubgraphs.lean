import Overfull.Basic
import Overfull.CutCounting
import Overfull.Relabeling
import Mathlib.Combinatorics.SimpleGraph.Subgraph

/-!
# Overfull vertex sets and overfull subgraphs

The manuscript asks for an intrinsically overfull subgraph whose maximum degree
is the maximum degree of its host. The main formal specification instead uses
an overfull vertex set at the host's degree parameter. This file proves their
exact equivalence for finite simple graphs.
-/

namespace Overfull

open Finset Classical

variable {V W : Type*} [Fintype V] [Fintype W]
variable {G : SimpleGraph V} {H : SimpleGraph W}

/-- A graph is intrinsically overfull when its actual number of edges exceeds
the matching bound using its own maximum degree and its own vertex count. -/
noncomputable def IsOverfullGraph (G : SimpleGraph V) : Prop :=
  G.maxDegree * (Fintype.card V / 2) < G.edgeFinset.card

/-- The internal edges of the entire vertex set are exactly all actual edges. -/
theorem internalEdges_univ_card (G : SimpleGraph V) :
    (internalEdges G (univ : Finset V)).card = G.edgeFinset.card := by
  simp [internalEdges]

theorem isOverfullGraph_iff_univ :
    IsOverfullGraph G ↔ IsOverfull G G.maxDegree (univ : Finset V) := by
  simp only [IsOverfullGraph, IsOverfull, Finset.card_univ, internalEdges_univ_card]

/-- Intrinsic overfullness is invariant under graph isomorphism. -/
theorem isOverfullGraph_iso_iff (f : H ≃g G) :
    IsOverfullGraph H ↔ IsOverfullGraph G := by
  unfold IsOverfullGraph
  rw [iso_maxDegree_eq f, Fintype.card_congr f.toEquiv,
    SimpleGraph.Iso.card_edgeFinset_eq f]

/-- The edge count of the induced graph on `X` is the number of actual edges
of the host with both endpoints in `X`. -/
theorem induced_edgeFinset_card (G : SimpleGraph V) (X : Finset V) :
    (G.induce (X : Set V)).edgeFinset.card = (internalEdges G X).card := by
  have himage : (internalEdges G X).image Subtype.val = G.edgeFinset ∩ X.sym2 := by
    ext e
    obtain ⟨v, w⟩ := e
    simp [internalEdges, Sym2.toFinset_mk_eq, Finset.insert_subset_iff,
      Finset.singleton_subset_iff, and_comm]
  have hmap' : (G.induce (X : Set V)).edgeFinset.map
      (Function.Embedding.subtype (X : Set V)).sym2Map = G.edgeFinset ∩ X.sym2 := by
    simp_rw [Finset.ext_iff, Sym2.forall, Finset.mem_inter, Finset.mk_mem_sym2_iff,
      Finset.mem_map, Sym2.exists, SimpleGraph.mem_edgeFinset,
      SimpleGraph.mem_edgeSet, SimpleGraph.comap_adj,
      Function.Embedding.sym2Map_apply, Function.Embedding.coe_subtype,
      Sym2.map_pair_eq, Sym2.eq_iff]
    intro v w
    constructor
    · rintro ⟨x, y, hadj, ⟨hv, hw⟩ | ⟨hw, hv⟩⟩
      all_goals rw [← hv, ← hw]
      · exact ⟨hadj, x.property, y.property⟩
      · exact ⟨hadj.symm, y.property, x.property⟩
    · rintro ⟨hadj, hv, hw⟩
      exact ⟨⟨v, hv⟩, ⟨w, hw⟩, hadj, Or.inl ⟨rfl, rfl⟩⟩
  calc
    (G.induce (X : Set V)).edgeFinset.card =
        ((G.induce (X : Set V)).edgeFinset.map
          (Function.Embedding.subtype (X : Set V)).sym2Map).card :=
      (Finset.card_map _).symm
    _ = (G.edgeFinset ∩ X.sym2).card := congrArg Finset.card hmap'
    _ = ((internalEdges G X).image Subtype.val).card :=
      congrArg Finset.card himage.symm
    _ = (internalEdges G X).card :=
      Finset.card_image_of_injective _ Subtype.val_injective

/-- An injective graph homomorphism cannot decrease the number of internal
edges after the vertex set is mapped into the host. -/
theorem internalEdges_card_le_of_injective_hom (f : H →g G)
    (hf : Function.Injective f) (X : Finset W) :
    (internalEdges H X).card ≤
      (internalEdges G (X.map (⟨f, hf⟩ : W ↪ V))).card := by
  apply Finset.card_le_card_of_injOn f.mapEdgeSet
  · intro e he
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hX := (Finset.mem_filter.mp he).2
    intro v hv
    have hv' : v ∈ Sym2.map f e.val := Sym2.mem_toFinset.mp hv
    obtain ⟨w, hw, rfl⟩ := Sym2.mem_map.mp hv'
    exact Finset.mem_map.mpr ⟨w, hX (Sym2.mem_toFinset.mpr hw), rfl⟩
  · intro e he d hd hed
    exact SimpleGraph.Hom.mapEdgeSet.injective f hf hed

/-- Maximum degree is bounded by the host's maximum degree under an injective
graph homomorphism, including for edge subgraphs that are not induced. -/
theorem maxDegree_le_of_injective_hom (f : H →g G) (hf : Function.Injective f) :
    H.maxDegree ≤ G.maxDegree := by
  apply H.maxDegree_le_of_forall_degree_le
  intro v
  have hinj : Function.Injective (f.mapNeighborSet v) := by
    intro u w h
    apply Subtype.ext
    exact hf (congrArg (fun a : G.neighborSet (f v) => a.val) h)
  have hcard := Fintype.card_le_of_injective (f.mapNeighborSet v) hinj
  have hdeg : H.degree v ≤ G.degree (f v) := by
    simpa only [SimpleGraph.card_neighborSet_eq_degree] using hcard
  exact hdeg.trans (G.degree_le_maxDegree (f v))

omit [Fintype W] in
/-- In a simple graph, exceeding the matching bound at any parameter at least
its maximum degree forces that parameter to be its actual maximum degree.
The conclusion uses both the graph degree sum and the simple-graph order bound. -/
theorem maxDegree_eq_of_overfull_bound (G : SimpleGraph V) (k : ℕ)
    (hmax : G.maxDegree ≤ k)
    (hover : k * (Fintype.card V / 2) < G.edgeFinset.card) : G.maxDegree = k := by
  have hsum : 2 * G.edgeFinset.card ≤ G.maxDegree * Fintype.card V := by
    simpa only [internalEdges_univ_card, Finset.card_univ] using
      internal_edges_le_degree_bound G univ G.maxDegree G.degree_le_maxDegree
  have hsumk : 2 * G.edgeFinset.card ≤ k * Fintype.card V :=
    hsum.trans (Nat.mul_le_mul_right _ hmax)
  have hodd : Fintype.card V % 2 = 1 := by
    by_contra h
    have heven : Fintype.card V = 2 * (Fintype.card V / 2) := by omega
    rw [heven] at hsumk
    nlinarith
  have horder : G.maxDegree ≤ Fintype.card V - 1 := by
    apply G.maxDegree_le_of_forall_degree_le
    intro v
    exact Nat.le_sub_one_of_lt (G.degree_lt_card_verts v)
  apply Nat.le_antisymm hmax
  by_contra h
  have hlt : G.maxDegree + 1 ≤ k := by omega
  have hsub : Fintype.card V - 1 = 2 * (Fintype.card V / 2) := by omega
  have hprod : G.maxDegree * Fintype.card V ≤ k * (Fintype.card V - 1) := by
    have hpos : 1 ≤ Fintype.card V := by omega
    calc
      G.maxDegree * Fintype.card V =
          G.maxDegree * ((Fintype.card V - 1) + 1) := by
        rw [Nat.sub_add_cancel hpos]
      _ = G.maxDegree * (Fintype.card V - 1) + G.maxDegree := by ring
      _ ≤ G.maxDegree * (Fintype.card V - 1) + (Fintype.card V - 1) :=
        Nat.add_le_add_left horder _
      _ = (G.maxDegree + 1) * (Fintype.card V - 1) := by ring
      _ ≤ k * (Fintype.card V - 1) := Nat.mul_le_mul_right _ hlt
  rw [hsub] at hprod
  nlinarith

omit [Fintype W] in
/-- A host-degree-overfull vertex set induces an intrinsically overfull graph
of exactly the same maximum degree as the host. -/
theorem overfull_induce_same_maxDegree (X : Finset V)
    (hX : IsOverfull G G.maxDegree X) :
    (G.induce (X : Set V)).maxDegree = G.maxDegree ∧
      IsOverfullGraph (G.induce (X : Set V)) := by
  have hcount : G.maxDegree * (Fintype.card (X : Set V) / 2) <
      (G.induce (X : Set V)).edgeFinset.card := by
    have hcard : Fintype.card (X : Set V) = X.card :=
      @Fintype.card_coe V X (inferInstance : Fintype (X : Set V))
    rw [hcard, induced_edgeFinset_card]
    exact hX
  have hle : (G.induce (X : Set V)).maxDegree ≤ G.maxDegree :=
    maxDegree_le_of_injective_hom
      (SimpleGraph.Embedding.induce (G := G) (X : Set V)).toHom Subtype.val_injective
  have heq := maxDegree_eq_of_overfull_bound (G.induce (X : Set V)) G.maxDegree hle hcount
  refine ⟨heq, ?_⟩
  unfold IsOverfullGraph
  rw [heq]
  exact hcount

/-- Any intrinsically overfull graph mapped injectively into the host, with
the same maximum degree, yields an overfull set consisting of its image vertices.
The homomorphism may omit host edges, so this also covers noninduced subgraphs. -/
theorem overfull_image_of_injective_hom (f : H →g G) (hf : Function.Injective f)
    (hdegree : H.maxDegree = G.maxDegree) (hH : IsOverfullGraph H) :
    IsOverfull G G.maxDegree ((univ : Finset W).map (⟨f, hf⟩ : W ↪ V)) := by
  unfold IsOverfull
  rw [Finset.card_map, Finset.card_univ]
  have hcount := internalEdges_card_le_of_injective_hom f hf (univ : Finset W)
  rw [internalEdges_univ_card] at hcount
  have hbound : G.maxDegree * (Fintype.card W / 2) < H.edgeFinset.card := by
    simpa only [IsOverfullGraph, hdegree] using hH
  exact hbound.trans_le hcount

omit [Fintype W] in
/-- Every genuine mathlib subgraph that is intrinsically overfull and has the
host's maximum degree gives an overfull vertex set in the host. -/
theorem overfull_set_of_same_degree_subgraph (K : G.Subgraph)
    (hdegree : K.coe.maxDegree = G.maxDegree) (hK : IsOverfullGraph K.coe) :
    IsOverfull G G.maxDegree K.verts.toFinset := by
  have h := overfull_image_of_injective_hom K.hom
    SimpleGraph.Subgraph.hom_injective hdegree hK
  have himage : (univ : Finset K.verts).map
      (⟨K.hom, SimpleGraph.Subgraph.hom_injective⟩ : K.verts ↪ V) = K.verts.toFinset := by
    ext v
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Set.mem_toFinset]
    constructor
    · rintro ⟨u, hu⟩
      change u.val = v at hu
      exact hu ▸ u.property
    · intro hv
      exact ⟨⟨v, hv⟩, rfl⟩
  simpa only [himage] using h

omit [Fintype W] in
private theorem same_degree_overfull_of_induced_iso (X : Finset V)
    (hX : IsOverfull G G.maxDegree X) (K : G.Subgraph)
    (f : (G.induce (X : Set V)) ≃g K.coe) :
    K.coe.maxDegree = G.maxDegree ∧ IsOverfullGraph K.coe := by
  obtain ⟨hdegree, hfull⟩ := overfull_induce_same_maxDegree X hX
  exact ⟨(iso_maxDegree_eq f).symm.trans hdegree, (isOverfullGraph_iso_iff f).mp hfull⟩

omit [Fintype W] in
/-- Every overfull vertex set provides a genuine mathlib subgraph with the
same maximum degree and intrinsic overfullness. The witness is induced. -/
theorem exists_same_degree_overfull_subgraph_of_set (X : Finset V)
    (hX : IsOverfull G G.maxDegree X) :
    ∃ K : G.Subgraph, K.coe.maxDegree = G.maxDegree ∧ IsOverfullGraph K.coe := by
  let K := (⊤ : G.Subgraph).induce (X : Set V)
  let f : (G.induce (X : Set V)) ≃g K.coe :=
    { toEquiv := Equiv.refl _
      map_rel_iff' := by
        intro v w
        change (v.val ∈ X ∧ w.val ∈ X ∧ G.Adj v.val w.val) ↔ G.Adj v.val w.val
        exact ⟨fun h => h.2.2, fun h => ⟨v.property, w.property, h⟩⟩ }
  exact ⟨K, same_degree_overfull_of_induced_iso X hX K f⟩

omit [Fintype W] in
/-- The vertex-set formulation is exactly equivalent to the manuscript's
existence of an overfull subgraph with the same maximum degree. -/
theorem exists_overfull_set_iff_same_degree_subgraph :
    (∃ X : Finset V, IsOverfull G G.maxDegree X) ↔
      ∃ K : G.Subgraph, K.coe.maxDegree = G.maxDegree ∧ IsOverfullGraph K.coe := by
  constructor
  · rintro ⟨X, hX⟩
    exact exists_same_degree_overfull_subgraph_of_set X hX
  · rintro ⟨K, hdegree, hK⟩
    exact ⟨K.verts.toFinset, overfull_set_of_same_degree_subgraph K hdegree hK⟩

omit [Fintype W] in
/-- Equivalent absence quantifiers for the two formulations of the overfull
obstruction. The subgraphs here include arbitrary vertex and edge deletions. -/
theorem no_overfull_iff_no_same_degree_overfull_subgraph :
    (∀ X : Finset V, ¬ IsOverfull G G.maxDegree X) ↔
      ∀ K : G.Subgraph, K.coe.maxDegree = G.maxDegree → ¬ IsOverfullGraph K.coe := by
  constructor
  · intro h K hdegree hK
    exact h K.verts.toFinset (overfull_set_of_same_degree_subgraph K hdegree hK)
  · intro h X hX
    obtain ⟨K, hdegree, hK⟩ := exists_same_degree_overfull_subgraph_of_set X hX
    exact h K hdegree hK

omit [Fintype W] in
/-- The no-overfull predicate in `MainTheorem` states precisely that no
intrinsically overfull subgraph of the host's maximum degree exists. -/
theorem no_overfull_iff_not_exists_same_degree_overfull_subgraph :
    (∀ X : Finset V, ¬ IsOverfull G G.maxDegree X) ↔
      ¬ ∃ K : G.Subgraph, K.coe.maxDegree = G.maxDegree ∧ IsOverfullGraph K.coe := by
  rw [← exists_overfull_set_iff_same_degree_subgraph]
  simp only [not_exists]

end Overfull
