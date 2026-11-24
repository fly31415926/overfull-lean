import Overfull.AuxiliaryCompletion.CoreCuts
import Overfull.BipartitePackingAccounting
import Overfull.OverfullSubgraphs

/-!
# Replacing the edges of a graph on a prescribed vertex set

The old and new cores are graphs on the actual subtype of core vertices.
Their ambient lifts have no edges outside that set.
-/

namespace Overfull.Replacement

open Finset Classical SimpleGraph
open scoped BigOperators

variable {V : Type*}

def lift (U : Finset V) (H : SimpleGraph U) : SimpleGraph V :=
  H.map (Function.Embedding.subtype (fun v => v ∈ U))

@[simp] theorem lift_adj (U : Finset V) (H : SimpleGraph U) (v w : U) :
    (lift U H).Adj v.val w.val ↔ H.Adj v w :=
  SimpleGraph.map_adj_apply

theorem lift_adj_mem (U : Finset V) (H : SimpleGraph U) {v w : V}
    (h : (lift U H).Adj v w) : v ∈ U ∧ w ∈ U := by
  obtain ⟨x,y,_hxy,rfl,rfl⟩ := h
  exact ⟨x.property,y.property⟩

theorem lift_le (U : Finset V) (H : SimpleGraph U) (G : SimpleGraph V)
    (hH : H ≤ G.induce (U : Set V)) : lift U H ≤ G := by
  rintro v w ⟨x,y,hxy,rfl,rfl⟩
  exact hH hxy

theorem lift_mono (U : Finset V) {H R : SimpleGraph U} (hHR : H ≤ R) :
    lift U H ≤ lift U R := SimpleGraph.map_monotone _ hHR

variable [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem lift_neighbors (U : Finset V) (H : SimpleGraph U) (v : U) :
    (lift U H).neighborFinset v.val =
      (H.neighborFinset v).map (Function.Embedding.subtype (fun w => w ∈ U)) := by
  ext w
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_map]
  constructor
  · rintro ⟨x,y,hxy,hx,hy⟩
    have hx' : x = v := Subtype.ext hx
    subst x
    exact ⟨y,hxy,hy⟩
  · rintro ⟨y,hy,rfl⟩
    exact (lift_adj U H v y).mpr hy

omit [DecidableEq V] in
theorem lift_degree (U : Finset V) (H : SimpleGraph U) (v : U) :
    (lift U H).degree v.val = H.degree v := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, lift_neighbors, Finset.card_map]
  exact SimpleGraph.card_neighborFinset_eq_degree _ _

omit [DecidableEq V] in
theorem lift_degree_outside (U : Finset V) (H : SimpleGraph U) (v : V) (hv : v ∉ U) :
    (lift U H).degree v = 0 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  exact hv (lift_adj_mem U H ((lift U H).mem_neighborFinset v w |>.mp hw)).1

def core (G : SimpleGraph V) (U : Finset V) (H R : SimpleGraph U) : SimpleGraph U :=
  R \ (G.induce (U : Set V) \ H)

def graph (G : SimpleGraph V) (U : Finset V) (H R : SimpleGraph U) : SimpleGraph V :=
  (G \ lift U H) ⊔ lift U (core G U H R)

omit [Fintype V] [DecidableEq V] in
theorem core_le (G : SimpleGraph V) (U : Finset V) (H R : SimpleGraph U) :
    core G U H R ≤ R := sdiff_le

omit [Fintype V] [DecidableEq V] in
theorem exterior_disjoint_core (G : SimpleGraph V) (U : Finset V)
    (H R : SimpleGraph U) :
    Disjoint (G \ lift U H) (lift U (core G U H R)) := by
  apply disjoint_iff_inf_le.mpr
  intro v w hvw
  obtain ⟨x,y,hxy,rfl,rfl⟩ := hvw.2
  exact hxy.2 ⟨hvw.1.1,fun h => hvw.1.2 ((lift_adj U H x y).mpr h)⟩

omit [Fintype V] [DecidableEq V] in
theorem exterior_le (G : SimpleGraph V) (U : Finset V) (H R : SimpleGraph U) :
    G \ lift U H ≤ graph G U H R := le_sup_left

omit [Fintype V] [DecidableEq V] in
theorem core_lift_le (G : SimpleGraph V) (U : Finset V) (H R : SimpleGraph U) :
    lift U (core G U H R) ≤ graph G U H R := le_sup_right

omit [DecidableEq V] in
theorem graph_degree_identity (G : SimpleGraph V) (U : Finset V) (H R : SimpleGraph U)
    (hH : H ≤ G.induce (U : Set V)) (v : V) :
    (graph G U H R).degree v + (lift U H).degree v =
      G.degree v + (lift U (core G U H R)).degree v := by
  have hs := BipartitePackingAccounting.degree_sup_add_degree_inf
    (G \ lift U H) (lift U (core G U H R)) v
  have hd := BipartitePackingAccounting.degree_sdiff_add_of_le G (lift U H)
    (lift_le U H G hH) v
  have hz : ((G \ lift U H) ⊓ lift U (core G U H R)).degree v = 0 := by
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
    rw [(exterior_disjoint_core G U H R).eq_bot]
    simp
  simp only [graph, ← SimpleGraph.card_neighborSet_eq_degree,
    ← Nat.card_eq_fintype_card] at hs hd hz ⊢
  omega

theorem graph_degree_le (G : SimpleGraph V) (U : Finset V) (H R : SimpleGraph U)
    (hH : H ≤ G.induce (U : Set V)) (hdegree : ∀ v, R.degree v ≤ H.degree v) (v : V) :
    (graph G U H R).degree v ≤ G.degree v := by
  have hh := graph_degree_identity G U H R hH v
  by_cases hv : v ∈ U
  · have hnew : (lift U (core G U H R)).degree v ≤ (lift U H).degree v := by
      rw [lift_degree U (core G U H R) ⟨v,hv⟩, lift_degree U H ⟨v,hv⟩]
      exact ((core G U H R).degree_le_of_le (core_le G U H R)).trans (hdegree ⟨v,hv⟩)
    omega
  · rw [lift_degree_outside U H v hv, lift_degree_outside U (core G U H R) v hv] at hh
    omega

theorem internal_count_eq (G : SimpleGraph V) (X : Finset V) :
    (internalEdges G X).card = (G.edgeFinset ∩ X.sym2).card := by
  have himage : (internalEdges G X).image Subtype.val = G.edgeFinset ∩ X.sym2 := by
    ext e
    obtain ⟨v,w⟩ := e
    simp [internalEdges, Sym2.toFinset_mk_eq, Finset.insert_subset_iff,
      Finset.singleton_subset_iff, and_comm]
  rw [← himage, Finset.card_image_of_injective _ Subtype.val_injective]

theorem internal_count_sup (G H : SimpleGraph V) (hdisj : Disjoint G H) (X : Finset V) :
    (internalEdges (G ⊔ H) X).card = (internalEdges G X).card + (internalEdges H X).card := by
  simp only [internal_count_eq, SimpleGraph.edgeFinset_sup, Finset.union_inter_distrib_right]
  apply Finset.card_union_of_disjoint
  exact (SimpleGraph.disjoint_edgeFinset.mpr hdisj).mono
    Finset.inter_subset_left Finset.inter_subset_left

theorem internal_count_sdiff_add (G H : SimpleGraph V) (hH : H ≤ G) (X : Finset V) :
    (internalEdges (G \ H) X).card + (internalEdges H X).card = (internalEdges G X).card := by
  have heq : G = (G \ H) ⊔ H := by
    ext v w
    simp only [SimpleGraph.sup_adj, SimpleGraph.sdiff_adj]
    constructor
    · intro h
      by_cases hh : H.Adj v w
      · exact Or.inr hh
      · exact Or.inl ⟨h,hh⟩
    · rintro (h | h)
      · exact h.1
      · exact hH h
  have hdisj : Disjoint (G \ H) H :=
    disjoint_iff_inf_le.mpr (fun _ _ h => h.1.2 h.2)
  calc
    _ = (internalEdges ((G \ H) ⊔ H) X).card := (internal_count_sup _ _ hdisj X).symm
    _ = _ := by rw [← heq]

theorem internal_lift_count (U X : Finset V) (H : SimpleGraph U) :
    (internalEdges (lift U H) X).card = (internalEdges H (SmallCuts.shore U X)).card := by
  rw [internal_count_eq, internal_count_eq]
  let f := (Function.Embedding.subtype (fun v => v ∈ U)).sym2Map
  have heq : (H.edgeFinset ∩ (SmallCuts.shore U X).sym2).map f =
      (lift U H).edgeFinset ∩ X.sym2 := by
    ext e
    obtain ⟨v,w⟩ := e
    simp only [f, Finset.mem_map, Finset.mem_inter, SimpleGraph.mem_edgeFinset,
      SimpleGraph.mem_edgeSet, Finset.mk_mem_sym2_iff, Sym2.exists,
      Function.Embedding.sym2Map_apply, Sym2.map_pair_eq, Sym2.eq_iff,
      SmallCuts.mem_shore]
    constructor
    · rintro ⟨x,y,⟨hxy,hx,hy⟩,heq⟩
      rcases heq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact ⟨(lift_adj U H x y).mpr hxy,hx,hy⟩
      · exact ⟨(lift_adj U H y x).mpr hxy.symm,hy,hx⟩
    · rintro ⟨⟨x,y,hxy,hx,hy⟩,hvX,hwX⟩
      have hx' : x.val = v := hx
      have hy' : y.val = w := hy
      exact ⟨x,y,⟨hxy,by rw [hx']; exact hvX,by rw [hy']; exact hwX⟩,Or.inl ⟨hx,hy⟩⟩
  rw [← heq, Finset.card_map]

theorem graph_internal_count_identity (G : SimpleGraph V) (U : Finset V)
    (H R : SimpleGraph U) (hH : H ≤ G.induce (U : Set V)) (X : Finset V) :
    (internalEdges (graph G U H R) X).card + (internalEdges H (SmallCuts.shore U X)).card =
      (internalEdges G X).card + (internalEdges (core G U H R) (SmallCuts.shore U X)).card := by
  have hs := internal_count_sup (G \ lift U H) (lift U (core G U H R))
    (exterior_disjoint_core G U H R) X
  have hd := internal_count_sdiff_add G (lift U H) (lift_le U H G hH) X
  rw [internal_lift_count] at hd
  rw [internal_lift_count] at hs
  change (internalEdges (graph G U H R) X).card = _ at hs
  omega

noncomputable def embeddedCore (G : SimpleGraph V) (U : Finset V) (H : SimpleGraph U)
    (hH : lift U H ≤ G) : SmallCuts.Core (Multigraph.ofSimpleGraph G) U := by
  let f : H →g G := ⟨Subtype.val,fun h => hH ((lift_adj U H _ _).mpr h)⟩
  exact { graph := H
          edgeMap := ⟨f.mapEdgeSet,SimpleGraph.Hom.mapEdgeSet.injective f Subtype.val_injective⟩
          map_edge := fun _ => rfl }

omit [DecidableEq V] in
theorem cut_core_le (G : SimpleGraph V) (U : Finset V) (H : SimpleGraph U)
    (hH : lift U H ≤ G) (X : Finset V) :
    (Multigraph.ofSimpleGraph H).cutSize (SmallCuts.shore U X) ≤
      (Multigraph.ofSimpleGraph G).cutSize X :=
  (embeddedCore G U H hH).cut_le X

end Overfull.Replacement
