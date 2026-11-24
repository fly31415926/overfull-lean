import Overfull.PrescribedMatching.ShortPaths
import Overfull.TutteBerge.Graph

namespace Overfull.PrescribedMatching

open Finset Classical SimpleGraph

variable {V I : Type*}

theorem clique_reachable (G : SimpleGraph V) (S : Set V) (hS : G.IsClique S)
    {u v : V} (hu : u ∈ S) (hv : v ∈ S) : G.Reachable u v := by
  obtain ⟨p,_⟩ := clique_walk_le_one G S hS u v hu hv
  exact p.reachable

/-- If every vertex reaches a clique in a fixed family, distinct
components require distinct clique labels. -/
theorem component_card_le_of_core_attachment [Finite V] [Fintype I]
    (G : SimpleGraph V) (U : I → Set V)
    (hclique : ∀ i, G.IsClique (U i))
    (hattach : ∀ v, ∃ i, ∃ a ∈ U i, G.Reachable v a) :
    Nat.card G.ConnectedComponent ≤ Fintype.card I := by
  classical
  have hrep (C : G.ConnectedComponent) : ∃ i, ∃ a ∈ U i, a ∈ C.supp := by
    obtain ⟨v,hv⟩ := C.nonempty_supp
    obtain ⟨i,a,ha,hreach⟩ := hattach v
    refine ⟨i,a,ha,?_⟩
    change G.connectedComponentMk a = C
    exact (ConnectedComponent.sound hreach).symm.trans hv
  choose label anchor hanchor hcomponent using hrep
  have hinj : Function.Injective label := by
    intro C D hCD
    have hreach : G.Reachable (anchor C) (anchor D) := by
      apply clique_reachable G (U (label C)) (hclique (label C)) (hanchor C)
      simpa only [hCD] using hanchor D
    exact (hcomponent C).symm.trans ((ConnectedComponent.sound hreach).trans (hcomponent D))
  simpa only [Nat.card_eq_fintype_card] using Nat.card_le_card_of_injective label hinj

/-- Under arbitrary vertex deletion, surviving core cliques and the
individual exceptional vertices give at most `|I| + |Z|` components. -/
theorem component_card_le_cores_add_exceptional [Fintype V] [Fintype I]
    (G : SimpleGraph V) (U : I → Set V) (Z : Finset V)
    (hclique : ∀ i, G.IsClique (U i))
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i) (D : Set V) :
    Nat.card (G.induce Dᶜ).ConnectedComponent ≤ Fintype.card I + Z.card := by
  classical
  let H := G.induce Dᶜ
  let U' : I ⊕ {v // v ∈ Z} → Set {v : V // v ∉ D} := fun j => match j with
    | .inl i => {v | v.val ∈ U i}
    | .inr z => {v | v.val = z.val}
  have hclique' (j : I ⊕ {v // v ∈ Z}) : H.IsClique (U' j) := by
    cases j with
    | inl i =>
        intro u hu v hv hne
        exact hclique i hu hv (fun h => hne (Subtype.ext h))
    | inr z =>
        intro u hu v hv hne
        exact False.elim (hne (Subtype.ext (hu.trans hv.symm)))
  have hattach' (v : {v : V // v ∉ D}) : ∃ j, ∃ a ∈ U' j, H.Reachable v a := by
    rcases hcover v.val with hz | ⟨i,hi⟩
    · exact ⟨.inr ⟨v.val,hz⟩,v,rfl,.rfl⟩
    · exact ⟨.inl i,v,hi,.rfl⟩
  simpa only [Fintype.card_sum,Fintype.card_coe] using
    component_card_le_of_core_attachment H U' hclique' hattach'

/-- A core survives whenever fewer core vertices are deleted than its
order. Only deletions outside the exceptional set need to be counted. -/
theorem exists_core_outside [Finite V] (U Z D : Set V)
    (hUZ : Disjoint U Z) (hsize : (D \ Z).ncard < U.ncard) :
    ∃ a ∈ U, a ∉ D := by
  obtain ⟨a,ha,haD⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hsize
  refine ⟨a,ha,?_⟩
  intro had
  exact haD ⟨had,fun haz => Set.disjoint_left.mp hUZ ha haz⟩

/-- A vertex with more core neighbors than deleted core vertices still
has an actual surviving core neighbor. -/
theorem exists_core_neighbor_outside [Finite V] (G : SimpleGraph V)
    (Z D : Set V) (v : V)
    (hsize : (D \ Z).ncard < (G.neighborSet v \ Z).ncard) :
    ∃ a, G.Adj v a ∧ a ∉ Z ∧ a ∉ D := by
  obtain ⟨a,ha,haD⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hsize
  exact ⟨a,ha.1,ha.2,fun had => haD ⟨had,ha.2⟩⟩

/-- The original order and neighborhood assumptions imply actual core
attachment after any deletion with fewer than `2|Z|+4` core vertices. -/
theorem core_attachment_after_deletion [Fintype V]
    (G : SimpleGraph V) (U : I → Set V) (Z : Finset V) (D : Set V)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (hneighbors : ∀ v ∈ Z, 2*Z.card+4 < (G.neighborSet v \ (Z : Set V)).ncard)
    (hdeleted : (D \ (Z : Set V)).ncard < 2*Z.card+4) :
    ∀ v, v ∉ D → ∃ i, ∃ a ∈ U i, a ∉ D ∧ (v = a ∨ G.Adj v a) := by
  intro v hv
  by_cases hvZ : v ∈ Z
  · obtain ⟨a,hva,haZ,haD⟩ := exists_core_neighbor_outside G (Z : Set V) D v
      (hdeleted.trans (hneighbors v hvZ))
    obtain ⟨i,hi⟩ := (hcover a).resolve_left haZ
    exact ⟨i,a,hi,haD,Or.inr hva⟩
  · obtain ⟨i,hi⟩ := (hcover v).resolve_left hvZ
    exact ⟨i,v,hi,hv,Or.inl rfl⟩

/-- Actual attachment bounds the components of the vertex-deleted graph
by the number of core labels. -/
theorem component_card_le_after_attachment [Finite V] [Fintype I]
    (G : SimpleGraph V) (U : I → Set V) (D : Set V)
    (hclique : ∀ i, G.IsClique (U i))
    (hattach : ∀ v, v ∉ D → ∃ i, ∃ a ∈ U i,
      a ∉ D ∧ (v = a ∨ G.Adj v a)) :
    Nat.card (G.induce Dᶜ).ConnectedComponent ≤ Fintype.card I := by
  let H := G.induce Dᶜ
  let U' : I → Set {v : V // v ∉ D} := fun i => {v | v.val ∈ U i}
  have hclique' (i : I) : H.IsClique (U' i) := by
    intro u hu v hv hne
    exact hclique i hu hv (fun h => hne (Subtype.ext h))
  have hattach' (v : {v : V // v ∉ D}) : ∃ i, ∃ a ∈ U' i, H.Reachable v a := by
    obtain ⟨i,a,ha,haD,hnear⟩ := hattach v.val v.property
    refine ⟨i,⟨a,haD⟩,ha,?_⟩
    rcases hnear with heq | hadj
    · have hv : v = ⟨a,haD⟩ := Subtype.ext heq
      rw [hv]
    · exact (show H.Adj v ⟨a,haD⟩ from hadj).reachable
  exact component_card_le_of_core_attachment H U' hclique' hattach'

/-- For the order estimates only the deleted vertices outside `Z` count. -/
theorem deleted_core_union_bound [Finite V] (D X Z : Set V) :
    ((D ∪ X) \ Z).ncard ≤ (D \ Z).ncard + X.ncard := by
  calc
    ((D ∪ X) \ Z).ncard ≤ ((D \ Z) ∪ X).ncard := by
      exact Set.ncard_le_ncard (by
        intro v hv
        rcases hv.1 with hd | hx
        · exact Or.inl ⟨hd,hv.2⟩
        · exact Or.inr hx) (Set.toFinite _)
    _ ≤ _ := Set.ncard_union_le _ _

theorem induced_reachable_of_near (G : SimpleGraph V) (D : Set V)
    (u v : {x : V // x ∉ D}) (h : u.val = v.val ∨ G.Adj u.val v.val) :
    (G.induce Dᶜ).Reachable u v := by
  rcases h with heq | hadj
  · have h : u = v := Subtype.ext heq
    rw [h]
  · exact (show (G.induce Dᶜ).Adj u v from hadj).reachable

theorem induced_clique_reachable (G : SimpleGraph V) (D S : Set V)
    (hclique : G.IsClique S) (u v : {x : V // x ∉ D})
    (hu : u.val ∈ S) (hv : v.val ∈ S) :
    (G.induce Dᶜ).Reachable u v := by
  apply induced_reachable_of_near
  by_cases heq : u.val = v.val
  · exact Or.inl heq
  · exact Or.inr (hclique hu hv heq)

/-- If each original component reaches a core and each core still has
a vertex, every original component has a survivor. -/
theorem component_has_survivor (G : SimpleGraph V) (U : I → Set V)
    (D X : Set V) (hclique : ∀ i, G.IsClique (U i))
    (hattach : ∀ v, v ∉ X → ∃ i, ∃ a ∈ U i,
      a ∉ X ∧ (v = a ∨ G.Adj v a))
    (hcore : ∀ i, ∃ a ∈ U i, a ∉ D ∪ X) :
    ∀ C : (G.induce Xᶜ).ConnectedComponent,
      ∃ v ∈ C.supp, v.val ∉ D := by
  intro C
  obtain ⟨v,hv⟩ := C.nonempty_supp
  obtain ⟨i,a,ha,haX,hnear⟩ := hattach v.val v.property
  obtain ⟨b,hb,hbDX⟩ := hcore i
  let a' : {x : V // x ∉ X} := ⟨a,haX⟩
  let b' : {x : V // x ∉ X} := ⟨b,fun hx => hbDX (Or.inr hx)⟩
  have hreach : (G.induce Xᶜ).Reachable v b' :=
    (induced_reachable_of_near G X v a' hnear).trans
      (induced_clique_reachable G X (U i) (hclique i) a' b' ha hb)
  refine ⟨b',?_,fun hd => hbDX (Or.inl hd)⟩
  exact (ConnectedComponent.sound hreach).symm.trans hv

/-- Retained paths through `W` reflect the actual connectivity of
surviving vertices after at most three additional deletions. -/
theorem reachable_reflection_of_witness [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : I → Set V) (W : Finset V) (D X : Set V)
    (hclique : ∀ i, G.IsClique (U i)) (hdisjoint : Disjoint D (W : Set V))
    (hW : ∀ Y : Finset V, Y.card ≤ 3 → ∀ i j, i ≠ j →
      CoresConnectedOutside G U Y i j →
      ∃ a ∈ U i, ∃ b ∈ U j, ∃ p : G.Walk a b,
        p.IsPath ∧ p.support.toFinset ⊆ W ∧ ∀ x ∈ p.support, x ∉ Y)
    (hX : X.ncard ≤ 3)
    (hattach : ∀ v, v ∉ D ∪ X → ∃ i, ∃ a ∈ U i,
      a ∉ D ∪ X ∧ (v = a ∨ G.Adj v a)) :
    ∀ u v : {x : V // x ∉ D ∪ X},
      (G.induce Xᶜ).Reachable
        ⟨u.val,fun hx => u.property (Or.inr hx)⟩
        ⟨v.val,fun hx => v.property (Or.inr hx)⟩ →
      (G.induce (D ∪ X)ᶜ).Reachable u v := by
  classical
  let H := G.induce Xᶜ
  let R := G.induce (D ∪ X)ᶜ
  let f : R →g H :=
    { toFun := fun v => ⟨v.val,fun hx => v.property (Or.inr hx)⟩
      map_rel' := fun h => h }
  intro u v hconn
  obtain ⟨i,a,ha,haDX,hua⟩ := hattach u.val u.property
  obtain ⟨j,b,hb,hbDX,hvb⟩ := hattach v.val v.property
  let a' : {x : V // x ∉ D ∪ X} := ⟨a,haDX⟩
  let b' : {x : V // x ∉ D ∪ X} := ⟨b,hbDX⟩
  have h_u_a : R.Reachable u a' := induced_reachable_of_near G (D ∪ X) u a' hua
  have h_v_b : R.Reachable v b' := induced_reachable_of_near G (D ∪ X) v b' hvb
  have h_a_b : H.Reachable (f a') (f b') :=
    (h_u_a.map f).symm.trans (hconn.trans (h_v_b.map f))
  have hab : R.Reachable a' b' := by
    by_cases hij : i = j
    · exact induced_clique_reachable G (D ∪ X) (U i) (hclique i) a' b'
        ha (by simpa only [hij] using hb)
    · let g : H →g G.induce {x | x ∉ X.toFinset} :=
        { toFun := fun v => ⟨v.val,by simpa only [Set.mem_toFinset] using v.property⟩
          map_rel' := fun h => h }
      have hcores : CoresConnectedOutside G U X.toFinset i j :=
        ⟨g (f a'),g (f b'),ha,hb,h_a_b.map g⟩
      have hXcard : X.toFinset.card ≤ 3 := by
        simpa only [← Set.ncard_eq_toFinset_card'] using hX
      obtain ⟨c,hc,d,hd,p,_hp,hpW,hpX⟩ := hW X.toFinset hXcard i j hij hcores
      have hpR : ∀ x ∈ p.support, x ∈ (D ∪ X)ᶜ := by
        intro x hx
        rintro (hxD | hxX)
        · exact Set.disjoint_left.mp hdisjoint hxD (hpW (List.mem_toFinset.mpr hx))
        · exact hpX x hx (by simpa only [Set.mem_toFinset] using hxX)
      let c' : {x : V // x ∉ D ∪ X} := ⟨c,hpR c p.start_mem_support⟩
      let d' : {x : V // x ∉ D ∪ X} := ⟨d,hpR d p.end_mem_support⟩
      have hcd : R.Reachable c' d' := reachable_induce_of_walk G p (D ∪ X)ᶜ hpR
      exact (induced_clique_reachable G (D ∪ X) (U i) (hclique i) a' c' ha hc).trans
        (hcd.trans (induced_clique_reachable G (D ∪ X) (U j) (hclique j) d' b' hd hb))
  exact h_u_a.trans (hab.trans h_v_b.symm)

end Overfull.PrescribedMatching
