import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Clique
import Overfull.ForbiddenSetWitness
import Mathlib.Tactic

namespace Overfull.PrescribedMatching

open Finset Classical

variable {V I : Type*}

theorem walk_le_one_of_eq_or_adj (G : SimpleGraph V) (u v : V)
    (h : u = v ∨ G.Adj u v) : ∃ p : G.Walk u v, p.length ≤ 1 := by
  rcases h with rfl | h
  · exact ⟨.nil,by simp⟩
  · exact ⟨h.toWalk,by simp⟩

theorem clique_walk_le_one (G : SimpleGraph V) (U : Set V) (hU : G.IsClique U)
    (u v : V) (hu : u ∈ U) (hv : v ∈ U) :
    ∃ p : G.Walk u v, p.length ≤ 1 := by
  apply walk_le_one_of_eq_or_adj
  by_cases h : u = v
  · exact Or.inl h
  · exact Or.inr (hU hu hv h)

/-- A label edge is witnessed by an actual walk of at most three edges
between the two core vertex sets. -/
def coreLinkGraph (G : SimpleGraph V) (U : I → Set V) : SimpleGraph I where
  Adj i j := i ≠ j ∧ ∃ u ∈ U i, ∃ v ∈ U j, ∃ p : G.Walk u v, p.length ≤ 3
  symm := by
    intro i j h
    obtain ⟨hne,u,hu,v,hv,p,hp⟩ := h
    exact ⟨hne.symm,v,hv,u,hu,p.reverse,by simpa using hp⟩
  loopless := by intro i h; exact h.1 rfl

/-- Attaching every vertex to a core transfers actual connectivity to
the finite core-label graph. No contraction existence is assumed. -/
theorem coreLinkGraph_reachable (G : SimpleGraph V) (U : I → Set V)
    (hattach : ∀ v, ∃ i, ∃ a ∈ U i, v = a ∨ G.Adj v a)
    {i j : I} {u v : V} (hu : u ∈ U i) (hv : v ∈ U j) (hconn : G.Reachable u v) :
    (coreLinkGraph G U).Reachable i j := by
  classical
  choose label anchor hanchor hnear using hattach
  have hwalk (x : V) : ∃ p : G.Walk x (anchor x), p.length ≤ 1 :=
    walk_le_one_of_eq_or_adj G x (anchor x) (hnear x)
  choose p hp using hwalk
  have hedge (x y : V) (hxy : G.Adj x y) :
      (coreLinkGraph G U).Reachable (label x) (label y) := by
    by_cases hlabel : label x = label y
    · rw [hlabel]
    · apply SimpleGraph.Adj.reachable
      refine ⟨hlabel,anchor x,hanchor x,anchor y,hanchor y,
        (p x).reverse.append (hxy.toWalk.append (p y)),?_⟩
      simp only [SimpleGraph.Walk.length_append,SimpleGraph.Walk.length_reverse,
        SimpleGraph.Adj.toWalk,SimpleGraph.Walk.length_cons,SimpleGraph.Walk.length_nil]
      have hx := hp x
      have hy := hp y
      omega
  have hmap {x y : V} (hxy : G.Reachable x y) :
      (coreLinkGraph G U).Reachable (label x) (label y) := by
    obtain ⟨q⟩ := hxy
    induction q with
    | nil => exact SimpleGraph.Reachable.rfl
    | @cons x y z hxy q ih => exact (hedge x y hxy).trans ih
  have hpoint (k : I) (x : V) (hx : x ∈ U k) :
      (coreLinkGraph G U).Reachable k (label x) := by
    by_cases hlabel : k = label x
    · rw [hlabel]
    · exact SimpleGraph.Adj.reachable ⟨hlabel,x,hx,anchor x,hanchor x,p x,
        (hp x).trans (by norm_num)⟩
  exact (hpoint i u hu).trans ((hmap hconn).trans (hpoint j v hv).symm)

/-- With a fixed first core vertex, each label edge costs at most four
graph edges: one clique join and the short link witnessing that edge. -/
theorem lift_coreLink_walk (G : SimpleGraph V) (U : I → Set V)
    (hclique : ∀ i, G.IsClique (U i)) {i j : I}
    (p : (coreLinkGraph G U).Walk i j) :
    ∀ a ∈ U i, ∃ b ∈ U j, ∃ q : G.Walk a b, q.length ≤ 4*p.length := by
  induction p with
  | nil =>
      intro a ha
      exact ⟨a,ha,.nil,by simp⟩
  | @cons i k j hik p ih =>
      intro a ha
      obtain ⟨_,x,hx,y,hy,q,hq⟩ := hik
      obtain ⟨r,hr⟩ := clique_walk_le_one G (U i) (hclique i) a x ha hx
      obtain ⟨b,hb,s,hs⟩ := ih y hy
      refine ⟨b,hb,r.append (q.append s),?_⟩
      simp only [SimpleGraph.Walk.length_append,SimpleGraph.Walk.length_cons]
      omega

/-- At most four core labels give a path with at most eleven edges,
when its endpoints may be chosen within the two specified cores. -/
theorem short_core_path [Fintype I] (G : SimpleGraph V) (U : I → Set V)
    (hcard : Fintype.card I ≤ 4) (hclique : ∀ i, G.IsClique (U i))
    {i j : I} (hne : i ≠ j) (hconn : (coreLinkGraph G U).Reachable i j) :
    ∃ a ∈ U i, ∃ b ∈ U j, ∃ p : G.Walk a b, p.IsPath ∧ p.length ≤ 11 := by
  classical
  obtain ⟨p,hp⟩ := hconn.exists_isPath
  have hlen := hp.length_lt
  cases p with
  | nil => exact False.elim (hne rfl)
  | @cons i k j hik p =>
      obtain ⟨_,a,ha,b,hb,q,hq⟩ := hik
      obtain ⟨c,hc,r,hr⟩ := lift_coreLink_walk G U hclique p b hb
      let w := q.append r
      have hw : w.length ≤ 11 := by
        dsimp [w]
        simp only [SimpleGraph.Walk.length_cons] at hlen
        rw [SimpleGraph.Walk.length_append]
        omega
      exact ⟨a,ha,c,hc,w.bypass,w.bypass_isPath,(w.length_bypass_le).trans hw⟩

/-- Connected distinct cores in a graph with at most four clique cores
have an actual short connecting path, provided every vertex attaches to a core. -/
theorem short_path_between_cores [Fintype I] (G : SimpleGraph V) (U : I → Set V)
    (hcard : Fintype.card I ≤ 4) (hclique : ∀ i, G.IsClique (U i))
    (hattach : ∀ v, ∃ i, ∃ a ∈ U i, v = a ∨ G.Adj v a)
    {i j : I} (hne : i ≠ j) {u v : V} (hu : u ∈ U i) (hv : v ∈ U j)
    (hconn : G.Reachable u v) :
    ∃ a ∈ U i, ∃ b ∈ U j, ∃ p : G.Walk a b, p.IsPath ∧ p.length ≤ 11 :=
  short_core_path G U hcard hclique hne (coreLinkGraph_reachable G U hattach hu hv hconn)

variable [DecidableEq V]

/-- The two indicated cores meet one component after deleting `Y`. -/
def CoresConnectedOutside (G : SimpleGraph V) (U : I → Set V)
    (Y : Finset V) (i j : I) : Prop :=
  ∃ u v : {x : V // x ∉ Y}, u.val ∈ U i ∧ v.val ∈ U j ∧
    (G.induce {x | x ∉ Y}).Reachable u v

omit [DecidableEq V] in
theorem CoresConnectedOutside.symm (G : SimpleGraph V) (U : I → Set V)
    (Y : Finset V) {i j : I} (h : CoresConnectedOutside G U Y i j) :
    CoresConnectedOutside G U Y j i := by
  obtain ⟨u,v,hu,hv,hreach⟩ := h
  exact ⟨v,u,hv,hu,hreach.symm⟩

omit [DecidableEq V] in
theorem reachable_induce_of_walk (G : SimpleGraph V) {u v : V}
    (p : G.Walk u v) (S : Set V) (hS : ∀ x ∈ p.support, x ∈ S) :
    (G.induce S).Reachable
      ⟨u,hS u p.start_mem_support⟩ ⟨v,hS v p.end_mem_support⟩ := by
  let f : (G.induce {x | x ∈ p.support}) →g G.induce S :=
    { toFun := fun x => ⟨x.val,hS x.val x.property⟩
      map_rel' := fun h => h }
  exact (p.connected_induce_support.preconnected
    ⟨u,p.start_mem_support⟩ ⟨v,p.end_mem_support⟩).map f

/-- The short path is an actual path in the ambient graph and avoids
every deleted vertex. Its support contains at most twelve vertices. -/
theorem short_path_avoiding [Fintype I] (G : SimpleGraph V) (U : I → Set V)
    (hcard : Fintype.card I ≤ 4) (hclique : ∀ i, G.IsClique (U i))
    (Y : Finset V)
    (hattach : ∀ v, v ∉ Y → ∃ i, ∃ a ∈ U i,
      a ∉ Y ∧ (v = a ∨ G.Adj v a))
    {i j : I} (hne : i ≠ j) (hconn : CoresConnectedOutside G U Y i j) :
    ∃ a ∈ U i, ∃ b ∈ U j, ∃ p : G.Walk a b,
      p.IsPath ∧ p.length ≤ 11 ∧ p.support.toFinset.card ≤ 12 ∧
      ∀ x ∈ p.support, x ∉ Y := by
  classical
  let H := G.induce {x | x ∉ Y}
  let U' : I → Set {x : V // x ∉ Y} := fun i => {x | x.val ∈ U i}
  have hclique' (i : I) : H.IsClique (U' i) := by
    intro u hu v hv hne
    exact hclique i hu hv (fun h => hne (Subtype.ext h))
  have hattach' (v : {x : V // x ∉ Y}) :
      ∃ i, ∃ a ∈ U' i, v = a ∨ H.Adj v a := by
    obtain ⟨i,a,ha,haY,hnear⟩ := hattach v.val v.property
    refine ⟨i,⟨a,haY⟩,ha,?_⟩
    rcases hnear with heq | hadj
    · exact Or.inl (Subtype.ext heq)
    · exact Or.inr hadj
  obtain ⟨u,v,hu,hv,hreach⟩ := hconn
  obtain ⟨a,ha,b,hb,p,hpath,hlen⟩ :=
    short_path_between_cores H U' hcard hclique' hattach' hne hu hv hreach
  let f : H →g G := { toFun := Subtype.val, map_rel' := fun h => h }
  let q := p.map f
  have hqpath : q.IsPath := p.map_isPath_of_injective Subtype.val_injective hpath
  have hqlen : q.length ≤ 11 := by
    simpa only [q,SimpleGraph.Walk.length_map] using hlen
  refine ⟨a.val,ha,b.val,hb,q,hqpath,hqlen,?_,?_⟩
  · have hc := List.toFinset_card_le q.support
    rw [SimpleGraph.Walk.length_support] at hc
    omega
  · intro x hx
    change x ∈ (p.map f).support at hx
    rw [SimpleGraph.Walk.support_map] at hx
    obtain ⟨w,_hw,rfl⟩ := List.mem_map.mp hx
    exact w.property

/-- A finite vertex set is the support of a path joining the two cores. -/
def CorePathSupport (G : SimpleGraph V) (U : I → Set V) (i j : I)
    (S : Finset V) : Prop :=
  ∃ a ∈ U i, ∃ b ∈ U j, ∃ p : G.Walk a b,
    p.IsPath ∧ p.support.toFinset = S

theorem CorePathSupport.symm (G : SimpleGraph V) (U : I → Set V)
    {i j : I} {S : Finset V} (h : CorePathSupport G U i j S) :
    CorePathSupport G U j i S := by
  obtain ⟨a,ha,b,hb,p,hp,hS⟩ := h
  refine ⟨b,hb,a,ha,p.reverse,p.isPath_reverse_iff.mpr hp,?_⟩
  simpa only [SimpleGraph.Walk.support_reverse,List.toFinset_reverse] using hS

variable [DecidableEq I]

theorem corePathSupport_of_pair (G : SimpleGraph V) (U : I → Set V)
    {i j : I} (hne : i ≠ j) {S : Finset V}
    (h : ∃ a b, a ≠ b ∧ ({i,j} : Finset I) = {a,b} ∧
      CorePathSupport G U a b S) : CorePathSupport G U i j S := by
  obtain ⟨a,b,_hab,heq,hpath⟩ := h
  have hi : i = a ∨ i = b := by
    have hi' : i ∈ ({a,b} : Finset I) := by rw [← heq]; simp
    simpa using hi'
  have hj : j = a ∨ j = b := by
    have hj' : j ∈ ({a,b} : Finset I) := by rw [← heq]; simp
    simpa using hj'
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact False.elim (hne rfl)
  · exact hpath
  · exact hpath.symm G U
  · exact False.elim (hne rfl)

omit [DecidableEq V] [DecidableEq I] in
/-- There are at most six pairs of distinct core labels. -/
theorem core_pairs_card [Fintype I] (hcard : Fintype.card I ≤ 4) :
    ((univ : Finset I).powersetCard 2).card ≤ 6 := by
  rw [card_powersetCard,card_univ]
  exact (Nat.choose_le_choose 2 hcard).trans (by decide)

/-- The witness set preserves every connection between distinct core
labels after at most three vertex deletions. Its bound comes from the
actual twelve-vertex paths and the finite forbidden-set construction. -/
theorem exists_core_connection_witness [Fintype V] [Fintype I]
    (G : SimpleGraph V) (U : I → Set V)
    (hcard : Fintype.card I ≤ 4) (hclique : ∀ i, G.IsClique (U i))
    (hattach : ∀ Y : Finset V, Y.card ≤ 3 → ∀ v, v ∉ Y →
      ∃ i, ∃ a ∈ U i, a ∉ Y ∧ (v = a ∨ G.Adj v a)) :
    ∃ W : Finset V, W.card ≤ 135720 ∧
      ∀ Y : Finset V, Y.card ≤ 3 → ∀ i j, i ≠ j →
        CoresConnectedOutside G U Y i j →
        ∃ a ∈ U i, ∃ b ∈ U j, ∃ p : G.Walk a b,
          p.IsPath ∧ p.support.toFinset ⊆ W ∧
          ∀ x ∈ p.support, x ∉ Y := by
  classical
  let T := (univ : Finset I).powersetCard 2
  let F : Finset I → Finset (Finset V) := fun P => univ.filter fun S =>
    S.card ≤ 12 ∧ ∃ i j, i ≠ j ∧ P = {i,j} ∧ CorePathSupport G U i j S
  have hT : T.card ≤ 6 := core_pairs_card hcard
  have hsize : ∀ P ∈ T, ∀ S ∈ F P, S.card ≤ 12 := by
    intro P _hP S hS
    exact (mem_filter.mp hS).2.1
  obtain ⟨W,hW,hpreserve⟩ :=
    ForbiddenSetWitness.exists_six_family_witness T F hT hsize
  refine ⟨W,hW,?_⟩
  intro Y hY i j hne hconn
  have hpair : ({i,j} : Finset I) ∈ T := by
    simp only [T,mem_powersetCard]
    exact ⟨subset_univ _,by simp [hne]⟩
  obtain ⟨a,ha,b,hb,p,hpath,_hlen,hsize,havoid⟩ :=
    short_path_avoiding G U hcard hclique Y (hattach Y hY) hne hconn
  have hmem : p.support.toFinset ∈ F {i,j} := by
    apply mem_filter.mpr
    exact ⟨mem_univ _,hsize,i,j,hne,rfl,a,ha,b,hb,p,hpath,rfl⟩
  have hdisjoint : Disjoint p.support.toFinset Y := by
    apply disjoint_left.mpr
    intro x hx hxy
    exact havoid x (List.mem_toFinset.mp hx) hxy
  obtain ⟨S,hS,hSW,hSY⟩ := hpreserve {i,j} hpair Y hY
    ⟨p.support.toFinset,hmem,hdisjoint⟩
  have hsupport : CorePathSupport G U i j S :=
    corePathSupport_of_pair G U hne (mem_filter.mp hS).2.2
  obtain ⟨c,hc,d,hd,q,hq,hqS⟩ := hsupport
  refine ⟨c,hc,d,hd,q,hq,?_,?_⟩
  · simpa only [hqS] using hSW
  · intro x hx hxy
    have hxS : x ∈ S := by rw [← hqS]; exact List.mem_toFinset.mpr hx
    exact disjoint_left.mp hSY hxS hxy

end Overfull.PrescribedMatching
