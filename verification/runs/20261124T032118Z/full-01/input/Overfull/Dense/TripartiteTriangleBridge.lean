import Overfull.Dense.TriangleDecomposition
import Overfull.Dense.CycleAbsorber

/-!
# Unordered edges and triangle decompositions

The coordinate model of a simple tripartite graph and the unordered-edge
model of the cycle gadget describe the same edges and decompositions.
-/

namespace Overfull.TripartiteGraph

open Finset Classical

variable {A B W : Type*}

/-- The actual unordered pair associated with a tripartite edge coordinate. -/
def edgePair : EdgePosition (A := A) (B := B) (W := W) → Sym2 (A ⊕ B ⊕ W)
  | .inl (a,b) => s(Sum.inl a,Sum.inr (Sum.inl b))
  | .inr (.inl (a,w)) => s(Sum.inl a,Sum.inr (Sum.inr w))
  | .inr (.inr (b,w)) => s(Sum.inr (Sum.inl b),Sum.inr (Sum.inr w))

theorem edgePair_injective : Function.Injective (edgePair (A := A) (B := B) (W := W)) := by
  rintro (⟨a,b⟩ | ⟨a,w⟩ | ⟨b,w⟩) (⟨a',b'⟩ | ⟨a',w'⟩ | ⟨b',w'⟩) h <;>
    simp only [edgePair,Sym2.eq_iff,Sum.inl.injEq,Sum.inr.injEq,
      Sum.inl_ne_inr,Sum.inr_ne_inl,false_and,and_false,or_false] at h <;>
    first | contradiction | rcases h with ⟨rfl,rfl⟩; rfl

theorem edgePair_mem (G : TripartiteGraph A B W)
    (e : EdgePosition (A := A) (B := B) (W := W)) :
    edgePair e ∈ G.toSimpleGraph.edgeSet ↔ G.IsEdge e := by
  rcases e with ⟨a,b⟩ | ⟨a,w⟩ | ⟨b,w⟩ <;> rfl

/-- Every triangle in the simple host has a canonical A, B, W ordering. -/
theorem exists_actual_triangle (G : TripartiteGraph A B W)
    (T : Dense.Triangle (A ⊕ B ⊕ W))
    (hab : G.toSimpleGraph.Adj T.a T.b)
    (hbc : G.toSimpleGraph.Adj T.b T.c)
    (hca : G.toSimpleGraph.Adj T.c T.a) :
    ∃ t : G.Triangle, ∀ e, G.ContainsEdge t e ↔ ∃ j, T.edge j = edgePair e := by
  rcases T with ⟨x,y,z,hxy,hyz,hzx⟩
  rcases x with a | b | w <;>
    rcases y with a' | b' | w' <;>
    rcases z with a'' | b'' | w'' <;>
    simp only [toSimpleGraph] at hab hbc hca
  · refine ⟨⟨(a,b',w''),hab,hca,hbc⟩,?_⟩
    rintro (⟨u,v⟩ | ⟨u,s⟩ | ⟨v,s⟩) <;>
      simp [ContainsEdge,Dense.Triangle.edge,edgePair,Fin.exists_fin_succ,and_comm]
  · refine ⟨⟨(a,b'',w'),hca,hab,hbc⟩,?_⟩
    rintro (⟨u,v⟩ | ⟨u,s⟩ | ⟨v,s⟩) <;>
      simp [ContainsEdge,Dense.Triangle.edge,edgePair,Fin.exists_fin_succ,and_comm]
  · refine ⟨⟨(a',b,w''),hab,hbc,hca⟩,?_⟩
    rintro (⟨u,v⟩ | ⟨u,s⟩ | ⟨v,s⟩) <;>
      simp [ContainsEdge,Dense.Triangle.edge,edgePair,Fin.exists_fin_succ,and_comm]
  · refine ⟨⟨(a'',b,w'),hca,hbc,hab⟩,?_⟩
    rintro (⟨u,v⟩ | ⟨u,s⟩ | ⟨v,s⟩) <;>
      simp [ContainsEdge,Dense.Triangle.edge,edgePair,Fin.exists_fin_succ,and_comm]
  · refine ⟨⟨(a',b'',w),hbc,hab,hca⟩,?_⟩
    rintro (⟨u,v⟩ | ⟨u,s⟩ | ⟨v,s⟩) <;>
      simp [ContainsEdge,Dense.Triangle.edge,edgePair,Fin.exists_fin_succ,and_comm]
  · refine ⟨⟨(a'',b',w),hbc,hca,hab⟩,?_⟩
    rintro (⟨u,v⟩ | ⟨u,s⟩ | ⟨v,s⟩) <;>
      simp [ContainsEdge,Dense.Triangle.edge,edgePair,Fin.exists_fin_succ,and_comm]

variable [Fintype A] [Fintype B] [Fintype W]

omit [Fintype A] [Fintype B] [Fintype W] in
/-- Transfer an actual unordered-edge decomposition into canonical tripartite
triangle coordinates. -/
theorem decomposition_of_simpleGraph (G : TripartiteGraph A B W)
    {I : Type*} [Fintype I] (H : SimpleGraph (A ⊕ B ⊕ W))
    (D : I → Dense.Triangle (A ⊕ B ⊕ W))
    (hH : H ≤ G.toSimpleGraph) (hD : Dense.IsTriangleDecomposition H D)
    (E : Finset (EdgePosition (A := A) (B := B) (W := W)))
    (hE : ∀ e, e ∈ E ↔ edgePair e ∈ H.edgeSet) :
    ∃ T : Finset G.Triangle, G.IsTriangleDecomposition T E := by
  have hhost (i : I) (j : Fin 3) : (D i).edge j ∈ G.toSimpleGraph.edgeSet := by
    apply SimpleGraph.edgeSet_mono hH
    rw [hD.2]
    exact Finset.mem_image.mpr ⟨(i,j),Finset.mem_univ _,rfl⟩
  have hactual (i : I) : ∃ t : G.Triangle, ∀ e,
      G.ContainsEdge t e ↔ ∃ j, (D i).edge j = edgePair e := by
    exact exists_actual_triangle G (D i) (hhost i 0) (hhost i 1) (hhost i 2)
  choose T hT using hactual
  refine ⟨univ.image T,G.isTriangleDecomposition_of_unique _ E ?_ ?_⟩
  · intro t ht e hte
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨j,hj⟩ := (hT i e).mp hte
    apply (hE e).mpr
    rw [hD.2]
    exact Finset.mem_image.mpr ⟨(i,j),Finset.mem_univ _,hj⟩
  · intro e he
    have heH := (hE e).mp he
    rw [hD.2] at heH
    obtain ⟨⟨i,j⟩,_,hij⟩ := Finset.mem_image.mp heH
    refine ⟨T i,⟨Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,
      (hT i e).mpr ⟨j,hij⟩⟩,?_⟩
    intro t ht
    obtain ⟨i',_,rfl⟩ := Finset.mem_image.mp ht.1
    obtain ⟨j',hij'⟩ := (hT i' e).mp ht.2
    have hidx : (i',j') = (i,j) := hD.1 (hij'.trans hij.symm)
    exact congrArg T (congrArg Prod.fst hidx)

omit [Fintype A] [Fintype B] [Fintype W] in
/-- Edge-disjoint decompositions combine by taking their triangle sets. -/
theorem IsTriangleDecomposition.union (G : TripartiteGraph A B W)
    {T S : Finset G.Triangle}
    {E F : Finset (EdgePosition (A := A) (B := B) (W := W))}
    (hT : G.IsTriangleDecomposition T E) (hS : G.IsTriangleDecomposition S F)
    (hd : Disjoint E F) : G.IsTriangleDecomposition (T ∪ S) (E ∪ F) := by
  apply G.isTriangleDecomposition_of_unique
  · intro t ht e hte
    rcases Finset.mem_union.mp ht with ht | ht
    · exact Finset.mem_union_left _ (hT.support G ht hte)
    · exact Finset.mem_union_right _ (hS.support G ht hte)
  · intro e he
    rcases Finset.mem_union.mp he with he | he
    · obtain ⟨t,ht,hu⟩ := hT.unique G he
      refine ⟨t,⟨Finset.mem_union_left _ ht.1,ht.2⟩,?_⟩
      intro s hs
      rcases Finset.mem_union.mp hs.1 with hsT | hsS
      · exact hu s ⟨hsT,hs.2⟩
      · exact (Finset.disjoint_left.mp hd he (hS.support G hsS hs.2)).elim
    · obtain ⟨t,ht,hu⟩ := hS.unique G he
      refine ⟨t,⟨Finset.mem_union_right _ ht.1,ht.2⟩,?_⟩
      intro s hs
      rcases Finset.mem_union.mp hs.1 with hsT | hsS
      · exact (Finset.disjoint_left.mp hd (hT.support G hsT hs.2) he).elim
      · exact hu s ⟨hsS,hs.2⟩

omit [Fintype A] [Fintype B] [Fintype W] in
theorem decomposition_biUnion (G : TripartiteGraph A B W) {I : Type*} [Fintype I]
    (E : I → Finset (EdgePosition (A := A) (B := B) (W := W)))
    (hd : Pairwise (fun i j => Disjoint (E i) (E j)))
    (hE : ∀ i, ∃ T : Finset G.Triangle, G.IsTriangleDecomposition T (E i)) :
    ∃ T : Finset G.Triangle, G.IsTriangleDecomposition T (univ.biUnion E) := by
  have hfinite (s : Finset I) :
      ∃ T : Finset G.Triangle, G.IsTriangleDecomposition T (s.biUnion E) := by
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨∅,?_⟩
      intro e
      simp [trianglesAt]
    | @insert i s hi ih =>
      obtain ⟨T,hT⟩ := hE i
      obtain ⟨S,hS⟩ := ih
      have hdis : Disjoint (E i) (s.biUnion E) := by
        apply Finset.disjoint_left.mpr
        intro e hei hes
        obtain ⟨j,hjs,hej⟩ := Finset.mem_biUnion.mp hes
        exact Finset.disjoint_left.mp (hd (fun h : i = j => hi (h.symm ▸ hjs))) hei hej
      refine ⟨T ∪ S,?_⟩
      rw [Finset.biUnion_insert]
      exact hT.union G hS hdis
  exact hfinite univ

end Overfull.TripartiteGraph
