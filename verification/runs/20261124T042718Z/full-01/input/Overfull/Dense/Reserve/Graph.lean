import Overfull.Dense.UnequalFlow
import Mathlib.Data.ZMod.Basic

/-!
# An actual directed graph on six cyclic vertex classes

Every directed edge advances one class. Each pair is an actual simple
bipartite graph on the corresponding class subtypes.
-/

namespace Overfull.Dense

open Finset Classical

structure SixCycleGraph (V : Type*) where
  part : V → ZMod 6
  adj : V → V → Prop
  crosses : ∀ {u v}, adj u v → part v = part u + 1

namespace SixCycleGraph

variable {V : Type*} (G : SixCycleGraph V)

abbrev Part (j : ZMod 6) := {v : V // G.part v = j}

def pairGraph (j : ZMod 6) : SimpleGraph (G.Part j ⊕ G.Part (j+1)) where
  Adj x y := match x,y with
    | .inl u, .inr v => G.adj u.val v.val
    | .inr v, .inl u => G.adj u.val v.val
    | _, _ => False
  symm := by rintro (u|v) (u'|v') h <;> exact h
  loopless := by rintro (u|v) <;> exact not_false

variable [Fintype V]

noncomputable def outNeighbors (v : V) : Finset V := univ.filter (G.adj v)
noncomputable def inNeighbors (v : V) : Finset V := univ.filter (fun u => G.adj u v)
noncomputable def outDegree (v : V) : ℕ := (G.outNeighbors v).card
noncomputable def inDegree (v : V) : ℕ := (G.inNeighbors v).card

noncomputable def pairEdges (j : ZMod 6) : Finset (G.Part j × G.Part (j+1)) :=
  univ.filter (fun e => G.adj e.1.val e.2.val)

noncomputable def edgeCount (j : ZMod 6) : ℕ := (G.pairEdges j).card

theorem pair_rightNeighbors_card (j : ZMod 6) (u : G.Part j) :
    (rightNeighbors (G.pairGraph j) u).card = G.outDegree u.val := by
  unfold outDegree
  refine Finset.card_bij (fun v _ => v.val) ?_ ?_ ?_
  · intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hv).2⟩
  · intro v hv w hw h
    exact Subtype.ext h
  · intro v hv
    have huv : G.adj u.val v := (Finset.mem_filter.mp hv).2
    have hvp : G.part v = j+1 := (G.crosses huv).trans (by rw [u.property])
    exact ⟨⟨v,hvp⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,huv⟩,rfl⟩

theorem pair_leftNeighbors_card (j : ZMod 6) (v : G.Part (j+1)) :
    (leftNeighbors (G.pairGraph j) v).card = G.inDegree v.val := by
  unfold inDegree
  refine Finset.card_bij (fun u _ => u.val) ?_ ?_ ?_
  · intro u hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hu).2⟩
  · intro u hu w hw h
    exact Subtype.ext h
  · intro u hu
    have huv : G.adj u v.val := (Finset.mem_filter.mp hu).2
    have hup : G.part u = j := by
      have h := G.crosses huv
      rw [v.property] at h
      exact add_right_cancel h.symm
    exact ⟨⟨u,hup⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,huv⟩,rfl⟩

theorem outDegree_le_part_card (j : ZMod 6) (u : G.Part j) :
    G.outDegree u.val ≤ Fintype.card (G.Part (j+1)) := by
  rw [← G.pair_rightNeighbors_card j u]
  exact Finset.card_le_card (Finset.subset_univ _)

theorem inDegree_le_part_card (j : ZMod 6) (v : G.Part (j+1)) :
    G.inDegree v.val ≤ Fintype.card (G.Part j) := by
  rw [← G.pair_leftNeighbors_card j v]
  exact Finset.card_le_card (Finset.subset_univ _)

theorem sum_outDegree (j : ZMod 6) :
    (∑ u : G.Part j, G.outDegree u.val) = G.edgeCount j := by
  simp_rw [← G.pair_rightNeighbors_card j]
  simp only [rightNeighbors, pairGraph, edgeCount, pairEdges,
    Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type]

theorem sum_inDegree (j : ZMod 6) :
    (∑ v : G.Part (j+1), G.inDegree v.val) = G.edgeCount j := by
  simp_rw [← G.pair_leftNeighbors_card j]
  simp only [leftNeighbors, pairGraph, edgeCount, pairEdges,
    Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type]
  exact Finset.sum_comm

theorem sum_inDegree_at (j : ZMod 6) :
    (∑ v : G.Part j, G.inDegree v.val) = G.edgeCount (j-1) := by
  have h (i j : ZMod 6) (hij : i+1=j) :
      (∑ v : G.Part j, G.inDegree v.val) = G.edgeCount i := by
    subst j
    exact G.sum_inDegree i
  exact h (j-1) j (sub_add_cancel j 1)

theorem sum_outDegree_real (j : ZMod 6) :
    (∑ u : G.Part j, (G.outDegree u.val : ℝ)) = G.edgeCount j := by
  exact_mod_cast G.sum_outDegree j

theorem sum_inDegree_real (j : ZMod 6) :
    (∑ v : G.Part (j+1), (G.inDegree v.val : ℝ)) = G.edgeCount j := by
  exact_mod_cast G.sum_inDegree j

theorem sum_inDegree_at_real (j : ZMod 6) :
    (∑ v : G.Part j, (G.inDegree v.val : ℝ)) = G.edgeCount (j-1) := by
  exact_mod_cast G.sum_inDegree_at j

end SixCycleGraph
end Overfull.Dense
