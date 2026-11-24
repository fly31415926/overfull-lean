import Overfull.AuxiliarySimple.Coloring
import Overfull.AuxiliarySimple.CoreTransport
import Overfull.AuxiliaryCompletion.Structure

/-!
# The auxiliary completion as an actual simple host

For a simple original graph the completion has an injective unordered edge
map.  Its simple realization preserves all counts, carries the original and
auxiliary core graphs, and restricts every coloring to the original copies.
-/

noncomputable section

namespace Overfull.AuxiliarySimple

open Finset Classical SimpleGraph Multigraph AuxiliaryCompletion

variable {V W : Type*} (G : SimpleGraph V) (N : V → Finset W) (H : SimpleGraph W)

def completion : SimpleGraph (V ⊕ W) :=
  simpleGraph (graph (Multigraph.ofSimpleGraph G) N H)

theorem completion_original_adj (v w : V) (hvw : G.Adj v w) :
    (completion G N H).Adj (Sum.inl v) (Sum.inl w) := by
  apply (simpleGraph_adj _ _ _).mpr
  refine ⟨Sum.inl ⟨s(v,w), hvw⟩, ?_⟩
  rw [original_edge_map]
  rfl

theorem completion_auxiliary_adj (v w : W) (hvw : H.Adj v w) :
    (completion G N H).Adj (Sum.inr v) (Sum.inr w) := by
  apply (simpleGraph_adj _ _ _).mpr
  refine ⟨Sum.inr (Sum.inr ⟨s(v,w), hvw⟩), ?_⟩
  rw [auxiliary_edge]
  rfl

/-- Every original core is transported by `Sum.inl` without changing its
degree or robust expansion parameters. -/
theorem completion_original_core (U : Finset V) (K : SimpleGraph U)
    (hK : K ≤ G.induce (U : Set V)) :
    mappedCore Function.Embedding.inl U K ≤
      (completion G N H).induce ((U.map Function.Embedding.inl : Finset (V ⊕ W)) : Set (V ⊕ W)) :=
  mappedCore_embed Function.Embedding.inl U G (completion G N H) K hK
    (completion_original_adj G N H)

variable [Fintype V] [Fintype W]

theorem completion_degree (v : V ⊕ W) :
    (completion G N H).degree v = (graph (Multigraph.ofSimpleGraph G) N H).degree v :=
  degree_eq _ (ofSimpleGraph_completion_simple G N H) v

theorem completion_overfull_iff (k : ℕ) (X : Finset (V ⊕ W)) :
    Overfull.IsOverfull (completion G N H) k X ↔
      (graph (Multigraph.ofSimpleGraph G) N H).IsOverfull k X :=
  isOverfull_iff _ (ofSimpleGraph_completion_simple G N H) k X

/-- The whole auxiliary graph is a core on exactly the right summand. -/
theorem completion_auxiliary_core :
    mappedCore Function.Embedding.inr (univ : Finset W) (H.induce (Set.univ : Set W)) ≤
      (completion G N H).induce
        (((univ : Finset W).map Function.Embedding.inr : Finset (V ⊕ W)) : Set (V ⊕ W)) := by
  apply mappedCore_embed Function.Embedding.inr univ H (completion G N H) _
    (by simpa only [Finset.coe_univ] using (le_refl (H.induce (Set.univ : Set W))))
  exact completion_auxiliary_adj G N H

/-- The coloring restricted to the exact original copies. -/
def restrictCompletionColoring {k : ℕ}
    (c : (Multigraph.ofSimpleGraph (completion G N H)).EdgeColoring k) :
    (Multigraph.ofSimpleGraph G).EdgeColoring k := by
  let d := originalColoring (graph (Multigraph.ofSimpleGraph G) N H)
    (ofSimpleGraph_completion_simple G N H) c
  refine ⟨fun e => d.color (Sum.inl e), ?_⟩
  intro e f v h he hf
  apply Sum.inl_injective
  apply d.proper (v := Sum.inl v) h
  · rw [original_edge_map]
    exact Sym2.mem_map.mpr ⟨v, he, rfl⟩
  · rw [original_edge_map]
    exact Sym2.mem_map.mpr ⟨v, hf, rfl⟩

end Overfull.AuxiliarySimple
