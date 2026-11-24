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

omit [Fintype V]

def auxiliaryVertices (V W : Type*) [Fintype W] : Finset (V ⊕ W) :=
  (univ : Finset W).map Function.Embedding.inr

def auxiliaryEquiv : W ≃ auxiliaryVertices V W :=
  Equiv.ofBijective
    (fun w => ⟨Sum.inr w, mem_map.mpr ⟨w, mem_univ w, rfl⟩⟩)
    ⟨by intro v w h; exact Sum.inr_injective (congrArg Subtype.val h), by
      intro w
      obtain ⟨v, _, h⟩ := mem_map.mp w.property
      exact ⟨v, Subtype.ext h⟩⟩

@[simp] theorem auxiliaryEquiv_coe (w : W) :
    (auxiliaryEquiv (V := V) w).val = Sum.inr w := rfl

@[simp] theorem auxiliaryEquiv_symm_coe (w : auxiliaryVertices V W) :
    Sum.inr ((auxiliaryEquiv (V := V)).symm w) = w.val := by
  rw [← auxiliaryEquiv_coe, Equiv.apply_symm_apply]

/-- The auxiliary core uses exactly its original graph, with right-summand
vertex names. -/
def auxiliaryCore : SimpleGraph (auxiliaryVertices V W) :=
  H.comap (auxiliaryEquiv (V := V)).symm

theorem auxiliaryCore_degree (v : auxiliaryVertices V W) :
    (auxiliaryCore (V := V) H).degree v =
      H.degree ((auxiliaryEquiv (V := V)).symm v) :=
  RobustRealization.comap_equiv_degree H (auxiliaryEquiv (V := V)).symm v

theorem auxiliaryCore_robust (ν τ : ℝ) (hH : IsRobustExpander H ν τ) :
    IsRobustExpander (auxiliaryCore (V := V) H) ν τ :=
  RobustRealization.robust_comap_equiv H (auxiliaryEquiv (V := V)).symm ν τ hH

/-- The entire auxiliary core embeds in the actual simple completion. -/
theorem completion_auxiliary_core :
    auxiliaryCore (V := V) H ≤
      (completion G N H).induce ((auxiliaryVertices V W : Finset (V ⊕ W)) : Set (V ⊕ W)) := by
  intro v w hvw
  change (completion G N H).Adj v.val w.val
  rw [← auxiliaryEquiv_symm_coe v, ← auxiliaryEquiv_symm_coe w]
  exact completion_auxiliary_adj G N H _ _ hvw

theorem auxiliaryVertices_card : (auxiliaryVertices V W).card = Fintype.card W := by
  simp [auxiliaryVertices]

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
