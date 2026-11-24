import Overfull.Basic
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Saturated color classes

These are graph-level consequences of a proper edge coloring. A color occurs
exactly once at every vertex whose degree equals the number of available
colors. In a regular graph, its color class is therefore a perfect matching.
Equality in the internal-edge counting bound forces every color to attain the
same matching bound. These statements do not assume any factorization or
edge-colorability theorem.
-/

namespace Overfull

open Finset

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}

/-- At a vertex of degree `k`, properness makes the neighbor-to-color map
bijective onto the `k` available colors. -/
theorem EdgeColoring.neighborColor_bijective_of_degree_eq
    [DecidableRel G.Adj] (c : EdgeColoring G k) (v : V) (hv : G.degree v = k) :
    Function.Bijective (fun u : G.neighborSet v =>
      c.color (⟨s(v, u.val), u.property⟩ : G.edgeSet)) := by
  classical
  let f : G.neighborSet v → Fin k := fun u => c.color ⟨s(v, u.val), u.property⟩
  have hf : Function.Injective f := by
    intro u w h
    have he : (⟨s(v, u.val), u.property⟩ : G.edgeSet) =
        ⟨s(v, w.val), w.property⟩ :=
      c.proper (v := v) (by simp) (by simp) h
    apply Subtype.ext
    have hval := congrArg Subtype.val he
    rcases Sym2.eq_iff.mp hval with ⟨_, huw⟩ | ⟨hvw, huv⟩
    · exact huw
    · exact huv.trans hvw
  apply (Fintype.bijective_iff_injective_and_card f).2
  refine ⟨hf, ?_⟩
  simpa only [SimpleGraph.card_neighborSet_eq_degree, Fintype.card_fin] using hv

/-- Every available color occurs on exactly one edge at a vertex of degree `k`. -/
theorem EdgeColoring.existsUnique_incident_color_of_degree_eq
    [DecidableRel G.Adj] (c : EdgeColoring G k) (v : V) (hv : G.degree v = k)
    (i : Fin k) :
    ∃! e : G.edgeSet, v ∈ e.val ∧ c.color e = i := by
  classical
  obtain ⟨u, hu⟩ := (c.neighborColor_bijective_of_degree_eq v hv).2 i
  refine ⟨⟨s(v, u.val), u.property⟩, ⟨by simp, hu⟩, ?_⟩
  intro e he
  exact c.proper he.1 (by simp) (he.2.trans hu.symm)

/-- The spanning subgraph containing exactly the edges of one color. -/
def EdgeColoring.colorClassSubgraph (c : EdgeColoring G k) (i : Fin k) :
    G.Subgraph where
  verts := Set.univ
  Adj u v := ∃ h : G.Adj u v, c.color (⟨s(u, v), h⟩ : G.edgeSet) = i
  adj_sub := fun h => h.choose
  edge_vert := fun _ => Set.mem_univ _
  symm := by
    intro u v h
    obtain ⟨huv, hcolor⟩ := h
    refine ⟨huv.symm, ?_⟩
    have he : (⟨s(v, u), huv.symm⟩ : G.edgeSet) = ⟨s(u, v), huv⟩ :=
      Subtype.ext (Sym2.eq_swap)
    rw [he]
    exact hcolor

/-- Each color class in a `k`-edge-colored `k`-regular graph is a perfect
matching in mathlib's `SimpleGraph.Subgraph.IsPerfectMatching` sense. -/
theorem EdgeColoring.colorClassSubgraph_isPerfectMatching
    [DecidableRel G.Adj] (c : EdgeColoring G k) (hregular : ∀ v, G.degree v = k)
    (i : Fin k) :
    (c.colorClassSubgraph i).IsPerfectMatching := by
  classical
  apply SimpleGraph.Subgraph.isPerfectMatching_iff.2
  intro v
  have hbij := c.neighborColor_bijective_of_degree_eq v (hregular v)
  obtain ⟨u, hu⟩ := hbij.2 i
  refine ⟨u.val, ⟨u.property, hu⟩, ?_⟩
  intro w hw
  obtain ⟨hvw, hwcolor⟩ := hw
  have he : (⟨w, hvw⟩ : G.neighborSet v) = u :=
    hbij.1 (hwcolor.trans hu.symm)
  exact congrArg Subtype.val he

/-- Equality in the overfull counting bound forces every color to attain the
matching bound inside `X`. This is the saturation step used for odd cliques
in Proposition 7.1. -/
theorem EdgeColoring.colorClass_card_eq_of_internalEdges_card_eq
    (c : EdgeColoring G k) (X : Finset V)
    (hX : (internalEdges G X).card = k * (X.card / 2)) (i : Fin k) :
    ((internalEdges G X).filter (fun e => c.color e = i)).card = X.card / 2 := by
  classical
  have hcount : (internalEdges G X).card =
      ∑ j : Fin k, ((internalEdges G X).filter (fun e => c.color e = j)).card := by
    exact Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
  have hsum :
      ∑ j : Fin k, ((internalEdges G X).filter (fun e => c.color e = j)).card =
        ∑ _j : Fin k, X.card / 2 := by
    rw [← hcount, hX]
    simp
  exact (Finset.sum_eq_sum_iff_of_le
    (fun j _ => c.colorClass_card_le X j)).mp hsum i (Finset.mem_univ i)

end Overfull
