import Overfull.ColoringExtension.VertexConstraints
import Overfull.Vizing.Theorem

/-!
# Simple graphs with forbidden colors

The verified Vizing construction supplies the initial coloring. The finite
permutation-and-repair theorem then respects the fixed forbidden labels;
when these arise from vertex footprints, the classes can also be balanced.
-/

namespace Overfull.ColoringExtension

open Finset Classical

variable {V : Type*} {G : SimpleGraph V} {k : ℕ}

/-- Keep the actual unordered edge copies when passing to the multigraph
coloring interface. -/
def toMultigraphColoring (c : Overfull.EdgeColoring G k) :
    (Multigraph.ofSimpleGraph G).EdgeColoring k where
  color := c.color
  proper h he hf := c.proper he hf h

/-- Recover the original simple-graph coloring interface on the same edges. -/
def toSimpleColoring (c : (Multigraph.ofSimpleGraph G).EdgeColoring k) :
    Overfull.EdgeColoring G k where
  color := c.color
  proper he hf h := c.proper h he hf

variable [Fintype V]

/-- Vizing's proved bound with the actual multigraph edge-copy interface. -/
theorem exists_initial_simple_coloring (G : SimpleGraph V) [DecidableRel G.Adj] :
    Nonempty ((Multigraph.ofSimpleGraph G).EdgeColoring (G.maxDegree + 1)) := by
  obtain ⟨c⟩ := Overfull.vizing_finite G
  exact ⟨toMultigraphColoring c⟩

/-- The exact finite forbidden-label criterion for a simple graph, with
no initial coloring supplied by the caller. -/
theorem exists_simple_avoiding_coloring (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : ℕ) (hpalette : G.maxDegree + 1 ≤ h)
    (B : G.edgeSet → Finset (Fin h)) (b t : ℕ)
    (ht : 1 ≤ t) (hB : ∀ e, (B e).card ≤ b)
    (htail : Fintype.card V * b ^ t < t.factorial)
    (hslack : b + 2 * (t - 1) < h - (G.maxDegree + 1)) :
    ∃ c : Overfull.EdgeColoring G h, ∀ e, c.color e ∉ B e := by
  classical
  obtain ⟨c₀⟩ := exists_initial_simple_coloring G
  obtain ⟨c, hc⟩ := exists_avoiding_coloring c₀ hpalette B b t ht hB htail hslack
  exact ⟨toSimpleColoring c, hc⟩

/-- Construct balanced internal classes compatible with fixed exterior
footprints, starting only from a simple graph and the finite bounds. -/
theorem exists_simple_balanced_avoiding (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : ℕ) (hpalette : G.maxDegree + 1 ≤ h)
    (F : Fin h → Finset V) (a f t : ℕ)
    (hF : ∀ i, (F i).card ≤ f)
    (hload : ∀ v, (forbiddenColors F v).card ≤ a)
    (ht : 1 ≤ t) (htail : Fintype.card V * (2 * a) ^ t < t.factorial)
    (hslack : 2 * a + 2 * (t - 1) < h - (G.maxDegree + 1)) :
    ∃ c : (Multigraph.ofSimpleGraph G).EdgeColoring h, c.AvoidsVertices F ∧
      ∀ i j, |((c.colorClass i).card : ℤ) - ((c.colorClass j).card : ℤ)| ≤ (f : ℤ) + 1 := by
  classical
  obtain ⟨c₀⟩ := exists_initial_simple_coloring G
  exact exists_balanced_coloring_avoiding c₀ hpalette F a f t hF hload ht htail hslack

end Overfull.ColoringExtension
