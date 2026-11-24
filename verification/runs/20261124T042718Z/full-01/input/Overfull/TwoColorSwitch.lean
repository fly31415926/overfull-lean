import Overfull.MultigraphColoring
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Switching two colors in an actual multigraph

The auxiliary simple graph records connectivity only. All degrees and edge
counts below retain the original edge copies, including parallel copies.
-/

namespace Overfull.Multigraph.EdgeColoring

open Finset Classical
open scoped BigOperators

variable {V E : Type*} {G : Multigraph V E} {q : ℕ}

/-- A color covers a vertex precisely when an actual edge of that color is incident. -/
def Covers (c : G.EdgeColoring q) (i : Fin q) (v : V) : Prop :=
  ∃ e, c.color e = i ∧ v ∈ G.edge e

/-- Connectivity of the two selected colors, with parallel copies identified
only for the purpose of determining connected components. -/
def twoColorGraph (c : G.EdgeColoring q) (i j : Fin q) : SimpleGraph V where
  Adj u v := u ≠ v ∧ ∃ e, (c.color e = i ∨ c.color e = j) ∧
    u ∈ G.edge e ∧ v ∈ G.edge e
  symm := by
    rintro u v ⟨hne, e, hc, hu, hv⟩
    exact ⟨hne.symm, e, hc, hv, hu⟩
  loopless := by intro u h; exact h.1 rfl

theorem twoColorGraph_edge (c : G.EdgeColoring q) (i j : Fin q) (e : E)
    (he : c.color e = i ∨ c.color e = j) :
    (c.twoColorGraph i j).Adj (G.firstEnd e) (G.secondEnd e) := by
  refine ⟨G.endpoints_distinct e, e, he, ?_, ?_⟩
  · exact (G.incident_iff _ _).mpr (Or.inl rfl)
  · exact (G.incident_iff _ _).mpr (Or.inr rfl)

variable [Fintype V]

noncomputable def coveredVertices (c : G.EdgeColoring q) (i : Fin q) : Finset V :=
  univ.filter (c.Covers i)

@[simp] theorem mem_coveredVertices (c : G.EdgeColoring q) (i : Fin q) (v : V) :
    v ∈ c.coveredVertices i ↔ c.Covers i v := by simp [coveredVertices]

/-- No edge of either selected color crosses this vertex set. -/
def TwoColorClosed (c : G.EdgeColoring q) (i j : Fin q) (X : Finset V) : Prop :=
  ∀ e, (c.color e = i ∨ c.color e = j) →
    (G.firstEnd e ∈ X ↔ G.secondEnd e ∈ X)

omit [Fintype V] in
theorem closed_incident_iff (c : G.EdgeColoring q) {i j : Fin q} {X : Finset V}
    (hX : c.TwoColorClosed i j X) {e : E}
    (he : c.color e = i ∨ c.color e = j) {v : V} (hv : v ∈ G.edge e) :
    G.firstEnd e ∈ X ↔ v ∈ X := by
  rcases (G.incident_iff e v).mp hv with h | h
  · rw [h]
  · rw [← h]
    exact hX e he

omit [Fintype V] in
private theorem swap_color_at_vertex (c : G.EdgeColoring q) (i j : Fin q)
    (X : Finset V) (hX : c.TwoColorClosed i j X) (e : E) (v : V)
    (hv : v ∈ G.edge e) :
    (if G.firstEnd e ∈ X then Equiv.swap i j (c.color e) else c.color e) =
      if v ∈ X then Equiv.swap i j (c.color e) else c.color e := by
  by_cases hc : c.color e = i ∨ c.color e = j
  · simp only [c.closed_incident_iff hX hc hv]
  · have hi : c.color e ≠ i := fun h => hc (Or.inl h)
    have hj : c.color e ≠ j := fun h => hc (Or.inr h)
    simp only [Equiv.swap_apply_of_ne_of_ne hi hj, ite_self]

/-- Interchange the two colors on every selected-color edge in a closed set. -/
noncomputable def swapOn (c : G.EdgeColoring q) (i j : Fin q)
    (X : Finset V) (hX : c.TwoColorClosed i j X) : G.EdgeColoring q where
  color e := if G.firstEnd e ∈ X then Equiv.swap i j (c.color e) else c.color e
  proper := by
    intro e f v hef hev hfv
    rw [c.swap_color_at_vertex i j X hX e v hev,
      c.swap_color_at_vertex i j X hX f v hfv] at hef
    by_cases hv : v ∈ X
    · rw [if_pos hv, if_pos hv] at hef
      exact c.proper ((Equiv.swap i j).injective hef) hev hfv
    · rw [if_neg hv, if_neg hv] at hef
      exact c.proper hef hev hfv

omit [Fintype V] in
theorem swapOn_color_at_vertex (c : G.EdgeColoring q) (i j : Fin q)
    (X : Finset V) (hX : c.TwoColorClosed i j X) {e : E} {v : V}
    (hv : v ∈ G.edge e) :
    (c.swapOn i j X hX).color e =
      if v ∈ X then Equiv.swap i j (c.color e) else c.color e :=
  c.swap_color_at_vertex i j X hX e v hv

omit [Fintype V] in
theorem swapOn_covers (c : G.EdgeColoring q) (i j r : Fin q)
    (X : Finset V) (hX : c.TwoColorClosed i j X) (v : V) :
    (c.swapOn i j X hX).Covers r v ↔
      if v ∈ X then c.Covers (Equiv.swap i j r) v else c.Covers r v := by
  by_cases hv : v ∈ X
  · rw [if_pos hv]
    constructor
    · rintro ⟨e, he, hev⟩
      rw [c.swapOn_color_at_vertex i j X hX hev, if_pos hv] at he
      refine ⟨e, ?_, hev⟩
      have h := congrArg (Equiv.swap i j) he
      simpa only [Equiv.swap_apply_self] using h
    · rintro ⟨e, he, hev⟩
      refine ⟨e, ?_, hev⟩
      rw [c.swapOn_color_at_vertex i j X hX hev, if_pos hv, he,
        Equiv.swap_apply_self]
  · rw [if_neg hv]
    constructor <;> rintro ⟨e, he, hev⟩
    · exact ⟨e, by simpa only [c.swapOn_color_at_vertex i j X hX hev, if_neg hv] using he, hev⟩
    · exact ⟨e, by rw [c.swapOn_color_at_vertex i j X hX hev, if_neg hv]; exact he, hev⟩

noncomputable def componentVertices (c : G.EdgeColoring q) (i j : Fin q)
    (C : (c.twoColorGraph i j).ConnectedComponent) : Finset V := C.supp.toFinset

@[simp] theorem mem_componentVertices (c : G.EdgeColoring q) (i j : Fin q)
    (C : (c.twoColorGraph i j).ConnectedComponent) (v : V) :
    v ∈ c.componentVertices i j C ↔ v ∈ C.supp := Set.mem_toFinset

theorem component_closed (c : G.EdgeColoring q) (i j : Fin q)
    (C : (c.twoColorGraph i j).ConnectedComponent) :
    c.TwoColorClosed i j (c.componentVertices i j C) := by
  intro e he
  simp only [mem_componentVertices]
  exact C.mem_supp_congr_adj (c.twoColorGraph_edge i j e he)

omit [Fintype V] in
theorem closed_union (c : G.EdgeColoring q) {i j : Fin q} {X Y : Finset V}
    (hX : c.TwoColorClosed i j X) (hY : c.TwoColorClosed i j Y) :
    c.TwoColorClosed i j (X ∪ Y) := by
  intro e he
  simp only [Finset.mem_union, hX e he, hY e he]

theorem componentVertices_disjoint (c : G.EdgeColoring q) (i j : Fin q)
    {C D : (c.twoColorGraph i j).ConnectedComponent} (hCD : C ≠ D) :
    Disjoint (c.componentVertices i j C) (c.componentVertices i j D) := by
  apply Finset.disjoint_left.mpr
  intro v hC hD
  simp only [mem_componentVertices, SimpleGraph.ConnectedComponent.mem_supp_iff] at hC hD
  exact hCD (hC.symm.trans hD)

end Overfull.Multigraph.EdgeColoring
