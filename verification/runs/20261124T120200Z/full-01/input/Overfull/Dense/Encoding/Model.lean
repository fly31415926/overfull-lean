import Overfull.Konig
import Overfull.Dense.TriangleDecomposition

/-!
# The actual graphs and prescribed coloring in the tripartite encoding

The distinguished simple bipartite part has one possible edge for each pair
of opposite vertices. Its edges are injected into actual host edge copies.
The complementary copies form the graph carrying the prescribed coloring.
-/

namespace Overfull.Multigraph.EdgeColoring

open Finset Classical

variable {V E : Type*} {G : Multigraph V E} {k : ℕ}

/-- A color is available when no edge of that color meets the vertex. -/
def Available (c : G.EdgeColoring k) (v : V) (w : Fin k) : Prop :=
  ¬ ∃ e : E, v ∈ G.edge e ∧ c.color e = w

noncomputable def availableColors (c : G.EdgeColoring k) (v : V) : Finset (Fin k) :=
  univ.filter (c.Available v)

variable [Fintype E]

theorem color_injective_on_incident (c : G.EdgeColoring k) (v : V) :
    Set.InjOn c.color (G.incidenceEdges v) := by
  intro e he f hf hef
  exact c.proper hef ((G.mem_incidenceEdges v e).mp he) ((G.mem_incidenceEdges v f).mp hf)

/-- Properness counts one different used color per incident edge copy. -/
theorem availableColors_card_add_degree (c : G.EdgeColoring k) (v : V) :
    (c.availableColors v).card + G.degree v = k := by
  have hused : (univ.filter (fun w => ¬ c.Available v w)) =
      (G.incidenceEdges v).image c.color := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Available, not_not,
      Finset.mem_image, G.mem_incidenceEdges]
  have hpart := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (univ : Finset (Fin k))) (c.Available v)
  rw [hused, Finset.card_image_iff.mpr (c.color_injective_on_incident v)] at hpart
  simpa only [availableColors, Multigraph.degree, Finset.card_univ, Fintype.card_fin] using hpart

/-- At a vertex of degree `k`, a proper `k`-edge-coloring uses every color
on exactly one actual incident edge copy. -/
theorem incident_color_unique (c : G.EdgeColoring k) (v : V)
    (hdegree : G.degree v = k) (w : Fin k) :
    ∃! e : E, v ∈ G.edge e ∧ c.color e = w := by
  have hcard : ((G.incidenceEdges v).image c.color).card = Fintype.card (Fin k) := by
    rw [Finset.card_image_iff.mpr (c.color_injective_on_incident v)]
    simpa only [Fintype.card_fin, Multigraph.degree] using hdegree
  have hall := Finset.eq_univ_of_card ((G.incidenceEdges v).image c.color) hcard
  have hw : w ∈ (G.incidenceEdges v).image c.color := by rw [hall]; exact mem_univ _
  obtain ⟨e, he, hew⟩ := Finset.mem_image.mp hw
  refine ⟨e, ⟨(G.mem_incidenceEdges v e).mp he, hew⟩, ?_⟩
  intro f hf
  exact c.proper (hf.2.trans hew.symm) hf.1 ((G.mem_incidenceEdges v e).mp he)

end Overfull.Multigraph.EdgeColoring

namespace Overfull.Dense.Encoding

open Finset Classical

variable {A B E : Type*}

/-- The two endpoints of each actual edge copy on the specified sides. -/
structure Bipartition (G : Multigraph (A ⊕ B) E) where
  left : E → A
  right : E → B
  edge_eq : ∀ e, G.edge e = s(Sum.inl (left e), Sum.inr (right e))

noncomputable def Bipartition.of_crossing (G : Multigraph (A ⊕ B) E)
    (hcross : ∀ e, ∃ a b, G.edge e = s(Sum.inl a, Sum.inr b)) : Bipartition G where
  left e := (hcross e).choose
  right e := (hcross e).choose_spec.choose
  edge_eq e := (hcross e).choose_spec.choose_spec

namespace Bipartition

variable {G : Multigraph (A ⊕ B) E} (P : Bipartition G)

@[simp] theorem mem_left (e : E) (a : A) :
    Sum.inl a ∈ G.edge e ↔ P.left e = a := by
  rw [P.edge_eq]
  simp [eq_comm]

@[simp] theorem mem_right (e : E) (b : B) :
    Sum.inr b ∈ G.edge e ↔ P.right e = b := by
  rw [P.edge_eq]
  simp [eq_comm]

end Bipartition

/-- A simple bipartite subgraph whose unordered edges are represented by
distinct specified copies of the host. -/
structure SimplePart (G : Multigraph (A ⊕ B) E) where
  adj : A → B → Prop
  edgeMap : {p : A × B // adj p.1 p.2} ↪ E
  map_edge : ∀ e, G.edge (edgeMap e) = s(Sum.inl e.val.1, Sum.inr e.val.2)

namespace SimplePart

variable {G : Multigraph (A ⊕ B) E} (H : SimplePart G)

abbrev Edge := {p : A × B // H.adj p.1 p.2}

/-- The distinguished part as an ordinary simple graph on the actual sides. -/
def toSimpleGraph : SimpleGraph (A ⊕ B) where
  Adj x y := match x,y with
    | .inl a, .inr b => H.adj a b
    | .inr b, .inl a => H.adj a b
    | _, _ => False
  symm := by rintro (a | b) (a' | b') h <;> exact h
  loopless := by rintro (a | b) <;> exact not_false

variable [Fintype A] [Fintype B]

noncomputable def edges : Finset E := univ.map H.edgeMap

@[simp] theorem mem_edges (e : E) : e ∈ H.edges ↔ ∃ h : H.Edge, H.edgeMap h = e := by
  simp [edges]

noncomputable def edgeOfMem (e : E) (he : e ∈ H.edges) : H.Edge :=
  ((H.mem_edges e).mp he).choose

@[simp] theorem edgeMap_edgeOfMem (e : E) (he : e ∈ H.edges) :
    H.edgeMap (H.edgeOfMem e he) = e :=
  ((H.mem_edges e).mp he).choose_spec

@[simp] theorem edgeMap_mem_edges (e : H.Edge) : H.edgeMap e ∈ H.edges :=
  (H.mem_edges _).mpr ⟨e,rfl⟩

noncomputable def remainder : Multigraph (A ⊕ B) {e : E // e ∉ H.edges} :=
  MultigraphMatchingProbability.remainingGraph G H.edges

variable {k : ℕ}

/-- The tripartite graph of actual uncolored edges and available colors. -/
def encoded (c₀ : H.remainder.EdgeColoring k) : TripartiteGraph A B (Fin k) where
  ab := H.adj
  aw a w := c₀.Available (.inl a) w
  bw b w := c₀.Available (.inr b) w

def Extends (c₀ : H.remainder.EdgeColoring k) (c : G.EdgeColoring k) : Prop :=
  ∀ e : {e : E // e ∉ H.edges}, c.color e.val = c₀.color e

end SimplePart
end Overfull.Dense.Encoding

