import Overfull.TwoColorSwitch

/-!
# Endpoints of a component in two color classes

The simple graph is used only for its connected-component edge bound.
The handshake and degree counts retain every actual multigraph edge copy.
-/

namespace Overfull.Multigraph.EdgeColoring

open Finset Classical
open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E]
variable {G : Multigraph V E} {q : ℕ} (c : G.EdgeColoring q)

noncomputable def colorIncidence (i : Fin q) (v : V) : Finset E :=
  univ.filter (fun e => c.color e = i ∧ v ∈ G.edge e)

omit [Fintype V] in
theorem colorIncidence_card (i : Fin q) (v : V) :
    (c.colorIncidence i v).card = if c.Covers i v then 1 else 0 := by
  by_cases h : c.Covers i v
  · obtain ⟨e,he,hev⟩ := h
    have hs : c.colorIncidence i v = {e} := by
      ext f
      simp only [colorIncidence, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      constructor
      · intro hf
        exact c.proper (hf.1.trans he.symm) hf.2 hev
      · rintro rfl
        exact ⟨he,hev⟩
    rw [hs, Finset.card_singleton, if_pos ⟨e,he,hev⟩]
  · have hs : c.colorIncidence i v = ∅ := by
      ext e
      simp only [colorIncidence, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.notMem_empty, iff_false]
      exact fun he => h ⟨e,he.1,he.2⟩
    rw [hs, Finset.card_empty, if_neg h]

/-- The selected actual edge copies in a component. -/
noncomputable def componentEdges (i j : Fin q)
    (C : (c.twoColorGraph i j).ConnectedComponent) : Finset E :=
  univ.filter (fun e => (c.color e = i ∨ c.color e = j) ∧
    G.firstEnd e ∈ c.componentVertices i j C)

/-- Vertices incident with exactly one of the two colors. -/
noncomputable def componentEndpoints (i j : Fin q)
    (C : (c.twoColorGraph i j).ConnectedComponent) : Finset V :=
  (c.componentVertices i j C).filter (fun v => (c.Covers i v ∧ ¬ c.Covers j v) ∨ (c.Covers j v ∧ ¬ c.Covers i v))

theorem componentEdges_endpoints (i j : Fin q)
    (C : (c.twoColorGraph i j).ConnectedComponent) {e : E}
    (he : e ∈ c.componentEdges i j C) :
    G.firstEnd e ∈ c.componentVertices i j C ∧
      G.secondEnd e ∈ c.componentVertices i j C := by
  obtain ⟨hcolor,hfirst⟩ := (Finset.mem_filter.mp he).2
  exact ⟨hfirst, (c.component_closed i j C e hcolor).mp hfirst⟩

theorem component_incidence_card (i j : Fin q) (hij : i ≠ j)
    (C : (c.twoColorGraph i j).ConnectedComponent) {v : V}
    (hv : v ∈ c.componentVertices i j C) :
    ((c.componentEdges i j C).filter (fun e => v ∈ G.edge e)).card =
      (if c.Covers i v then 1 else 0) + (if c.Covers j v then 1 else 0) := by
  have heq : (c.componentEdges i j C).filter (fun e => v ∈ G.edge e) =
      c.colorIncidence i v ∪ c.colorIncidence j v := by
    ext e
    simp only [componentEdges, colorIncidence, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_union]
    constructor
    · rintro ⟨⟨he,_⟩,hev⟩
      exact he.elim (fun h => Or.inl ⟨h,hev⟩) (fun h => Or.inr ⟨h,hev⟩)
    · rintro (⟨h,hev⟩ | ⟨h,hev⟩)
      · exact ⟨⟨Or.inl h,
          (c.closed_incident_iff (c.component_closed i j C) (Or.inl h) hev).mpr hv⟩,hev⟩
      · exact ⟨⟨Or.inr h,
          (c.closed_incident_iff (c.component_closed i j C) (Or.inr h) hev).mpr hv⟩,hev⟩
  have hdisj : Disjoint (c.colorIncidence i v) (c.colorIncidence j v) := by
    apply Finset.disjoint_left.mpr
    intro e hi hj
    exact hij ((Finset.mem_filter.mp hi).2.1.symm.trans (Finset.mem_filter.mp hj).2.1)
  rw [heq, Finset.card_union_of_disjoint hdisj, c.colorIncidence_card,
    c.colorIncidence_card]

theorem component_incidence_sum (i j : Fin q)
    (C : (c.twoColorGraph i j).ConnectedComponent) :
    (∑ v ∈ c.componentVertices i j C,
      ((c.componentEdges i j C).filter (fun e => v ∈ G.edge e)).card) =
      2 * (c.componentEdges i j C).card := by
  have hsum : (∑ v ∈ c.componentVertices i j C,
      ((c.componentEdges i j C).filter (fun e => v ∈ G.edge e)).card) =
      ∑ e ∈ c.componentEdges i j C,
        ((c.componentVertices i j C).filter (fun v => v ∈ G.edge e)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  rw [hsum]
  have htwo (e : E) (he : e ∈ c.componentEdges i j C) :
      ((c.componentVertices i j C).filter (fun v => v ∈ G.edge e)).card = 2 := by
    have hend := c.componentEdges_endpoints i j C he
    have hs : (c.componentVertices i j C).filter (fun v => v ∈ G.edge e) =
        {G.firstEnd e,G.secondEnd e} := by
      ext v
      simp only [Finset.mem_filter, G.incident_iff, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · rintro ⟨_,h | h⟩
        · exact Or.inl h.symm
        · exact Or.inr h.symm
      · rintro (rfl | rfl)
        · exact ⟨hend.1,Or.inl rfl⟩
        · exact ⟨hend.2,Or.inr rfl⟩
    rw [hs]
    simp [G.endpoints_distinct e]
  calc
    _ = ∑ _e ∈ c.componentEdges i j C, 2 := Finset.sum_congr rfl htwo
    _ = _ := by simp [Nat.mul_comm]

theorem componentEndpoints_handshake (i j : Fin q) (hij : i ≠ j)
    (C : (c.twoColorGraph i j).ConnectedComponent) :
    (c.componentEndpoints i j C).card + 2 * (c.componentEdges i j C).card =
      2 * ((c.componentVertices i j C).filter
        (fun v => c.Covers i v ∨ c.Covers j v)).card := by
  rw [← c.component_incidence_sum i j C]
  simp only [componentEndpoints, Finset.card_eq_sum_ones, Finset.sum_filter,
    ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  have hinc := c.component_incidence_card i j hij C hv
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter] at hinc
  rw [hinc]
  by_cases hi : c.Covers i v <;> by_cases hj : c.Covers j v <;> simp [hi,hj]

theorem componentEndpoints_even (i j : Fin q) (hij : i ≠ j)
    (C : (c.twoColorGraph i j).ConnectedComponent) :
    Even (c.componentEndpoints i j C).card := by
  have h := c.componentEndpoints_handshake i j hij C
  rw [Nat.even_iff]
  omega

/-- Every edge of the component's simple connectivity graph comes from
an actual selected edge copy. -/
theorem component_simple_edge_lift (i j : Fin q)
    (C : (c.twoColorGraph i j).ConnectedComponent) (z : C.toSimpleGraph.edgeSet) :
    ∃ e ∈ c.componentEdges i j C,
      G.edge e = Sym2.map (fun v : C => v.val) z.val := by
  rcases z with ⟨z,hz⟩
  induction z using Sym2.ind with
  | h u v =>
    have hadj : (c.twoColorGraph i j).Adj u.val v.val := hz
    obtain ⟨hne,e,hcolor,heu,hev⟩ := hadj
    have hfirst : G.firstEnd e ∈ c.componentVertices i j C :=
      (c.closed_incident_iff (c.component_closed i j C) hcolor heu).mpr
        ((c.mem_componentVertices i j C u.val).mpr u.property)
    refine ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hcolor,hfirst⟩, ?_⟩
    exact (Sym2.mem_and_mem_iff hne).mp ⟨heu,hev⟩

theorem componentVertices_card_le_edges_add_one (i j : Fin q)
    (C : (c.twoColorGraph i j).ConnectedComponent) :
    (c.componentVertices i j C).card ≤ (c.componentEdges i j C).card + 1 := by
  choose f hf hmap using c.component_simple_edge_lift i j C
  let g : C.toSimpleGraph.edgeSet → {e // e ∈ c.componentEdges i j C} :=
    fun z => ⟨f z,hf z⟩
  have hginj : Function.Injective g := by
    intro z w hzw
    have hfw : f z = f w := congrArg Subtype.val hzw
    apply Subtype.ext
    apply Sym2.map.injective Subtype.val_injective
    rw [← hmap z, ← hmap w, hfw]
  have hecard : Nat.card C.toSimpleGraph.edgeSet ≤ (c.componentEdges i j C).card := by
    have h := Nat.card_le_card_of_injective g hginj
    simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using h
  have hvcard : Nat.card C = (c.componentVertices i j C).card := by
    change Nat.card {v : V // v ∈ C.supp} = _
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext v
    simp
  have hconn := C.connected_toSimpleGraph.card_vert_le_card_edgeSet_add_one
  omega

/-- There are at most two vertices incident with exactly one selected
color, even when the host has parallel edge copies. -/
theorem componentEndpoints_card_le_two (i j : Fin q) (hij : i ≠ j)
    (C : (c.twoColorGraph i j).ConnectedComponent) :
    (c.componentEndpoints i j C).card ≤ 2 := by
  have hhand := c.componentEndpoints_handshake i j hij C
  have hconn := c.componentVertices_card_le_edges_add_one i j C
  have hsub := Finset.card_filter_le (c.componentVertices i j C)
    (fun v => c.Covers i v ∨ c.Covers j v)
  omega

theorem componentEndpoints_card (i j : Fin q) (hij : i ≠ j)
    (C : (c.twoColorGraph i j).ConnectedComponent) :
    (c.componentEndpoints i j C).card ≤ 2 ∧ Even (c.componentEndpoints i j C).card :=
  ⟨c.componentEndpoints_card_le_two i j hij C, c.componentEndpoints_even i j hij C⟩

end Overfull.Multigraph.EdgeColoring
