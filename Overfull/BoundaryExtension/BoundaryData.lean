import Overfull.SparseColoring

/-!
# Actual boundary color classes and their core footprints

Each boundary edge is an original edge copy. Properness identifies its unique
core endpoint injectively within a color, so the forbidden set has exactly
the size of that color class. Counting all footprints is exactly counting
boundary incidences at the core vertex.
-/

namespace Overfull.BoundaryExtension

open Finset Classical

variable {V E : Type*} [Fintype E]

abbrev boundaryGraph (G : Multigraph V E) (U : Finset V) :=
  G.restrictEdges (G.cutEdges U)

private theorem exists_boundary_ends (G : Multigraph V E) (U : Finset V)
    (e : G.cutEdges U) :
    ∃ p : U × {v : V // v ∉ U}, G.edge e.val = s(p.1.val, p.2.val) := by
  obtain ⟨v, w, he, hv, hw⟩ := (G.mem_cutEdges_iff U e.val).mp e.property
  exact ⟨(⟨v, hv⟩, ⟨w, hw⟩), he⟩

noncomputable def boundaryEnds (G : Multigraph V E) (U : Finset V)
    (e : G.cutEdges U) : U × {v : V // v ∉ U} :=
  (exists_boundary_ends G U e).choose

noncomputable def boundaryEnd (G : Multigraph V E) (U : Finset V)
    (e : G.cutEdges U) : U := (boundaryEnds G U e).1

theorem boundary_edge_eq (G : Multigraph V E) (U : Finset V)
    (e : G.cutEdges U) :
    G.edge e.val = s((boundaryEnd G U e).val, (boundaryEnds G U e).2.val) :=
  (exists_boundary_ends G U e).choose_spec

theorem boundaryEnd_incident (G : Multigraph V E) (U : Finset V)
    (e : G.cutEdges U) : (boundaryEnd G U e).val ∈ G.edge e.val := by
  rw [boundary_edge_eq]
  exact Sym2.mem_mk_left _ _

theorem boundary_incident_iff (G : Multigraph V E) (U : Finset V)
    (e : G.cutEdges U) (v : U) :
    v.val ∈ G.edge e.val ↔ v = boundaryEnd G U e := by
  rw [boundary_edge_eq, Sym2.mem_iff]
  constructor
  · rintro (h | h)
    · exact Subtype.ext h
    · exact ((boundaryEnds G U e).2.property (h ▸ v.property)).elim
  · intro h
    exact Or.inl (congrArg Subtype.val h)

variable {G : Multigraph V E} {U : Finset V} {d : ℕ}

/-- A precoloring records the exact labels of every original boundary copy. -/
abbrev BoundaryColoring (G : Multigraph V E) (U : Finset V) (d : ℕ) :=
  (boundaryGraph G U).EdgeColoring d

namespace BoundaryColoring

noncomputable def classEdges (c : BoundaryColoring G U d) (i : Fin d) :
    Finset (G.cutEdges U) := univ.filter (fun e => c.color e = i)

noncomputable def footprint (c : BoundaryColoring G U d) (i : Fin d) : Finset U :=
  (c.classEdges i).image (boundaryEnd G U)

@[simp] theorem mem_classEdges (c : BoundaryColoring G U d) (i : Fin d)
    (e : G.cutEdges U) : e ∈ c.classEdges i ↔ c.color e = i := by simp [classEdges]

theorem mem_footprint (c : BoundaryColoring G U d) (i : Fin d) (v : U) :
    v ∈ c.footprint i ↔ ∃ e : G.cutEdges U, c.color e = i ∧ v.val ∈ G.edge e.val := by
  simp only [footprint, Finset.mem_image, mem_classEdges, boundary_incident_iff]
  constructor
  · rintro ⟨e, he, hv⟩
    exact ⟨e, he, hv.symm⟩
  · rintro ⟨e, he, hv⟩
    exact ⟨e, he, hv.symm⟩

theorem footprint_card (c : BoundaryColoring G U d) (i : Fin d) :
    (c.footprint i).card = (c.classEdges i).card := by
  apply Finset.card_image_iff.mpr
  intro e he f hf hends
  apply c.proper ((mem_classEdges c i e).mp he |>.trans ((mem_classEdges c i f).mp hf).symm)
    (v := (boundaryEnd G U e).val)
  · exact boundaryEnd_incident G U e
  · rw [hends]
    exact boundaryEnd_incident G U f

/-- A core vertex appears once for each boundary edge incident with it. -/
theorem footprint_incidence_eq_degree (c : BoundaryColoring G U d) (v : U) :
    (univ.filter (fun i : Fin d => v ∈ c.footprint i)).card =
      (boundaryGraph G U).degree v.val := by
  have himage : ((boundaryGraph G U).incidenceEdges v.val).image c.color =
      univ.filter (fun i : Fin d => v ∈ c.footprint i) := by
    ext i
    simp only [Finset.mem_image, Multigraph.mem_incidenceEdges,
      Finset.mem_filter, Finset.mem_univ, true_and, mem_footprint]
    constructor
    · rintro ⟨e, he, hi⟩
      exact ⟨e, hi, he⟩
    · rintro ⟨e, hi, he⟩
      exact ⟨e, he, hi⟩
  rw [← himage, Multigraph.degree]
  apply Finset.card_image_iff.mpr
  intro e he f hf hcolor
  exact c.proper hcolor ((boundaryGraph G U).mem_incidenceEdges v.val e |>.mp he)
    ((boundaryGraph G U).mem_incidenceEdges v.val f |>.mp hf)

theorem selected_footprint_incidence_le {J : Type*} [Fintype J]
    (c : BoundaryColoring G U d) (label : J ↪ Fin d) (v : U) :
    (univ.filter (fun j : J => v ∈ c.footprint (label j))).card ≤
      (boundaryGraph G U).degree v.val := by
  rw [← c.footprint_incidence_eq_degree v]
  apply Finset.card_le_card_of_injOn label
  · intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩
  · exact label.injective.injOn

noncomputable def singletonColors (c : BoundaryColoring G U d) : Finset (Fin d) :=
  univ.filter (fun i => (c.classEdges i).card = 1)

noncomputable def tripleColors (c : BoundaryColoring G U d) : Finset (Fin d) :=
  univ.filter (fun i => (c.classEdges i).card = 3)

theorem singletons_add_triples (c : BoundaryColoring G U d)
    (hclasses : ∀ i, (c.classEdges i).card = 1 ∨ (c.classEdges i).card = 3) :
    c.singletonColors.card + c.tripleColors.card = d := by
  have htriple : c.tripleColors =
      univ.filter (fun i : Fin d => ¬ (c.classEdges i).card = 1) := by
    ext i
    simp only [tripleColors, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hclasses i with h | h <;> simp [h]
  rw [htriple]
  simpa only [singletonColors, Finset.card_univ, Fintype.card_fin] using
    Finset.filter_card_add_filter_neg_card_eq_card
      (s := (univ : Finset (Fin d))) (fun i => (c.classEdges i).card = 1)

/-- The singleton reserve is exactly the room needed in the packing
horizon after every triple class is selected. -/
theorem triple_horizon (c : BoundaryColoring G U d) (γ : ℝ)
    (hclasses : ∀ i, (c.classEdges i).card = 1 ∨ (c.classEdges i).card = 3)
    (hsingle : γ * U.card ≤ c.singletonColors.card) :
    c.tripleColors.card ≤ Nat.floor ((d : ℝ) - γ * U.card) := by
  apply Nat.le_floor
  have h := c.singletons_add_triples hclasses
  have hreal : (c.singletonColors.card : ℝ) + c.tripleColors.card = d := by exact_mod_cast h
  linarith

/-- The prescribed labels remain explicit when triples are enumerated. -/
noncomputable def tripleLabel (c : BoundaryColoring G U d) :
    Fin c.tripleColors.card ↪ Fin d :=
  c.tripleColors.equivFin.symm.toEmbedding.trans
    ⟨Subtype.val, Subtype.val_injective⟩

theorem tripleLabel_mem (c : BoundaryColoring G U d) (j : Fin c.tripleColors.card) :
    c.tripleLabel j ∈ c.tripleColors :=
  (c.tripleColors.equivFin.symm j).property

theorem tripleLabel_range (c : BoundaryColoring G U d) (i : Fin d) :
    i ∈ c.tripleColors ↔ ∃ j : Fin c.tripleColors.card, c.tripleLabel j = i := by
  constructor
  · intro hi
    refine ⟨c.tripleColors.equivFin ⟨i, hi⟩, ?_⟩
    change (c.tripleColors.equivFin.symm (c.tripleColors.equivFin ⟨i, hi⟩)).val = i
    rw [Equiv.symm_apply_apply]
  · rintro ⟨j, rfl⟩
    exact c.tripleLabel_mem j

theorem triple_footprint_card (c : BoundaryColoring G U d) (j : Fin c.tripleColors.card) :
    (c.footprint (c.tripleLabel j)).card = 3 := by
  rw [c.footprint_card]
  exact (Finset.mem_filter.mp (c.tripleLabel_mem j)).2

end BoundaryColoring

end Overfull.BoundaryExtension

