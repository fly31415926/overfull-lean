import Overfull.BoundaryExtension.BoundaryData

/-!
# Exact singleton labels on the surviving boundary

Restricting a host preserves each surviving boundary edge copy.  If exactly
the triple-colored boundary copies were deleted, the residual boundary is
bijective with the original singleton palette.  Its labels and cardinality
are therefore conclusions of the actual deletion.
-/

namespace Overfull.BoundaryExtension

open Finset Classical

variable {V E : Type*} [Fintype E]

@[simp] theorem restrictedBoundary_mem_iff (G : Multigraph V E) (U : Finset V)
    (F : Finset E) (e : F) :
    e ∈ (G.restrictEdges F).cutEdges U ↔ e.val ∈ G.cutEdges U := by
  rw [(G.restrictEdges F).mem_cutEdges, G.mem_cutEdges]
  rfl

/-- A boundary edge of an edge-restricted host is the same original boundary copy. -/
def restrictedBoundaryEmbedding (G : Multigraph V E) (U : Finset V) (F : Finset E) :
    ↥((G.restrictEdges F).cutEdges U) ↪ ↥(G.cutEdges U) where
  toFun e := ⟨e.val.val, by
    rw [G.mem_cutEdges]
    exact ((G.restrictEdges F).mem_cutEdges U e.val).mp e.property⟩
  inj' := by
    intro e f h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : G.cutEdges U => x.val) h

@[simp] theorem restrictedBoundaryEmbedding_val (G : Multigraph V E)
    (U : Finset V) (F : Finset E) (e : (G.restrictEdges F).cutEdges U) :
    (restrictedBoundaryEmbedding G U F e).val = e.val.val := rfl

/-- An original boundary copy survives whenever its original edge is retained. -/
def restrictedBoundaryLift (G : Multigraph V E) (U : Finset V) (F : Finset E)
    (e : G.cutEdges U) (he : e.val ∈ F) : (G.restrictEdges F).cutEdges U :=
  ⟨⟨e.val, he⟩, by
    rw [(G.restrictEdges F).mem_cutEdges]
    exact (G.mem_cutEdges U e.val).mp e.property⟩

@[simp] theorem restrictedBoundaryEmbedding_lift (G : Multigraph V E)
    (U : Finset V) (F : Finset E) (e : G.cutEdges U) (he : e.val ∈ F) :
    restrictedBoundaryEmbedding G U F (restrictedBoundaryLift G U F e he) = e := rfl

namespace BoundaryColoring

variable {G : Multigraph V E} {U : Finset V} {d : ℕ}

/-- A singleton label belongs to exactly one original boundary edge copy. -/
theorem eq_of_singleton_color (c : BoundaryColoring G U d) (i : Fin d)
    (hi : i ∈ c.singletonColors) {e f : G.cutEdges U}
    (he : c.color e = i) (hf : c.color f = i) : e = f := by
  have hcard : (c.classEdges i).card = 1 := (Finset.mem_filter.mp hi).2
  exact Finset.card_le_one.mp hcard.le e ((c.mem_classEdges i e).mpr he)
    f ((c.mem_classEdges i f).mpr hf)

section Deletion

variable [DecidableEq E]

/-- The surviving edge retains its original prescribed color label. -/
def residualLabel (c : BoundaryColoring G U d) (D : Finset E)
    (e : (G.restrictEdges Dᶜ).cutEdges U) : Fin d :=
  c.color (restrictedBoundaryEmbedding G U Dᶜ e)

@[simp] theorem residualLabel_lift (c : BoundaryColoring G U d) (D : Finset E)
    (e : G.cutEdges U) (he : e.val ∈ Dᶜ) :
    residualLabel c D (restrictedBoundaryLift G U Dᶜ e he) = c.color e := by
  simp only [residualLabel, restrictedBoundaryEmbedding_lift]

theorem residualLabel_not_mem_triples (c : BoundaryColoring G U d) (D : Finset E)
    (hdeleted : ∀ e : G.cutEdges U, e.val ∈ D ↔ c.color e ∈ c.tripleColors)
    (e : (G.restrictEdges Dᶜ).cutEdges U) : residualLabel c D e ∉ c.tripleColors := by
  intro h
  exact (Finset.mem_compl.mp e.val.property)
    ((hdeleted (restrictedBoundaryEmbedding G U Dᶜ e)).mpr h)

theorem residualLabel_mem_singleton (c : BoundaryColoring G U d) (D : Finset E)
    (hclasses : ∀ i, (c.classEdges i).card = 1 ∨ (c.classEdges i).card = 3)
    (hdeleted : ∀ e : G.cutEdges U, e.val ∈ D ↔ c.color e ∈ c.tripleColors)
    (e : (G.restrictEdges Dᶜ).cutEdges U) : residualLabel c D e ∈ c.singletonColors := by
  have hnottriple := c.residualLabel_not_mem_triples D hdeleted e
  rcases hclasses (residualLabel c D e) with h | h
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
  · exact (hnottriple (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)).elim

/-- Distinct surviving boundary copies have distinct original singleton labels. -/
theorem residualLabel_injective (c : BoundaryColoring G U d) (D : Finset E)
    (hclasses : ∀ i, (c.classEdges i).card = 1 ∨ (c.classEdges i).card = 3)
    (hdeleted : ∀ e : G.cutEdges U, e.val ∈ D ↔ c.color e ∈ c.tripleColors) :
    Function.Injective (residualLabel c D) := by
  intro e f h
  apply (restrictedBoundaryEmbedding G U Dᶜ).injective
  exact c.eq_of_singleton_color (residualLabel c D e)
    (c.residualLabel_mem_singleton D hclasses hdeleted e) rfl h.symm

theorem residualLabel_surjective (c : BoundaryColoring G U d) (D : Finset E)
    (hdeleted : ∀ e : G.cutEdges U, e.val ∈ D ↔ c.color e ∈ c.tripleColors)
    (i : c.singletonColors) :
    ∃ e : (G.restrictEdges Dᶜ).cutEdges U, residualLabel c D e = i.val := by
  have hcard : (c.classEdges i.val).card = 1 := (Finset.mem_filter.mp i.property).2
  obtain ⟨e, he⟩ := Finset.card_pos.mp (by omega : 0 < (c.classEdges i.val).card)
  have hcolor : c.color e = i.val := (c.mem_classEdges i.val e).mp he
  have hnottriple : c.color e ∉ c.tripleColors := by
    rw [hcolor]
    simp only [tripleColors, Finset.mem_filter, Finset.mem_univ, true_and, hcard]
    norm_num
  have hsurvives : e.val ∈ Dᶜ := by
    apply Finset.mem_compl.mpr
    intro h
    exact hnottriple ((hdeleted e).mp h)
  refine ⟨restrictedBoundaryLift G U Dᶜ e hsurvives, ?_⟩
  unfold residualLabel
  rw [restrictedBoundaryEmbedding_lift]
  exact hcolor

/-- The actual surviving boundary and the original singleton palette correspond
bijectively, through the prescribed color of each original copy. -/
noncomputable def singletonBoundaryEquiv (c : BoundaryColoring G U d) (D : Finset E)
    (hclasses : ∀ i, (c.classEdges i).card = 1 ∨ (c.classEdges i).card = 3)
    (hdeleted : ∀ e : G.cutEdges U, e.val ∈ D ↔ c.color e ∈ c.tripleColors) :
    ↥((G.restrictEdges Dᶜ).cutEdges U) ≃ ↥(c.singletonColors) :=
  Equiv.ofBijective
    (fun e => ⟨residualLabel c D e, c.residualLabel_mem_singleton D hclasses hdeleted e⟩)
    (by
      constructor
      · intro e f h
        exact c.residualLabel_injective D hclasses hdeleted (congrArg Subtype.val h)
      · intro i
        obtain ⟨e, he⟩ := c.residualLabel_surjective D hdeleted i
        exact ⟨e, Subtype.ext he⟩)

@[simp] theorem singletonBoundaryEquiv_val (c : BoundaryColoring G U d) (D : Finset E)
    (hclasses : ∀ i, (c.classEdges i).card = 1 ∨ (c.classEdges i).card = 3)
    (hdeleted : ∀ e : G.cutEdges U, e.val ∈ D ↔ c.color e ∈ c.tripleColors)
    (e : (G.restrictEdges Dᶜ).cutEdges U) :
    (c.singletonBoundaryEquiv D hclasses hdeleted e).val = residualLabel c D e := rfl

/-- The residual boundary count is derived from the actual singleton labels. -/
theorem residual_cutSize_eq_singletons (c : BoundaryColoring G U d) (D : Finset E)
    (hclasses : ∀ i, (c.classEdges i).card = 1 ∨ (c.classEdges i).card = 3)
    (hdeleted : ∀ e : G.cutEdges U, e.val ∈ D ↔ c.color e ∈ c.tripleColors) :
    (G.restrictEdges Dᶜ).cutSize U = c.singletonColors.card := by
  have h := Fintype.card_congr (c.singletonBoundaryEquiv D hclasses hdeleted)
  simpa only [Fintype.card_coe, Multigraph.cutSize] using h

theorem residual_cutSize_eq_sub (c : BoundaryColoring G U d) (D : Finset E)
    (hclasses : ∀ i, (c.classEdges i).card = 1 ∨ (c.classEdges i).card = 3)
    (hdeleted : ∀ e : G.cutEdges U, e.val ∈ D ↔ c.color e ∈ c.tripleColors) :
    (G.restrictEdges Dᶜ).cutSize U = d - c.tripleColors.card := by
  rw [c.residual_cutSize_eq_singletons D hclasses hdeleted]
  have h := c.singletons_add_triples hclasses
  omega

end Deletion

end BoundaryColoring

end Overfull.BoundaryExtension
