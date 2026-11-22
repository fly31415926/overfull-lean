import Overfull.OrdinaryFactorization.Assembly

/-!
# Exact residual accounting after the completed exterior classes

The residual host deletes the union of the completed original edge-copy
classes. Every vertex loses exactly one incidence per selected label. Among
the original complementary copies, deletion is exactly selection of their
original colors. The surviving complementary restriction inherits its proper
coloring; no coloring of the whole residual graph is assumed.
-/

noncomputable section

namespace Overfull.OrdinaryFactorization

open Finset Classical SmallCuts BoundaryExtension

variable {V E : Type*} [Fintype E]
variable {G : Multigraph V E} {U : Finset V} {k h : ℕ}
variable (C : Core G U)
variable (c : (G.restrictEdges (OneCore.coreEdges C)ᶜ).EdgeColoring k)
variable (l : Fin h ↪ Fin k) (N : Fin h → C.graph.Subgraph)

/-- The original host copies removed by all completed selected classes. -/
def deleted : Finset E := univ.biUnion (completedClass C c l N)

@[simp] theorem mem_deleted (e : E) :
    e ∈ deleted C c l N ↔ ∃ i, e ∈ completedClass C c l N i := by
  simp only [deleted, mem_biUnion, mem_univ, true_and]

theorem deleted_complement (e : ↥((OneCore.coreEdges C)ᶜ)) :
    e.val ∈ deleted C c l N ↔ ∃ i, c.color e = l i := by
  rw [mem_deleted]
  exact exists_congr (fun i => completedClass_complement C c l N i e)

/-- A complementary copy is removed precisely when its original label is selected. -/
theorem deleted_complement_range (e : ↥((OneCore.coreEdges C)ᶜ)) :
    e.val ∈ deleted C c l N ↔ c.color e ∈ Set.range l := by
  rw [deleted_complement, Set.mem_range]
  exact exists_congr (fun _ => eq_comm)

theorem complement_survives_iff (e : ↥((OneCore.coreEdges C)ᶜ)) :
    e.val ∈ (deleted C c l N)ᶜ ↔ c.color e ∉ Set.range l := by
  rw [mem_compl, deleted_complement_range]

/-- Delete exactly the completed classes, retaining every other original copy. -/
def residualGraph : Multigraph V ↥((deleted C c l N)ᶜ) :=
  G.restrictEdges (deleted C c l N)ᶜ

section Degree

variable [Fintype V]
variable (hN : ∀ i, (N i).IsMatching)
variable (hverts : ∀ i, (N i).verts = (selectedFootprint C c l i : Set U)ᶜ)
variable (hdisj : Pairwise (fun i j => Disjoint (N i).spanningCoe (N j).spanningCoe))
variable (hregular : ∀ v, G.degree v = k)

include hN hverts hdisj hregular

/-- Every selected class removes one incidence at every host vertex. -/
theorem deleted_incidence_card (v : V) :
    ((deleted C c l N).filter (fun e => v ∈ G.edge e)).card = h := by
  have hsets : (deleted C c l N).filter (fun e => v ∈ G.edge e) =
      univ.biUnion (fun i => (completedClass C c l N i).filter
        (fun e => v ∈ G.edge e)) := by
    ext e
    simp only [mem_filter, mem_deleted, mem_biUnion, mem_univ, true_and]
    constructor
    · rintro ⟨⟨i, hi⟩, hv⟩
      exact ⟨i, hi, hv⟩
    · rintro ⟨i, hi, hv⟩
      exact ⟨⟨i, hi⟩, hv⟩
  rw [hsets, Finset.card_biUnion]
  · simp only [completedClass_incidence_card C c l N hN hverts hregular,
      sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  · intro i _hi j _hj hij
    exact (completedClass_pairwiseDisjoint C c l N hdisj hij).mono
      (filter_subset _ _) (filter_subset _ _)

theorem deleted_degree (v : V) :
    (G.restrictEdges (deleted C c l N)).degree v = h := by
  rw [Multigraph.restrictEdges_degree]
  have hsets : deleted C c l N ∩ G.incidenceEdges v =
      (deleted C c l N).filter (fun e => v ∈ G.edge e) := by
    ext e
    simp only [mem_inter, Multigraph.mem_incidenceEdges, mem_filter]
  rw [hsets, deleted_incidence_card C c l N hN hverts hdisj hregular]

/-- Exact degree accounting precedes the natural-number subtraction. -/
theorem residualGraph_degree_add (v : V) :
    (residualGraph C c l N).degree v + h = G.degree v := by
  have hh := OneCore.complement_degree_add G (deleted C c l N) v
  rw [deleted_degree C c l N hN hverts hdisj hregular v] at hh
  exact hh

theorem residualGraph_regular (v : V) :
    (residualGraph C c l N).degree v = k - h := by
  have hh := residualGraph_degree_add C c l N hN hverts hdisj hregular v
  rw [hregular v] at hh
  omega

end Degree

/-- The residual edge copies that belonged to the original core complement. -/
def residualComplementEdges : Finset ↥((deleted C c l N)ᶜ) :=
  univ.filter (fun e => e.val ∈ (OneCore.coreEdges C)ᶜ)

@[simp] theorem mem_residualComplementEdges (e : ↥((deleted C c l N)ᶜ)) :
    e ∈ residualComplementEdges C c l N ↔ e.val ∈ (OneCore.coreEdges C)ᶜ := by
  simp only [residualComplementEdges, mem_filter, mem_univ, true_and]

/-- Forgetting the residual restriction keeps exactly the original complementary copy. -/
def residualComplementOriginal :
    ↥(residualComplementEdges C c l N) ↪ ↥((OneCore.coreEdges C)ᶜ) where
  toFun e := ⟨e.val.val, (mem_residualComplementEdges C c l N e.val).mp e.property⟩
  inj' := by
    intro e f hef
    have hval : e.val.val = f.val.val :=
      congrArg (fun a : ↥((OneCore.coreEdges C)ᶜ) => a.val) hef
    exact Subtype.ext (Subtype.ext hval)

@[simp] theorem residualComplementOriginal_val (e : ↥(residualComplementEdges C c l N)) :
    (residualComplementOriginal C c l N e).val = e.val.val := rfl

/-- The actual residual complementary restriction keeps its original proper labels. -/
def residualComplementColoring :
    ((residualGraph C c l N).restrictEdges (residualComplementEdges C c l N)).EdgeColoring k where
  color e := c.color (residualComplementOriginal C c l N e)
  proper := by
    intro e f v hef hev hfv
    apply (residualComplementOriginal C c l N).injective
    exact c.proper hef hev hfv

@[simp] theorem residualComplementColoring_color
    (e : ↥(residualComplementEdges C c l N)) :
    (residualComplementColoring C c l N).color e =
      c.color (residualComplementOriginal C c l N e) := rfl

theorem residualComplementColoring_avoids_selected
    (e : ↥(residualComplementEdges C c l N)) :
    (residualComplementColoring C c l N).color e ∉ Set.range l := by
  change c.color (residualComplementOriginal C c l N e) ∉ Set.range l
  exact (complement_survives_iff C c l N (residualComplementOriginal C c l N e)).mp
    e.val.property

/-- Conversely, every original complementary copy with an unselected label
occurs in the actual residual complementary restriction. -/
theorem residualComplementOriginal_surjective_onto
    (e : ↥((OneCore.coreEdges C)ᶜ)) (he : c.color e ∉ Set.range l) :
    ∃ f : ↥(residualComplementEdges C c l N), residualComplementOriginal C c l N f = e := by
  let r : ↥((deleted C c l N)ᶜ) :=
    ⟨e.val, (complement_survives_iff C c l N e).mpr he⟩
  let f : ↥(residualComplementEdges C c l N) :=
    ⟨r, (mem_residualComplementEdges C c l N r).mpr e.property⟩
  exact ⟨f, Subtype.ext rfl⟩

end Overfull.OrdinaryFactorization
