import Overfull.Konig
import Mathlib.Data.Fintype.EquivFin

/-!
# Exact palette alignment at a saturated vertex

The palette may be any finite type, including a subtype of the original
labels. A proper coloring uses every palette label exactly once at a
vertex whose degree equals the palette cardinality. This gives the
explicit permutation needed to restore prescribed singleton colors.
-/

noncomputable section

namespace Overfull.Multigraph

open Finset Classical

variable {V E C D : Type*}

/-- A proper coloring of actual edge copies with an arbitrary palette. -/
structure PaletteColoring (G : Multigraph V E) (C : Type*) where
  color : E → C
  proper : ∀ {e f : E} {v : V}, color e = color f →
    v ∈ G.edge e → v ∈ G.edge f → e = f

namespace PaletteColoring

variable {G : Multigraph V E}

/-- Forget only the special presentation of the palette as `Fin k`. -/
def ofEdgeColoring {k : ℕ} (c : G.EdgeColoring k) : PaletteColoring G (Fin k) :=
  ⟨c.color, c.proper⟩

/-- Recover the existing finite-palette edge-coloring interface. -/
def toEdgeColoring {k : ℕ} (c : PaletteColoring G (Fin k)) : G.EdgeColoring k :=
  ⟨c.color, c.proper⟩

/-- An injective relabeling preserves properness at every original vertex. -/
def map (c : PaletteColoring G C) (f : C → D) (hf : Function.Injective f) :
    PaletteColoring G D where
  color e := f (c.color e)
  proper h hef hff := c.proper (hf h) hef hff

@[simp] theorem map_color (c : PaletteColoring G C) (f : C → D)
    (hf : Function.Injective f) (e : E) : (c.map f hf).color e = f (c.color e) := rfl

/-- Pull a coloring back along an injective edge-copy map and an
incidence-preserving vertex map. The vertex map may identify vertices. -/
def pullback {W F : Type*} {H : Multigraph W F} (c : PaletteColoring G C)
    (onEdge : F → E) (onVertex : W → V) (hinj : Function.Injective onEdge)
    (hinc : ∀ e v, v ∈ H.edge e → onVertex v ∈ G.edge (onEdge e)) :
    PaletteColoring H C where
  color e := c.color (onEdge e)
  proper {e f v} h he hf := hinj (c.proper h (hinc e v he) (hinc f v hf))

@[simp] theorem pullback_color {W F : Type*} {H : Multigraph W F}
    (c : PaletteColoring G C) (onEdge : F → E) (onVertex : W → V)
    (hinj : Function.Injective onEdge)
    (hinc : ∀ e v, v ∈ H.edge e → onVertex v ∈ G.edge (onEdge e)) (e : F) :
    (c.pullback onEdge onVertex hinj hinc).color e = c.color (onEdge e) := rfl

section Incidence

variable [Fintype E] [Fintype C]

omit [Fintype C] in
/-- Properness makes the colors at any vertex injective on edge copies. -/
theorem incidence_injective (c : PaletteColoring G C) (z : V) :
    Function.Injective (fun e : G.incidenceEdges z => c.color e.val) := by
  intro e f h
  apply Subtype.ext
  exact c.proper h ((G.mem_incidenceEdges z e.val).mp e.property)
    ((G.mem_incidenceEdges z f.val).mp f.property)

/-- At a vertex of full palette degree, every color occurs exactly once. -/
theorem incidence_bijective (c : PaletteColoring G C) (z : V)
    (hdegree : G.degree z = Fintype.card C) :
    Function.Bijective (fun e : G.incidenceEdges z => c.color e.val) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  exact ⟨c.incidence_injective z, by simpa only [Fintype.card_coe, degree] using hdegree⟩

/-- The edge-copy-to-palette bijection at a saturated vertex. -/
def incidenceColorEquiv (c : PaletteColoring G C) (z : V)
    (hdegree : G.degree z = Fintype.card C) : G.incidenceEdges z ≃ C :=
  Equiv.ofBijective (fun e => c.color e.val) (c.incidence_bijective z hdegree)

@[simp] theorem incidenceColorEquiv_apply (c : PaletteColoring G C) (z : V)
    (hdegree : G.degree z = Fintype.card C) (e : G.incidenceEdges z) :
    c.incidenceColorEquiv z hdegree e = c.color e.val := rfl

/-- Distinct prescribed labels give an embedding into any original
palette, even when other labels have already been removed. -/
def prescribedPaletteEmbedding (c : PaletteColoring G C) (z : V)
    (hdegree : G.degree z = Fintype.card C)
    (label : G.incidenceEdges z → D) (hinj : Function.Injective label) : C ↪ D where
  toFun i := label ((c.incidenceColorEquiv z hdegree).symm i)
  inj' := hinj.comp (c.incidenceColorEquiv z hdegree).symm.injective

@[simp] theorem prescribedPaletteEmbedding_agrees (c : PaletteColoring G C) (z : V)
    (hdegree : G.degree z = Fintype.card C)
    (label : G.incidenceEdges z → D) (hinj : Function.Injective label)
    (e : G.incidenceEdges z) :
    c.prescribedPaletteEmbedding z hdegree label hinj (c.color e.val) = label e := by
  change label ((c.incidenceColorEquiv z hdegree).symm
    ((c.incidenceColorEquiv z hdegree) e)) = label e
  rw [Equiv.symm_apply_apply]

/-- Align with prescribed labels in a possibly larger original palette. -/
def alignLabelsAtVertex (c : PaletteColoring G C) (z : V)
    (hdegree : G.degree z = Fintype.card C)
    (label : G.incidenceEdges z → D) (hinj : Function.Injective label) :
    PaletteColoring G D :=
  c.map (c.prescribedPaletteEmbedding z hdegree label hinj)
    (c.prescribedPaletteEmbedding z hdegree label hinj).injective

@[simp] theorem alignLabelsAtVertex_agrees (c : PaletteColoring G C) (z : V)
    (hdegree : G.degree z = Fintype.card C)
    (label : G.incidenceEdges z → D) (hinj : Function.Injective label)
    (e : G.incidenceEdges z) :
    (c.alignLabelsAtVertex z hdegree label hinj).color e.val = label e :=
  c.prescribedPaletteEmbedding_agrees z hdegree label hinj e

/-- Relabeling introduces no color outside the prescribed surviving labels. -/
theorem alignLabelsAtVertex_range (c : PaletteColoring G C) (z : V)
    (hdegree : G.degree z = Fintype.card C)
    (label : G.incidenceEdges z → D) (hinj : Function.Injective label) (e : E) :
    ∃ b : G.incidenceEdges z,
      (c.alignLabelsAtVertex z hdegree label hinj).color e = label b :=
  ⟨(c.incidenceColorEquiv z hdegree).symm (c.color e), rfl⟩

variable [Fintype D]

/-- Distinct prescribed labels on the saturated vertex determine an
equivalence from the current palette to the prescribed palette. -/
def prescribedPaletteEquiv (c : PaletteColoring G C) (z : V)
    (hdegree : G.degree z = Fintype.card C)
    (label : G.incidenceEdges z → D) (hinj : Function.Injective label)
    (hcard : G.degree z = Fintype.card D) : C ≃ D :=
  (c.incidenceColorEquiv z hdegree).symm.trans
    (Equiv.ofBijective label ((Fintype.bijective_iff_injective_and_card label).mpr
      ⟨hinj, by simpa only [Fintype.card_coe, degree] using hcard⟩))

@[simp] theorem prescribedPaletteEquiv_agrees (c : PaletteColoring G C) (z : V)
    (hdegree : G.degree z = Fintype.card C)
    (label : G.incidenceEdges z → D) (hinj : Function.Injective label)
    (hcard : G.degree z = Fintype.card D) (e : G.incidenceEdges z) :
    c.prescribedPaletteEquiv z hdegree label hinj hcard (c.color e.val) = label e := by
  change label ((c.incidenceColorEquiv z hdegree).symm
    ((c.incidenceColorEquiv z hdegree) e)) = label e
  rw [Equiv.symm_apply_apply]

/-- Relabel the whole coloring to match all prescribed incidences exactly. -/
def alignAtVertex (c : PaletteColoring G C) (z : V)
    (hdegree : G.degree z = Fintype.card C)
    (label : G.incidenceEdges z → D) (hinj : Function.Injective label)
    (hcard : G.degree z = Fintype.card D) : PaletteColoring G D :=
  c.map (c.prescribedPaletteEquiv z hdegree label hinj hcard)
    (c.prescribedPaletteEquiv z hdegree label hinj hcard).injective

@[simp] theorem alignAtVertex_agrees (c : PaletteColoring G C) (z : V)
    (hdegree : G.degree z = Fintype.card C)
    (label : G.incidenceEdges z → D) (hinj : Function.Injective label)
    (hcard : G.degree z = Fintype.card D) (e : G.incidenceEdges z) :
    (c.alignAtVertex z hdegree label hinj hcard).color e.val = label e :=
  c.prescribedPaletteEquiv_agrees z hdegree label hinj hcard e

end Incidence

/-- Assemble proper color classes using their original labels. The
covering assumption concerns actual edge copies. -/
def ofMatchingClasses (M : C → Finset E) (hM : ∀ i, G.IsMatching (M i))
    (hcover : ∀ e, ∃ i, e ∈ M i) : PaletteColoring G C where
  color e := Classical.choose (hcover e)
  proper {e f v} h he hf := by
    have hem := Classical.choose_spec (hcover e)
    have hfm := Classical.choose_spec (hcover f)
    rw [← h] at hfm
    exact hM _ e hem f hfm v he hf

theorem ofMatchingClasses_mem (M : C → Finset E) (hM : ∀ i, G.IsMatching (M i))
    (hcover : ∀ e, ∃ i, e ∈ M i) (e : E) :
    e ∈ M ((ofMatchingClasses M hM hcover).color e) := Classical.choose_spec (hcover e)

/-- Pairwise disjoint classes recover their given labels, including the
classes restored after the residual coloring. -/
theorem ofMatchingClasses_color_eq_iff (M : C → Finset E)
    (hM : ∀ i, G.IsMatching (M i)) (hcover : ∀ e, ∃ i, e ∈ M i)
    (hdisjoint : Pairwise (fun i j => Disjoint (M i) (M j))) (e : E) (i : C) :
    (ofMatchingClasses M hM hcover).color e = i ↔ e ∈ M i := by
  have hem := ofMatchingClasses_mem M hM hcover e
  constructor
  · intro h
    rwa [← h]
  · intro hi
    by_contra h
    exact Finset.disjoint_left.mp (hdisjoint h) hem hi

end PaletteColoring
end Overfull.Multigraph
