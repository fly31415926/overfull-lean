import Overfull.BoundaryExtension.Contraction
import Overfull.BoundaryExtension.BoundaryData
import Overfull.BoundaryExtension.Palette

/-!
# Reassembling completed colors with an actual residual coloring

Selected colors are matchings of original edge copies. Their labels are
distinct, and the residual coloring avoids all selected labels. Combining
the two preserves properness at every original vertex and agrees exactly
with the prescribed boundary coloring. This is a restoration theorem from
an actual residual coloring, not a factorization existence theorem.
-/

noncomputable section
namespace Overfull.BoundaryExtension

open Finset Classical Multigraph

variable {V E : Type*} [Fintype E]

/-- Regard a retained residual copy as the same original retained copy. -/
def restoredResidualEdge (G : Multigraph V E) (U : Finset V) (T : Finset E)
    (e : RetainedEdge (G.restrictEdges Tᶜ) U) : RetainedEdge G U :=
  ⟨e.val.val,e.property⟩

@[simp] theorem restoredResidualEdge_val (G : Multigraph V E) (U : Finset V)
    (T : Finset E) (e : RetainedEdge (G.restrictEdges Tᶜ) U) :
    (restoredResidualEdge G U T e).val = e.val.val := rfl

/-- A retained original copy outside the deleted set is a retained
residual copy, with its identity and both endpoints unchanged. -/
def retainedResidualEdge (G : Multigraph V E) (U : Finset V) (T : Finset E)
    (e : RetainedEdge G U) (he : e.val ∉ T) :
    RetainedEdge (G.restrictEdges Tᶜ) U :=
  ⟨⟨e.val,Finset.mem_compl.mpr he⟩,e.property⟩

@[simp] theorem retainedResidualEdge_val (G : Multigraph V E) (U : Finset V)
    (T : Finset E) (e : RetainedEdge G U) (he : e.val ∉ T) :
    (retainedResidualEdge G U T e he).val.val = e.val := rfl

/-- Restore actual deleted matching classes using their original labels.
The residual palette is disjoint from those labels, so properness holds
at exterior vertices as well as at core vertices. -/
theorem reassemble_deleted_colors
    (G : Multigraph V E) (U : Finset V) {d : ℕ} (c : BoundaryColoring G U d)
    (q : ℕ) (labels : Fin q ↪ Fin d) (M : Fin q → Finset E)
    (hM : ∀ j, G.IsMatching (M j))
    (hdisjoint : Pairwise (fun i j => Disjoint (M i) (M j)))
    (hretained : ∀ j e, e ∈ M j → ∃ u : U, u.val ∈ G.edge e)
    (hboundary : ∀ (e : G.cutEdges U) (j : Fin q),
      e.val ∈ M j ↔ c.color e = labels j)
    (cRest : PaletteColoring
      (retainedGraph (G.restrictEdges ((univ : Finset (Fin q)).biUnion M)ᶜ) U) (Fin d))
    (hpalette : ∀ e, cRest.color e ∉ Set.range labels)
    (hagrees : ∀ e : RetainedEdge
        (G.restrictEdges ((univ : Finset (Fin q)).biUnion M)ᶜ) U,
      ∀ he : e.val.val ∈ G.cutEdges U,
        cRest.color e = c.color ⟨e.val.val,he⟩) :
    ∃ cFinal : (retainedGraph G U).EdgeColoring d,
      (∀ e : G.cutEdges U, cFinal.color (boundaryLift G U e) = c.color e) ∧
      (∀ j e (he : e ∈ M j),
        cFinal.color ⟨e,hretained j e he⟩ = labels j) ∧
      (∀ e : RetainedEdge
          (G.restrictEdges ((univ : Finset (Fin q)).biUnion M)ᶜ) U,
        cFinal.color (restoredResidualEdge G U _ e) = cRest.color e) := by
  let T := (univ : Finset (Fin q)).biUnion M
  have hmem (e : E) : e ∈ T ↔ ∃ j : Fin q, e ∈ M j := by simp [T]
  let pick (e : E) (he : e ∈ T) : Fin q := Classical.choose ((hmem e).mp he)
  have hpick (e : E) (he : e ∈ T) : e ∈ M (pick e he) :=
    Classical.choose_spec ((hmem e).mp he)
  let color (e : RetainedEdge G U) : Fin d :=
    if he : e.val ∈ T then labels (pick e.val he)
    else cRest.color (retainedResidualEdge G U T e he)
  have hproper : ∀ {e f : RetainedEdge G U} {v : V}, color e = color f →
      v ∈ (retainedGraph G U).edge e → v ∈ (retainedGraph G U).edge f → e = f := by
    intro e f v hef hev hfv
    apply Subtype.ext
    by_cases he : e.val ∈ T
    · by_cases hf : f.val ∈ T
      · have hc : labels (pick e.val he) = labels (pick f.val hf) := by
          simpa only [color,dif_pos he,dif_pos hf] using hef
        have hp := labels.injective hc
        apply hM (pick e.val he) e.val (hpick e.val he) f.val ?_ v hev hfv
        rw [hp]
        exact hpick f.val hf
      · exact False.elim (hpalette (retainedResidualEdge G U T f hf)
          ⟨pick e.val he,by simpa only [color,dif_pos he,dif_neg hf] using hef⟩)
    · by_cases hf : f.val ∈ T
      · exact False.elim (hpalette (retainedResidualEdge G U T e he)
          ⟨pick f.val hf,by simpa only [color,dif_neg he,dif_pos hf] using hef.symm⟩)
      · have hc : cRest.color (retainedResidualEdge G U T e he) =
            cRest.color (retainedResidualEdge G U T f hf) := by
          simpa only [color,dif_neg he,dif_neg hf] using hef
        have hh := cRest.proper hc hev hfv
        exact congrArg (fun a : RetainedEdge (G.restrictEdges Tᶜ) U => a.val.val) hh
  let cFinal : (retainedGraph G U).EdgeColoring d := ⟨color,hproper⟩
  have hselected (j : Fin q) (e : E) (he : e ∈ M j) :
      cFinal.color ⟨e,hretained j e he⟩ = labels j := by
    have heT : e ∈ T := (hmem e).mpr ⟨j,he⟩
    have hj : pick e heT = j := by
      by_contra hne
      exact Finset.disjoint_left.mp (hdisjoint hne) (hpick e heT) he
    change (if h : e ∈ T then labels (pick e h) else _) = labels j
    rw [dif_pos heT,hj]
  have hrest (e : RetainedEdge (G.restrictEdges Tᶜ) U) :
      cFinal.color (restoredResidualEdge G U T e) = cRest.color e := by
    have heT : e.val.val ∉ T := Finset.mem_compl.mp e.val.property
    change (if h : e.val.val ∈ T then labels (pick e.val.val h) else _) = cRest.color e
    rw [dif_neg heT]
    rfl
  refine ⟨cFinal,?_,hselected,hrest⟩
  intro e
  by_cases he : e.val ∈ T
  · have heM := hpick e.val he
    have hs := hselected (pick e.val he) e.val heM
    exact hs.trans ((hboundary e (pick e.val he)).mp heM).symm
  · let eR := retainedResidualEdge G U T (boundaryLift G U e) he
    exact (hrest eR).trans (hagrees eR e.property)

end Overfull.BoundaryExtension
