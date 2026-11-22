import Overfull.OrdinaryFactorization.ExteriorSelection
import Overfull.OrdinaryFactorization.ResidualColoring
import Overfull.CriticalMultigraph
import Mathlib.Data.Fintype.EquivFin

/-!
# Coloring the unreserved exterior and the internal complement

Keep every internal complementary copy and every exterior copy whose original
label is outside the reserved palette. The exterior vertices then have exactly
the remaining palette degree. Compress the prescribed unreserved labels and
extend them across the internal copies using the actual complementary degree
bound. Every omitted copy is either in the embedded core or an exterior copy
with one of the reserved original labels.
-/

noncomputable section

namespace Overfull.BoundedExterior

open Finset Classical SmallCuts OneCore OrdinaryFactorization

variable {V E : Type*} [Fintype E]

/-- Retain the unreserved exterior and every internal complementary copy,
with a proper coloring in exactly the unreserved palette size. -/
theorem exists_selected_coloring
    (G : Multigraph V E) (U : Finset V) (C : Core G U) (k : ℕ) (a : ℝ)
    (c : (G.restrictEdges (coreEdges C)ᶜ).EdgeColoring k) (J : Finset (Fin k))
    (hregular : ∀ v, G.degree v = k)
    (hlow : ∀ v : U, ((G.restrictEdges (coreEdges C)ᶜ).degree v.val : ℝ) ≤ a)
    (hslack : 2 * a < ((k - J.card : ℕ) : ℝ)) :
    ∃ F : Finset E, ∃ _d : (G.restrictEdges F).EdgeColoring (k - J.card),
      F ⊆ (coreEdges C)ᶜ ∧
      (∀ v, v ∉ U → (G.restrictEdges F).degree v = k - J.card) ∧
      (∀ f : E, f ∉ F → f ∈ coreEdges C ∨
        ∃ hf : f ∈ (coreEdges C)ᶜ,
          f ∉ G.internalEdges U ∧ c.color ⟨f, hf⟩ ∈ J) := by
  let F : Finset E := ((coreEdges C)ᶜ).filter (fun f =>
    f ∈ G.internalEdges U ∨ ∃ hf : f ∈ (coreEdges C)ᶜ, c.color ⟨f, hf⟩ ∉ J)
  have hF : F ⊆ (coreEdges C)ᶜ := filter_subset _ _
  have hNotInternal (v : V) (hv : v ∉ U) (f : E) (hf : v ∈ G.edge f) :
      f ∉ G.internalEdges U := by
    intro hint
    obtain ⟨hfirst, hsecond⟩ := (G.mem_internalEdges U f).mp hint
    rcases (G.incident_iff f v).mp hf with rfl | rfl
    · exact hv hfirst
    · exact hv hsecond
  have hOutside (v : V) (hv : v ∉ U) :
      (G.restrictEdges F).degree v = k - J.card := by
    rw [G.restrictEdges_degree]
    calc
      (F ∩ G.incidenceEdges v).card = (Jᶜ).card := by
        apply Finset.card_bij
          (fun f hf => c.color ⟨f, hF (mem_inter.mp hf).1⟩)
        · intro f hf
          have hinc : v ∈ G.edge f := (G.mem_incidenceEdges v f).mp (mem_inter.mp hf).2
          have hchoice := (mem_filter.mp (mem_inter.mp hf).1).2
          rcases hchoice with hint | ⟨hfcomp, hlabel⟩
          · exact (hNotInternal v hv f hinc hint).elim
          · exact mem_compl.mpr hlabel
        · intro f hf g hg hcolor
          exact congrArg Subtype.val (c.proper hcolor
            ((G.mem_incidenceEdges v f).mp (mem_inter.mp hf).2)
            ((G.mem_incidenceEdges v g).mp (mem_inter.mp hg).2))
        · intro i hi
          obtain ⟨f, hcolor, hinc⟩ := c.covers_of_degree_eq v
            ((complement_degree_outside C v hv).trans (hregular v)) i
          have hfF : f.val ∈ F := mem_filter.mpr ⟨f.property, Or.inr
            ⟨f.property, by simpa only [hcolor] using (mem_compl.mp hi)⟩⟩
          exact ⟨f.val, mem_inter.mpr ⟨hfF, (G.mem_incidenceEdges v f.val).mpr hinc⟩,
            hcolor⟩
      _ = k - J.card := by simp only [card_compl, Fintype.card_fin]
  let palette : ↥(Jᶜ) ≃ Fin (k - J.card) :=
    Finset.equivFinOfCardEq (by simp only [card_compl, Fintype.card_fin])
  let S : Finset F := univ.filter (fun f => c.color ⟨f.val, hF f.property⟩ ∉ J)
  have hS (f : S) : c.color ⟨f.val.val, hF f.val.property⟩ ∉ J :=
    (mem_filter.mp f.property).2
  let cS : ((G.restrictEdges F).restrictEdges S).EdgeColoring (k - J.card) := {
    color := fun f => palette ⟨c.color ⟨f.val.val, hF f.val.property⟩,
      mem_compl.mpr (hS f)⟩
    proper := by
      intro f g v hcolor hf hg
      have hlabel : c.color ⟨f.val.val, hF f.val.property⟩ =
          c.color ⟨g.val.val, hF g.val.property⟩ :=
        congrArg Subtype.val (palette.injective hcolor)
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun e : ↥((coreEdges C)ᶜ) => e.val) (c.proper hlabel hf hg)
  }
  have hInternal (f : F) (hf : f ∉ S) :
      (G.restrictEdges F).firstEnd f ∈ U ∧ (G.restrictEdges F).secondEnd f ∈ U := by
    have hlabel : c.color ⟨f.val, hF f.property⟩ ∈ J := by
      by_contra hnot
      exact hf (mem_filter.mpr ⟨mem_univ _, hnot⟩)
    have hint : f.val ∈ G.internalEdges U := by
      rcases (mem_filter.mp f.property).2 with hint | ⟨hfcomp, hnot⟩
      · exact hint
      · exact (hnot hlabel).elim
    exact (G.mem_internalEdges U f.val).mp hint
  have hDegree (v : V) (hv : v ∈ U) : ((G.restrictEdges F).degree v : ℝ) ≤ a :=
    (Nat.cast_le.mpr (G.restrictEdges_degree_mono hF v)).trans (hlow ⟨v, hv⟩)
  obtain ⟨d, _hpreserves⟩ := extend_restriction_coloring_of_endpoints
    (G.restrictEdges F) U S cS a hInternal hDegree hslack
  refine ⟨F, d, hF, hOutside, ?_⟩
  intro f hf
  by_cases hcore : f ∈ coreEdges C
  · exact Or.inl hcore
  · have hfcomp : f ∈ (coreEdges C)ᶜ := mem_compl.mpr hcore
    refine Or.inr ⟨hfcomp, ?_, ?_⟩
    · intro hint
      exact hf (mem_filter.mpr ⟨hfcomp, Or.inl hint⟩)
    · by_contra hnot
      exact hf (mem_filter.mpr ⟨hfcomp, Or.inr ⟨hfcomp, hnot⟩⟩)

end Overfull.BoundedExterior
