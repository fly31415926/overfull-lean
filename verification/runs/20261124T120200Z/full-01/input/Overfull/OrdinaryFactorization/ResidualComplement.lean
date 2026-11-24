import Overfull.OrdinaryFactorization.ResidualCore
import Overfull.OrdinaryFactorization.ResidualInternal
import Overfull.OrdinaryFactorization.ResidualColoring

/-!
# Coloring the actual complement of the residual crossing core

Each complementary incidence is either inherited from the original exterior
or is the original copy of a surviving same-side simple edge. This gives
the actual bounded-core degree estimate. The inherited compressed coloring
then extends to the whole new complement while preserving its labels.
-/

noncomputable section

namespace Overfull.OrdinaryFactorization

open Finset Classical SmallCuts SimpleGraph

variable {V E : Type*} [Fintype V] [Fintype E]
variable {G : Multigraph V E} {U : Finset V} {k : ℕ}
variable {α ν τ ξ p σ κ δ μ : ℝ}
variable (C : Core G U) (D : FirstHalfData G U C k α ν τ ξ p σ κ δ μ)

/-- The same original host copy, forgetting both residual restrictions. -/
def residualCrossingComplementOriginal :
    ↥((OneCore.coreEdges (residualCrossingCore C D))ᶜ) ↪ E where
  toFun e := e.val.val
  inj' := by
    intro e f hef
    exact Subtype.ext (Subtype.ext hef)

@[simp] theorem residualCrossingComplementOriginal_val
    (e : ↥((OneCore.coreEdges (residualCrossingCore C D))ᶜ)) :
    residualCrossingComplementOriginal C D e = e.val.val := rfl

/-- Embed the surviving same-side simple edges by their original core copies. -/
def remainingInsideOriginal : D.remainingInside.edgeSet ↪ E where
  toFun f := C.edgeMap ⟨f.val, SimpleGraph.edgeSet_mono D.remainingInside_le_core f.property⟩
  inj' := by
    intro f g hfg
    exact Subtype.ext (congrArg (fun e : C.graph.edgeSet => e.val) (C.edgeMap.injective hfg))

theorem remainingInsideOriginal_incident (f : D.remainingInside.edgeSet) (v : U) :
    v.val ∈ G.edge (remainingInsideOriginal C D f) ↔ v ∈ f.val :=
  OneCore.core_incident_iff C _ v

/-- An original core edge that survives deletion but is outside the
crossing residual is one of the actual remaining inside edges. -/
theorem coreCopy_surviving_not_crossing_inside (f : C.graph.edgeSet)
    (hsurvives : C.edgeMap f ∉ deleted C D.exteriorColor D.labels D.matchings)
    (hnotCrossing : f.val ∉ (residualCrossing C D).edgeSet) :
    f.val ∈ D.remainingInside.edgeSet := by
  rcases f with ⟨⟨v, w⟩, hcore⟩
  have hnotUsed : ∀ i, ¬ (D.matchings i).Adj v w := by
    intro i hi
    exact hsurvives ((coreCopy_deleted_iff C D _).mpr ⟨i, hi⟩)
  have hsame : (v ∈ D.geometry.left) ↔ (w ∈ D.geometry.left) := by
    by_contra hnotSame
    apply hnotCrossing
    apply (residualCrossing_adj C D v w).mpr
    refine ⟨hcore, ?_, hnotUsed⟩
    intro heq
    exact hnotSame (eq_iff_iff.mp heq)
  exact (D.remainingInside_adj v w).mpr ⟨hcore, hsame, hnotUsed⟩

/-- Every actual new complementary copy is inherited from the original
complement or comes from a surviving same-side edge, with copy identity
retained in both alternatives. -/
theorem residualCrossingComplement_copy_cases
    (e : ↥((OneCore.coreEdges (residualCrossingCore C D))ᶜ)) :
    residualCrossingComplementOriginal C D e ∈ (OneCore.coreEdges C)ᶜ ∨
      ∃ f : D.remainingInside.edgeSet,
        remainingInsideOriginal C D f = residualCrossingComplementOriginal C D e := by
  by_cases hcore : residualCrossingComplementOriginal C D e ∈ OneCore.coreEdges C
  · obtain ⟨f, hf⟩ := (OneCore.mem_coreEdges C _).mp hcore
    have hsurvives : C.edgeMap f ∉ deleted C D.exteriorColor D.labels D.matchings := by
      rw [hf]
      exact mem_compl.mp e.val.property
    have hnotCrossing : f.val ∉ (residualCrossing C D).edgeSet := by
      intro hcross
      exact (mem_compl.mp e.property)
        ((mem_residualCrossingCore_iff C D e.val).mpr ⟨f, hf, hcross⟩)
    have hins := coreCopy_surviving_not_crossing_inside C D f hsurvives hnotCrossing
    refine Or.inr ⟨⟨f.val, hins⟩, ?_⟩
    exact hf
  · exact Or.inl (mem_compl.mpr hcore)

/-- The actual complementary incidence set maps into the original exterior
incidences and the surviving same-side simple incidences. -/
theorem residualCrossingComplement_incidence_subset (v : U) :
    ((residualCrossingComplement C D).incidenceEdges v.val).map
        (residualCrossingComplementOriginal C D) ⊆
      ((OneCore.coreEdges C)ᶜ ∩ G.incidenceEdges v.val) ∪
        ((Multigraph.ofSimpleGraph D.remainingInside).incidenceEdges v).map
          (remainingInsideOriginal C D) := by
  intro e he
  obtain ⟨f, hf, rfl⟩ := mem_map.mp he
  have hv : v.val ∈ G.edge (residualCrossingComplementOriginal C D f) :=
    ((residualCrossingComplement C D).mem_incidenceEdges v.val f).mp hf
  rcases residualCrossingComplement_copy_cases C D f with hext | ⟨g, hg⟩
  · exact mem_union_left _ (mem_inter.mpr ⟨hext, (G.mem_incidenceEdges v.val _).mpr hv⟩)
  · apply mem_union_right
    apply mem_map.mpr
    refine ⟨g, ?_, hg⟩
    apply ((Multigraph.ofSimpleGraph D.remainingInside).mem_incidenceEdges v g).mpr
    rw [← hg] at hv
    exact (remainingInsideOriginal_incident C D g v).mp hv

/-- Deleting first-group original copies can only reduce exterior incidence.
The other complementary incidences are bounded by the actual remaining
inside degree. No regularity assumption is needed for this inequality. -/
theorem residualCrossingComplement_degree_le (v : U) :
    (residualCrossingComplement C D).degree v.val ≤
      (G.restrictEdges (OneCore.coreEdges C)ᶜ).degree v.val + D.remainingInside.degree v := by
  calc
    _ = (((residualCrossingComplement C D).incidenceEdges v.val).map
        (residualCrossingComplementOriginal C D)).card := by rw [card_map]; rfl
    _ ≤ (((OneCore.coreEdges C)ᶜ ∩ G.incidenceEdges v.val) ∪
        ((Multigraph.ofSimpleGraph D.remainingInside).incidenceEdges v).map
          (remainingInsideOriginal C D)).card :=
      card_le_card (residualCrossingComplement_incidence_subset C D v)
    _ ≤ ((OneCore.coreEdges C)ᶜ ∩ G.incidenceEdges v.val).card +
        (((Multigraph.ofSimpleGraph D.remainingInside).incidenceEdges v).map
          (remainingInsideOriginal C D)).card := card_union_le _ _
    _ = _ := by
      rw [card_map, ← G.restrictEdges_degree]
      change _ + (Multigraph.ofSimpleGraph D.remainingInside).degree v = _
      rw [Multigraph.ofSimpleGraph_degree]

/-- The new complementary graph has the required small degree at every
core vertex, with all inherited and new edge copies counted. -/
theorem residualCrossingComplement_degree_le_error (a : ℝ) (hp : 0 ≤ p)
    (hregular : ∀ v, G.degree v = k)
    (hcore : ∀ v : U, (k : ℝ) - a ≤ C.graph.degree v) (v : U) :
    ((residualCrossingComplement C D).degree v.val : ℝ) ≤
      a + (p + 4 * δ + μ) * U.card := by
  have hcopies : ((residualCrossingComplement C D).degree v.val : ℝ) ≤
      (G.restrictEdges (OneCore.coreEdges C)ᶜ).degree v.val + D.remainingInside.degree v := by
    exact_mod_cast residualCrossingComplement_degree_le C D v
  calc
    _ ≤ _ := hcopies
    _ ≤ a + (p * U.card + 4 * δ * U.card + μ * U.card) :=
      add_le_add (OneCore.complement_degree_le_error C k a hregular hcore v)
        (D.remainingInside_degree_le_order hp v)
    _ = _ := by ring

/-- Extend the actual inherited compressed coloring to the whole new
complement. The strict palette bound concerns the actual residual degree. -/
theorem exists_residualCrossingComplement_coloring (a : ℝ) (hp : 0 ≤ p)
    (hregular : ∀ v, G.degree v = k)
    (hcore : ∀ v : U, (k : ℝ) - a ≤ C.graph.degree v)
    (hslack : 2 * (a + (p + 4 * δ + μ) * U.card) < ((k - D.count : ℕ) : ℝ)) :
    ∃ c : (residualCrossingComplement C D).EdgeColoring (k - D.count),
      ∀ e : ↥(inheritedComplementEdges C D),
        c.color e.val = (inheritedComplementColoring C D).color e := by
  have hdegree : ∀ v ∈ U, ((residualCrossingComplement C D).degree v : ℝ) ≤
      a + (p + 4 * δ + μ) * U.card := by
    intro v hv
    exact residualCrossingComplement_degree_le_error C D a hp hregular hcore ⟨v, hv⟩
  exact extend_restriction_coloring
    (V := V) (E := ↥((OneCore.coreEdges (residualCrossingCore C D))ᶜ))
    (k := k - D.count) (residualCrossingComplement C D) U
    (inheritedComplementEdges C D) (inheritedComplementColoring C D)
    (a + (p + 4 * δ + μ) * U.card)
    (by
      intro e he
      apply inheritedComplement_uncolored_internal C D
      simpa only [Finset.mem_compl] using he) hdegree hslack

/-- Restoring the residual labels recovers every inherited original
exterior label exactly. -/
theorem exists_residualCrossingComplement_coloring_preserving_original (a : ℝ) (hp : 0 ≤ p)
    (hregular : ∀ v, G.degree v = k)
    (hcore : ∀ v : U, (k : ℝ) - a ≤ C.graph.degree v)
    (hslack : 2 * (a + (p + 4 * δ + μ) * U.card) < ((k - D.count : ℕ) : ℝ)) :
    ∃ c : (residualCrossingComplement C D).EdgeColoring (k - D.count),
      ∀ e : ↥(inheritedComplementEdges C D),
        remainingLabel D.labels (c.color e.val) =
          D.exteriorColor.color (residualComplementOriginal C D.exteriorColor D.labels D.matchings
            (inheritedComplementOriginal C D e)) := by
  obtain ⟨c, hc⟩ := exists_residualCrossingComplement_coloring C D a hp hregular hcore hslack
  refine ⟨c, ?_⟩
  intro e
  rw [hc e]
  exact inheritedComplementColoring_restore C D e

end Overfull.OrdinaryFactorization
