import Overfull.OneCore.Complement
import Overfull.ColoringExtension.Exterior

/-!
# Selected actual exterior classes and their core footprints

The complementary graph retains exactly the host copies outside the embedded
simple core. Selected color classes are mapped back to those same host copies.
Their core footprints record precisely their covered core vertices, with
degree, parity, and size estimates obtained from an actual equitable coloring.
-/

noncomputable section

namespace Overfull.OrdinaryFactorization

open Finset Classical SmallCuts

variable {V E : Type*} [Fintype E]
variable {G : Multigraph V E} {U : Finset V} (C : Core G U) {k h : ℕ}

/-- A selected exterior class, represented by its original host edge copies. -/
def selectedClass (c : (G.restrictEdges (OneCore.coreEdges C)ᶜ).EdgeColoring k)
    (l : Fin h ↪ Fin k) (i : Fin h) : Finset E :=
  (c.colorClass (l i)).map (Function.Embedding.subtype
    (fun e => e ∈ (OneCore.coreEdges C)ᶜ))

@[simp] theorem mem_selectedClass
    (c : (G.restrictEdges (OneCore.coreEdges C)ᶜ).EdgeColoring k)
    (l : Fin h ↪ Fin k) (i : Fin h) (e : E) :
    e ∈ selectedClass C c l i ↔
      ∃ f : ↥((OneCore.coreEdges C)ᶜ), c.color f = l i ∧ f.val = e := by
  simp only [selectedClass, Finset.mem_map, Multigraph.EdgeColoring.colorClass,
    Finset.mem_filter, Finset.mem_univ, true_and, Function.Embedding.subtype_apply]

theorem selectedClass_card
    (c : (G.restrictEdges (OneCore.coreEdges C)ᶜ).EdgeColoring k)
    (l : Fin h ↪ Fin k) (i : Fin h) :
    (selectedClass C c l i).card = (c.colorClass (l i)).card := by
  exact Finset.card_map _

theorem selectedClass_isMatching
    (c : (G.restrictEdges (OneCore.coreEdges C)ᶜ).EdgeColoring k)
    (l : Fin h ↪ Fin k) (i : Fin h) : G.IsMatching (selectedClass C c l i) := by
  intro e he f hf v hev hfv
  obtain ⟨e', he', rfl⟩ := (mem_selectedClass C c l i e).mp he
  obtain ⟨f', hf', rfl⟩ := (mem_selectedClass C c l i f).mp hf
  exact congrArg Subtype.val (c.proper (he'.trans hf'.symm) hev hfv)

theorem selectedClass_pairwiseDisjoint
    (c : (G.restrictEdges (OneCore.coreEdges C)ᶜ).EdgeColoring k)
    (l : Fin h ↪ Fin k) :
    Pairwise (fun i j => Disjoint (selectedClass C c l i) (selectedClass C c l j)) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro e hei hej
  obtain ⟨e', he', rfl⟩ := (mem_selectedClass C c l i e).mp hei
  obtain ⟨f', hf', hfe⟩ := (mem_selectedClass C c l j e'.val).mp hej
  have hfe' : f' = e' := Subtype.ext hfe
  subst f'
  exact hij (l.injective (he'.symm.trans hf'))

theorem selectedClass_subset_complement
    (c : (G.restrictEdges (OneCore.coreEdges C)ᶜ).EdgeColoring k)
    (l : Fin h ↪ Fin k) (i : Fin h) :
    selectedClass C c l i ⊆ (OneCore.coreEdges C)ᶜ := by
  intro e he
  obtain ⟨f, _, rfl⟩ := (mem_selectedClass C c l i e).mp he
  exact f.property

theorem selectedClass_disjoint_coreEdges
    (c : (G.restrictEdges (OneCore.coreEdges C)ᶜ).EdgeColoring k)
    (l : Fin h ↪ Fin k) (i : Fin h) :
    Disjoint (selectedClass C c l i) (OneCore.coreEdges C) := by
  apply Finset.disjoint_left.mpr
  intro e he hcore
  exact (Finset.mem_compl.mp (selectedClass_subset_complement C c l i he)) hcore

/-- Mapping a class to the host preserves its exact coverage. -/
theorem selectedClass_covers
    (c : (G.restrictEdges (OneCore.coreEdges C)ᶜ).EdgeColoring k)
    (l : Fin h ↪ Fin k) (i : Fin h) (v : V) :
    (∃ e ∈ selectedClass C c l i, v ∈ G.edge e) ↔ c.Covers (l i) v := by
  constructor
  · rintro ⟨e, he, hv⟩
    obtain ⟨f, hf, rfl⟩ := (mem_selectedClass C c l i e).mp he
    exact ⟨f, hf, hv⟩
  · rintro ⟨f, hf, hv⟩
    exact ⟨f.val, (mem_selectedClass C c l i f.val).mpr ⟨f, hf, rfl⟩, hv⟩

/-- Core deletion removes no incidence at a vertex outside the core. -/
theorem complement_degree_outside (v : V) (hv : v ∉ U) :
    (G.restrictEdges (OneCore.coreEdges C)ᶜ).degree v = G.degree v := by
  rw [Multigraph.restrictEdges_degree]
  change _ = (G.incidenceEdges v).card
  congr 1
  apply Finset.inter_eq_right.mpr
  intro e he
  exact Finset.mem_compl.mpr (fun hcore =>
    hv (OneCore.coreEdges_endpoint C hcore ((G.mem_incidenceEdges v e).mp he)))

/-- Every selected class covers every exterior vertex exactly once in a
regular host, with uniqueness stated for original edge copies. -/
theorem selectedClass_covers_outside_uniquely
    (c : (G.restrictEdges (OneCore.coreEdges C)ᶜ).EdgeColoring k)
    (l : Fin h ↪ Fin k) (hregular : ∀ v, G.degree v = k)
    (i : Fin h) (v : V) (hv : v ∉ U) :
    ∃! e, e ∈ selectedClass C c l i ∧ v ∈ G.edge e := by
  have hdegree : (G.restrictEdges (OneCore.coreEdges C)ᶜ).degree v = k :=
    (complement_degree_outside C v hv).trans (hregular v)
  obtain ⟨e, he, hev⟩ := (selectedClass_covers C c l i v).mpr
    (c.covers_of_degree_eq v hdegree (l i))
  refine ⟨e, ⟨he, hev⟩, ?_⟩
  intro f hf
  exact selectedClass_isMatching C c l i f hf.1 e he v hf.2 hev

variable [Fintype V]

/-- The actual core vertices covered by a selected exterior class. -/
def selectedFootprint (c : (G.restrictEdges (OneCore.coreEdges C)ᶜ).EdgeColoring k)
    (l : Fin h ↪ Fin k) (i : Fin h) : Finset U :=
  SmallCuts.shore U (c.coveredVertices (l i))

@[simp] theorem mem_selectedFootprint
    (c : (G.restrictEdges (OneCore.coreEdges C)ᶜ).EdgeColoring k)
    (l : Fin h ↪ Fin k) (i : Fin h) (v : U) :
    v ∈ selectedFootprint C c l i ↔ c.Covers (l i) v.val := by
  simp only [selectedFootprint, SmallCuts.mem_shore, c.mem_coveredVertices]

/-- Core incidence agrees exactly with the footprint. -/
theorem selectedFootprint_iff_incident
    (c : (G.restrictEdges (OneCore.coreEdges C)ᶜ).EdgeColoring k)
    (l : Fin h ↪ Fin k) (i : Fin h) (v : U) :
    v ∈ selectedFootprint C c l i ↔
      ∃ e ∈ selectedClass C c l i, v.val ∈ G.edge e := by
  rw [mem_selectedFootprint, selectedClass_covers]

theorem selectedFootprint_iff_unique_incident
    (c : (G.restrictEdges (OneCore.coreEdges C)ᶜ).EdgeColoring k)
    (l : Fin h ↪ Fin k) (i : Fin h) (v : U) :
    v ∈ selectedFootprint C c l i ↔
      ∃! e, e ∈ selectedClass C c l i ∧ v.val ∈ G.edge e := by
  constructor
  · intro hv
    obtain ⟨e, he, hev⟩ := (selectedFootprint_iff_incident C c l i v).mp hv
    refine ⟨e, ⟨he, hev⟩, ?_⟩
    intro f hf
    exact selectedClass_isMatching C c l i f hf.1 e he v.val hf.2 hev
  · rintro ⟨e, he, _⟩
    exact (selectedFootprint_iff_incident C c l i v).mpr ⟨e, he.1, he.2⟩

/-- Passing from host vertices to the core subtype preserves footprint size. -/
theorem selectedFootprint_card
    (c : (G.restrictEdges (OneCore.coreEdges C)ᶜ).EdgeColoring k)
    (l : Fin h ↪ Fin k) (i : Fin h) :
    (selectedFootprint C c l i).card = (c.exteriorFootprint U (l i)).card := by
  simp only [selectedFootprint, SmallCuts.shore_card,
    Multigraph.EdgeColoring.exteriorFootprint, Finset.inter_comm]

/-- Distinct selected labels give at most the full complementary incidence load. -/
theorem selectedFootprint_load_le_degree
    (c : (G.restrictEdges (OneCore.coreEdges C)ᶜ).EdgeColoring k)
    (l : Fin h ↪ Fin k) (v : U) :
    (univ.filter (fun i => v ∈ selectedFootprint C c l i)).card ≤
      (G.restrictEdges (OneCore.coreEdges C)ᶜ).degree v.val := by
  calc
    _ ≤ (univ.filter (fun j : Fin k => c.Covers j v.val)).card := by
      apply Finset.card_le_card_of_injOn l
      · intro i hi
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (mem_selectedFootprint C c l i v).mp (Finset.mem_filter.mp hi).2⟩
      · exact l.injective.injOn
    _ = _ := c.coveredColors_card v.val

theorem selectedFootprint_load_le_error
    (c : (G.restrictEdges (OneCore.coreEdges C)ᶜ).EdgeColoring k)
    (l : Fin h ↪ Fin k) (a : ℝ) (hregular : ∀ v, G.degree v = k)
    (hdegree : ∀ v, (k : ℝ) - a ≤ (C.graph.degree v : ℝ)) (v : U) :
    ((univ.filter (fun i => v ∈ selectedFootprint C c l i)).card : ℝ) ≤ a := by
  have hload : ((univ.filter (fun i => v ∈ selectedFootprint C c l i)).card : ℝ) ≤
      (G.restrictEdges (OneCore.coreEdges C)ᶜ).degree v.val := by
    exact_mod_cast selectedFootprint_load_le_degree C c l v
  exact hload.trans (OneCore.complement_degree_le_error C k a hregular hdegree v)

theorem selectedFootprint_even
    (c : (G.restrictEdges (OneCore.coreEdges C)ᶜ).EdgeColoring k)
    (l : Fin h ↪ Fin k) (hregular : ∀ v, G.degree v = k)
    (heven : Even Uᶜ.card) (i : Fin h) :
    Even (selectedFootprint C c l i).card := by
  rw [selectedFootprint_card]
  apply c.exteriorFootprint_even U _ heven (l i)
  intro v hv
  exact (complement_degree_outside C v (Finset.mem_compl.mp hv)).trans (hregular v)

/-- Equitability of the full exterior coloring bounds every selected footprint. -/
theorem selectedFootprint_scaled_bound
    (c : (G.restrictEdges (OneCore.coreEdges C)ᶜ).EdgeColoring k)
    (l : Fin h ↪ Fin k) (a : ℝ) (hregular : ∀ v, G.degree v = k)
    (hdegree : ∀ v, (k : ℝ) - a ≤ (C.graph.degree v : ℝ))
    (hspread : ∀ i j,
      |((c.colorClass i).card : ℤ) - ((c.colorClass j).card : ℤ)| ≤ 1)
    (i : Fin h) :
    (k : ℝ) * (selectedFootprint C c l i).card ≤ a * U.card + 2 * k := by
  rw [selectedFootprint_card]
  apply c.exteriorFootprint_scaled_bound U a _ _ hspread (l i)
  · intro v hv
    exact OneCore.complement_degree_le_error C k a hregular hdegree ⟨v, hv⟩
  · intro v hv
    exact (complement_degree_outside C v (Finset.mem_compl.mp hv)).trans (hregular v)

/-- Starting with an actual coloring of the core complement, equitize it and
obtain the selected footprint bounds directly from host regularity and the
core degree lower bound. Exterior saturation is derived, not assumed. -/
theorem exists_equitable_selected_exterior
    (c₀ : (G.restrictEdges (OneCore.coreEdges C)ᶜ).EdgeColoring k)
    (l : Fin h ↪ Fin k) (a : ℝ) (hregular : ∀ v, G.degree v = k)
    (hdegree : ∀ v, (k : ℝ) - a ≤ (C.graph.degree v : ℝ))
    (heven : Even Uᶜ.card) :
    ∃ c : (G.restrictEdges (OneCore.coreEdges C)ᶜ).EdgeColoring k,
      (∀ i j, |((c.colorClass i).card : ℤ) - ((c.colorClass j).card : ℤ)| ≤ 1) ∧
      (∀ i, Even (selectedFootprint C c l i).card) ∧
      (∀ i, (k : ℝ) * (selectedFootprint C c l i).card ≤ a * U.card + 2 * k) ∧
      (∀ v : U,
        ((univ.filter (fun i => v ∈ selectedFootprint C c l i)).card : ℝ) ≤ a) := by
  have hcore : ∀ v ∈ U,
      ((G.restrictEdges (OneCore.coreEdges C)ᶜ).degree v : ℝ) ≤ a := by
    intro v hv
    exact OneCore.complement_degree_le_error C k a hregular hdegree ⟨v, hv⟩
  have hZ : ∀ v ∈ Uᶜ, (G.restrictEdges (OneCore.coreEdges C)ᶜ).degree v = k := by
    intro v hv
    exact (complement_degree_outside C v (Finset.mem_compl.mp hv)).trans (hregular v)
  obtain ⟨c, hspread, _hcovered, hbound, hparity, _hload⟩ :=
    c₀.exists_equitable_exterior U a hcore hZ heven
  refine ⟨c, hspread, ?_, ?_, selectedFootprint_load_le_error C c l a hregular hdegree⟩
  · intro i
    rw [selectedFootprint_card]
    exact hparity (l i)
  · intro i
    rw [selectedFootprint_card]
    exact hbound (l i)

end Overfull.OrdinaryFactorization
