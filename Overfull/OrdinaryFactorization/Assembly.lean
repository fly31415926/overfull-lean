import Overfull.OrdinaryFactorization.ExteriorSelection
import Overfull.BoundaryExtension.Assembly

/-!
# Completing selected exterior classes in the original host

An actual core matching on the complement of each selected footprint completes
that exterior class to a perfect matching of the whole multigraph. Every edge
remains its original host copy. The supplied core matchings stay explicit;
their existence is established by the reserve and packing constructions.
-/

noncomputable section

namespace Overfull.OrdinaryFactorization

open Finset Classical SmallCuts BoundaryExtension

variable {V E : Type*} [Fintype V] [Fintype E]
variable {G : Multigraph V E} {U : Finset V} {k h : ℕ}
variable (C : Core G U)
variable (c : (G.restrictEdges (OneCore.coreEdges C)ᶜ).EdgeColoring k)
variable (l : Fin h ↪ Fin k) (N : Fin h → C.graph.Subgraph)

omit [Fintype V] in
@[simp] theorem complement_mem_selectedClass (i : Fin h)
    (e : ↥((OneCore.coreEdges C)ᶜ)) :
    e.val ∈ selectedClass C c l i ↔ c.color e = l i := by
  rw [mem_selectedClass]
  constructor
  · rintro ⟨f, hf, hfe⟩
    have hfe' : f = e := Subtype.ext hfe
    simpa only [hfe'] using hf
  · intro he
    exact ⟨e, he, rfl⟩

omit [Fintype V] in
theorem selectedClass_coreCopies_disjoint (i : Fin h) (Q : C.graph.Subgraph) :
    Disjoint (selectedClass C c l i) (coreMatchingCopies C Q) :=
  (selectedClass_disjoint_coreEdges C c l i).mono_right
    (coreMatchingCopies_subset_core C Q)

private theorem selectedClass_coreCopies_no_common (i : Fin h)
    (Q : C.graph.Subgraph)
    (hverts : Q.verts = (selectedFootprint C c l i : Set U)ᶜ)
    {e f : E} (he : e ∈ selectedClass C c l i) (hf : f ∈ coreMatchingCopies C Q)
    {v : V} (hev : v ∈ G.edge e) (hfv : v ∈ G.edge f) : False := by
  have hvU := OneCore.coreEdges_endpoint C (coreMatchingCopies_subset_core C Q hf) hfv
  let u : U := ⟨v, hvU⟩
  have hfoot : u ∈ selectedFootprint C c l i :=
    (selectedFootprint_iff_incident C c l i u).mpr ⟨e, he, hev⟩
  have hver := coreMatchingCopies_incident_verts C Q hf u hfv
  rw [hverts] at hver
  exact hver hfoot

/-- The exterior class and its supplied internal completion, as original copies. -/
def completedClass (i : Fin h) : Finset E :=
  selectedClass C c l i ∪ coreMatchingCopies C (N i)

theorem completedClass_isMatching
    (hN : ∀ i, (N i).IsMatching)
    (hverts : ∀ i, (N i).verts = (selectedFootprint C c l i : Set U)ᶜ)
    (i : Fin h) : G.IsMatching (completedClass C c l N i) := by
  intro e he f hf v hev hfv
  rcases mem_union.mp he with he | he <;> rcases mem_union.mp hf with hf | hf
  · exact selectedClass_isMatching C c l i e he f hf v hev hfv
  · exact (selectedClass_coreCopies_no_common C c l i (N i) (hverts i)
      he hf hev hfv).elim
  · exact (selectedClass_coreCopies_no_common C c l i (N i) (hverts i)
      hf he hfv hev).elim
  · exact coreMatchingCopies_isMatching C (N i) (hN i) e he f hf v hev hfv

/-- Every core vertex is covered by the exterior class or its internal completion. -/
theorem completedClass_covers_core
    (hN : ∀ i, (N i).IsMatching)
    (hverts : ∀ i, (N i).verts = (selectedFootprint C c l i : Set U)ᶜ)
    (i : Fin h) (u : U) :
    ∃ e ∈ completedClass C c l N i, u.val ∈ G.edge e := by
  by_cases hu : u ∈ selectedFootprint C c l i
  · obtain ⟨e, he, hev⟩ := (selectedFootprint_iff_incident C c l i u).mp hu
    exact ⟨e, mem_union_left _ he, hev⟩
  · have hver : u ∈ (N i).verts := by rw [hverts i]; exact hu
    obtain ⟨e, he, hev⟩ := coreMatchingCopies_covers C (N i) (hN i) u hver
    exact ⟨e, mem_union_right _ he, hev⟩

theorem completedClass_covers
    (hN : ∀ i, (N i).IsMatching)
    (hverts : ∀ i, (N i).verts = (selectedFootprint C c l i : Set U)ᶜ)
    (hregular : ∀ v, G.degree v = k) (i : Fin h) (v : V) :
    ∃ e ∈ completedClass C c l N i, v ∈ G.edge e := by
  by_cases hv : v ∈ U
  · exact completedClass_covers_core C c l N hN hverts i ⟨v, hv⟩
  · obtain ⟨e, he, _⟩ := selectedClass_covers_outside_uniquely C c l hregular i v hv
    exact ⟨e, mem_union_left _ he.1, he.2⟩

/-- The completion is a perfect matching of the entire original multigraph. -/
theorem completedClass_isPerfectMatching
    (hN : ∀ i, (N i).IsMatching)
    (hverts : ∀ i, (N i).verts = (selectedFootprint C c l i : Set U)ᶜ)
    (hregular : ∀ v, G.degree v = k) (i : Fin h) :
    G.IsPerfectMatching (completedClass C c l N i) :=
  G.isPerfectMatching_iff.mpr ⟨completedClass_isMatching C c l N hN hverts i,
    completedClass_covers C c l N hN hverts hregular i⟩

theorem completedClass_covers_uniquely
    (hN : ∀ i, (N i).IsMatching)
    (hverts : ∀ i, (N i).verts = (selectedFootprint C c l i : Set U)ᶜ)
    (hregular : ∀ v, G.degree v = k) (i : Fin h) (v : V) :
    ∃! e, e ∈ completedClass C c l N i ∧ v ∈ G.edge e := by
  obtain ⟨e, he, hev⟩ := completedClass_covers C c l N hN hverts hregular i v
  refine ⟨e, ⟨he, hev⟩, ?_⟩
  intro f hf
  exact completedClass_isMatching C c l N hN hverts i f hf.1 e he v hf.2 hev

omit [Fintype V] in
/-- Internal completion adds no original complementary edge copy. -/
theorem completedClass_complement (i : Fin h) (e : ↥((OneCore.coreEdges C)ᶜ)) :
    e.val ∈ completedClass C c l N i ↔ c.color e = l i := by
  constructor
  · intro he
    rcases mem_union.mp he with hs | hn
    · exact (complement_mem_selectedClass C c l i e).mp hs
    · exact ((mem_compl.mp e.property) (coreMatchingCopies_subset_core C (N i) hn)).elim
  · intro he
    exact mem_union_left _ ((complement_mem_selectedClass C c l i e).mpr he)

omit [Fintype V] in
theorem completedClass_complement_inter (i : Fin h) :
    completedClass C c l N i ∩ (OneCore.coreEdges C)ᶜ = selectedClass C c l i := by
  ext e
  constructor
  · intro he
    obtain ⟨he, hcomp⟩ := mem_inter.mp he
    exact (complement_mem_selectedClass C c l i ⟨e, hcomp⟩).mpr
      ((completedClass_complement C c l N i ⟨e, hcomp⟩).mp he)
  · intro he
    exact mem_inter.mpr ⟨mem_union_left _ he, selectedClass_subset_complement C c l i he⟩

omit [Fintype V] in
/-- Distinct exterior labels and disjoint core matchings give disjoint full classes. -/
theorem completedClass_pairwiseDisjoint
    (hdisj : Pairwise (fun i j => Disjoint (N i).spanningCoe (N j).spanningCoe)) :
    Pairwise (fun i j => Disjoint (completedClass C c l N i) (completedClass C c l N j)) := by
  intro i j hij
  apply Finset.disjoint_union_left.mpr
  constructor
  · apply Finset.disjoint_union_right.mpr
    exact ⟨selectedClass_pairwiseDisjoint C c l hij,
      selectedClass_coreCopies_disjoint C c l i (N j)⟩
  · apply Finset.disjoint_union_right.mpr
    exact ⟨(selectedClass_coreCopies_disjoint C c l j (N i)).symm,
      coreMatchingCopies_disjoint C (N i) (N j) (hdisj hij)⟩

theorem completedClass_incidence_card
    (hN : ∀ i, (N i).IsMatching)
    (hverts : ∀ i, (N i).verts = (selectedFootprint C c l i : Set U)ᶜ)
    (hregular : ∀ v, G.degree v = k) (i : Fin h) (v : V) :
    ((completedClass C c l N i).filter (fun e => v ∈ G.edge e)).card = 1 :=
  completedClass_isPerfectMatching C c l N hN hverts hregular i v

end Overfull.OrdinaryFactorization
