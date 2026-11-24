import Overfull.CompatibleCircuits.SmallKernelData

/-!
# Actual compatible partitions of the small regular cores

The checked finite certificates from `SmallKernelData` are converted to
`Multigraph.CompatibleCircuitPartition`.  The finite theorem proved here does
not assert the minimal-counterexample, cut-vertex, or degree-two-suppression
reductions needed for the full restricted Fan--Zhang theorem.
-/

namespace Overfull.CompatibleCircuits.SmallKernel

open Finset

/-- The actual loopless multigraph represented by a canonical template. -/
def graph (kind : Fin 5) : Multigraph (Fin 4) (Fin 8) where
  edge e := s(first kind e, second kind e)
  loopless e := by simpa using endpoints_ne kind e

@[simp] theorem graph_incident (kind : Fin 5) (v : Fin 4) (e : Fin 8) :
    v ∈ (graph kind).edge e ↔ incident kind v e := by
  simp [graph, incident, Sym2.mem_iff]

theorem graph_support (kind : Fin 5) (C : Finset (Fin 8)) :
    (graph kind).edgeSupport C = codeSupport kind C := by
  ext v
  simp [Multigraph.mem_edgeSupport, codeSupport]

theorem graph_degree (kind : Fin 5) (C : Finset (Fin 8)) (v : Fin 4) :
    (graph kind).degreeOn C v = codeDegree kind C v := by
  simp [Multigraph.degreeOn, codeDegree]

/-- The number of active quotient vertices in a template. -/
def vertexCount : Fin 5 → ℕ := ![2, 3, 4, 4, 4]

/-- Each active vertex has exactly four incident copies; the other labels
are isolated in the selected edge-copy graph. -/
theorem degree_copies (kind : Fin 5) (v : Fin 4) :
    (graph kind).degreeOn (copies kind) v =
      if v.val < vertexCount kind then 4 else 0 := by
  rw [graph_degree]
  have h : ∀ (k : Fin 5) (w : Fin 4), codeDegree k (copies k) w =
      if w.val < vertexCount k then 4 else 0 := by decide +kernel
  exact h kind v

/-- The recorded local ranks distinguish the active incidences. -/
theorem incidenceRank_injective : ∀ (kind : Fin 5) (v : Fin 4) (e f : Fin 8),
    e ∈ copies kind → f ∈ copies kind → incident kind v e → incident kind v f →
    incidenceRank kind v e = incidenceRank kind v f → e = f := by
  decide +kernel

/-- Each local pair choice has precisely two incidences in each of its two
classes at an active vertex. -/
theorem local_class_card : ∀ (kind : Fin 5) (v : Fin 4) (q : Fin 3) (b : Bool),
    ((copies kind).filter (fun e =>
      incident kind v e ∧ pairClass q (incidenceRank kind v e) = b)).card =
      if v.val < vertexCount kind then 2 else 0 := by
  decide +kernel

theorem graph_cut (kind : Fin 5) (C : Finset (Fin 8)) (X : Finset (Fin 4)) :
    (graph kind).cutOn C X = codeCut kind C X := by
  ext e
  simp only [Multigraph.mem_cutOn, codeCut, mem_filter]
  have h := (graph kind).edge_eq e
  change s((graph kind).firstEnd e, (graph kind).secondEnd e) =
    s(first kind e, second kind e) at h
  rcases Sym2.eq_iff.mp h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · simp [h₁, h₂]
  · simp only [h₁, h₂, ne_eq, eq_iff_iff]
    tauto

theorem codeCircuit_isCircuit (kind : Fin 5) (C : Finset (Fin 8))
    (h : CodeCircuit kind C) : (graph kind).IsCircuit C := by
  simpa only [Multigraph.IsCircuit, graph_support, graph_degree, graph_cut] using h

theorem witnessPart_isCircuit (kind : Fin 5) (choice : Fin 4 → Fin 3) (i : Fin 4)
    (h : (witnessPart kind choice i).Nonempty) :
    (graph kind).IsCircuit (witnessPart kind choice i) :=
  codeCircuit_isCircuit kind _ (catalog_circuit kind _ h)

theorem witnessPart_compatible (kind : Fin 5) (choice : Fin 4 → Fin 3) (i : Fin 4) :
    (graph kind).Compatible (classOf kind choice) (witnessPart kind choice i) := by
  intro v e he hve f hf hvf hclass
  have hbound := catalog_class_bound kind (witnessCircuit kind choice i) v (choice v)
    ((witness_valid kind choice).2.2 i v) (classOf kind choice v e)
  apply Finset.card_le_one.mp hbound
  · exact Finset.mem_filter.mpr ⟨he, (graph_incident kind v e).mp hve, rfl⟩
  · exact Finset.mem_filter.mpr ⟨hf, (graph_incident kind v f).mp hvf, hclass.symm⟩

/-- A partition of all selected actual edge copies into compatible circuits. -/
noncomputable def partition (kind : Fin 5) (choice : Fin 4 → Fin 3) :
    (graph kind).CompatibleCircuitPartition (classOf kind choice) (copies kind) where
  parts := (univ.filter (fun i => (witnessPart kind choice i).Nonempty)).image
    (witnessPart kind choice)
  circuit := by
    intro C hC
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hC
    exact witnessPart_isCircuit kind choice i (mem_filter.mp hi).2
  compatible := by
    intro C hC
    obtain ⟨i, _, rfl⟩ := mem_image.mp hC
    exact witnessPart_compatible kind choice i
  disjoint := by
    intro C hC D hD hCD
    obtain ⟨i, _, rfl⟩ := mem_image.mp hC
    obtain ⟨j, _, rfl⟩ := mem_image.mp hD
    exact (witness_valid kind choice).2.1 i j (fun h => hCD (congrArg _ h))
  cover := by
    rw [← (witness_valid kind choice).1]
    ext e
    simp only [mem_biUnion, mem_image, mem_filter, mem_univ, true_and, id_eq]
    constructor
    · rintro ⟨C, ⟨i, _, rfl⟩, heC⟩
      exact ⟨i, heC⟩
    · rintro ⟨i, hei⟩
      exact ⟨witnessPart kind choice i, ⟨i, ⟨e, hei⟩, rfl⟩, hei⟩

/-- Every canonical core and local pair-class assignment has an actual
compatible circuit partition. -/
theorem exists_partition (kind : Fin 5) (choice : Fin 4 → Fin 3) :
    Nonempty ((graph kind).CompatibleCircuitPartition (classOf kind choice) (copies kind)) :=
  ⟨partition kind choice⟩

/-- Refining any forbidden pair classes preserves the certified partition. -/
theorem exists_partition_of_refinement {K : Type*} (kind : Fin 5)
    (choice : Fin 4 → Fin 3) (classes : Fin 4 → Fin 8 → K)
    (hrefine : ∀ v e, e ∈ copies kind → incident kind v e →
      ∀ f, f ∈ copies kind → incident kind v f → classes v e = classes v f →
        classOf kind choice v e = classOf kind choice v f) :
    Nonempty ((graph kind).CompatibleCircuitPartition classes (copies kind)) := by
  let P := partition kind choice
  refine ⟨{ P with compatible := ?_ }⟩
  intro C hC v e he hve f hf hvf hclasses
  have hsub : C ⊆ copies kind := by
    rw [← P.cover]
    intro a ha
    simp only [mem_biUnion, id_eq]
    exact ⟨C, hC, ha⟩
  exact P.compatible C hC v e he hve f hf hvf
    (hrefine v e (hsub he) ((graph_incident kind v e).mp hve)
      f (hsub hf) ((graph_incident kind v f).mp hvf) hclasses)

end Overfull.CompatibleCircuits.SmallKernel
