import Overfull.NativeCore.Incidence
import Overfull.WeightedPalette.StarWeights

/-!
# Exact exceptional coverage and restriction of weighted resources

In an h-regular host, h pairwise disjoint color classes covering an
exception already contain every actual copy incident with that exception.
Consequently original-copy coverage follows from saturation, without
replacing parallel copies by pairs of endpoint vertices.
-/

noncomputable section

namespace Overfull.NativeCore

open Finset Classical AssignedParts NativeReserve WeightedPalette

variable {V E : Type*} [Fintype E]

/-- A weight for the union of the old cores also controls the assigned
star weight for either individual core. -/
theorem starWeight_mono_core (G : Multigraph V E) (z : V)
    (U W : Finset V) (hUW : U ⊆ W) (B : Finset E) :
    starWeight G z U B ≤ starWeight G z W B := by
  apply card_le_card
  intro e he
  obtain ⟨hpool, hs⟩ := (mem_starBlockedCopies G z U B e).mp he
  exact (mem_starBlockedCopies G z W B e).mpr
    ⟨mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hpool).2.1,
      hUW (mem_filter.mp hpool).2.2⟩, hs⟩

/-- All h incident copies of a degree-h vertex occur once h disjoint
classes each cover the vertex. The classes need not be perfect matchings. -/
theorem incidence_covered_of_full_palette (G : Multigraph V E) (h : ℕ)
    (B : Fin h → Finset E)
    (hdisj : Pairwise (fun i j => Disjoint (B i) (B j)))
    (z : V) (hdegree : G.degree z = h)
    (hcover : ∀ j, z ∈ G.edgeSupport (B j)) :
    G.incidenceEdges z ⊆ univ.biUnion B := by
  let A := univ.biUnion B
  have hsub (j : Fin h) : B j ⊆ A :=
    fun _ he => mem_biUnion.mpr ⟨j, mem_univ _, he⟩
  have hload := G.family_support_load_le_degreeOn B A hdisj hsub z
  have hfilter : univ.filter (fun j : Fin h => z ∈ G.edgeSupport (B j)) = univ := by
    apply filter_eq_self.mpr
    intro j _
    exact hcover j
  rw [hfilter, card_univ, Fintype.card_fin] at hload
  have hin : A.filter (fun e => z ∈ G.edge e) ⊆ G.incidenceEdges z := by
    intro e he
    exact (G.mem_incidenceEdges z e).mpr (mem_filter.mp he).2
  have heq : A.filter (fun e => z ∈ G.edge e) = G.incidenceEdges z :=
    eq_of_subset_of_card_le hin (by simpa only [← hdegree] using hload)
  intro e he
  rw [← heq] at he
  exact (mem_filter.mp he).1

/-- Covering every exception in every color gives exact coverage of all
original exceptional copies, regardless of their parallel multiplicities. -/
theorem exceptionalCopies_covered_of_full_palette (G : Multigraph V E) (h : ℕ)
    (B : Fin h → Finset E) (Z : Finset V)
    (hdisj : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hregular : ∀ z ∈ Z, G.degree z = h)
    (hcover : ∀ j, Z ⊆ G.edgeSupport (B j)) :
    exceptionalCopies G univ Z ⊆ univ.biUnion B := by
  intro e he
  obtain ⟨_, hz | hz⟩ := (mem_exceptionalCopies G univ Z e).mp he
  · exact incidence_covered_of_full_palette G h B hdisj _ (hregular _ hz)
      (fun j => hcover j hz) ((G.mem_incidenceEdges _ e).mpr
        ((G.incident_iff e _).mpr (Or.inl rfl)))
  · exact incidence_covered_of_full_palette G h B hdisj _ (hregular _ hz)
      (fun j => hcover j hz) ((G.mem_incidenceEdges _ e).mpr
        ((G.incident_iff e _).mpr (Or.inr rfl)))

/-- A family containing the joining palette, covering all exceptions, and
using only those two types of copies partitions the full external set. -/
theorem external_union_eq_of_saturation {K : Type*} [DecidableEq K]
    (G : Multigraph V E) (label : V → K) (h : ℕ)
    (B : Fin h → Finset E) (Z : Finset V)
    (hdisj : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hregular : ∀ z ∈ Z, G.degree z = h)
    (hcover : ∀ j, Z ⊆ G.edgeSupport (B j))
    (hjoining : FourOdd.joiningCopies G label ⊆ univ.biUnion B)
    (hsub : ∀ j, B j ⊆ FourOdd.joiningCopies G label ∪ exceptionalCopies G univ Z) :
    univ.biUnion B = FourOdd.joiningCopies G label ∪ exceptionalCopies G univ Z := by
  apply subset_antisymm
  · intro e he
    obtain ⟨j, _, hej⟩ := mem_biUnion.mp he
    exact hsub j hej
  · exact union_subset hjoining
      (exceptionalCopies_covered_of_full_palette G h B Z hdisj hregular hcover)

end Overfull.NativeCore
