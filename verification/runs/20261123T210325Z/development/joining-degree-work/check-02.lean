import Overfull.NativeReserve.CompletionConstruction
import Overfull.AssignedParts.JoiningConstruction

/-!
# Joining incidence bounds in the actual native residual

Old-core copies are internal to their assigned parts. At every exceptional
vertex, each protected compressed boundary supplies a distinct surviving
internal incidence. These facts bound the actual residual joining degrees,
without identifying its representative matching with a residual matching.
-/

noncomputable section
namespace Overfull.NativeReserve
open Finset Classical AssignedParts
open scoped BigOperators

variable {V E I : Type*}

/-- Both endpoints of every selected exceptional copy have the same actual
assigned label. This concerns selected exceptional copies only. -/
theorem exceptional_selected_label_eq (G : Multigraph V E) {M : Finset E}
    (hM : G.IsMatching M) (U₀ U₁ Z : Finset V)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    {e : E} (he : e ∈ M) (hZ : G.firstEnd e ∈ Z ∨ G.secondEnd e ∈ Z) :
    assignedLabel G M U₀ U₁ Z (G.firstEnd e) =
      assignedLabel G M U₀ U₁ Z (G.secondEnd e) := by
  have hsame (U : Finset V) (hUZ : Disjoint U Z) :
      G.firstEnd e ∈ corePart G M Z U ↔ G.secondEnd e ∈ corePart G M Z U := by
    rw [firstEnd_mem_corePart_iff G hM Z U he,
      secondEnd_mem_corePart_iff G hM Z U he]
    rcases hZ with hz | hz
    · have hn : G.firstEnd e ∉ U := fun hh => disjoint_left.mp hUZ hh hz
      simp [hz, hn]
    · have hn : G.secondEnd e ∉ U := fun hh => disjoint_left.mp hUZ hh hz
      simp [hz, hn]
  unfold assignedLabel labelOfThreeParts
  rw [hsame U₀ h0Z, hsame U₁ h1Z]

/-- The original first core always has assigned label zero. -/
theorem assignedLabel_on_core₀ (G : Multigraph V E) (M : Finset E)
    (U₀ U₁ Z : Finset V) {v : V} (hv : v ∈ U₀) :
    assignedLabel G M U₀ U₁ Z v = 0 := by
  apply (labelOfThreeParts_eq_zero_iff _ _ _).mpr
  exact core_subset_corePart G M Z U₀ hv

/-- The original second core has assigned label one. -/
theorem assignedLabel_on_core₁ (G : Multigraph V E) {M : Finset E}
    (hM : G.IsMatching M) (U₀ U₁ Z : Finset V)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    {v : V} (hv : v ∈ U₁) : assignedLabel G M U₀ U₁ Z v = 1 := by
  have hv₁ := core_subset_corePart G M Z U₁ hv
  apply (labelOfThreeParts_eq_one_iff _ _ _).mpr
  exact ⟨fun hv₀ => disjoint_left.mp (coreParts_disjoint G hM U₀ U₁ Z h01 h0Z h1Z)
    hv₀ hv₁, hv₁⟩

variable [Fintype E] [DecidableEq I]

/-- A simple embedded core on which the label is constant has no joining
copy; all remaining parallel host copies are still counted separately. -/
theorem joiningCopies_disjoint_core (G : Multigraph V E) (label : V → I)
    (U : Finset V) (C : SmallCuts.Core G U) (i : I)
    (hlabel : ∀ v ∈ U, label v = i) :
    Disjoint (FourOdd.joiningCopies G label) (OneCore.coreEdges C) := by
  apply disjoint_left.mpr
  intro e hj hc
  have hfirst : G.firstEnd e ∈ U := OneCore.coreEdges_endpoint C hc
    ((G.incident_iff e _).mpr (Or.inl rfl))
  have hsecond : G.secondEnd e ∈ U := OneCore.coreEdges_endpoint C hc
    ((G.incident_iff e _).mpr (Or.inr rfl))
  exact (FourOdd.mem_joiningCopies G label e).mp hj
    ((hlabel _ hfirst).trans (hlabel _ hsecond).symm)

/-- Joining incidence at an old-core vertex is bounded by the actual
retained core-complement error. -/
theorem joining_degree_le_core_error (G : Multigraph V E) (label : V → I)
    (U : Finset V) (C : SmallCuts.Core G U) (i : I)
    (hlabel : ∀ v ∈ U, label v = i) (h : ℕ) (a : ℝ)
    (hregular : ∀ v, G.degree v = h)
    (hcore : ∀ v, (h : ℝ)-a ≤ (C.graph.degree v : ℝ)) (v : U) :
    ((FourOdd.joiningGraph G label).degree v.val : ℝ) ≤ a := by
  have hsubset : FourOdd.joiningCopies G label ⊆ (OneCore.coreEdges C)ᶜ := by
    intro e he
    exact mem_compl.mpr (fun hc => disjoint_left.mp
      (joiningCopies_disjoint_core G label U C i hlabel) he hc)
  have hle := G.restrictEdges_degree_mono hsubset v.val
  have hleR : ((FourOdd.joiningGraph G label).degree v.val : ℝ) ≤
      (G.restrictEdges (OneCore.coreEdges C)ᶜ).degree v.val := by exact_mod_cast hle
  exact hleR.trans (OneCore.complement_degree_le_error C h a hregular hcore v)

/-- Surviving reserved incidences which are internal under the fixed labels
occupy distinct nonjoining incidences of the actual residual. -/
theorem residual_joining_degree_add_reserved_le (G : Multigraph V E)
    (label : V → I) (D A : Finset E) (havoid : Disjoint A D) (z : V)
    (hinternal : ∀ e ∈ A, z ∈ G.edge e →
      label (G.firstEnd e) = label (G.secondEnd e)) :
    (FourOdd.joiningGraph (MultigraphMatchingProbability.remainingGraph G D) label).degree z +
      G.degreeOn A z ≤ (MultigraphMatchingProbability.remainingGraph G D).degree z := by
  let R := MultigraphMatchingProbability.remainingGraph G D
  let S := A.filter (fun e => z ∈ G.edge e)
  let T := R.incidenceEdges z \ FourOdd.joiningCopies R label
  let f (e : S) : T := ⟨⟨e.val, fun hd =>
      disjoint_left.mp havoid (mem_filter.mp e.property).1 hd⟩, by
    apply mem_sdiff.mpr
    refine ⟨(R.mem_incidenceEdges z _).mpr (mem_filter.mp e.property).2, ?_⟩
    intro hj
    exact (FourOdd.mem_joiningCopies R label _).mp hj
      (hinternal e.val (mem_filter.mp e.property).1 (mem_filter.mp e.property).2)⟩
  have hf : Function.Injective f := by
    intro e e' he
    exact Subtype.ext (congrArg (fun x : T => x.val.val) he)
  have hcount : G.degreeOn A z ≤ T.card := by
    have hc := Fintype.card_le_of_injective f hf
    simpa only [Fintype.card_coe, S, Multigraph.degreeOn] using hc
  have hsplit := card_sdiff_add_card_inter (R.incidenceEdges z) (FourOdd.joiningCopies R label)
  have hjoin : (FourOdd.joiningGraph R label).degree z =
      (R.incidenceEdges z ∩ FourOdd.joiningCopies R label).card := by
    rw [FourOdd.joiningGraph, Multigraph.restrictEdges_degree, inter_comm]
  change (FourOdd.joiningGraph R label).degree z + G.degreeOn A z ≤ R.degree z
  rw [hjoin]
  change G.degreeOn A z ≤ (R.incidenceEdges z \ FourOdd.joiningCopies R label).card at hcount
  change _ + _ = R.degree z at hsplit
  omega

end Overfull.NativeReserve
