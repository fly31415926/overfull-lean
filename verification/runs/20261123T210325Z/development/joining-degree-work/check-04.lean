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
  simp only [hsame U₀ h0Z, hsame U₁ h1Z]

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
    rw [FourOdd.joiningGraph_degree_eq]
    unfold Multigraph.degreeOn
    congr 1
    ext e
    simp only [mem_filter, mem_inter, Multigraph.mem_incidenceEdges]
    exact and_comm
  change (FourOdd.joiningGraph R label).degree z + G.degreeOn A z ≤ R.degree z
  rw [hjoin]
  change G.degreeOn A z ≤ (R.incidenceEdges z \ FourOdd.joiningCopies R label).card at hcount
  change _ + _ = R.degree z at hsplit
  omega



namespace BoundaryPacking
variable {G : Multigraph V E} {U₀ U₁ Z : Finset V} {M : Finset E} {r : ℕ}
  (Q : BoundaryPacking G U₀ U₁ Z M r)

/-- Every reserve copy at an exceptional vertex is internal for the fixed
original representative's assignment, even though the parents may differ. -/
theorem exceptional_label_eq (hM : G.IsPerfectMatching M)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2)
    (j : Fin r) {z : V} (hz : z ∈ Z) {e : E}
    (he : e ∈ Q.boundary j) (hze : z ∈ G.edge e) :
    AssignedParts.assignedLabel G M U₀ U₁ Z (G.firstEnd e) =
      AssignedParts.assignedLabel G M U₀ U₁ Z (G.secondEnd e) := by
  have hsame := assignedLabel_eq_of_signature_eq G (Q.perfect j) hM U₀ U₁ Z
    h01 h0Z h1Z hcover hZ (Q.sameSignature j)
  rw [← hsame]
  apply exceptional_selected_label_eq G ((Q.perfect j).isMatching G)
    U₀ U₁ Z h0Z h1Z (compressedBoundary_subset G (Q.parent j) U₀ U₁ Z he)
  rcases (G.incident_iff e z).mp hze with h | h
  · exact Or.inl (h.symm ▸ hz)
  · exact Or.inr (h.symm ▸ hz)

/-- The actual union of protected boundaries has exactly r incidences at
every exceptional vertex. Distinct parallel copies remain distinct. -/
theorem reserved_exceptional_degree {z : V} (hz : z ∈ Z) :
    G.degreeOn (removedCopies Q.boundary univ) z = r := by
  rw [removed_degreeOn G Q.boundary univ
    (fun _ _ _ _ hij => Q.pairwise_disjoint hij)]
  simp only [Q.exceptional_degree _ hz, sum_const, card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one]

/-- If every removed matching avoids the reserve, their union avoids it. -/
theorem reserved_disjoint_removed {J : Type*} (N : J → Finset E) (T : Finset J)
    (havoid : ∀ j ∈ T, Disjoint (N j) (removedCopies Q.boundary univ)) :
    Disjoint (removedCopies Q.boundary univ) (removedCopies N T) := by
  apply disjoint_left.mpr
  intro e heA heD
  obtain ⟨j, hj, heN⟩ := (mem_removedCopies N T e).mp heD
  exact disjoint_left.mp (havoid j hj) heN heA

/-- The surviving r internal reserve incidences bound the exceptional
joining degree by h-r in the actual h-regular residual. -/
theorem residual_exceptional_joining_degree (hM : G.IsPerfectMatching M)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2)
    {J : Type*} (N : J → Finset E) (T : Finset J)
    (havoid : ∀ j ∈ T, Disjoint (N j) (removedCopies Q.boundary univ))
    (h : ℕ) (hregular : ∀ v, (residualGraph G N T).degree v = h)
    {z : V} (hz : z ∈ Z) :
    (FourOdd.joiningGraph (residualGraph G N T)
      (AssignedParts.assignedLabel G M U₀ U₁ Z)).degree z ≤ h-r := by
  have hcount := residual_joining_degree_add_reserved_le G
    (AssignedParts.assignedLabel G M U₀ U₁ Z)
    (removedCopies N T) (removedCopies Q.boundary univ)
    (Q.reserved_disjoint_removed N T havoid) z (by
      intro e he hze
      obtain ⟨j, _hj, he⟩ := (mem_removedCopies Q.boundary univ e).mp he
      exact Q.exceptional_label_eq hM h01 h0Z h1Z hcover hZ j hz he hze)
  change (FourOdd.joiningGraph (residualGraph G N T)
      (AssignedParts.assignedLabel G M U₀ U₁ Z)).degree z +
    G.degreeOn (removedCopies Q.boundary univ) z ≤ (residualGraph G N T).degree z at hcount
  rw [Q.reserved_exceptional_degree hz, hregular] at hcount
  omega

end BoundaryPacking

/-- Both old cores and all exceptions satisfy their separate sharp bounds,
and hence every residual joining degree is at most max(a,h-r). The label
map is still the original representative's assignment. -/
theorem native_residual_joining_degree_bounds (G : Multigraph V E)
    (U₀ U₁ Z : Finset V) {M : Finset E} (hM : G.IsPerfectMatching M)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2)
    (r : ℕ) (Q : BoundaryPacking G U₀ U₁ Z M r)
    {J : Type*} (N : J → Finset E) (T : Finset J)
    (havoid : ∀ j ∈ T, Disjoint (N j) (removedCopies Q.boundary univ))
    (h : ℕ) (a : ℝ) (hrh : r ≤ h)
    (hregular : ∀ v, (residualGraph G N T).degree v = h)
    (C₀ : SmallCuts.Core (residualGraph G N T) U₀)
    (C₁ : SmallCuts.Core (residualGraph G N T) U₁)
    (hcore₀ : ∀ v, (h : ℝ)-a ≤ (C₀.graph.degree v : ℝ))
    (hcore₁ : ∀ v, (h : ℝ)-a ≤ (C₁.graph.degree v : ℝ)) :
    (∀ v ∈ U₀, ((FourOdd.joiningGraph (residualGraph G N T)
      (assignedLabel G M U₀ U₁ Z)).degree v : ℝ) ≤ a) ∧
    (∀ v ∈ U₁, ((FourOdd.joiningGraph (residualGraph G N T)
      (assignedLabel G M U₀ U₁ Z)).degree v : ℝ) ≤ a) ∧
    (∀ z ∈ Z, (FourOdd.joiningGraph (residualGraph G N T)
      (assignedLabel G M U₀ U₁ Z)).degree z ≤ h-r) ∧
    (∀ v, ((FourOdd.joiningGraph (residualGraph G N T)
      (assignedLabel G M U₀ U₁ Z)).degree v : ℝ) ≤ max a ((h : ℝ)-r)) := by
  let label := assignedLabel G M U₀ U₁ Z
  have hb₀ (v : V) (hv : v ∈ U₀) :
      ((FourOdd.joiningGraph (residualGraph G N T) label).degree v : ℝ) ≤ a :=
    joining_degree_le_core_error (residualGraph G N T) label U₀ C₀ 0
      (fun _ hv => assignedLabel_on_core₀ G M U₀ U₁ Z hv) h a hregular hcore₀ ⟨v, hv⟩
  have hb₁ (v : V) (hv : v ∈ U₁) :
      ((FourOdd.joiningGraph (residualGraph G N T) label).degree v : ℝ) ≤ a :=
    joining_degree_le_core_error (residualGraph G N T) label U₁ C₁ 1
      (fun _ hv => assignedLabel_on_core₁ G (hM.isMatching G) U₀ U₁ Z
        h01 h0Z h1Z hv) h a hregular hcore₁ ⟨v, hv⟩
  have hbZ (z : V) (hz : z ∈ Z) :
      (FourOdd.joiningGraph (residualGraph G N T) label).degree z ≤ h-r :=
    Q.residual_exceptional_joining_degree hM h01 h0Z h1Z hcover hZ N T havoid h hregular hz
  refine ⟨hb₀, hb₁, hbZ, ?_⟩
  intro v
  rcases hcover v with hv | hv | hv
  · exact (hb₀ v hv).trans (le_max_left _ _)
  · exact (hb₁ v hv).trans (le_max_left _ _)
  · have hb : ((FourOdd.joiningGraph (residualGraph G N T) label).degree v : ℝ) ≤
        ((h-r : ℕ) : ℝ) := by exact_mod_cast hbZ v hv
    rw [Nat.cast_sub hrh] at hb
    exact hb.trans (le_max_right _ _)

end Overfull.NativeReserve
