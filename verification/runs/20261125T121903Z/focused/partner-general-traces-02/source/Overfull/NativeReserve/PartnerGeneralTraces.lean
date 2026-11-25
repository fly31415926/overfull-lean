import Overfull.NativeReserve.PartnerTraces

/-!
# Exact partner-reserve traces with unpaired exceptions allowed

A selected exceptional matching copy is internal to its actual assigned
core or to one of the two separate pair fibers. The full partner code keeps
those labels unchanged across the reserve. Thus additional unpaired
exceptions do not change the empty-or-singleton native joining trace.
-/

noncomputable section

namespace Overfull.AssignedParts

open Finset Classical FourOdd

variable {V E : Type*} (G : Multigraph V E)

/-- Every selected copy meeting the exceptional set has equal actual
four-label endpoints. This permits arbitrarily many unpaired exceptions. -/
theorem exceptional_selected_twoPair_label_eq {M : Finset E}
    (hM : G.IsMatching M) (U₀ U₁ Z : Finset V)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (e₀ : E) (he₀ : e₀ ∈ M) {e : E} (he : e ∈ M)
    (hZ : G.firstEnd e ∈ Z ∨ G.secondEnd e ∈ Z) :
    twoPairAssignedLabel G M U₀ U₁ Z e₀ (G.firstEnd e) =
      twoPairAssignedLabel G M U₀ U₁ Z e₀ (G.secondEnd e) := by
  have hsame (U : Finset V) (hUZ : Disjoint U Z) :
      G.firstEnd e ∈ corePart G M Z U ↔ G.secondEnd e ∈ corePart G M Z U := by
    rw [firstEnd_mem_corePart_iff G hM Z U he,
      secondEnd_mem_corePart_iff G hM Z U he]
    rcases hZ with hz | hz
    · have hn : G.firstEnd e ∉ U := fun hh => disjoint_left.mp hUZ hh hz
      simp [hz, hn]
    · have hn : G.secondEnd e ∉ U := fun hh => disjoint_left.mp hUZ hh hz
      simp [hz, hn]
  have hpair : G.firstEnd e ∈ exceptionalPairPart G e₀ ↔
      G.secondEnd e ∈ exceptionalPairPart G e₀ := by
    constructor
    · intro hv
      have heq := hM e he e₀ he₀ (G.firstEnd e)
        ((G.incident_iff e _).mpr (Or.inl rfl)) ((mem_exceptionalPairPart G e₀ _).mp hv)
      rw [heq]
      exact (mem_exceptionalPairPart G e₀ _).mpr ((G.incident_iff e₀ _).mpr (Or.inr rfl))
    · intro hv
      have heq := hM e he e₀ he₀ (G.secondEnd e)
        ((G.incident_iff e _).mpr (Or.inr rfl)) ((mem_exceptionalPairPart G e₀ _).mp hv)
      rw [heq]
      exact (mem_exceptionalPairPart G e₀ _).mpr ((G.incident_iff e₀ _).mpr (Or.inl rfl))
  simp only [twoPairAssignedLabel, hsame U₀ h0Z, hsame U₁ h1Z, hpair]

end Overfull.AssignedParts

namespace Overfull.NativeReserve.PartnerBoundaryPacking

open Finset Classical AssignedParts FourOdd

variable {V E J : Type*} [Fintype V] [Fintype E]
    {G : Multigraph V E} {U₀ U₁ Z : Finset V} {M : Finset E} {r : ℕ}
    (Q : PartnerBoundaryPacking G U₀ U₁ Z M r)

omit [Fintype E] in
/-- Full partner-label transfer preserves the internal assigned label of
every exceptional boundary copy, including each unpaired assigned-core copy. -/
theorem exceptionalCopies_twoPair_label_eq
    (hM : G.IsPerfectMatching M)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (e₀ e₁ : E) (he : e₀ ≠ e₁) (hpair : G.internalOn M Z = {e₀,e₁})
    (i : Fin r) {e : E} (heZ : e ∈ exceptionalCopies G (Q.parent i) Z) :
    twoPairAssignedLabel G M U₀ U₁ Z e₀ (G.firstEnd e) =
      twoPairAssignedLabel G M U₀ U₁ Z e₀ (G.secondEnd e) := by
  obtain ⟨f₀, f₁, _hf, hfull, _hedge₀, _hedge₁, hlabel, _hfibers⟩ :=
    exists_two_pair_assigned_label_transfer G hM (Q.perfect i) U₀ U₁ Z
      h01 h0Z h1Z hcover (Q.sameSignature i).symm e₀ e₁ he hpair
  have hf₀ : f₀ ∈ Q.parent i := by
    have hh : f₀ ∈ G.internalOn (Q.parent i) Z := by rw [hfull]; exact mem_insert_self _ _
    exact (mem_filter.mp hh).1
  obtain ⟨heM, heZ⟩ := (mem_exceptionalCopies G (Q.parent i) Z e).mp heZ
  rw [hlabel]
  exact exceptional_selected_twoPair_label_eq G ((Q.perfect i).isMatching G)
    U₀ U₁ Z h0Z h1Z f₀ hf₀ heM heZ

/-- The original joining trace is precisely the selected old-core crossing,
even when unpaired exceptions are assigned into either core. -/
theorem boundary_twoPair_joining_trace_general
    (hM : G.IsPerfectMatching M)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (e₀ e₁ : E) (he : e₀ ≠ e₁) (hpair : G.internalOn M Z = {e₀,e₁}) (i : Fin r) :
    Q.boundary i ∩ joiningCopies G (twoPairAssignedLabel G M U₀ U₁ Z e₀) =
      paritySelection (G.cutOn (Q.parent i) U₀ ∩ G.cutOn (Q.parent i) U₁) := by
  ext e
  constructor
  · rintro heT
    obtain ⟨heB, heJ⟩ := mem_inter.mp heT
    rcases mem_union.mp heB with heZ | heX
    · exact ((mem_joiningCopies G _ e).mp heJ
        (Q.exceptionalCopies_twoPair_label_eq hM h01 h0Z h1Z hcover e₀ e₁ he hpair i heZ)).elim
    · exact heX
  · intro heX
    refine mem_inter.mpr ⟨mem_union_right _ heX, ?_⟩
    apply (mem_joiningCopies G _ e).mpr
    rcases ((mem_coreCrossings_iff G (Q.parent i) U₀ U₁ h01 e).mp
      (paritySelection_subset _ heX)).2 with hc | hc
    · rw [twoPairAssignedLabel_on_core₀ G M U₀ U₁ Z e₀ hc.1,
        twoPairAssignedLabel_on_core₁ G (hM.isMatching G) U₀ U₁ Z h01 h0Z h1Z e₀ hc.2]
      decide
    · rw [twoPairAssignedLabel_on_core₁ G (hM.isMatching G) U₀ U₁ Z h01 h0Z h1Z e₀ hc.1,
        twoPairAssignedLabel_on_core₀ G M U₀ U₁ Z e₀ hc.2]
      decide

/-- The joining trace has the parity of the assigned core, including its
unpaired exceptional vertices; it need not have the parity of the old core. -/
theorem boundary_twoPair_joining_trace_card_general
    (hM : G.IsPerfectMatching M)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (e₀ e₁ : E) (he : e₀ ≠ e₁) (hpair : G.internalOn M Z = {e₀,e₁}) (i : Fin r) :
    (Q.boundary i ∩ joiningCopies G (twoPairAssignedLabel G M U₀ U₁ Z e₀)).card =
      (corePart G M Z U₀).card % 2 := by
  rw [Q.boundary_twoPair_joining_trace_general hM h01 h0Z h1Z hcover e₀ e₁ he hpair i,
    paritySelection_card, ← corePart_card_parity G (Q.perfect i) U₀ U₁ Z h01 h0Z h1Z hcover,
    (Q.assignedParts hM h01 h0Z h1Z hcover i).1]

/-- All selected native joining traces survive with their actual parity
size after reserve-avoiding deletion, including the unpaired branch. -/
theorem residualBoundary_twoPair_joining_trace_card_general
    (hM : G.IsPerfectMatching M)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (e₀ e₁ : E) (he : e₀ ≠ e₁) (hpair : G.internalOn M Z = {e₀,e₁})
    (N : J → Finset E) (T : Finset J)
    (havoid : ∀ j ∈ T, Disjoint (N j) (removedCopies Q.boundary univ)) (i : Fin r) :
    (Q.residualBoundary N T i ∩
      joiningCopies (residualGraph G N T) (twoPairAssignedLabel G M U₀ U₁ Z e₀)).card =
      (corePart G M Z U₀).card % 2 := by
  rw [Q.residualBoundary_joining_trace_eq_surviving,
    survivingCopies_card _ _ ((Q.boundary_disjoint_removed N T havoid i).mono_left
      inter_subset_left)]
  exact Q.boundary_twoPair_joining_trace_card_general hM h01 h0Z h1Z hcover e₀ e₁ he hpair i

/-- Every selected trace is empty when the actual assigned cores are even,
with no requirement that the exceptional pairs exhaust the exceptional set. -/
theorem residualBoundary_twoPair_joining_trace_empty_general
    (hM : G.IsPerfectMatching M)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (e₀ e₁ : E) (he : e₀ ≠ e₁) (hpair : G.internalOn M Z = {e₀,e₁})
    (heven : (corePart G M Z U₀).card % 2 = 0)
    (N : J → Finset E) (T : Finset J)
    (havoid : ∀ j ∈ T, Disjoint (N j) (removedCopies Q.boundary univ)) (i : Fin r) :
    Q.residualBoundary N T i ∩
      joiningCopies (residualGraph G N T) (twoPairAssignedLabel G M U₀ U₁ Z e₀) = ∅ := by
  apply card_eq_zero.mp
  rw [Q.residualBoundary_twoPair_joining_trace_card_general hM h01 h0Z h1Z hcover
    e₀ e₁ he hpair N T havoid i, heven]

/-- Every odd assigned-core trace is one actual residual zero-one crossing.
All indices and parallel copies remain distinct even with unpaired exceptions. -/
theorem exists_twoPair_residual_joining_singletons_general
    (hM : G.IsPerfectMatching M)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (e₀ e₁ : E) (he : e₀ ≠ e₁) (hpair : G.internalOn M Z = {e₀,e₁})
    (hodd : (corePart G M Z U₀).card % 2 = 1)
    (N : J → Finset E) (T : Finset J)
    (havoid : ∀ j ∈ T, Disjoint (N j) (removedCopies Q.boundary univ)) :
    ∃ f : Fin r → joiningCopies (residualGraph G N T) (twoPairAssignedLabel G M U₀ U₁ Z e₀),
      Function.Injective f ∧
      (∀ i, Q.residualBoundary N T i ∩
        joiningCopies (residualGraph G N T) (twoPairAssignedLabel G M U₀ U₁ Z e₀) = {(f i).val}) ∧
      (∀ i, (joiningQuotient (residualGraph G N T)
        (twoPairAssignedLabel G M U₀ U₁ Z e₀)).edge (f i) = s(0,1)) := by
  let label := twoPairAssignedLabel G M U₀ U₁ Z e₀
  have hex (i : Fin r) : ∃ e,
      Q.residualBoundary N T i ∩ joiningCopies (residualGraph G N T) label = {e} := by
    apply card_eq_one.mp
    rw [Q.residualBoundary_twoPair_joining_trace_card_general hM h01 h0Z h1Z hcover
      e₀ e₁ he hpair N T havoid i, hodd]
  choose g hg using hex
  have hmem (i : Fin r) : g i ∈ Q.residualBoundary N T i ∩
      joiningCopies (residualGraph G N T) label := by
    rw [hg i]
    exact mem_singleton_self _
  let f (i : Fin r) : joiningCopies (residualGraph G N T) label :=
    ⟨g i, (mem_inter.mp (hmem i)).2⟩
  refine ⟨f, ?_, hg, ?_⟩
  · intro i j hij
    have hgij : g i = g j := congrArg Subtype.val hij
    by_contra hne
    exact disjoint_left.mp (Q.residualBoundary_disjoint N T hne)
      (mem_inter.mp (hmem i)).1 (hgij.symm ▸ (mem_inter.mp (hmem j)).1)
  · intro i
    have hraw : (g i).val ∈ Q.boundary i ∩ joiningCopies G label := by
      exact mem_image.mpr ⟨g i, hmem i, rfl⟩ |> fun hh =>
        Q.residualBoundary_joining_trace_image N T havoid label i ▸ hh
    rw [Q.boundary_twoPair_joining_trace_general hM h01 h0Z h1Z hcover e₀ e₁ he hpair i] at hraw
    exact coreCrossing_twoPairAssignedLabel_pair G (hM.isMatching G) (Q.parent i)
      U₀ U₁ Z h01 h0Z h1Z e₀ (paritySelection_subset _ hraw)

end Overfull.NativeReserve.PartnerBoundaryPacking
