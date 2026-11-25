import Overfull.NativeReserve.PartnerResidual
import Overfull.AssignedParts.PartnerLabels

/-!
# Exact protected joining traces for two native exceptional pairs

When the two exceptional endpoint pairs exhaust the exceptional set, the
partner code makes every exceptional boundary copy internal to its own pair
fiber.  The joining trace is therefore precisely the selected old-core
crossing.  Reserve-avoiding deletion preserves its original copy and index.
-/

noncomputable section

namespace Overfull.AssignedParts

open Finset Classical FourOdd

variable {V E : Type*} (G : Multigraph V E)

/-- If every exceptional vertex is paired inside a matching, every matching
copy incident with an exception is an internal exceptional copy. -/
theorem exceptionalCopies_eq_internalOn_of_pairPart_eq {M : Finset E}
    (hM : G.IsMatching M) (Z : Finset V) (hpaired : pairPart G M Z = Z) :
    exceptionalCopies G M Z = G.internalOn M Z := by
  apply subset_antisymm
  · intro e he
    obtain ⟨heM, hz⟩ := (mem_exceptionalCopies G M Z e).mp he
    have hex : ∃ v ∈ Z, v ∈ G.edge e := by
      rcases hz with hz | hz
      · exact ⟨G.firstEnd e, hz, (G.incident_iff e _).mpr (Or.inl rfl)⟩
      · exact ⟨G.secondEnd e, hz, (G.incident_iff e _).mpr (Or.inr rfl)⟩
    obtain ⟨v, hvZ, hve⟩ := hex
    have hvP : v ∈ pairPart G M Z := hpaired.symm ▸ hvZ
    obtain ⟨f, hf, hvf⟩ := (G.mem_edgeSupport _ v).mp hvP
    have hef := hM e heM f (mem_filter.mp hf).1 v hve hvf
    exact hef.symm ▸ hf
  · intro e he
    exact (mem_exceptionalCopies G M Z e).mpr
      ⟨(mem_filter.mp he).1, Or.inl (mem_filter.mp he).2.1⟩

theorem twoPairAssignedLabel_on_core₀ (M : Finset E) (U₀ U₁ Z : Finset V)
    (e : E) {v : V} (hv : v ∈ U₀) :
    twoPairAssignedLabel G M U₀ U₁ Z e v = 0 := by
  simp only [twoPairAssignedLabel, if_pos (core_subset_corePart G M Z U₀ hv)]

theorem twoPairAssignedLabel_on_core₁ {M : Finset E} (hM : G.IsMatching M)
    (U₀ U₁ Z : Finset V) (h01 : Disjoint U₀ U₁)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z) (e : E)
    {v : V} (hv : v ∈ U₁) :
    twoPairAssignedLabel G M U₀ U₁ Z e v = 1 := by
  have hv1 := core_subset_corePart G M Z U₁ hv
  have hv0 : v ∉ corePart G M Z U₀ :=
    fun hh => disjoint_left.mp (coreParts_disjoint G hM U₀ U₁ Z h01 h0Z h1Z) hh hv1
  simp only [twoPairAssignedLabel, if_neg hv0, if_pos hv1]

/-- An old-core crossing joins precisely the first two actual pair-assigned
labels, independently of its parallel-copy representative. -/
theorem coreCrossing_twoPairAssignedLabel_pair {M : Finset E}
    (hM : G.IsMatching M) (F : Finset E) (U₀ U₁ Z : Finset V)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (e₀ : E) {e : E} (he : e ∈ G.cutOn F U₀ ∩ G.cutOn F U₁) :
    s(twoPairAssignedLabel G M U₀ U₁ Z e₀ (G.firstEnd e),
      twoPairAssignedLabel G M U₀ U₁ Z e₀ (G.secondEnd e)) = s(0,1) := by
  rcases ((mem_coreCrossings_iff G F U₀ U₁ h01 e).mp he).2 with hc | hc
  · rw [twoPairAssignedLabel_on_core₀ G M U₀ U₁ Z e₀ hc.1,
      twoPairAssignedLabel_on_core₁ G hM U₀ U₁ Z h01 h0Z h1Z e₀ hc.2]
  · rw [twoPairAssignedLabel_on_core₁ G hM U₀ U₁ Z h01 h0Z h1Z e₀ hc.1,
      twoPairAssignedLabel_on_core₀ G M U₀ U₁ Z e₀ hc.2]
    exact Sym2.eq_swap

end Overfull.AssignedParts

namespace Overfull.NativeReserve.PartnerBoundaryPacking

open Finset Classical AssignedParts FourOdd

variable {V E J : Type*} [Fintype V] [Fintype E]
    {G : Multigraph V E} {U₀ U₁ Z : Finset V} {M : Finset E} {r : ℕ}
    (Q : PartnerBoundaryPacking G U₀ U₁ Z M r)

/-- Equal full partner codes keep all exceptional copies inside their two
separately labeled endpoint pairs. -/
theorem exceptionalCopies_not_joining_twoPair
    (hM : G.IsPerfectMatching M)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (e₀ e₁ : E) (he : e₀ ≠ e₁) (hpair : G.internalOn M Z = {e₀,e₁})
    (hZ : Z = exceptionalPairPart G e₀ ∪ exceptionalPairPart G e₁)
    (i : Fin r) {e : E} (heZ : e ∈ exceptionalCopies G (Q.parent i) Z) :
    e ∉ joiningCopies G (twoPairAssignedLabel G M U₀ U₁ Z e₀) := by
  obtain ⟨f₀, f₁, _hf, hfull, _hedge₀, _hedge₁, _hlabel, _h0, _h1, h2, h3⟩ :=
    exists_two_pair_assigned_label_transfer G hM (Q.perfect i) U₀ U₁ Z
      h01 h0Z h1Z hcover (Q.sameSignature i).symm e₀ e₁ he hpair
  have hpM : pairPart G M Z = Z := (pairPart_eq_two_pair_union G e₀ e₁ hpair).trans hZ.symm
  have hp : pairPart G (Q.parent i) Z = Z :=
    (Q.assignedParts hM h01 h0Z h1Z hcover i).2.2.trans hpM
  rw [exceptionalCopies_eq_internalOn_of_pairPart_eq G ((Q.perfect i).isMatching G) Z hp,
    hfull] at heZ
  have hinternal (f : E) (k : Fin 4)
      (hfib : labelShore (twoPairAssignedLabel G M U₀ U₁ Z e₀) {k} = exceptionalPairPart G f) :
      f ∉ joiningCopies G (twoPairAssignedLabel G M U₀ U₁ Z e₀) := by
    have hfirst : twoPairAssignedLabel G M U₀ U₁ Z e₀ (G.firstEnd f) = k := by
      apply mem_singleton.mp
      apply (mem_labelShore _ _ _).mp
      rw [hfib]
      exact (mem_exceptionalPairPart G f _).mpr ((G.incident_iff f _).mpr (Or.inl rfl))
    have hsecond : twoPairAssignedLabel G M U₀ U₁ Z e₀ (G.secondEnd f) = k := by
      apply mem_singleton.mp
      apply (mem_labelShore _ _ _).mp
      rw [hfib]
      exact (mem_exceptionalPairPart G f _).mpr ((G.incident_iff f _).mpr (Or.inr rfl))
    simp only [mem_joiningCopies, hfirst, hsecond, ne_eq, not_true_eq_false, not_false_eq_true]
  rcases mem_insert.mp heZ with heZ | heZ
  · exact heZ.symm ▸ hinternal f₀ 2 h2
  · exact (mem_singleton.mp heZ).symm ▸ hinternal f₁ 3 h3

/-- The exact original joining trace contains only the selected old-core
crossing.  The two exceptional copies retain their separate pair fibers. -/
theorem boundary_twoPair_joining_trace
    (hM : G.IsPerfectMatching M)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (e₀ e₁ : E) (he : e₀ ≠ e₁) (hpair : G.internalOn M Z = {e₀,e₁})
    (hZ : Z = exceptionalPairPart G e₀ ∪ exceptionalPairPart G e₁) (i : Fin r) :
    Q.boundary i ∩ joiningCopies G (twoPairAssignedLabel G M U₀ U₁ Z e₀) =
      paritySelection (G.cutOn (Q.parent i) U₀ ∩ G.cutOn (Q.parent i) U₁) := by
  ext e
  constructor
  · rintro heT
    obtain ⟨heB, heJ⟩ := mem_inter.mp heT
    rcases mem_union.mp heB with heZ | heX
    · exact (Q.exceptionalCopies_not_joining_twoPair hM h01 h0Z h1Z hcover
        e₀ e₁ he hpair hZ i heZ heJ).elim
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

/-- The full partner code, without a bound of two on the exceptional set,
fixes the parity and exact size of every selected old-core crossing trace. -/
theorem boundary_twoPair_joining_trace_card
    (hM : G.IsPerfectMatching M)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (e₀ e₁ : E) (he : e₀ ≠ e₁) (hpair : G.internalOn M Z = {e₀,e₁})
    (hZ : Z = exceptionalPairPart G e₀ ∪ exceptionalPairPart G e₁) (i : Fin r) :
    (Q.boundary i ∩ joiningCopies G (twoPairAssignedLabel G M U₀ U₁ Z e₀)).card =
      (corePart G M Z U₀).card % 2 := by
  rw [Q.boundary_twoPair_joining_trace hM h01 h0Z h1Z hcover e₀ e₁ he hpair hZ i,
    paritySelection_card, ← corePart_card_parity G (Q.perfect i) U₀ U₁ Z h01 h0Z h1Z hcover,
    (Q.assignedParts hM h01 h0Z h1Z hcover i).1]

/-- Taking the joining trace commutes with retaining the actual residual
copies. This identity holds for every label function. -/
theorem residualBoundary_joining_trace_eq_surviving {K : Type*} [DecidableEq K]
    (N : J → Finset E) (T : Finset J) (label : V → K) (i : Fin r) :
    Q.residualBoundary N T i ∩ joiningCopies (residualGraph G N T) label =
      survivingCopies (removedCopies N T) (Q.boundary i ∩ joiningCopies G label) := by
  ext e
  simp only [mem_inter, mem_residualBoundary, mem_joiningCopies, mem_survivingCopies]
  rfl

/-- Reserve avoidance preserves the exact original joining trace as an
image, including every parallel copy. -/
theorem residualBoundary_joining_trace_image {K : Type*} [DecidableEq K]
    (N : J → Finset E) (T : Finset J)
    (havoid : ∀ j ∈ T, Disjoint (N j) (removedCopies Q.boundary univ))
    (label : V → K) (i : Fin r) :
    (Q.residualBoundary N T i ∩ joiningCopies (residualGraph G N T) label).image
        Subtype.val = Q.boundary i ∩ joiningCopies G label := by
  rw [Q.residualBoundary_joining_trace_eq_surviving N T label i]
  exact survivingCopies_image _ _ ((Q.boundary_disjoint_removed N T havoid i).mono_left
    inter_subset_left)

/-- A reserve-avoiding residual keeps the parity-sized native joining
trace of every selected boundary. -/
theorem residualBoundary_twoPair_joining_trace_card
    (hM : G.IsPerfectMatching M)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (e₀ e₁ : E) (he : e₀ ≠ e₁) (hpair : G.internalOn M Z = {e₀,e₁})
    (hZ : Z = exceptionalPairPart G e₀ ∪ exceptionalPairPart G e₁)
    (N : J → Finset E) (T : Finset J)
    (havoid : ∀ j ∈ T, Disjoint (N j) (removedCopies Q.boundary univ)) (i : Fin r) :
    (Q.residualBoundary N T i ∩
      joiningCopies (residualGraph G N T) (twoPairAssignedLabel G M U₀ U₁ Z e₀)).card =
      (corePart G M Z U₀).card % 2 := by
  rw [Q.residualBoundary_joining_trace_eq_surviving,
    survivingCopies_card _ _ ((Q.boundary_disjoint_removed N T havoid i).mono_left
      inter_subset_left)]
  exact Q.boundary_twoPair_joining_trace_card hM h01 h0Z h1Z hcover e₀ e₁ he hpair hZ i

/-- Even assigned cores have exactly empty native joining traces at every
reserve index; the exceptional pair copies remain in the whole boundaries. -/
theorem residualBoundary_twoPair_joining_trace_empty
    (hM : G.IsPerfectMatching M)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (e₀ e₁ : E) (he : e₀ ≠ e₁) (hpair : G.internalOn M Z = {e₀,e₁})
    (hZ : Z = exceptionalPairPart G e₀ ∪ exceptionalPairPart G e₁)
    (heven : (corePart G M Z U₀).card % 2 = 0)
    (N : J → Finset E) (T : Finset J)
    (havoid : ∀ j ∈ T, Disjoint (N j) (removedCopies Q.boundary univ)) (i : Fin r) :
    Q.residualBoundary N T i ∩
      joiningCopies (residualGraph G N T) (twoPairAssignedLabel G M U₀ U₁ Z e₀) = ∅ := by
  apply card_eq_zero.mp
  rw [Q.residualBoundary_twoPair_joining_trace_card hM h01 h0Z h1Z hcover
    e₀ e₁ he hpair hZ N T havoid i, heven]

/-- Odd assigned cores give an injective family of actual residual
zero-one crossing copies. Each singleton is the complete joining trace of
the boundary with the same original reserve index. -/
theorem exists_twoPair_residual_joining_singletons
    (hM : G.IsPerfectMatching M)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (e₀ e₁ : E) (he : e₀ ≠ e₁) (hpair : G.internalOn M Z = {e₀,e₁})
    (hZ : Z = exceptionalPairPart G e₀ ∪ exceptionalPairPart G e₁)
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
    rw [Q.residualBoundary_twoPair_joining_trace_card hM h01 h0Z h1Z hcover
      e₀ e₁ he hpair hZ N T havoid i, hodd]
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
    rw [Q.boundary_twoPair_joining_trace hM h01 h0Z h1Z hcover e₀ e₁ he hpair hZ i] at hraw
    exact coreCrossing_twoPairAssignedLabel_pair G (hM.isMatching G) (Q.parent i)
      U₀ U₁ Z h01 h0Z h1Z e₀ (paritySelection_subset _ hraw)

end Overfull.NativeReserve.PartnerBoundaryPacking
