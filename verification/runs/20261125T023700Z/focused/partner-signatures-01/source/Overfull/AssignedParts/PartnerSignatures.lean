import Overfull.AssignedParts.Signatures
import Overfull.AssignedParts.BoundaryCompression

/-!
# Assignment codes that retain every exceptional partner

The code records either a core assignment or the actual exceptional partner
of each exceptional vertex. Parallel copies give the same partner code, but
two different exceptional pairs are not collapsed into one optional flag.
The semantic results have no upper bound on the exceptional set.
-/

noncomputable section

namespace Overfull.AssignedParts

open Finset Classical

variable {V E : Type*} (G : Multigraph V E)

/-- The opposite endpoint of the selected matching copy, when it exists. -/
def matchingPartner (M : Finset E) (v : V) : V :=
  if h : ∃ e ∈ M, v ∈ G.edge e then
    G.otherEnd v (Classical.choose h)
  else v

/-- Matching uniqueness makes the selected partner independent of the choice. -/
theorem matchingPartner_eq_of_mem {M : Finset E} (hM : G.IsMatching M)
    {e : E} (he : e ∈ M) {v : V} (hve : v ∈ G.edge e) :
    matchingPartner G M v = G.otherEnd v e := by
  have hex : ∃ f ∈ M, v ∈ G.edge f := ⟨e, he, hve⟩
  rw [matchingPartner, dif_pos hex]
  exact congrArg (G.otherEnd v)
    (hM _ (Classical.choose_spec hex).1 e he v (Classical.choose_spec hex).2 hve)

/-- Each exception records one of two cores or one of the actual exceptions. -/
abbrev PartnerSignature (Z : Finset V) := ↥Z → (Fin 2 ⊕ ↥Z)

def partnerSignature (M : Finset E) (U₀ Z : Finset V) : PartnerSignature Z :=
  fun z => if h : matchingPartner G M z.val ∈ Z then
    Sum.inr ⟨matchingPartner G M z.val, h⟩
  else Sum.inl (assignmentChoice G M U₀ Z z)

theorem partnerSignature_pair_iff (M : Finset E) (U₀ Z : Finset V) (z w : ↥Z) :
    partnerSignature G M U₀ Z z = Sum.inr w ↔
      matchingPartner G M z.val = w.val := by
  unfold partnerSignature
  split_ifs with hp
  · simp only [Sum.inr.injEq, Subtype.mk.injEq]
  · simp only [Sum.inl_ne_inr, false_iff]
    intro heq
    exact hp (heq.symm ▸ w.property)

theorem partnerSignature_core_iff (M : Finset E) (U₀ Z : Finset V)
    (z : ↥Z) (i : Fin 2) :
    partnerSignature G M U₀ Z z = Sum.inl i ↔
      matchingPartner G M z.val ∉ Z ∧ assignmentChoice G M U₀ Z z = i := by
  unfold partnerSignature
  split_ifs with hp <;> simp [hp]

/-- The code detects membership in the full exceptional pair support. -/
theorem partner_mem_iff_pairPart {M : Finset E} (hM : G.IsPerfectMatching M)
    (Z : Finset V) (z : ↥Z) :
    matchingPartner G M z.val ∈ Z ↔ z.val ∈ pairPart G M Z := by
  obtain ⟨e, he, hze⟩ := (G.isPerfectMatching_iff.mp hM).2 z.val
  rw [matchingPartner_eq_of_mem G (hM.isMatching G) he hze]
  constructor
  · intro ho
    exact (G.mem_edgeSupport _ z.val).mpr
      ⟨e, G.mem_internalOn_of_incident_otherEnd he hze z.property ho, hze⟩
  · intro hz
    obtain ⟨f, hf, hzf⟩ := (G.mem_edgeSupport _ z.val).mp hz
    have hef := (hM.isMatching G) e he f (mem_filter.mp hf).1 z.val hze hzf
    subst f
    exact G.otherEnd_mem_of_mem_internalOn hf z.val

theorem partnerSignature_paired_iff {M : Finset E} (hM : G.IsPerfectMatching M)
    (U₀ Z : Finset V) (z : ↥Z) :
    (∃ w : ↥Z, partnerSignature G M U₀ Z z = Sum.inr w) ↔
      z.val ∈ pairPart G M Z := by
  rw [← partner_mem_iff_pairPart G hM Z z]
  constructor
  · rintro ⟨w, hw⟩
    exact (partnerSignature_pair_iff G M U₀ Z z w).mp hw ▸ w.property
  · intro hp
    exact ⟨⟨_, hp⟩, (partnerSignature_pair_iff G M U₀ Z z ⟨_, hp⟩).mpr rfl⟩

/-- A core code has its literal assigned-core meaning even when other
exceptions form two or more separate matching pairs. -/
theorem partnerSignature_first_core_iff {M : Finset E}
    (hM : G.IsPerfectMatching M) (U₀ Z : Finset V) (h0Z : Disjoint U₀ Z)
    (z : ↥Z) :
    partnerSignature G M U₀ Z z = Sum.inl 0 ↔ z.val ∈ corePart G M Z U₀ := by
  rw [partnerSignature_core_iff]
  constructor
  · exact fun h => (assignmentChoice_eq_zero_iff G M U₀ Z z).mp h.2
  · intro hz
    refine ⟨?_, (assignmentChoice_eq_zero_iff G M U₀ Z z).mpr hz⟩
    intro hp
    exact disjoint_left.mp (corePart_pairPart_disjoint G (hM.isMatching G) U₀ Z h0Z)
      hz ((partner_mem_iff_pairPart G hM Z z).mp hp)

theorem pairPart_eq_of_partnerSignature_eq {M N : Finset E}
    (hM : G.IsPerfectMatching M) (hN : G.IsPerfectMatching N)
    (U₀ Z : Finset V)
    (hcode : partnerSignature G M U₀ Z = partnerSignature G N U₀ Z) :
    pairPart G M Z = pairPart G N Z := by
  ext v
  by_cases hz : v ∈ Z
  · rw [← partnerSignature_paired_iff G hM U₀ Z ⟨v, hz⟩,
      ← partnerSignature_paired_iff G hN U₀ Z ⟨v, hz⟩, hcode]
  · have hm : v ∉ pairPart G M Z := fun hv => hz (pairPart_subset G M Z hv)
    have hn : v ∉ pairPart G N Z := fun hv => hz (pairPart_subset G N Z hv)
    simp [hm, hn]

theorem firstCorePart_eq_of_partnerSignature_eq {M N : Finset E}
    (hM : G.IsPerfectMatching M) (hN : G.IsPerfectMatching N)
    (U₀ Z : Finset V) (h0Z : Disjoint U₀ Z)
    (hcode : partnerSignature G M U₀ Z = partnerSignature G N U₀ Z) :
    corePart G M Z U₀ = corePart G N Z U₀ := by
  ext v
  by_cases hz : v ∈ Z
  · rw [← partnerSignature_first_core_iff G hM U₀ Z h0Z ⟨v, hz⟩,
      ← partnerSignature_first_core_iff G hN U₀ Z h0Z ⟨v, hz⟩, hcode]
  · simp [mem_corePart, hz]

/-- Equal partner codes recover both assigned cores and the paired support. -/
theorem assignedParts_eq_of_partnerSignature_eq {M N : Finset E}
    (hM : G.IsPerfectMatching M) (hN : G.IsPerfectMatching N)
    (U₀ U₁ Z : Finset V) (h01 : Disjoint U₀ U₁)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (hcode : partnerSignature G M U₀ Z = partnerSignature G N U₀ Z) :
    corePart G M Z U₀ = corePart G N Z U₀ ∧
      corePart G M Z U₁ = corePart G N Z U₁ ∧ pairPart G M Z = pairPart G N Z := by
  have hfirst := firstCorePart_eq_of_partnerSignature_eq G hM hN U₀ Z h0Z hcode
  have hpair := pairPart_eq_of_partnerSignature_eq G hM hN U₀ Z hcode
  exact ⟨hfirst, secondCorePart_eq_of_other_parts_eq G hM hN U₀ U₁ Z
    h01 h0Z h1Z hcover hfirst hpair, hpair⟩

/-- Each internal matching copy has a parallel actual copy in every
matching with the same partner code. No edge multiplicities are collapsed. -/
theorem exists_parallel_of_partnerSignature_eq {M N : Finset E}
    (hM : G.IsPerfectMatching M) (hN : G.IsPerfectMatching N)
    (U₀ Z : Finset V)
    (hcode : partnerSignature G M U₀ Z = partnerSignature G N U₀ Z)
    {e : E} (he : e ∈ G.internalOn M Z) :
    ∃ f ∈ G.internalOn N Z, G.edge f = G.edge e := by
  have hends := (mem_filter.mp he).2
  let z : ↥Z := ⟨G.firstEnd e, hends.1⟩
  let w : ↥Z := ⟨G.secondEnd e, hends.2⟩
  have hze : z.val ∈ G.edge e := (G.incident_iff e _).mpr (Or.inl rfl)
  have hpartnerM : matchingPartner G M z.val = w.val := by
    rw [matchingPartner_eq_of_mem G (hM.isMatching G) (mem_filter.mp he).1 hze]
    exact G.otherEnd_eq_of_edge e z.val w.val (G.edge_eq e)
  have hpartnerN : matchingPartner G N z.val = w.val := by
    apply (partnerSignature_pair_iff G N U₀ Z z w).mp
    rw [← hcode]
    exact (partnerSignature_pair_iff G M U₀ Z z w).mpr hpartnerM
  obtain ⟨f, hf, hzf⟩ := (G.isPerfectMatching_iff.mp hN).2 z.val
  rw [matchingPartner_eq_of_mem G (hN.isMatching G) hf hzf] at hpartnerN
  refine ⟨f, G.mem_internalOn_of_incident_otherEnd hf hzf z.property
    (hpartnerN.symm ▸ w.property), ?_⟩
  rw [G.edge_eq_otherEnd z.val f hzf, hpartnerN]
  exact (G.edge_eq e).symm

/-- The code space is finite even when unrealizable partner functions are included. -/
theorem card_partnerSignature (Z : Finset V) :
    Fintype.card (PartnerSignature Z) = (2 + Z.card) ^ Z.card := by
  simp [PartnerSignature]

theorem card_partnerSignature_le_seven_pow_five (Z : Finset V) (hZ : Z.card ≤ 5) :
    Fintype.card (PartnerSignature Z) ≤ 7 ^ 5 := by
  rw [card_partnerSignature]
  exact (Nat.pow_le_pow_left (by omega : 2 + Z.card ≤ 7)).trans
    (Nat.pow_le_pow_right (by omega) hZ)

end Overfull.AssignedParts
