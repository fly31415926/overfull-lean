import Overfull.AssignedParts.Basic

/-!
# Exact selected cuts of matched-core parts

Every set below consists of actual original copies of the specified matching.
The enlarged core cuts are exactly the copies selected between the two old
cores, and the exceptional pair support has no selected crossing copy.
The parity formula uses this concrete crossing-copy count. It does not identify
that count with a separate heavy-pattern code or construct an edge reserve.
-/

noncomputable section

namespace Overfull.AssignedParts

open Finset Classical
open scoped BigOperators

variable {V E : Type*} (G : Multigraph V E)

private theorem prop_ne_iff_xor (p q : Prop) :
    p ≠ q ↔ (p ∧ ¬ q) ∨ (¬ p ∧ q) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

/-- A small propositional kernel, isolated from the graph context. -/
private theorem assigned_cut_iff_core_crossing (a b z c d w : Prop)
    (hacover : a ∨ b ∨ z) (hccover : c ∨ d ∨ w)
    (hab : ¬ (a ∧ b)) (haz : ¬ (a ∧ z)) (hbz : ¬ (b ∧ z))
    (hcd : ¬ (c ∧ d)) (hcw : ¬ (c ∧ w)) (hdw : ¬ (d ∧ w)) :
    ((a ∨ (z ∧ c)) ≠ (c ∨ (w ∧ a))) ↔ (a ≠ c) ∧ (b ≠ d) := by
  simp only [prop_ne_iff_xor]
  tauto

/-- On a selected copy, a first endpoint is assigned using that same copy. -/
theorem firstEnd_mem_corePart_iff {M : Finset E} (hM : G.IsMatching M)
    (Z U : Finset V) {e : E} (he : e ∈ M) :
    G.firstEnd e ∈ corePart G M Z U ↔
      G.firstEnd e ∈ U ∨ (G.firstEnd e ∈ Z ∧ G.secondEnd e ∈ U) := by
  have hinc : G.firstEnd e ∈ G.edge e := (G.incident_iff e _).mpr (Or.inl rfl)
  have hother : G.otherEnd (G.firstEnd e) e = G.secondEnd e := by
    simp [Multigraph.otherEnd]
  rw [mem_corePart]
  constructor
  · rintro (hU | ⟨hZ, f, hf, hif, hof⟩)
    · exact Or.inl hU
    · have hef : e = f := hM e he f hf _ hinc hif
      subst f
      exact Or.inr ⟨hZ, hother ▸ hof⟩
  · rintro (hU | ⟨hZ, hU⟩)
    · exact Or.inl hU
    · exact Or.inr ⟨hZ, e, he, hinc, hother.symm ▸ hU⟩

/-- On a selected copy, a second endpoint is assigned using that same copy. -/
theorem secondEnd_mem_corePart_iff {M : Finset E} (hM : G.IsMatching M)
    (Z U : Finset V) {e : E} (he : e ∈ M) :
    G.secondEnd e ∈ corePart G M Z U ↔
      G.secondEnd e ∈ U ∨ (G.secondEnd e ∈ Z ∧ G.firstEnd e ∈ U) := by
  have hinc : G.secondEnd e ∈ G.edge e := (G.incident_iff e _).mpr (Or.inr rfl)
  have hother : G.otherEnd (G.secondEnd e) e = G.firstEnd e := by
    simp [Multigraph.otherEnd, G.endpoints_distinct e]
  rw [mem_corePart]
  constructor
  · rintro (hU | ⟨hZ, f, hf, hif, hof⟩)
    · exact Or.inl hU
    · have hef : e = f := hM e he f hf _ hinc hif
      subst f
      exact Or.inr ⟨hZ, hother ▸ hof⟩
  · rintro (hU | ⟨hZ, hU⟩)
    · exact Or.inl hU
    · exact Or.inr ⟨hZ, e, he, hinc, hother.symm ▸ hU⟩

/-- Every selected edge touching the exceptional pair support stays inside it. -/
theorem pairPart_cutOn_eq_empty {M : Finset E} (hM : G.IsMatching M)
    (Z : Finset V) : G.cutOn M (pairPart G M Z) = ∅ := by
  apply eq_empty_iff_forall_not_mem.mpr
  intro e hecut
  obtain ⟨he, hcross⟩ := (G.mem_cutOn _ _ e).mp hecut
  have hfirst : G.firstEnd e ∈ G.edge e := (G.incident_iff e _).mpr (Or.inl rfl)
  have hsecond : G.secondEnd e ∈ G.edge e := (G.incident_iff e _).mpr (Or.inr rfl)
  apply hcross
  apply propext
  constructor
  · intro hv
    obtain ⟨f, hf, hif⟩ := (G.mem_edgeSupport _ _).mp hv
    have hef : e = f := hM e he f (mem_filter.mp hf).1 _ hfirst hif
    subst f
    exact (G.mem_edgeSupport _ _).mpr ⟨e, hf, hsecond⟩
  · intro hv
    obtain ⟨f, hf, hif⟩ := (G.mem_edgeSupport _ _).mp hv
    have hef : e = f := hM e he f (mem_filter.mp hf).1 _ hsecond hif
    subst f
    exact (G.mem_edgeSupport _ _).mpr ⟨e, hf, hfirst⟩

/-- The assigned core cut retains exactly the original selected copies between
old cores; exceptional-to-core and exceptional-pair copies become internal. -/
theorem corePart_cutOn_eq_core_crossings {M : Finset E} (hM : G.IsMatching M)
    (U₀ U₁ Z : Finset V) (h01 : Disjoint U₀ U₁)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) :
    G.cutOn M (corePart G M Z U₀) = G.cutOn M U₀ ∩ G.cutOn M U₁ := by
  ext e
  by_cases he : e ∈ M
  · simp only [Multigraph.mem_cutOn, mem_inter, he, true_and]
    rw [firstEnd_mem_corePart_iff G hM Z U₀ he,
      secondEnd_mem_corePart_iff G hM Z U₀ he]
    exact assigned_cut_iff_core_crossing _ _ _ _ _ _
      (hcover (G.firstEnd e)) (hcover (G.secondEnd e))
      (fun h => disjoint_left.mp h01 h.1 h.2)
      (fun h => disjoint_left.mp h0Z h.1 h.2)
      (fun h => disjoint_left.mp h1Z h.1 h.2)
      (fun h => disjoint_left.mp h01 h.1 h.2)
      (fun h => disjoint_left.mp h0Z h.1 h.2)
      (fun h => disjoint_left.mp h1Z h.1 h.2)
  · simp [Multigraph.mem_cutOn, he]

/-- Both assigned core cuts are the same set of actual selected copies. -/
theorem coreParts_cutOn_eq {M : Finset E} (hM : G.IsMatching M)
    (U₀ U₁ Z : Finset V) (h01 : Disjoint U₀ U₁)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) :
    G.cutOn M (corePart G M Z U₀) = G.cutOn M (corePart G M Z U₁) := by
  have hcover' : ∀ v, v ∈ U₁ ∨ v ∈ U₀ ∨ v ∈ Z := by
    intro v
    rcases hcover v with h0 | h1 | hZ
    · exact Or.inr (Or.inl h0)
    · exact Or.inl h1
    · exact Or.inr (Or.inr hZ)
  rw [corePart_cutOn_eq_core_crossings G hM U₀ U₁ Z h01 h0Z h1Z hcover,
    corePart_cutOn_eq_core_crossings G hM U₁ U₀ Z h01.symm h1Z h0Z hcover']
  exact inter_comm _ _

/-- The exact selected degree-sum identity gives cardinality/cut parity. -/
theorem perfectMatching_shore_card_parity {M : Finset E} (hM : G.IsPerfectMatching M)
    (A : Finset V) : A.card % 2 = (G.cutOn M A).card % 2 := by
  have hsum : (∑ v ∈ A, G.degreeOn M v) = A.card := by
    calc
      _ = ∑ _v ∈ A, 1 := sum_congr rfl (fun v _ => hM v)
      _ = _ := by simp
  have h := G.degreeOn_sum_on M A
  omega

/-- The assigned core parity is the parity of the concrete old-core crossing count. -/
theorem corePart_card_parity {M : Finset E} (hM : G.IsPerfectMatching M)
    (U₀ U₁ Z : Finset V) (h01 : Disjoint U₀ U₁)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) :
    (corePart G M Z U₀).card % 2 = (G.cutOn M U₀ ∩ G.cutOn M U₁).card % 2 := by
  rw [perfectMatching_shore_card_parity G hM,
    corePart_cutOn_eq_core_crossings G (hM.isMatching G) U₀ U₁ Z h01 h0Z h1Z hcover]

/-- The parity profile of the actual assigned label map uses precisely the
number of selected original copies crossing between the two original cores. -/
theorem assignedLabel_parity_eq_core_crossing [Fintype V]
    {M : Finset E} (hM : G.IsPerfectMatching M)
    (U₀ U₁ Z : Finset V) (h01 : Disjoint U₀ U₁)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) :
    ∀ i, (univ.filter (fun v => assignedLabel G M U₀ U₁ Z v = i)).card % 2 =
      if i = 0 ∨ i = 1 then (G.cutOn M U₀ ∩ G.cutOn M U₁).card % 2 else 0 := by
  have hfibers := assignedLabel_fibers G hM U₀ U₁ Z h01 h0Z h1Z hcover
  have hp0 := corePart_card_parity G hM U₀ U₁ Z h01 h0Z h1Z hcover
  have hp1 : (corePart G M Z U₁).card % 2 =
      (G.cutOn M U₀ ∩ G.cutOn M U₁).card % 2 := by
    rw [perfectMatching_shore_card_parity G hM,
      ← coreParts_cutOn_eq G (hM.isMatching G) U₀ U₁ Z h01 h0Z h1Z hcover]
    rw [corePart_cutOn_eq_core_crossings G (hM.isMatching G) U₀ U₁ Z h01 h0Z h1Z hcover]
  have hp2 := Nat.even_iff.mp (pairPart_card_even G (hM.isMatching G) Z)
  intro i
  fin_cases i
  · simpa [hfibers.1] using hp0
  · simpa [hfibers.2.1] using hp1
  · simpa [hfibers.2.2] using hp2

end Overfull.AssignedParts
