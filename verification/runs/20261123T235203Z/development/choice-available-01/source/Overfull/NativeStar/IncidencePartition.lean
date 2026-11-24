import Overfull.AssignedParts.SignaturePools
import Overfull.ResidualPalette.JoiningBounds
import Overfull.ExceptionalPalette.PairFree

/-!
# Exact assigned-star incidence partitions

At an unpaired exception, every actual residual incidence is either a
joining copy, a copy to its assigned original core, or a copy to another
exception with the same assigned label. These pools are disjoint. The
assignment comes from the original representative; the incidence host
may have a different actual edge type. No multiplicity bound is imposed
on copies between two exceptional vertices.
-/

noncomputable section

namespace Overfull.NativeStar

open Finset Classical AssignedParts FourOdd NativeReserve

variable {V E K : Type*} [Fintype E] [DecidableEq K]

/-- Joining copies actually incident with the indicated vertex. -/
def joiningIncidenceCopies (H : Multigraph V E) (label : V → K) (z : V) : Finset E :=
  H.incidenceEdges z ∩ joiningCopies H label

/-- Exceptional incidences internal to the fixed assigned label. -/
def exceptionInternalPool (H : Multigraph V E) (label : V → K)
    (Z : Finset V) (z : V) : Finset E :=
  (H.incidenceEdges z).filter (fun e =>
    H.otherEnd z e ∈ Z ∧ label (H.otherEnd z e) = label z)

@[simp] theorem mem_joiningIncidenceCopies (H : Multigraph V E) (label : V → K)
    (z : V) (e : E) :
    e ∈ joiningIncidenceCopies H label z ↔ z ∈ H.edge e ∧ e ∈ joiningCopies H label := by
  simp [joiningIncidenceCopies]

@[simp] theorem mem_exceptionInternalPool (H : Multigraph V E) (label : V → K)
    (Z : Finset V) (z : V) (e : E) :
    e ∈ exceptionInternalPool H label Z z ↔ z ∈ H.edge e ∧
      H.otherEnd z e ∈ Z ∧ label (H.otherEnd z e) = label z := by
  simp [exceptionInternalPool]

/-- Joining at an incident vertex is exactly a label change at its other end. -/
theorem joining_iff_otherEnd_label_ne (H : Multigraph V E) (label : V → K)
    (z : V) (e : E) (hz : z ∈ H.edge e) :
    e ∈ joiningCopies H label ↔ label (H.otherEnd z e) ≠ label z := by
  rcases (H.incident_iff e z).mp hz with hf | hs
  · simp [mem_joiningCopies, Multigraph.otherEnd, hf, ne_comm]
  · have hf : H.firstEnd e ≠ z := by
      intro hh
      exact H.endpoints_distinct e (hh.trans hs.symm)
    simp [mem_joiningCopies, Multigraph.otherEnd, hf, hs]

/-- The joining incidence pool has its actual degree-on cardinality. -/
theorem joiningIncidenceCopies_card (H : Multigraph V E) (label : V → K) (z : V) :
    (joiningIncidenceCopies H label z).card = H.degreeOn (joiningCopies H label) z := by
  unfold joiningIncidenceCopies Multigraph.degreeOn
  congr 1
  ext e
  simp only [mem_inter, Multigraph.mem_incidenceEdges, mem_filter]
  exact and_comm

/-- Assigned-core star copies are disjoint from joining incidences. -/
theorem joiningIncidence_disjoint_star (H : Multigraph V E) (label : V → K)
    (z : V) (U : Finset V) (hlabel : ∀ v ∈ U, label v = label z) :
    Disjoint (joiningIncidenceCopies H label z) (exceptionCorePool H z U) := by
  apply disjoint_left.mpr
  intro e heJ heS
  obtain ⟨hz,hj⟩ := (mem_joiningIncidenceCopies H label z e).mp heJ
  have hU := (mem_filter.mp heS).2.2
  exact (joining_iff_otherEnd_label_ne H label z e hz).mp hj (hlabel _ hU)

/-- An internal exceptional incidence cannot be a joining incidence. -/
theorem joiningIncidence_disjoint_internal (H : Multigraph V E) (label : V → K)
    (Z : Finset V) (z : V) :
    Disjoint (joiningIncidenceCopies H label z) (exceptionInternalPool H label Z z) := by
  apply disjoint_left.mpr
  intro e heJ heI
  obtain ⟨hz,hj⟩ := (mem_joiningIncidenceCopies H label z e).mp heJ
  exact (joining_iff_otherEnd_label_ne H label z e hz).mp hj
    ((mem_exceptionInternalPool H label Z z e).mp heI).2.2

/-- The old core and the exceptional set separate the other endpoints of
the two nonjoining incidence pools. -/
theorem star_disjoint_internal (H : Multigraph V E) (label : V → K)
    (Z U : Finset V) (z : V) (hUZ : Disjoint U Z) :
    Disjoint (exceptionCorePool H z U) (exceptionInternalPool H label Z z) := by
  apply disjoint_left.mpr
  intro e heS heI
  exact disjoint_left.mp hUZ (mem_filter.mp heS).2.2
    ((mem_exceptionInternalPool H label Z z e).mp heI).2.1

/-- If the assigned fiber lies in the old core and exceptions, the three
actual pools partition every incidence at the exception. -/
theorem incidence_partition (H : Multigraph V E) (label : V → K)
    (Z U : Finset V) (z : V) (hUZ : Disjoint U Z)
    (hlabel : ∀ v ∈ U, label v = label z)
    (hfiber : ∀ v, label v = label z → v ∈ U ∨ v ∈ Z) :
    Disjoint (joiningIncidenceCopies H label z) (exceptionCorePool H z U) ∧
      Disjoint (joiningIncidenceCopies H label z) (exceptionInternalPool H label Z z) ∧
      Disjoint (exceptionCorePool H z U) (exceptionInternalPool H label Z z) ∧
      joiningIncidenceCopies H label z ∪ exceptionCorePool H z U ∪
        exceptionInternalPool H label Z z = H.incidenceEdges z := by
  refine ⟨joiningIncidence_disjoint_star H label z U hlabel,
    joiningIncidence_disjoint_internal H label Z z,
    star_disjoint_internal H label Z U z hUZ, ?_⟩
  ext e
  constructor
  · intro he
    apply (H.mem_incidenceEdges z e).mpr
    rcases mem_union.mp he with he | he
    · rcases mem_union.mp he with he | he
      · exact ((mem_joiningIncidenceCopies H label z e).mp he).1
      · exact (mem_filter.mp he).2.1
    · exact ((mem_exceptionInternalPool H label Z z e).mp he).1
  · intro he
    have hz := (H.mem_incidenceEdges z e).mp he
    by_cases hj : e ∈ joiningCopies H label
    · exact mem_union_left _ (mem_union_left _
        ((mem_joiningIncidenceCopies H label z e).mpr ⟨hz,hj⟩))
    · have heq : label (H.otherEnd z e) = label z := by
        by_contra hn
        exact hj ((joining_iff_otherEnd_label_ne H label z e hz).mpr hn)
      rcases hfiber (H.otherEnd z e) heq with hU | hZ
      · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨mem_univ _,hz,hU⟩))
      · exact mem_union_right _ ((mem_exceptionInternalPool H label Z z e).mpr
          ⟨hz,hZ,heq⟩)

/-- Exact degree accounting includes the whole internal exceptional bundle. -/
theorem incidence_degree_balance (H : Multigraph V E) (label : V → K)
    (Z U : Finset V) (z : V) (hUZ : Disjoint U Z)
    (hlabel : ∀ v ∈ U, label v = label z)
    (hfiber : ∀ v, label v = label z → v ∈ U ∨ v ∈ Z) :
    H.degreeOn (joiningCopies H label) z + (exceptionCorePool H z U).card +
      (exceptionInternalPool H label Z z).card = H.degree z := by
  obtain ⟨hJS,hJI,hSI,hunion⟩ := incidence_partition H label Z U z hUZ hlabel hfiber
  have hJI' : Disjoint (joiningIncidenceCopies H label z ∪ exceptionCorePool H z U)
      (exceptionInternalPool H label Z z) := disjoint_union_left.mpr ⟨hJI,hSI⟩
  have hc := congrArg Finset.card hunion
  rw [card_union_of_disjoint hJI',card_union_of_disjoint hJS,
    joiningIncidenceCopies_card] at hc
  exact hc

/-- A supply of `r` distinct actual assigned-star copies bounds the combined
joining and internal-exceptional incidence, before natural subtraction. -/
theorem off_core_degree_add_reserve_le (H : Multigraph V E) (label : V → K)
    (Z U : Finset V) (z : V) (hUZ : Disjoint U Z)
    (hlabel : ∀ v ∈ U, label v = label z)
    (hfiber : ∀ v, label v = label z → v ∈ U ∨ v ∈ Z)
    (r : ℕ) (hreserve : r ≤ (exceptionCorePool H z U).card) :
    H.degreeOn (joiningCopies H label) z +
      (exceptionInternalPool H label Z z).card + r ≤ H.degree z := by
  have hb := incidence_degree_balance H label Z U z hUZ hlabel hfiber
  omega

/-- In a two-exception set, the same-label internal pool is exactly the
actual mutual parallel-copy pool, even when the fiber also contains a core. -/
theorem exceptionInternalPool_pair_eq (H : Multigraph V E) (label : V → K)
    (x y : V) (hlabel : label x = label y) :
    exceptionInternalPool H label {x,y} x = pairFiberCopies H x y := by
  ext e
  constructor
  · intro he
    obtain ⟨hx,ho,_⟩ := (mem_exceptionInternalPool H label {x,y} x e).mp he
    have hother : H.otherEnd x e = y := by
      rcases mem_insert.mp ho with hh | hh
      · exact (H.otherEnd_ne x e hx hh).elim
      · exact mem_singleton.mp hh
    apply (mem_pairFiberCopies_iff H x y e).mpr
    rw [H.edge_eq_otherEnd x e hx,hother]
  · intro he
    have hedge := (mem_pairFiberCopies_iff H x y e).mp he
    have hx : x ∈ H.edge e := by rw [hedge]; simp
    have ho := H.otherEnd_eq_of_edge e x y hedge
    apply (mem_exceptionInternalPool H label {x,y} x e).mpr
    rw [ho]
    exact ⟨hx,mem_insert_of_mem (mem_singleton_self y),hlabel.symm⟩

/-- Exceptions assigned to different cores have no nonjoining mutual pool. -/
theorem exceptionInternalPool_pair_eq_empty (H : Multigraph V E) (label : V → K)
    (x y : V) (hlabel : label x ≠ label y) :
    exceptionInternalPool H label {x,y} x = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨hx,ho,heq⟩ := (mem_exceptionInternalPool H label {x,y} x e).mp he
  rcases mem_insert.mp ho with hh | hh
  · exact H.otherEnd_ne x e hx hh
  · rw [mem_singleton.mp hh] at heq
    exact hlabel heq.symm

variable {E₀ : Type*}

/-- An unpaired original signature supplies exactly the fiber facts needed
by incidence accounting in any later host on the same vertex type. -/
theorem unpaired_assignment_fiber_bounds (G : Multigraph V E₀) {M : Finset E₀}
    (hM : G.IsPerfectMatching M) (U₀ U₁ Z : Finset V)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (σ : ↥Z → Fin 2) (hcode : coarseSignature G M U₀ Z = some σ) (z : ↥Z) :
    Disjoint (if σ z = 0 then U₀ else U₁) Z ∧
      (∀ v ∈ (if σ z = 0 then U₀ else U₁),
        assignedLabel G M U₀ U₁ Z v = assignedLabel G M U₀ U₁ Z z.val) ∧
      (∀ v, assignedLabel G M U₀ U₁ Z v = assignedLabel G M U₀ U₁ Z z.val →
        v ∈ (if σ z = 0 then U₀ else U₁) ∨ v ∈ Z) := by
  obtain ⟨hinternal,hchoice⟩ := (coarseSignature_eq_some_iff G M U₀ Z σ).mp hcode
  by_cases hz0 : σ z = 0
  · simp only [if_pos hz0]
    have hzpart : z.val ∈ corePart G M Z U₀ := by
      apply (assignmentChoice_eq_zero_iff G M U₀ Z z).mp
      rw [hchoice,hz0]
    have hzl : assignedLabel G M U₀ U₁ Z z.val = 0 :=
      (labelOfThreeParts_eq_zero_iff _ _ _).mpr hzpart
    refine ⟨h0Z,?_,?_⟩
    · intro v hv
      rw [hzl]
      exact assignedLabel_on_core₀ G M U₀ U₁ Z hv
    · intro v hv
      rw [hzl] at hv
      have hp : v ∈ corePart G M Z U₀ := (labelOfThreeParts_eq_zero_iff _ _ _).mp hv
      rcases (mem_corePart G M Z U₀ v).mp hp with hU | ⟨hZ,_⟩
      · exact Or.inl hU
      · exact Or.inr hZ
  · simp only [if_neg hz0]
    have hznot : z.val ∉ corePart G M Z U₀ := by
      intro hzpart
      have hc := (assignmentChoice_eq_zero_iff G M U₀ Z z).mpr hzpart
      rw [hchoice] at hc
      exact hz0 hc
    have hzpart : z.val ∈ corePart G M Z U₁ := by
      rcases coreParts_cover G hM U₀ U₁ Z hcover z.val with h0 | h1 | hp
      · exact (hznot h0).elim
      · exact h1
      · rw [pairPart_eq_empty_of_internal_eq_empty G M Z hinternal] at hp
        exact (notMem_empty _ hp).elim
    have hzl : assignedLabel G M U₀ U₁ Z z.val = 1 :=
      (labelOfThreeParts_eq_one_iff _ _ _).mpr ⟨hznot,hzpart⟩
    refine ⟨h1Z,?_,?_⟩
    · intro v hv
      rw [hzl]
      exact assignedLabel_on_core₁ G (hM.isMatching G) U₀ U₁ Z h01 h0Z h1Z hv
    · intro v hv
      rw [hzl] at hv
      have hp : v ∈ corePart G M Z U₁ := ((labelOfThreeParts_eq_one_iff _ _ _).mp hv).2
      rcases (mem_corePart G M Z U₁ v).mp hp with hU | ⟨hZ,_⟩
      · exact Or.inl hU
      · exact Or.inr hZ

/-- The original representative's unpaired assignment partitions actual
incidences in a possibly different residual host, retaining all edge copies. -/
theorem assigned_incidence_partition (G : Multigraph V E₀) (H : Multigraph V E)
    {M : Finset E₀} (hM : G.IsPerfectMatching M) (U₀ U₁ Z : Finset V)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (σ : ↥Z → Fin 2) (hcode : coarseSignature G M U₀ Z = some σ) (z : ↥Z) :
    let label := assignedLabel G M U₀ U₁ Z
    let U := if σ z = 0 then U₀ else U₁
    Disjoint (joiningIncidenceCopies H label z.val) (exceptionCorePool H z.val U) ∧
      Disjoint (joiningIncidenceCopies H label z.val) (exceptionInternalPool H label Z z.val) ∧
      Disjoint (exceptionCorePool H z.val U) (exceptionInternalPool H label Z z.val) ∧
      joiningIncidenceCopies H label z.val ∪ exceptionCorePool H z.val U ∪
        exceptionInternalPool H label Z z.val = H.incidenceEdges z.val := by
  obtain ⟨hd,hl,hf⟩ := unpaired_assignment_fiber_bounds G hM U₀ U₁ Z h01 h0Z h1Z
    hcover σ hcode z
  exact incidence_partition H _ Z _ z.val hd hl hf

/-- The exact native degree split includes all copies between same-assigned
exceptions, with no old-core multiplicity assumption on that bundle. -/
theorem assigned_degree_balance (G : Multigraph V E₀) (H : Multigraph V E)
    {M : Finset E₀} (hM : G.IsPerfectMatching M) (U₀ U₁ Z : Finset V)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (σ : ↥Z → Fin 2) (hcode : coarseSignature G M U₀ Z = some σ) (z : ↥Z) :
    H.degreeOn (joiningCopies H (assignedLabel G M U₀ U₁ Z)) z.val +
      (exceptionCorePool H z.val (if σ z = 0 then U₀ else U₁)).card +
      (exceptionInternalPool H (assignedLabel G M U₀ U₁ Z) Z z.val).card = H.degree z.val := by
  obtain ⟨hd,hl,hf⟩ := unpaired_assignment_fiber_bounds G hM U₀ U₁ Z h01 h0Z h1Z
    hcover σ hcode z
  exact incidence_degree_balance H _ Z _ z.val hd hl hf

/-- A distinct reserved supply in the actual assigned star pool gives the
combined off-core bound needed by the later free-palette balance. -/
theorem assigned_off_core_degree_bound (G : Multigraph V E₀) (H : Multigraph V E)
    {M : Finset E₀} (hM : G.IsPerfectMatching M) (U₀ U₁ Z : Finset V)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (σ : ↥Z → Fin 2) (hcode : coarseSignature G M U₀ Z = some σ) (z : ↥Z)
    (h r D : ℕ) (hdegree : H.degree z.val = h)
    (hreserve : r ≤ (exceptionCorePool H z.val (if σ z = 0 then U₀ else U₁)).card)
    (herror : h-r ≤ D) :
    H.degreeOn (joiningCopies H (assignedLabel G M U₀ U₁ Z)) z.val +
        (exceptionInternalPool H (assignedLabel G M U₀ U₁ Z) Z z.val).card ≤ h-r ∧
      H.degreeOn (joiningCopies H (assignedLabel G M U₀ U₁ Z)) z.val +
        (exceptionInternalPool H (assignedLabel G M U₀ U₁ Z) Z z.val).card ≤ D := by
  have hb := assigned_degree_balance G H hM U₀ U₁ Z h01 h0Z h1Z hcover σ hcode z
  rw [hdegree] at hb
  omega

end Overfull.NativeStar
