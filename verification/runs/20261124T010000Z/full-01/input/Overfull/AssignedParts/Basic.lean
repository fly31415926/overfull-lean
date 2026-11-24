import Overfull.CriticalMultigraph
import Overfull.CompatibleCircuits.Counting
import Overfull.AssignedParts.PairFiberParity
import Overfull.AssignedParts.ThreePartLabels

/-!
# Actual assigned parts for two cores and at most two exceptions

This supporting construction keeps every original edge copy and retains the
specified perfect-matching representative. It builds the assigned vertex parts;
it does not select a heavy boundary pattern or construct an edge reserve.

This source was recreated after the unpublished earlier draft was lost with
the transient workspace. Its current source receives fresh compiler checks.
-/

noncomputable section

namespace Overfull.Multigraph

open Finset Classical
open scoped BigOperators

variable {V E : Type*} (G : Multigraph V E)

/-- The support of a matching has exactly two vertices per actual copy. -/
theorem IsMatching.edgeSupport_card {M : Finset E} (hM : G.IsMatching M) :
    (G.edgeSupport M).card = 2 * M.card := by
  have hdegree (v : V) (hv : v ∈ G.edgeSupport M) : G.degreeOn M v = 1 := by
    have hlo := (G.degreeOn_pos_iff M v).mpr hv
    have hhi := (G.isMatching_iff_incident_card_le_one M).mp hM v
    change G.degreeOn M v ≤ 1 at hhi
    omega
  have h := G.degreeOn_sum M
  have hsum : (∑ v ∈ G.edgeSupport M, G.degreeOn M v) =
      (G.edgeSupport M).card := by
    calc
      _ = ∑ _v ∈ G.edgeSupport M, 1 := sum_congr rfl (fun v hv => hdegree v hv)
      _ = _ := by simp
  omega

/-- A perfect matching covers every vertex of the actual host. -/
theorem IsPerfectMatching.edgeSupport_eq_univ [Fintype V] {M : Finset E}
    (hM : G.IsPerfectMatching M) : G.edgeSupport M = univ := by
  ext v
  simp only [mem_edgeSupport, mem_univ, iff_true]
  exact (G.isPerfectMatching_iff.mp hM).2 v

/-- The order of a finite host with an actual perfect matching is even. -/
theorem IsPerfectMatching.even_card [Fintype V] {M : Finset E}
    (hM : G.IsPerfectMatching M) : Even (Fintype.card V) := by
  have h := (hM.isMatching G).edgeSupport_card G
  rw [hM.edgeSupport_eq_univ G, card_univ] at h
  rw [h]
  exact even_two_mul _

/-- A selected internal copy has its other endpoint in the same shore. -/
theorem otherEnd_mem_of_mem_internalOn {M : Finset E} {Z : Finset V}
    {e : E} (he : e ∈ G.internalOn M Z) (v : V) : G.otherEnd v e ∈ Z := by
  have hends := (mem_filter.mp he).2
  unfold otherEnd
  split_ifs
  · exact hends.2
  · exact hends.1

/-- A selected edge whose specified two endpoints lie in a shore is internal. -/
theorem mem_internalOn_of_incident_otherEnd {M : Finset E} {Z : Finset V}
    {e : E} (he : e ∈ M) {v : V} (hv : v ∈ G.edge e)
    (hvZ : v ∈ Z) (hoZ : G.otherEnd v e ∈ Z) : e ∈ G.internalOn M Z := by
  apply mem_filter.mpr
  refine ⟨he, ?_⟩
  have hends := (G.edge_eq e).trans (G.edge_eq_otherEnd v e hv)
  rcases Sym2.eq_iff.mp hends with ⟨hfirst, hsecond⟩ | ⟨hfirst, hsecond⟩
  · rw [hfirst, hsecond]
    exact ⟨hvZ, hoZ⟩
  · rw [hfirst, hsecond]
    exact ⟨hoZ, hvZ⟩

/-- Every endpoint of a selected internal copy belongs to its shore. -/
theorem edgeSupport_internalOn_subset (M : Finset E) (Z : Finset V) :
    G.edgeSupport (G.internalOn M Z) ⊆ Z := by
  intro v hv
  obtain ⟨e, he, hve⟩ := (G.mem_edgeSupport _ v).mp hv
  have hends := (mem_filter.mp he).2
  rcases (G.incident_iff e v).mp hve with h | h
  · exact h ▸ hends.1
  · exact h ▸ hends.2

/-- Restriction to actual internal copies preserves the matching property. -/
theorem IsMatching.internalOn {M : Finset E} (hM : G.IsMatching M) (Z : Finset V) :
    G.IsMatching (G.internalOn M Z) := by
  intro e he f hf v hev hfv
  exact hM e (mem_filter.mp he).1 f (mem_filter.mp hf).1 v hev hfv

end Overfull.Multigraph

namespace Overfull.AssignedParts

open Finset Classical

variable {V E : Type*} (G : Multigraph V E)

/-- Exceptional vertices whose selected matching edge goes to the indicated core. -/
def assignedExceptions (M : Finset E) (Z U : Finset V) : Finset V :=
  Z.filter (fun z => ∃ e ∈ M, z ∈ G.edge e ∧ G.otherEnd z e ∈ U)

/-- An original core together with its matched unpaired exceptional vertices. -/
def corePart (M : Finset E) (Z U : Finset V) : Finset V :=
  U ∪ assignedExceptions G M Z U

/-- Endpoints of the actual selected internal exceptional copies. -/
def pairPart (M : Finset E) (Z : Finset V) : Finset V :=
  G.edgeSupport (G.internalOn M Z)

@[simp] theorem mem_assignedExceptions (M : Finset E) (Z U : Finset V) (z : V) :
    z ∈ assignedExceptions G M Z U ↔
      z ∈ Z ∧ ∃ e ∈ M, z ∈ G.edge e ∧ G.otherEnd z e ∈ U := by
  simp [assignedExceptions]

@[simp] theorem mem_corePart (M : Finset E) (Z U : Finset V) (v : V) :
    v ∈ corePart G M Z U ↔
      v ∈ U ∨ (v ∈ Z ∧ ∃ e ∈ M, v ∈ G.edge e ∧ G.otherEnd v e ∈ U) := by
  simp [corePart]

theorem core_subset_corePart (M : Finset E) (Z U : Finset V) :
    U ⊆ corePart G M Z U := subset_union_left

theorem pairPart_subset (M : Finset E) (Z : Finset V) : pairPart G M Z ⊆ Z :=
  G.edgeSupport_internalOn_subset M Z

/-- Each exceptional pair contributes its two distinct original endpoints. -/
theorem pairPart_card {M : Finset E} (hM : G.IsMatching M) (Z : Finset V) :
    (pairPart G M Z).card = 2 * (G.internalOn M Z).card :=
  (hM.internalOn G Z).edgeSupport_card G

/-- At most two exceptions permit at most one actual internal matching copy. -/
theorem internalOn_card_le_one {M : Finset E} (hM : G.IsMatching M)
    (Z : Finset V) (hZ : Z.card ≤ 2) : (G.internalOn M Z).card ≤ 1 := by
  have h := card_le_card (pairPart_subset G M Z)
  rw [pairPart_card G hM Z] at h
  omega

/-- The optional pair part is empty or contains exactly two vertices. -/
theorem pairPart_card_eq_zero_or_two {M : Finset E} (hM : G.IsMatching M)
    (Z : Finset V) (hZ : Z.card ≤ 2) :
    (pairPart G M Z).card = 0 ∨ (pairPart G M Z).card = 2 := by
  have h := internalOn_card_le_one G hM Z hZ
  rw [pairPart_card G hM Z]
  omega

theorem pairPart_card_even {M : Finset E} (hM : G.IsMatching M) (Z : Finset V) :
    Even (pairPart G M Z).card := by
  rw [pairPart_card G hM Z]
  exact even_two_mul _

/-- The actual matched-core assignment cannot put one vertex in two core parts. -/
theorem coreParts_disjoint {M : Finset E} (hM : G.IsMatching M)
    (U₀ U₁ Z : Finset V) (h01 : Disjoint U₀ U₁)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z) :
    Disjoint (corePart G M Z U₀) (corePart G M Z U₁) := by
  apply disjoint_left.mpr
  intro v hv0 hv1
  rcases (mem_corePart G M Z U₀ v).mp hv0 with hv0 | ⟨hvZ, e, he, hve, hoe⟩
  · rcases (mem_corePart G M Z U₁ v).mp hv1 with hv1 | ⟨hvZ, _⟩
    · exact disjoint_left.mp h01 hv0 hv1
    · exact disjoint_left.mp h0Z hv0 hvZ
  · rcases (mem_corePart G M Z U₁ v).mp hv1 with hv1 | ⟨_, f, hf, hvf, hof⟩
    · exact disjoint_left.mp h1Z hv1 hvZ
    · have hef : e = f := hM e he f hf v hve hvf
      subst f
      exact disjoint_left.mp h01 hoe hof

/-- A vertex assigned into a core cannot also belong to an internal exceptional pair. -/
theorem corePart_pairPart_disjoint {M : Finset E} (hM : G.IsMatching M)
    (U Z : Finset V) (hUZ : Disjoint U Z) :
    Disjoint (corePart G M Z U) (pairPart G M Z) := by
  apply disjoint_left.mpr
  intro v hvA hvB
  rcases (mem_corePart G M Z U v).mp hvA with hvU | ⟨_, e, he, hve, hoe⟩
  · exact disjoint_left.mp hUZ hvU (pairPart_subset G M Z hvB)
  · obtain ⟨f, hf, hvf⟩ := (G.mem_edgeSupport _ v).mp hvB
    have hef : e = f := hM e he f (mem_filter.mp hf).1 v hve hvf
    subst f
    exact disjoint_left.mp hUZ hoe (G.otherEnd_mem_of_mem_internalOn hf v)

/-- Every original vertex lies in one matched core part or the optional pair part. -/
theorem coreParts_cover {M : Finset E} (hM : G.IsPerfectMatching M)
    (U₀ U₁ Z : Finset V)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (v : V) :
    v ∈ corePart G M Z U₀ ∨ v ∈ corePart G M Z U₁ ∨ v ∈ pairPart G M Z := by
  rcases hcover v with hv0 | hv1 | hvZ
  · exact Or.inl (core_subset_corePart G M Z U₀ hv0)
  · exact Or.inr (Or.inl (core_subset_corePart G M Z U₁ hv1))
  · obtain ⟨e, he, hve⟩ := (G.isPerfectMatching_iff.mp hM).2 v
    rcases hcover (G.otherEnd v e) with ho0 | ho1 | hoZ
    · exact Or.inl ((mem_corePart G M Z U₀ v).mpr
        (Or.inr ⟨hvZ, e, he, hve, ho0⟩))
    · exact Or.inr (Or.inl ((mem_corePart G M Z U₁ v).mpr
        (Or.inr ⟨hvZ, e, he, hve, ho1⟩)))
    · exact Or.inr (Or.inr ((G.mem_edgeSupport _ v).mpr
        ⟨e, G.mem_internalOn_of_incident_otherEnd he hve hvZ hoZ, hve⟩))

/-- At an exceptional vertex, membership in a core part records an actual
selected copy to that same original core. -/
theorem exceptional_corePart_iff (M : Finset E) (U Z : Finset V)
    (hUZ : Disjoint U Z) {z : V} (hz : z ∈ Z) :
    z ∈ corePart G M Z U ↔ ∃ e ∈ M, z ∈ G.edge e ∧ G.otherEnd z e ∈ U := by
  have hzU : z ∉ U := fun h => disjoint_left.mp hUZ h hz
  simp [mem_corePart, hz, hzU]

/-- Every unpaired exception is assigned to one of the two actual original cores. -/
theorem unpaired_exception_represented {M : Finset E} (hM : G.IsPerfectMatching M)
    (U₀ U₁ Z : Finset V) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    {z : V} (hz : z ∈ Z) (hnpair : z ∉ pairPart G M Z) :
    (∃ e ∈ M, z ∈ G.edge e ∧ G.otherEnd z e ∈ U₀) ∨
      (∃ e ∈ M, z ∈ G.edge e ∧ G.otherEnd z e ∈ U₁) := by
  rcases coreParts_cover G hM U₀ U₁ Z hcover z with h0 | h1 | hp
  · exact Or.inl ((exceptional_corePart_iff G M U₀ Z h0Z hz).mp h0)
  · exact Or.inr ((exceptional_corePart_iff G M U₁ Z h1Z hz).mp h1)
  · exact (hnpair hp).elim

/-- The two assigned core parts receive labels zero and one; the optional
exceptional pair is the third part. -/
def assignedLabel (M : Finset E) (U₀ U₁ Z : Finset V) : V → Fin 3 :=
  labelOfThreeParts (corePart G M Z U₀) (corePart G M Z U₁)

variable [Fintype V]

/-- The constructed labels have exactly the actual assigned vertex fibers. -/
theorem assignedLabel_fibers {M : Finset E} (hM : G.IsPerfectMatching M)
    (U₀ U₁ Z : Finset V) (h01 : Disjoint U₀ U₁)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) :
    (univ.filter (fun v => assignedLabel G M U₀ U₁ Z v = 0) = corePart G M Z U₀) ∧
      (univ.filter (fun v => assignedLabel G M U₀ U₁ Z v = 1) = corePart G M Z U₁) ∧
      (univ.filter (fun v => assignedLabel G M U₀ U₁ Z v = 2) = pairPart G M Z) := by
  exact labelOfThreeParts_fibers _ _ _
    (coreParts_disjoint G (hM.isMatching G) U₀ U₁ Z h01 h0Z h1Z)
    (corePart_pairPart_disjoint G (hM.isMatching G) U₀ Z h0Z)
    (corePart_pairPart_disjoint G (hM.isMatching G) U₁ Z h1Z)
    (coreParts_cover G hM U₀ U₁ Z hcover)

/-- The supplied actual perfect-matching representative determines the two
parity alternatives without assuming the parities of the assigned parts. -/
theorem assignedLabel_parity {M : Finset E} (hM : G.IsPerfectMatching M)
    (U₀ U₁ Z : Finset V) (h01 : Disjoint U₀ U₁)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) :
    (∀ i, (univ.filter (fun v => assignedLabel G M U₀ U₁ Z v = i)).card % 2 = 0) ∨
      (∀ i, (univ.filter (fun v => assignedLabel G M U₀ U₁ Z v = i)).card % 2 =
        if i = 0 ∨ i = 1 then 1 else 0) := by
  apply fiber_parity_cases_of_even_total_and_pair _ (hM.even_card G)
  rw [(assignedLabel_fibers G hM U₀ U₁ Z h01 h0Z h1Z hcover).2.2]
  exact pairPart_card_even G (hM.isMatching G) Z

/-- A matching-based construction of the exact source assignment on at most
three labels. The core and exception partition is supplied; reserve selection
and all residual incidence estimates remain separate obligations. -/
theorem exists_two_core_assigned_labels {M : Finset E} (hM : G.IsPerfectMatching M)
    (U₀ U₁ Z : Finset V) (h01 : Disjoint U₀ U₁)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2) :
    ∃ label : V → Fin 3,
      (univ.filter (fun v => label v = 0) = corePart G M Z U₀) ∧
      (univ.filter (fun v => label v = 1) = corePart G M Z U₁) ∧
      (univ.filter (fun v => label v = 2) = pairPart G M Z) ∧
      (G.internalOn M Z).card ≤ 1 ∧
      ((univ.filter (fun v => label v = 2)).card = 0 ∨
        (univ.filter (fun v => label v = 2)).card = 2) ∧
      ((∀ i, (univ.filter (fun v => label v = i)).card % 2 = 0) ∨
        (∀ i, (univ.filter (fun v => label v = i)).card % 2 =
          if i = 0 ∨ i = 1 then 1 else 0)) := by
  have hfibers := assignedLabel_fibers G hM U₀ U₁ Z h01 h0Z h1Z hcover
  refine ⟨assignedLabel G M U₀ U₁ Z, hfibers.1, hfibers.2.1, hfibers.2.2,
    internalOn_card_le_one G (hM.isMatching G) Z hZ, ?_,
    assignedLabel_parity G hM U₀ U₁ Z h01 h0Z h1Z hcover⟩
  rw [hfibers.2.2]
  exact pairPart_card_eq_zero_or_two G (hM.isMatching G) Z hZ

end Overfull.AssignedParts
