import Overfull.AssignedParts.MatchedCuts

/-!
# Native compression of a two-core matching boundary

Every retained edge is an original copy of the specified perfect matching.
All copies touching the exceptional set are retained, while the old-core
crossing set is replaced by zero or one of its own copies with the same parity.
No simplicity hypothesis or exceptional-pair deletion is used.
-/

noncomputable section

namespace Overfull.Multigraph

open Finset Classical
open scoped BigOperators

variable {V E : Type*} (G : Multigraph V E)

/-- Matching incidence in a shore counts its covered vertices exactly. -/
theorem IsMatching.degreeOn_sum_eq_covered {F : Finset E} (hF : G.IsMatching F)
    (U : Finset V) :
    (∑ v ∈ U, G.degreeOn F v) = (U ∩ G.edgeSupport F).card := by
  have hdegree (v : V) : G.degreeOn F v = if v ∈ G.edgeSupport F then 1 else 0 := by
    split_ifs with hv
    · have hlo := (G.degreeOn_pos_iff F v).mpr hv
      have hhi := (G.isMatching_iff_incident_card_le_one F).mp hF v
      change G.degreeOn F v ≤ 1 at hhi
      omega
    · exact G.degreeOn_eq_zero_of_not_mem hv
  simp_rw [hdegree]
  rw [sum_boole]
  congr 1

/-- Even uncovered order is equivalent to the original-copy cut parity. -/
theorem IsMatching.uncovered_even_iff_cut_parity {F : Finset E} (hF : G.IsMatching F)
    (U : Finset V) :
    Even (U \ G.edgeSupport F).card ↔ U.card % 2 = (G.cutOn F U).card % 2 := by
  have hsum := G.degreeOn_sum_on F U
  rw [hF.degreeOn_sum_eq_covered G U] at hsum
  have hcard := card_sdiff_add_card_inter U (G.edgeSupport F)
  rw [Nat.even_iff]
  omega

end Overfull.Multigraph

namespace Overfull.AssignedParts

open Finset Classical

variable {V E : Type*} (G : Multigraph V E)

/-- The original selected copies touching at least one exceptional vertex. -/
def exceptionalCopies (M : Finset E) (Z : Finset V) : Finset E :=
  M.filter (fun e => G.firstEnd e ∈ Z ∨ G.secondEnd e ∈ Z)

@[simp] theorem mem_exceptionalCopies (M : Finset E) (Z : Finset V) (e : E) :
    e ∈ exceptionalCopies G M Z ↔
      e ∈ M ∧ (G.firstEnd e ∈ Z ∨ G.secondEnd e ∈ Z) := by
  simp [exceptionalCopies]

theorem exceptionalCopies_subset (M : Finset E) (Z : Finset V) :
    exceptionalCopies G M Z ⊆ M := filter_subset _ _

/-- All selected copies at an exceptional vertex are retained. -/
theorem mem_exceptionalCopies_of_incident {M : Finset E} {Z : Finset V}
    {e : E} (he : e ∈ M) {z : V} (hz : z ∈ Z) (hze : z ∈ G.edge e) :
    e ∈ exceptionalCopies G M Z := by
  apply (mem_exceptionalCopies G M Z e).mpr
  refine ⟨he, ?_⟩
  rcases (G.incident_iff e z).mp hze with h | h
  · exact Or.inl (h.symm ▸ hz)
  · exact Or.inr (h.symm ▸ hz)

/-- Distinct matching copies touching the exceptions use distinct exceptional vertices. -/
theorem exceptionalCopies_card_le {M : Finset E} (hM : G.IsMatching M)
    (Z : Finset V) : (exceptionalCopies G M Z).card ≤ Z.card := by
  let pick : E → V := fun e => if G.firstEnd e ∈ Z then G.firstEnd e else G.secondEnd e
  have hinc (e : E) : pick e ∈ G.edge e := by
    dsimp [pick]
    split_ifs <;> apply (G.incident_iff e _).mpr
    · exact Or.inl rfl
    · exact Or.inr rfl
  apply card_le_card_of_injOn pick
  · intro e he
    obtain ⟨_, hfirst | hsecond⟩ := (mem_exceptionalCopies G M Z e).mp he
    · simp [pick, hfirst]
    · by_cases hfirst : G.firstEnd e ∈ Z <;> simp [pick, hfirst, hsecond]
  · intro e he f hf hef
    exact hM e (exceptionalCopies_subset G M Z he)
      f (exceptionalCopies_subset G M Z hf) (pick e) (hinc e) (hef.symm ▸ hinc f)

/-- Select no copy from an even set and one original copy from an odd set. -/
def paritySelection (T : Finset E) : Finset E :=
  if h : T.card % 2 = 1 then
    {Classical.choose (show T.Nonempty from card_pos.mp (by omega))}
  else ∅

theorem paritySelection_subset (T : Finset E) : paritySelection T ⊆ T := by
  unfold paritySelection
  split_ifs with h
  · intro e he
    rw [mem_singleton] at he
    subst e
    exact Classical.choose_spec (show T.Nonempty from card_pos.mp (by omega))
  · exact empty_subset _

theorem paritySelection_card (T : Finset E) : (paritySelection T).card = T.card % 2 := by
  unfold paritySelection
  split_ifs with h
  · simp [h]
  · have hmod := Nat.mod_lt T.card (by decide : 0 < 2)
    simp only [card_empty]
    omega

theorem paritySelection_card_le_one (T : Finset E) : (paritySelection T).card ≤ 1 := by
  rw [paritySelection_card]
  omega

/-- The compression retains all exceptional copies and only the required crossing parity. -/
def compressedBoundary (M : Finset E) (U₀ U₁ Z : Finset V) : Finset E :=
  exceptionalCopies G M Z ∪ paritySelection (G.cutOn M U₀ ∩ G.cutOn M U₁)

theorem compressedBoundary_subset (M : Finset E) (U₀ U₁ Z : Finset V) :
    compressedBoundary G M U₀ U₁ Z ⊆ M := by
  intro e he
  rcases mem_union.mp he with he | he
  · exact exceptionalCopies_subset G M Z he
  · exact (G.mem_cutOn M U₀ e).mp
      (mem_inter.mp (paritySelection_subset _ he)).1 |>.1

theorem compressedBoundary_isMatching {M : Finset E} (hM : G.IsMatching M)
    (U₀ U₁ Z : Finset V) : G.IsMatching (compressedBoundary G M U₀ U₁ Z) := by
  intro e he f hf v hev hfv
  exact hM e (compressedBoundary_subset G M U₀ U₁ Z he)
    f (compressedBoundary_subset G M U₀ U₁ Z hf) v hev hfv

theorem compressedBoundary_retains_exceptional (M : Finset E) (U₀ U₁ Z : Finset V) :
    exceptionalCopies G M Z ⊆ compressedBoundary G M U₀ U₁ Z := subset_union_left

/-- Every exceptional vertex remains covered by its original matching copy. -/
theorem compressedBoundary_covers_exceptional {M : Finset E}
    (hM : G.IsPerfectMatching M) (U₀ U₁ Z : Finset V) :
    Z ⊆ G.edgeSupport (compressedBoundary G M U₀ U₁ Z) := by
  intro z hz
  obtain ⟨e, he, hze⟩ := (G.isPerfectMatching_iff.mp hM).2 z
  exact (G.mem_edgeSupport _ z).mpr ⟨e,
    compressedBoundary_retains_exceptional G M U₀ U₁ Z
      (mem_exceptionalCopies_of_incident G he hz hze), hze⟩

/-- The retained degree at every exceptional vertex is exactly one. -/
theorem compressedBoundary_exceptional_degree {M : Finset E}
    (hM : G.IsPerfectMatching M) (U₀ U₁ Z : Finset V) {z : V} (hz : z ∈ Z) :
    G.degreeOn (compressedBoundary G M U₀ U₁ Z) z = 1 := by
  have hlo := (G.degreeOn_pos_iff _ z).mpr
    (compressedBoundary_covers_exceptional G hM U₀ U₁ Z hz)
  have hhi := (G.isMatching_iff_incident_card_le_one _).mp
    (compressedBoundary_isMatching G (hM.isMatching G) U₀ U₁ Z) z
  change G.degreeOn (compressedBoundary G M U₀ U₁ Z) z ≤ 1 at hhi
  omega

theorem compressedBoundary_card_le {M : Finset E} (hM : G.IsMatching M)
    (U₀ U₁ Z : Finset V) :
    (compressedBoundary G M U₀ U₁ Z).card ≤ Z.card + 1 := by
  have h := card_union_le (exceptionalCopies G M Z)
    (paritySelection (G.cutOn M U₀ ∩ G.cutOn M U₁))
  have hz := exceptionalCopies_card_le G hM Z
  have ht := paritySelection_card_le_one (G.cutOn M U₀ ∩ G.cutOn M U₁)
  unfold compressedBoundary
  omega

theorem compressedBoundary_support_card_le {M : Finset E} (hM : G.IsMatching M)
    (U₀ U₁ Z : Finset V) :
    (G.edgeSupport (compressedBoundary G M U₀ U₁ Z)).card ≤ 2 * (Z.card + 1) := by
  rw [(compressedBoundary_isMatching G hM U₀ U₁ Z).edgeSupport_card G]
  exact Nat.mul_le_mul_left 2 (compressedBoundary_card_le G hM U₀ U₁ Z)

/-- Compression preserves the exact assignment of exceptional vertices to any old core. -/
theorem compressedBoundary_assignedExceptions (M : Finset E) (U₀ U₁ Z U : Finset V) :
    assignedExceptions G (compressedBoundary G M U₀ U₁ Z) Z U =
      assignedExceptions G M Z U := by
  ext z
  simp only [mem_assignedExceptions]
  constructor
  · rintro ⟨hz, e, he, hze, hoe⟩
    exact ⟨hz, e, compressedBoundary_subset G M U₀ U₁ Z he, hze, hoe⟩
  · rintro ⟨hz, e, he, hze, hoe⟩
    exact ⟨hz, e, compressedBoundary_retains_exceptional G M U₀ U₁ Z
      (mem_exceptionalCopies_of_incident G he hz hze), hze, hoe⟩

theorem compressedBoundary_corePart (M : Finset E) (U₀ U₁ Z U : Finset V) :
    corePart G (compressedBoundary G M U₀ U₁ Z) Z U = corePart G M Z U := by
  simp only [corePart, compressedBoundary_assignedExceptions]

/-- The optional exceptional pair retains its actual original edge copy. -/
theorem compressedBoundary_internalOn (M : Finset E) (U₀ U₁ Z : Finset V) :
    G.internalOn (compressedBoundary G M U₀ U₁ Z) Z = G.internalOn M Z := by
  ext e
  simp only [Multigraph.internalOn, mem_filter]
  constructor
  · rintro ⟨he, hends⟩
    exact ⟨compressedBoundary_subset G M U₀ U₁ Z he, hends⟩
  · rintro ⟨he, hends⟩
    exact ⟨compressedBoundary_retains_exceptional G M U₀ U₁ Z
      ((mem_exceptionalCopies G M Z e).mpr ⟨he, Or.inl hends.1⟩), hends⟩

theorem compressedBoundary_pairPart (M : Finset E) (U₀ U₁ Z : Finset V) :
    pairPart G (compressedBoundary G M U₀ U₁ Z) Z = pairPart G M Z := by
  simp only [pairPart, compressedBoundary_internalOn]

theorem compressedBoundary_assignedLabel (M : Finset E) (U₀ U₁ Z : Finset V) :
    assignedLabel G (compressedBoundary G M U₀ U₁ Z) U₀ U₁ Z =
      assignedLabel G M U₀ U₁ Z := by
  simp only [assignedLabel, compressedBoundary_corePart]

end Overfull.AssignedParts
