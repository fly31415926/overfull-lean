import Overfull.ResidualPalette.NativeProtectedPalette

/-!
# Surviving original reserved boundaries

All boundary copies are transported to the actual residual copy subtype.
Their original indices, matching property, exceptional coverage, and old-core
uncovered parity are retained. Their joining part consists precisely of the
old-core crossings; exceptional incidences remain internal to the assignment.
-/

noncomputable section
namespace Overfull.NativeReserve
open Finset Classical AssignedParts FourOdd

variable {V E J : Type*} [Fintype E]

/-- The surviving members of an original copy set, in the actual residual type. -/
def survivingCopies (R A : Finset E) : Finset {e : E // e ∉ R} :=
  univ.filter (fun e => e.val ∈ A)

@[simp] theorem mem_survivingCopies (R A : Finset E) (e : {e : E // e ∉ R}) :
    e ∈ survivingCopies R A ↔ e.val ∈ A := by
  simp [survivingCopies]

theorem survivingCopies_image (R A : Finset E) (hdisj : Disjoint A R) :
    (survivingCopies R A).image Subtype.val = A := by
  ext e
  constructor
  · intro he
    obtain ⟨f,hf,rfl⟩ := mem_image.mp he
    exact (mem_survivingCopies R A f).mp hf
  · intro he
    exact mem_image.mpr ⟨⟨e,fun h => disjoint_left.mp hdisj he h⟩,
      (mem_survivingCopies R A _).mpr he,rfl⟩

theorem survivingCopies_card (R A : Finset E) (hdisj : Disjoint A R) :
    (survivingCopies R A).card = A.card := by
  calc
    _ = ((survivingCopies R A).image Subtype.val).card :=
      (card_image_of_injective _ Subtype.val_injective).symm
    _ = A.card := congrArg Finset.card (survivingCopies_image R A hdisj)

theorem survivingCopies_disjoint (R A B : Finset E) (hdisj : Disjoint A B) :
    Disjoint (survivingCopies R A) (survivingCopies R B) := by
  apply disjoint_left.mpr
  intro e he hf
  exact disjoint_left.mp hdisj ((mem_survivingCopies R A e).mp he)
    ((mem_survivingCopies R B e).mp hf)

variable (G : Multigraph V E)

theorem survivingCopies_isMatching (R A : Finset E) (hA : G.IsMatching A) :
    (MultigraphMatchingProbability.remainingGraph G R).IsMatching (survivingCopies R A) := by
  intro e he f hf v hev hfv
  apply Subtype.ext
  exact hA e.val ((mem_survivingCopies R A e).mp he)
    f.val ((mem_survivingCopies R A f).mp hf) v hev hfv

theorem survivingCopies_support (R A : Finset E) (hdisj : Disjoint A R) :
    (MultigraphMatchingProbability.remainingGraph G R).edgeSupport (survivingCopies R A) =
      G.edgeSupport A := by
  ext v
  simp only [Multigraph.mem_edgeSupport]
  constructor
  · rintro ⟨e,he,hve⟩
    exact ⟨e.val,(mem_survivingCopies R A e).mp he,hve⟩
  · rintro ⟨e,he,hve⟩
    exact ⟨⟨e,fun hr => disjoint_left.mp hdisj he hr⟩,
      (mem_survivingCopies R A _).mpr he,hve⟩

namespace BoundaryPacking
variable {G : Multigraph V E} {U₀ U₁ Z : Finset V} {M : Finset E} {r : ℕ}
    (Q : BoundaryPacking G U₀ U₁ Z M r)

/-- The whole compressed reserve boundary in the actual residual edge type. -/
def residualBoundary (N : J → Finset E) (T : Finset J) (i : Fin r) :=
  survivingCopies (removedCopies N T) (Q.boundary i)

@[simp] theorem mem_residualBoundary (N : J → Finset E) (T : Finset J)
    (i : Fin r) (e : {e : E // e ∉ removedCopies N T}) :
    e ∈ Q.residualBoundary N T i ↔ e.val ∈ Q.boundary i := by
  exact mem_survivingCopies _ _ _

omit [Fintype E] in
theorem boundary_disjoint_removed (N : J → Finset E) (T : Finset J)
    (havoid : ∀ j ∈ T, Disjoint (N j) (removedCopies Q.boundary univ)) (i : Fin r) :
    Disjoint (Q.boundary i) (removedCopies N T) :=
  (Q.reserved_disjoint_removed N T havoid).mono_left
    (fun e he => (mem_removedCopies Q.boundary univ e).mpr ⟨i,mem_univ _,he⟩)

theorem residualBoundary_image (N : J → Finset E) (T : Finset J)
    (havoid : ∀ j ∈ T, Disjoint (N j) (removedCopies Q.boundary univ)) (i : Fin r) :
    (Q.residualBoundary N T i).image Subtype.val = Q.boundary i :=
  survivingCopies_image _ _ (Q.boundary_disjoint_removed N T havoid i)

theorem residualBoundary_matching (N : J → Finset E) (T : Finset J) (i : Fin r) :
    (residualGraph G N T).IsMatching (Q.residualBoundary N T i) :=
  survivingCopies_isMatching G _ _ (Q.isMatching i)

theorem residualBoundary_disjoint (N : J → Finset E) (T : Finset J) :
    Pairwise (fun i j => Disjoint (Q.residualBoundary N T i) (Q.residualBoundary N T j)) :=
  fun _ _ hij => survivingCopies_disjoint _ _ _ (Q.pairwise_disjoint hij)

theorem residualBoundary_support (N : J → Finset E) (T : Finset J)
    (havoid : ∀ j ∈ T, Disjoint (N j) (removedCopies Q.boundary univ)) (i : Fin r) :
    (residualGraph G N T).edgeSupport (Q.residualBoundary N T i) =
      G.edgeSupport (Q.boundary i) :=
  survivingCopies_support G _ _ (Q.boundary_disjoint_removed N T havoid i)

theorem residualBoundary_card_le (N : J → Finset E) (T : Finset J)
    (havoid : ∀ j ∈ T, Disjoint (N j) (removedCopies Q.boundary univ)) (i : Fin r) :
    (Q.residualBoundary N T i).card ≤ Z.card+1 := by
  rw [residualBoundary,survivingCopies_card _ _ (Q.boundary_disjoint_removed N T havoid i)]
  exact Q.card_le i

theorem residualBoundary_covers_exceptional (N : J → Finset E) (T : Finset J)
    (havoid : ∀ j ∈ T, Disjoint (N j) (removedCopies Q.boundary univ)) (i : Fin r) :
    Z ⊆ (residualGraph G N T).edgeSupport (Q.residualBoundary N T i) := by
  rw [Q.residualBoundary_support N T havoid i]
  exact compressedBoundary_covers_exceptional G (Q.perfect i) U₀ U₁ Z

theorem residualBoundary_uncovered_even (N : J → Finset E) (T : Finset J)
    (havoid : ∀ j ∈ T, Disjoint (N j) (removedCopies Q.boundary univ))
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (i : Fin r) :
    Even (U₀ \ (residualGraph G N T).edgeSupport (Q.residualBoundary N T i)).card ∧
      Even (U₁ \ (residualGraph G N T).edgeSupport (Q.residualBoundary N T i)).card := by
  rw [Q.residualBoundary_support N T havoid i]
  exact Q.uncovered_even h01 h0Z h1Z hcover i


/-- A reserved boundary joins assigned fibers exactly on its old-core crossings. -/
theorem boundary_joining_eq_crossing (hM : G.IsPerfectMatching M)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2) (j : Fin r) :
    Q.boundary j ∩ joiningCopies G (AssignedParts.assignedLabel G M U₀ U₁ Z) =
      G.cutOn (Q.boundary j) U₀ ∩ G.cutOn (Q.boundary j) U₁ := by
  ext e
  constructor
  · rintro he
    obtain ⟨heB,heJ⟩ := mem_inter.mp he
    have hjoin := (mem_joiningCopies G (AssignedParts.assignedLabel G M U₀ U₁ Z) e).mp heJ
    have hecases : e ∈ exceptionalCopies G (Q.parent j) Z ∨
        e ∈ paritySelection (G.cutOn (Q.parent j) U₀ ∩ G.cutOn (Q.parent j) U₁) :=
      mem_union.mp heB
    rcases hecases with heZ | heX
    · obtain ⟨_,hz | hz⟩ := (mem_exceptionalCopies G (Q.parent j) Z e).mp heZ
      · exact (hjoin (Q.exceptional_label_eq hM h01 h0Z h1Z hcover hZ j hz heB
          ((G.incident_iff e _).mpr (Or.inl rfl)))).elim
      · exact (hjoin (Q.exceptional_label_eq hM h01 h0Z h1Z hcover hZ j hz heB
          ((G.incident_iff e _).mpr (Or.inr rfl)))).elim
    · obtain ⟨he₀,he₁⟩ := mem_inter.mp (paritySelection_subset _ heX)
      exact mem_inter.mpr ⟨(G.mem_cutOn _ _ _).mpr ⟨heB,(G.mem_cutOn _ _ _).mp he₀ |>.2⟩,
        (G.mem_cutOn _ _ _).mpr ⟨heB,(G.mem_cutOn _ _ _).mp he₁ |>.2⟩⟩
  · intro he
    refine mem_inter.mpr ⟨((G.mem_cutOn _ _ _).mp (mem_inter.mp he).1).1,?_⟩
    apply (mem_joiningCopies G (AssignedParts.assignedLabel G M U₀ U₁ Z) e).mpr
    intro hsame
    have hp := coreCrossing_assigned_label_pair G (hM.isMatching G)
      (Q.boundary j) U₀ U₁ Z h01 h0Z h1Z he
    have hd := congrArg Sym2.IsDiag hp
    rw [hsame] at hd
    simp at hd

/-- Any surviving selected crossing identifies the whole joining part of
its original reserve boundary; all other copies are internal. -/
theorem residualBoundary_joining_singleton (hM : G.IsPerfectMatching M)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2)
    (hodd : (corePart G M Z U₀).card % 2 = 1)
    (N : J → Finset E) (T : Finset J) (j : Fin r)
    (e : joiningCopies (residualGraph G N T) (AssignedParts.assignedLabel G M U₀ U₁ Z))
    (he : e.val.val ∈ Q.boundary j) :
    Q.residualBoundary N T j ∩ joiningCopies (residualGraph G N T)
      (AssignedParts.assignedLabel G M U₀ U₁ Z) = {e.val} := by
  have heJ : e.val.val ∈ joiningCopies G (AssignedParts.assignedLabel G M U₀ U₁ Z) := by
    simpa only [mem_joiningCopies] using e.property
  have hc : (Q.boundary j ∩ joiningCopies G (AssignedParts.assignedLabel G M U₀ U₁ Z)).card = 1 := by
    rw [Q.boundary_joining_eq_crossing hM h01 h0Z h1Z hcover hZ j]
    exact Q.crossing_card_one_of_odd hM h01 h0Z h1Z hcover hZ hodd j
  obtain ⟨a,ha⟩ := card_eq_one.mp hc
  have hea : e.val.val = a := by
    apply mem_singleton.mp
    rw [← ha]
    exact mem_inter.mpr ⟨he,heJ⟩
  ext x
  constructor
  · intro hx
    obtain ⟨hxB,hxJ⟩ := mem_inter.mp hx
    have hxa : x.val = a := by
      apply mem_singleton.mp
      rw [← ha]
      exact mem_inter.mpr ⟨(Q.mem_residualBoundary N T j x).mp hxB,by
        simpa only [mem_joiningCopies] using hxJ⟩
    exact mem_singleton.mpr (Subtype.ext (hxa.trans hea.symm))
  · intro hx
    rw [mem_singleton] at hx
    subst x
    exact mem_inter.mpr ⟨(Q.mem_residualBoundary N T j e.val).mpr he,e.property⟩

/-- In the all-even case every surviving reserve boundary is wholly internal
for the original assignment and can occupy a protected empty joining color. -/
theorem residualBoundary_joining_empty (hM : G.IsPerfectMatching M)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2)
    (heven : (corePart G M Z U₀).card % 2 = 0)
    (N : J → Finset E) (T : Finset J) (j : Fin r) :
    Q.residualBoundary N T j ∩ joiningCopies (residualGraph G N T)
      (AssignedParts.assignedLabel G M U₀ U₁ Z) = ∅ := by
  have hc : (Q.boundary j ∩ joiningCopies G (AssignedParts.assignedLabel G M U₀ U₁ Z)).card = 0 := by
    rw [Q.boundary_joining_eq_crossing hM h01 h0Z h1Z hcover hZ j,
      Q.crossing_card hM h01 h0Z h1Z hcover hZ j,
      ← corePart_card_parity G hM U₀ U₁ Z h01 h0Z h1Z hcover]
    exact heven
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  have hh : e.val ∈ Q.boundary j ∩ joiningCopies G (AssignedParts.assignedLabel G M U₀ U₁ Z) :=
    mem_inter.mpr ⟨(Q.mem_residualBoundary N T j e).mp (mem_inter.mp he).1,
      by simpa only [mem_joiningCopies] using (mem_inter.mp he).2⟩
  rw [card_eq_zero.mp hc] at hh
  exact notMem_empty _ hh

end BoundaryPacking
end Overfull.NativeReserve
