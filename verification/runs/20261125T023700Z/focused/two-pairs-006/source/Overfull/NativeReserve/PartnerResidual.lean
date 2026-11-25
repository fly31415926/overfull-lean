import Overfull.NativeReserve.PartnerPacking
import Overfull.ExceptionalPalette.ReserveCopies

/-!
# Surviving native reserves with exceptional partners retained

The actual compressed boundaries and their original reserve indices survive
any deletion avoiding their whole union. Each original exceptional matching
pair supplies distinct surviving parallel copies, on its own endpoint fiber.
-/

noncomputable section

namespace Overfull.NativeReserve.PartnerBoundaryPacking

open Finset Classical AssignedParts FourOdd

variable {V E J I K : Type*} [Fintype E]
    {G : Multigraph V E} {U₀ U₁ Z : Finset V} {M : Finset E} {r : ℕ}
    (Q : PartnerBoundaryPacking G U₀ U₁ Z M r)

/-- The actual surviving copies of a whole partner-preserving boundary. -/
def residualBoundary (N : J → Finset E) (T : Finset J) (i : Fin r) :=
  survivingCopies (removedCopies N T) (Q.boundary i)

@[simp] theorem mem_residualBoundary (N : J → Finset E) (T : Finset J)
    (i : Fin r) (e : {e : E // e ∉ removedCopies N T}) :
    e ∈ Q.residualBoundary N T i ↔ e.val ∈ Q.boundary i :=
  mem_survivingCopies _ _ _

/-- Avoiding the whole reserved union preserves every boundary copy. -/
theorem boundary_disjoint_removed (N : J → Finset E) (T : Finset J)
    (havoid : ∀ j ∈ T, Disjoint (N j) (removedCopies Q.boundary univ))
    (i : Fin r) : Disjoint (Q.boundary i) (removedCopies N T) := by
  apply disjoint_left.mpr
  intro e he hr
  obtain ⟨j, hj, hej⟩ := (mem_removedCopies N T e).mp hr
  exact disjoint_left.mp (havoid j hj) hej
    ((mem_removedCopies Q.boundary univ e).mpr ⟨i, mem_univ _, he⟩)

theorem residualBoundary_image (N : J → Finset E) (T : Finset J)
    (havoid : ∀ j ∈ T, Disjoint (N j) (removedCopies Q.boundary univ))
    (i : Fin r) : (Q.residualBoundary N T i).image Subtype.val = Q.boundary i :=
  survivingCopies_image _ _ (Q.boundary_disjoint_removed N T havoid i)

theorem residualBoundary_matching (N : J → Finset E) (T : Finset J) (i : Fin r) :
    (residualGraph G N T).IsMatching (Q.residualBoundary N T i) :=
  survivingCopies_isMatching G _ _ (Q.isMatching i)

theorem residualBoundary_disjoint (N : J → Finset E) (T : Finset J) :
    Pairwise (fun i j => Disjoint (Q.residualBoundary N T i)
      (Q.residualBoundary N T j)) :=
  fun _ _ hij => survivingCopies_disjoint _ _ _ (Q.disjoint hij)

theorem residualBoundary_support (N : J → Finset E) (T : Finset J)
    (havoid : ∀ j ∈ T, Disjoint (N j) (removedCopies Q.boundary univ))
    (i : Fin r) :
    (residualGraph G N T).edgeSupport (Q.residualBoundary N T i) =
      G.edgeSupport (Q.boundary i) :=
  survivingCopies_support G _ _ (Q.boundary_disjoint_removed N T havoid i)

theorem residualBoundary_card_le (N : J → Finset E) (T : Finset J)
    (havoid : ∀ j ∈ T, Disjoint (N j) (removedCopies Q.boundary univ))
    (i : Fin r) : (Q.residualBoundary N T i).card ≤ Z.card+1 := by
  rw [residualBoundary, survivingCopies_card _ _ (Q.boundary_disjoint_removed N T havoid i)]
  exact Q.card_le i

theorem residualBoundary_covers_exceptional (N : J → Finset E) (T : Finset J)
    (havoid : ∀ j ∈ T, Disjoint (N j) (removedCopies Q.boundary univ))
    (i : Fin r) : Z ⊆ (residualGraph G N T).edgeSupport (Q.residualBoundary N T i) := by
  rw [Q.residualBoundary_support N T havoid i]
  exact compressedBoundary_covers_exceptional G (Q.perfect i) U₀ U₁ Z

/-- Preserve actual reserve indices while selecting one surviving parallel
copy of any specified original exceptional matching edge. -/
theorem exists_residual_pair_injection (hM : G.IsPerfectMatching M)
    (e : G.internalOn M Z) (N : J → Finset E) (T : Finset J)
    (havoid : ∀ j ∈ T, Disjoint (N j) (removedCopies Q.boundary univ))
    (q : I → Fin r) (hq : Function.Injective q) :
    ∃ g : I → (residualGraph G N T).internalOn univ (G.edge e.val).toFinset,
      Function.Injective g ∧
      ∀ i, (g i).val ∈ Q.residualBoundary N T (q i) ∧
        (residualGraph G N T).edge (g i).val = G.edge e.val := by
  obtain ⟨g₀, hg₀, hgR⟩ := Q.exists_pair_injection hM e
  have hsurvive (i : I) : g₀ (q i) ∉ removedCopies N T :=
    fun hh => disjoint_left.mp (Q.boundary_disjoint_removed N T havoid (q i))
      (hgR (q i)).1 hh
  let a (i : I) : {e : E // e ∉ removedCopies N T} := ⟨g₀ (q i), hsurvive i⟩
  have ha (i : I) : a i ∈
      (residualGraph G N T).internalOn univ (G.edge e.val).toFinset := by
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_, ?_⟩
    · apply Sym2.mem_toFinset.mpr
      rw [← (hgR (q i)).2]
      exact (G.incident_iff (g₀ (q i)) _).mpr (Or.inl rfl)
    · apply Sym2.mem_toFinset.mpr
      rw [← (hgR (q i)).2]
      exact (G.incident_iff (g₀ (q i)) _).mpr (Or.inr rfl)
  let g (i : I) : (residualGraph G N T).internalOn univ (G.edge e.val).toFinset :=
    ⟨a i, ha i⟩
  refine ⟨g, ?_, ?_⟩
  · intro i j hij
    exact hq (hg₀ (congrArg (fun x => x.val.val) hij))
  · intro i
    exact ⟨(Q.mem_residualBoundary N T (q i) (a i)).mpr (hgR (q i)).1,
      (hgR (q i)).2⟩

/-- Distinct constant labels on the old cores classify every surviving
compressed crossing as joining. All other boundary copies touch `Z`. -/
theorem residualBoundary_subset_joining_exceptional [DecidableEq K]
    (N : J → Finset E) (T : Finset J) (label : V → K)
    (k₀ k₁ : K) (hk : k₀ ≠ k₁) (h01 : Disjoint U₀ U₁)
    (hlabel₀ : ∀ v ∈ U₀, label v = k₀) (hlabel₁ : ∀ v ∈ U₁, label v = k₁)
    (i : Fin r) :
    Q.residualBoundary N T i ⊆ joiningCopies (residualGraph G N T) label ∪
      exceptionalCopies (residualGraph G N T) univ Z := by
  intro e he
  have heB := (Q.mem_residualBoundary N T i e).mp he
  rcases mem_union.mp heB with heZ | heC
  · apply mem_union_right
    exact (mem_exceptionalCopies (residualGraph G N T) univ Z e).mpr
      ⟨mem_univ _, (mem_exceptionalCopies G (Q.parent i) Z e.val).mp heZ |>.2⟩
  · apply mem_union_left
    apply (mem_joiningCopies (residualGraph G N T) label e).mpr
    change label (G.firstEnd e.val) ≠ label (G.secondEnd e.val)
    rcases ((mem_coreCrossings_iff G (Q.parent i) U₀ U₁ h01 e.val).mp
      (paritySelection_subset _ heC)).2 with hc | hc
    · rw [hlabel₀ _ hc.1, hlabel₁ _ hc.2]
      exact hk
    · rw [hlabel₁ _ hc.1, hlabel₀ _ hc.2]
      exact Ne.symm hk

end Overfull.NativeReserve.PartnerBoundaryPacking
