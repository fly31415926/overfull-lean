import Overfull.NativeReserve.CompletionFootprints
import Overfull.ExceptionalPalette.ReserveCopies
import Overfull.BipartiteFactorization.Moves

/-!
# Native old-core multiplicity and full-family incidence bounds

Actual copies from an exterior exception to an old-core vertex belong to
the embedded core's complement. Their multiplicity is bounded by the true
core deficit. The same deficit bounds the global vertex load of any
disjoint family outside the core, including full protected reserve classes.
This uses the native core data in addition to the abstract joining palette.
-/

noncomputable section

namespace Overfull.NativeCore

open Finset Classical AssignedParts FourOdd NativeReserve SmallCuts

variable {V E F I : Type*} [Fintype E]

/-- An exterior star's parallel multiplicity is bounded by the actual
core-complement degree, with no extra rounding or simple-edge term. -/
theorem outside_parallel_le_core_error (G : Multigraph V E) (U : Finset V)
    (C : Core G U) (k : ℕ) (a : ℝ)
    (hregular : ∀ v, G.degree v = k)
    (hdegree : ∀ v, (k : ℝ)-a ≤ (C.graph.degree v : ℝ))
    (z : V) (hz : z ∉ U) (v : U) :
    ((G.parallelEdges z v.val).card : ℝ) ≤ a := by
  have hparallel := BipartiteFactorization.outside_parallel_le_complement
    (G := G) U (OneCore.coreEdges C) (OneCore.coreEdges_subset_internal C) z hz v.val
  exact (Nat.cast_le.mpr hparallel).trans
    (OneCore.complement_degree_le_error C k a hregular hdegree v)

/-- The original native integer joining bound can also bound every
exception-to-core parallel bundle when it is the floor of the full error. -/
theorem outside_parallel_le_floor_error (G : Multigraph V E) (U : Finset V)
    (C : Core G U) (k : ℕ) (a A : ℝ)
    (hregular : ∀ v, G.degree v = k)
    (hdegree : ∀ v, (k : ℝ)-a ≤ (C.graph.degree v : ℝ)) (haA : a ≤ A)
    (z : V) (hz : z ∉ U) (v : U) :
    (G.parallelEdges z v.val).card ≤ ⌊A⌋₊ :=
  Nat.le_floor ((outside_parallel_le_core_error G U C k a hregular hdegree z hz v).trans haA)

/-- A copy incident with an exceptional vertex lies outside every old
embedded core disjoint from the exceptional set. -/
theorem exceptionalCopies_disjoint_core (G : Multigraph V E) (U Z : Finset V)
    (C : Core G U) (hUZ : Disjoint U Z) :
    Disjoint (exceptionalCopies G univ Z) (OneCore.coreEdges C) := by
  apply disjoint_left.mpr
  intro e he hc
  obtain ⟨_, hz | hz⟩ := (mem_exceptionalCopies G univ Z e).mp he
  · exact disjoint_left.mp hUZ
      (OneCore.coreEdges_endpoint C hc ((G.incident_iff e _).mpr (Or.inl rfl))) hz
  · exact disjoint_left.mp hUZ
      (OneCore.coreEdges_endpoint C hc ((G.incident_iff e _).mpr (Or.inr rfl))) hz

/-- Joining copies and exceptional copies together are disjoint from any
old embedded core on which the assignment is constant. -/
theorem joining_exceptional_disjoint_core {K : Type*} [DecidableEq K]
    (G : Multigraph V E) (label : V → K) (U Z : Finset V)
    (C : Core G U) (hUZ : Disjoint U Z) (i : K)
    (hlabel : ∀ v ∈ U, label v = i) :
    Disjoint (joiningCopies G label ∪ exceptionalCopies G univ Z) (OneCore.coreEdges C) :=
  disjoint_union_left.mpr ⟨joiningCopies_disjoint_core G label U C i hlabel,
    exceptionalCopies_disjoint_core G U Z C hUZ⟩

/-- The global load of the entire actual external family is bounded by
the core deficit. This includes protected classes and is stronger than
an available-palette estimate, using the actual core-complement data. -/
theorem external_family_load_le_error {K : Type*} [DecidableEq K] [Fintype I]
    (G : Multigraph V E) (label : V → K) (U Z : Finset V)
    (C : Core G U) (hUZ : Disjoint U Z) (i : K)
    (hlabel : ∀ v ∈ U, label v = i) (k : ℕ) (a : ℝ)
    (hregular : ∀ v, G.degree v = k)
    (hdegree : ∀ v, (k : ℝ)-a ≤ (C.graph.degree v : ℝ))
    (B : I → Finset E) (hdisj : Pairwise (fun j l => Disjoint (B j) (B l)))
    (hsub : ∀ j, B j ⊆ joiningCopies G label ∪ exceptionalCopies G univ Z)
    (v : U) :
    ((univ.filter (fun j => v.val ∈ G.edgeSupport (B j))).card : ℝ) ≤ a := by
  have hout (j : I) : Disjoint (B j) (OneCore.coreEdges C) :=
    (joining_exceptional_disjoint_core G label U Z C hUZ i hlabel).mono_left (hsub j)
  have hh := coreFootprint_load_le_error G C B hdisj hout k a hregular hdegree v
  rwa [coreFootprint_load_eq] at hh

/-- All copies of an actual exceptional star are exceptional copies. -/
theorem exceptionCorePool_subset_exceptional (G : Multigraph V E)
    (z : V) (U Z : Finset V) (hz : z ∈ Z) :
    exceptionCorePool G z U ⊆ exceptionalCopies G univ Z := by
  intro e he
  exact mem_exceptionalCopies_of_incident G (mem_univ e) hz (mem_filter.mp he).2.1

variable [Fintype F]

/-- The real integer native bound controls stars to either old core,
including the cross-core multiplicity needed after the first star. -/
theorem native_exception_parallel_bounds
    (H : Multigraph V F) (U₀ U₁ Z : Finset V)
    (C₀ : Core H U₀) (C₁ : Core H U₁)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z) (h r : ℕ) (a : ℝ)
    (hregular : ∀ v, H.degree v = h)
    (hdegree₀ : ∀ v, (h : ℝ)-a ≤ (C₀.graph.degree v : ℝ))
    (hdegree₁ : ∀ v, (h : ℝ)-a ≤ (C₁.graph.degree v : ℝ)) :
    ∀ z ∈ Z, ∀ v ∈ U₀ ∪ U₁,
      (H.parallelEdges z v).card ≤ ⌊max a ((h : ℝ)-r)⌋₊ := by
  intro z hz v hv
  rcases mem_union.mp hv with hv | hv
  · exact outside_parallel_le_floor_error H U₀ C₀ h a _ hregular hdegree₀
      (le_max_left _ _) z (fun hh => disjoint_left.mp h0Z hh hz) ⟨v,hv⟩
  · exact outside_parallel_le_floor_error H U₁ C₁ h a _ hregular hdegree₁
      (le_max_left _ _) z (fun hh => disjoint_left.mp h1Z hh hz) ⟨v,hv⟩

omit [Fintype F] in
/-- Full native reserve boundaries consist of joining copies and copies
incident with exceptions, in the actual surviving copy type. -/
theorem residualBoundary_subset_joining_exceptional {J : Type*}
    (G : Multigraph V E) (U₀ U₁ Z : Finset V) {M : Finset E}
    (hM : G.IsPerfectMatching M)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (r : ℕ) (R : BoundaryPacking G U₀ U₁ Z M r)
    (N : J → Finset E) (T : Finset J) (i : Fin r) :
    R.residualBoundary N T i ⊆
      joiningCopies (residualGraph G N T) (assignedLabel G M U₀ U₁ Z) ∪
        exceptionalCopies (residualGraph G N T) univ Z := by
  intro e he
  have heB := (R.mem_residualBoundary N T i e).mp he
  rcases mem_union.mp heB with heZ | heX
  · apply mem_union_right
    have hends := (mem_exceptionalCopies G (R.parent i) Z e.val).mp heZ |>.2
    exact (mem_exceptionalCopies _ univ Z e).mpr ⟨mem_univ _, hends⟩
  · apply mem_union_left
    apply (mem_joiningCopies _ _ e).mpr
    intro hsame
    have hpair := coreCrossing_assigned_label_pair G (hM.isMatching G)
      (R.parent i) U₀ U₁ Z h01 h0Z h1Z (paritySelection_subset _ heX)
    have hd := congrArg Sym2.IsDiag hpair
    change assignedLabel G M U₀ U₁ Z (G.firstEnd e.val) =
      assignedLabel G M U₀ U₁ Z (G.secondEnd e.val) at hsame
    rw [hsame] at hd
    simp at hd

end Overfull.NativeCore
