import Overfull.NativeAssembly.NativeBundles

/-!
# Native completion with one exception or two separately assigned exceptions

When the internal exceptional pool is empty, the protected reserve and
joining classes already form the exact base for the remaining actual stars.
The native reserve proves copy/color balance, and available-color Hall
extension completes one star or both stars while preserving every protected
boundary and every assigned-fiber cut.
-/

noncomputable section

namespace Overfull.NativeAssembly

open Finset Classical AssignedParts FourOdd NativeReserve NativeStar WeightedPalette

variable {V E K I : Type*} [Fintype V] [Fintype E] [Fintype I] [DecidableEq K]
    {H : Multigraph V E} {label : V → K} {h D L d : ℕ} {p : K → ℕ}
    {C : JoiningPalette H label h D L p} {B : I → Finset E} {f : I → Fin h}

/-- Without an internal bundle, the remaining palette excludes exactly
the protected colors and the colors already incident at the star center. -/
def noBundleColors (C : JoiningPalette H label h D L p) (f : I → Fin h) (z : V) :
    Finset (Fin h) := remainingStarColors (univ.image f) (joiningUsedColors C z) ∅

theorem reserve_eq_on_noBundleColors (P : ReserveExtension C B f d)
    (z : V) (j : Fin h) (hj : j ∈ noBundleColors C f z) : P.classes j = C.classes j :=
  reserveExtension_eq_of_not_protected P j ((mem_remainingStarColors _ _ _ j).mp hj).1

theorem reserve_free_on_noBundleColors (P : ReserveExtension C B f d)
    (z : V) (j : Fin h) (hj : j ∈ noBundleColors C f z) :
    z ∉ H.edgeSupport (P.classes j) := by
  rw [reserve_eq_on_noBundleColors P z j hj]
  exact fun hz => ((mem_remainingStarColors _ _ _ j).mp hj).2.1
    ((mem_joiningUsedColors C z j).mpr hz)

theorem reserve_available_load_le (P : ReserveExtension C B f d) (z v : V) :
    ((noBundleColors C f z).filter
      (fun j => v ∈ H.edgeSupport (P.classes j))).card ≤ D := by
  apply (card_le_card (show _ ⊆ univ.filter
    (fun j => v ∈ H.edgeSupport (C.classes j)) from ?_)).trans (C.vertex_load_le v)
  intro j hj
  obtain ⟨hjF,hv⟩ := mem_filter.mp hj
  rw [reserve_eq_on_noBundleColors P z j hjF] at hv
  exact mem_filter.mpr ⟨mem_univ _,hv⟩

theorem reserve_available_weight_le (P : ReserveExtension C B f d)
    (z : V) (U : Finset V) (W : ℕ)
    (hweight : ∀ j, starWeight H z U (C.classes j) ≤ W) :
    ∀ j ∈ noBundleColors C f z, starWeight H z U (P.classes j) ≤ W := by
  intro j hj
  rw [reserve_eq_on_noBundleColors P z j hj]
  exact hweight j

/-- Every color outside the remaining palette already covers the center. -/
theorem reserve_covers_not_noBundleColors (P : ReserveExtension C B f d)
    (z : V) (hreserve : ∀ i, z ∈ H.edgeSupport (B i))
    (j : Fin h) (hj : j ∉ noBundleColors C f z) :
    z ∈ H.edgeSupport (P.classes j) := by
  have hc : j ∈ univ.image f ∨ j ∈ joiningUsedColors C z := by
    simpa only [noBundleColors, mem_remainingStarColors, notMem_empty,
      and_true, not_and_or, not_not] using hj
  rcases hc with hjQ | hjJ
  · obtain ⟨i,_,rfl⟩ := mem_image.mp hjQ
    rw [P.prescribed]
    exact hreserve i
  · obtain ⟨e,he,hze⟩ := (H.mem_edgeSupport _ z).mp
      ((mem_joiningUsedColors C z j).mp hjJ)
    exact (H.mem_edgeSupport _ z).mpr ⟨e,P.contains_original j he,hze⟩

/-- Removing the selected reserve part of an internal star leaves it
disjoint from every actual reserve-extended class. -/
theorem remaining_star_disjoint_reserve (P : ReserveExtension C B f d)
    (S : Finset E) (hSJ : Disjoint S (joiningCopies H label)) (j : Fin h) :
    Disjoint (S \ ((univ.biUnion B) ∩ S)) (P.classes j) := by
  apply disjoint_left.mpr
  intro e heA heP
  obtain ⟨heS,heR⟩ := mem_sdiff.mp heA
  have he : e ∈ joiningCopies H label ∪ univ.biUnion B := by
    rw [← P.cover]
    exact mem_biUnion.mpr ⟨j,mem_univ _,heP⟩
  rcases mem_union.mp he with heJ | heB
  · exact disjoint_left.mp hSJ heS heJ
  · exact heR (mem_inter.mpr ⟨heB,heS⟩)

omit [Fintype V] [Fintype E] in
/-- A selected reserve intersection and its remaining star recover the
entire original star without identifying or discarding any copy. -/
theorem union_remaining_star (J R S : Finset E) :
    (J ∪ R) ∪ (S \ (R ∩ S)) = J ∪ R ∪ S := by
  ext e
  simp only [mem_union,mem_sdiff,mem_inter]
  tauto

omit [Fintype V] in
/-- A single exception has no internal exceptional edge, since the
multigraph is loopless. -/
theorem exceptionInternalPool_singleton_eq_empty
    (H : Multigraph V E) (label : V → K) (z : V) :
    exceptionInternalPool H label {z} z = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨hz,ho,_⟩ := (mem_exceptionInternalPool H label {z} z e).mp he
  exact H.otherEnd_ne z e hz (mem_singleton.mp ho)

variable {J : Type*}

/-- With no internal exceptional bundle, native selected-reserve counts
give the exact actual remaining-star/free-color balance and Hall margin. -/
theorem native_no_bundle_star_balance
    (G : Multigraph V E) {M : Finset E} (hM : G.IsPerfectMatching M)
    (U₀ U₁ Z : Finset V) (h01 : Disjoint U₀ U₁)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (σ : Z → Fin 2) (hcode : coarseSignature G M U₀ Z = some σ)
    (r : ℕ) (R : BoundaryPacking G U₀ U₁ Z M r)
    (N : J → Finset E) (T : Finset J)
    (havoid : ∀ j ∈ T, Disjoint (N j) (removedCopies R.boundary univ))
    {h D L : ℕ} {p : Fin 3 → ℕ}
    (C : JoiningPalette (residualGraph G N T) (assignedLabel G M U₀ U₁ Z) h D L p)
    (z : Z) (hdegree : (residualGraph G N T).degree z.val = h) (herror : h-r ≤ D)
    (q : I → Fin r) (hq : Function.Injective q)
    (f : I → Fin h) (hf : Function.Injective f)
    (htrace : ∀ i, R.residualBoundary N T (q i) ∩
      joiningCopies (residualGraph G N T) (assignedLabel G M U₀ U₁ Z) = C.classes (f i))
    (hI : exceptionInternalPool (residualGraph G N T)
      (assignedLabel G M U₀ U₁ Z) Z z.val = ∅) :
    let S := exceptionCorePool (residualGraph G N T) z.val (if σ z = 0 then U₀ else U₁)
    let A := S \ ((univ.biUnion (fun i => R.residualBoundary N T (q i))) ∩ S)
    A.card = (noBundleColors C f z.val).card ∧ h-Fintype.card I-D ≤ A.card := by
  let H := residualGraph G N T
  let c : (∅ : Finset {e : E // e ∉ removedCopies N T}) → Fin h :=
    fun e => (notMem_empty e.val e.property).elim
  have hc : Function.Injective c := by
    intro e
    exact (notMem_empty e.val e.property).elim
  have hcavoid : ∀ e, c e ∉ univ.image f ∧ c e ∉ joiningUsedColors C z.val := by
    intro e
    exact (notMem_empty e.val e.property).elim
  have hcolors : univ.image c = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro j hj
    obtain ⟨e,_,_⟩ := mem_image.mp hj
    exact notMem_empty e.val e.property
  have hb := native_remaining_star_balance G hM U₀ U₁ Z h01 h0Z h1Z hcover
    σ hcode r R N T havoid C z hdegree herror univ q hq.injOn f hf.injOn
    (fun i _ => htrace i) ∅ hI.symm c hc hcavoid
  dsimp only at hb
  refine ⟨?_,?_⟩
  · simpa only [hcolors,noBundleColors] using hb.2.2.2.2.1
  · simpa only [card_univ] using hb.2.2.2.2.2

end Overfull.NativeAssembly
