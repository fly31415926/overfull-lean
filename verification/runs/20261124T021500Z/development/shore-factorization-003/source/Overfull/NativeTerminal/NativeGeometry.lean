import Overfull.NativeTerminal.ResidualGeometry

/-!
# Actual terminal geometry from the selected native external copies

The hypothesis is an exact endpoint-preserving image identity for the
residual's external copies. All shore cuts, their sizes, and the star
incidences are consequences. No coloring or matching completion is assumed.
-/

noncomputable section

namespace Overfull.NativeTerminal

open Finset Classical NativeReserve AssignedParts

variable {V E F : Type*} [Fintype E] [Fintype F]
  {G : Multigraph V E} {H : Multigraph V F}
  {U₀ U₁ Z : Finset V} {M : Finset E} {r s : ℕ}
  (Q : NativeReserve.BoundaryPacking G U₀ U₁ Z M r)
  (hM : G.IsPerfectMatching M)
  (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
  (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2)

include hM h01 h0Z h1Z

/-- The first assigned shore is a whole-core shore for exact copy accounting. -/
theorem first_assigned_cut_subset_external :
    G.cutEdges (corePart G M Z U₀) ⊆ externalCopies G U₀ U₁ := by
  apply whole_shore_cut_subset_external
  · exact Or.inl (core_subset_corePart G M Z U₀)
  · exact Or.inr ((coreParts_disjoint G (hM.isMatching G) U₀ U₁ Z
      h01 h0Z h1Z).symm.mono_left (core_subset_corePart G M Z U₁))

/-- The second assigned shore is also a whole-core shore. -/
theorem second_assigned_cut_subset_external :
    G.cutEdges (corePart G M Z U₁) ⊆ externalCopies G U₀ U₁ := by
  apply whole_shore_cut_subset_external
  · exact Or.inr ((coreParts_disjoint G (hM.isMatching G) U₀ U₁ Z
      h01 h0Z h1Z).mono_left (core_subset_corePart G M Z U₀))
  · exact Or.inl (core_subset_corePart G M Z U₁)

omit hM h01 in
/-- The pair part avoids both old cores. -/
theorem pair_assigned_cut_subset_external :
    G.cutEdges (pairPart G M Z) ⊆ externalCopies G U₀ U₁ := by
  apply whole_shore_cut_subset_external
  · exact Or.inr (h0Z.mono_right (pairPart_subset G M Z))
  · exact Or.inr (h1Z.mono_right (pairPart_subset G M Z))

include hcover hZ

variable (q : Fin s → Fin r) (ι : CopyEmbedding G H)
  (himage : (externalCopies H U₀ U₁).image ι.map = BoundaryPacking.selectedUnion Q q)

include himage

/-- The actual residual first-shore cut has exactly the native selected crossing count. -/
theorem residual_first_cutSize (hq : Function.Injective q) :
    H.cutSize (corePart G M Z U₀) = s * ((corePart G M Z U₀).card % 2) := by
  rw [ι.cutSize_of_external_image U₀ U₁ _ _ himage
    (first_assigned_cut_subset_external hM h01 h0Z h1Z)]
  exact BoundaryPacking.selectedUnion_first_cut_card Q hM h01 h0Z h1Z hcover hZ q hq

/-- The actual residual two assigned-shore cuts are equal as sets of original copies. -/
theorem residual_shore_cuts_eq :
    H.cutEdges (corePart G M Z U₀) = H.cutEdges (corePart G M Z U₁) := by
  apply Finset.image_injective ι.map.injective
  rw [ι.cut_image_of_external_image U₀ U₁ _ _ himage
      (first_assigned_cut_subset_external hM h01 h0Z h1Z),
    ι.cut_image_of_external_image U₀ U₁ _ _ himage
      (second_assigned_cut_subset_external hM h01 h0Z h1Z)]
  exact BoundaryPacking.selectedUnion_shore_cuts_eq Q hM h01 h0Z h1Z hcover hZ q

/-- The actual residual second-shore cut has its own exact parity count. -/
theorem residual_second_cutSize (hq : Function.Injective q) :
    H.cutSize (corePart G M Z U₁) = s * ((corePart G M Z U₁).card % 2) := by
  have hpar : (corePart G M Z U₀).card % 2 = (corePart G M Z U₁).card % 2 := by
    rw [perfectMatching_shore_card_parity G hM,
      perfectMatching_shore_card_parity G hM,
      coreParts_cutOn_eq G (hM.isMatching G) U₀ U₁ Z h01 h0Z h1Z hcover]
  rw [Multigraph.cutSize, ← residual_shore_cuts_eq Q hM h01 h0Z h1Z hcover hZ q ι himage]
  change H.cutSize (corePart G M Z U₀) = _
  rw [residual_first_cutSize Q hM h01 h0Z h1Z hcover hZ q ι himage hq,hpar]

/-- No actual residual copy leaves the optional exceptional pair component. -/
theorem residual_pair_cut_empty : H.cutEdges (pairPart G M Z) = ∅ := by
  exact ι.cut_empty_of_external_image U₀ U₁ _ _ himage
    (pair_assigned_cut_subset_external h0Z h1Z)
    (BoundaryPacking.selectedUnion_pair_cut Q hM h01 h0Z h1Z hcover hZ q)

/-- Every actual residual incidence at an assigned exception enters its old core. -/
theorem residual_assigned_star_incidence (U : Finset V) (hU : U = U₀ ∨ U = U₁)
    {z : V} (hz : z ∈ corePart G M Z U \ U) {e : F} (hze : z ∈ H.edge e) :
    H.otherEnd z e ∈ U := by
  have hzZ := corePart_sdiff_subset_exceptions G M Z U hz
  have heX := external_of_incident_outside H U₀ U₁
    (fun hh => disjoint_left.mp h0Z hh hzZ)
    (fun hh => disjoint_left.mp h1Z hh hzZ) hze
  have heR : ι.map e ∈ BoundaryPacking.selectedUnion Q q := by
    rw [← himage]
    exact mem_image.mpr ⟨e,heX,rfl⟩
  rw [ι.otherEnd]
  exact BoundaryPacking.selectedUnion_otherEnd_mem_core Q hM h01 h0Z h1Z hcover hZ q U hU
    hz heR ((ι.incident z e).mp hze)

/-- In particular the assigned exterior is independent in the actual residual. -/
theorem residual_assigned_exterior_independent (U : Finset V) (hU : U = U₀ ∨ U = U₁) :
    H.internalEdges (corePart G M Z U \ U) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨hx,hy⟩ := (H.mem_internalEdges _ e).mp he
  have hxinc : H.firstEnd e ∈ H.edge e := (H.incident_iff e _).mpr (Or.inl rfl)
  have hh := residual_assigned_star_incidence Q hM h01 h0Z h1Z hcover hZ q ι himage U hU hx hxinc
  have hother : H.otherEnd (H.firstEnd e) e = H.secondEnd e := by
    simp [Multigraph.otherEnd]
  exact (mem_sdiff.mp hy).2 (hother ▸ hh)

/-- The complete geometric interface used by terminal shore factorization. -/
theorem residual_geometry (hq : Function.Injective q) :
    H.cutSize (corePart G M Z U₀) = s * ((corePart G M Z U₀).card % 2) ∧
    H.cutSize (corePart G M Z U₁) = s * ((corePart G M Z U₁).card % 2) ∧
    H.cutEdges (corePart G M Z U₀) = H.cutEdges (corePart G M Z U₁) ∧
    H.cutEdges (pairPart G M Z) = ∅ ∧
    (∀ z ∈ corePart G M Z U₀ \ U₀, ∀ e, z ∈ H.edge e → H.otherEnd z e ∈ U₀) ∧
    (∀ z ∈ corePart G M Z U₁ \ U₁, ∀ e, z ∈ H.edge e → H.otherEnd z e ∈ U₁) := by
  refine ⟨residual_first_cutSize Q hM h01 h0Z h1Z hcover hZ q ι himage hq,
    residual_second_cutSize Q hM h01 h0Z h1Z hcover hZ q ι himage hq,
    residual_shore_cuts_eq Q hM h01 h0Z h1Z hcover hZ q ι himage,
    residual_pair_cut_empty Q hM h01 h0Z h1Z hcover hZ q ι himage,?_,?_⟩
  · intro z hz e he
    exact residual_assigned_star_incidence Q hM h01 h0Z h1Z hcover hZ q ι himage U₀
      (Or.inl rfl) hz he
  · intro z hz e he
    exact residual_assigned_star_incidence Q hM h01 h0Z h1Z hcover hZ q ι himage U₁
      (Or.inr rfl) hz he

end Overfull.NativeTerminal
