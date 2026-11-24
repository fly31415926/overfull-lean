import Overfull.NativeStar.StarChoice
import Overfull.NativeStar.StarAccounting

/-!
# Inserting an actual colored star into matching classes

The construction retains every existing copy, assigns each new actual copy
to its chosen color, preserves untouched colors and cuts of assigned fibers,
and derives matching, disjointness, coverage and support bounds.
-/

noncomputable section

namespace Overfull.NativeStar

open Finset Classical

variable {V E K : Type*} {h : ℕ}

/-- Add the actual star color fiber to each existing class. -/
def starExtendedClasses (C : Fin h → Finset E) (A : Finset E)
    (c : A → Fin h) (j : Fin h) : Finset E :=
  C j ∪ coloredStarCopies A c j

theorem classes_subset_starExtended (C : Fin h → Finset E) (A : Finset E)
    (c : A → Fin h) (j : Fin h) : C j ⊆ starExtendedClasses C A c j :=
  subset_union_left

theorem starExtended_card_le (C : Fin h → Finset E) (A : Finset E)
    (c : A → Fin h) (hc : Function.Injective c) (j : Fin h) :
    (starExtendedClasses C A c j).card ≤ (C j).card + 1 := by
  exact (card_union_le _ _).trans
    (Nat.add_le_add_left (coloredStarCopies_card_le_one A c hc j) _)

theorem starExtended_cover (C : Fin h → Finset E) (A : Finset E)
    (c : A → Fin h) :
    univ.biUnion (starExtendedClasses C A c) = univ.biUnion C ∪ A := by
  have hcover := coloredStarCopies_cover A c
  ext e
  simp only [mem_biUnion, mem_univ, true_and, starExtendedClasses, mem_union]
  constructor
  · rintro ⟨j, hj | hj⟩
    · exact Or.inl ⟨j, hj⟩
    · exact Or.inr (hcover ▸ mem_biUnion.mpr ⟨j, mem_univ _, hj⟩)
  · rintro (⟨j, hj⟩ | he)
    · exact ⟨j, Or.inl hj⟩
    · obtain ⟨j, _, hj⟩ := mem_biUnion.mp (hcover.symm ▸ he)
      exact ⟨j, Or.inr hj⟩

theorem starExtended_disjoint (C : Fin h → Finset E) (A : Finset E)
    (c : A → Fin h)
    (hC : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hAC : ∀ j, Disjoint A (C j)) :
    Pairwise (fun i j => Disjoint (starExtendedClasses C A c i)
      (starExtendedClasses C A c j)) := by
  intro i j hij
  have hCA (i j : Fin h) : Disjoint (C i) (coloredStarCopies A c j) :=
    (hAC i).symm.mono_right (coloredStarCopies_subset A c j)
  exact disjoint_union_left.mpr ⟨disjoint_union_right.mpr ⟨hC hij, hCA i j⟩,
    disjoint_union_right.mpr ⟨(hCA j i).symm, coloredStarCopies_disjoint A c hij⟩⟩

theorem starExtended_eq_of_color_avoided (C : Fin h → Finset E) (A : Finset E)
    (c : A → Fin h) (j : Fin h) (hj : ∀ e, c e ≠ j) :
    starExtendedClasses C A c j = C j := by
  have he : coloredStarCopies A c j = ∅ := by
    ext e
    simp [coloredStarCopies, hj]
  simp [starExtendedClasses, he]

theorem starExtended_isMatching (G : Multigraph V E)
    (C : Fin h → Finset E) (A : Finset E) (c : A → Fin h)
    (hc : Function.Injective c) (z : V)
    (hA : ∀ e ∈ A, z ∈ G.edge e)
    (hC : ∀ j, G.IsMatching (C j))
    (hfree : ∀ e, z ∉ G.edgeSupport (C (c e)))
    (hother : ∀ e, G.otherEnd z e.val ∉ G.edgeSupport (C (c e))) (j : Fin h) :
    G.IsMatching (starExtendedClasses C A c j) := by
  apply CircuitPatterns.isMatching_union_of_disjoint_support G _ _ (hC j)
    (coloredStarCopies_isMatching G A c hc j)
  apply disjoint_left.mpr
  intro v hvC hvS
  obtain ⟨e, he, hve⟩ := (G.mem_edgeSupport _ v).mp hvS
  obtain ⟨q, hq, rfl⟩ := mem_image.mp he
  have hcj : c q = j := (mem_filter.mp hq).2
  rw [G.edge_eq_otherEnd z q.val (hA _ q.property), Sym2.mem_iff] at hve
  rw [← hcj] at hvC
  rcases hve with rfl | rfl
  · exact hfree q hvC
  · exact hother q hvC

theorem starExtended_support_card_le (G : Multigraph V E)
    (C : Fin h → Finset E) (A : Finset E) (c : A → Fin h)
    (hc : Function.Injective c) (j : Fin h) :
    (G.edgeSupport (starExtendedClasses C A c j)).card ≤
      (G.edgeSupport (C j)).card + 2 := by
  have hs : G.edgeSupport (starExtendedClasses C A c j) ⊆
      G.edgeSupport (C j) ∪ G.edgeSupport (coloredStarCopies A c j) := by
    intro v hv
    obtain ⟨e, he, hve⟩ := (G.mem_edgeSupport _ v).mp hv
    rcases mem_union.mp he with he | he
    · exact mem_union_left _ ((G.mem_edgeSupport _ v).mpr ⟨e, he, hve⟩)
    · exact mem_union_right _ ((G.mem_edgeSupport _ v).mpr ⟨e, he, hve⟩)
  have hsmall := (G.edgeSupport_card_le (coloredStarCopies A c j)).trans
    (Nat.mul_le_mul_left 2 (coloredStarCopies_card_le_one A c hc j))
  exact (card_le_card hs).trans ((card_union_le _ _).trans (by omega))

/-- Adding copies internal to their assigned fiber leaves every fiber cut
unchanged; the resulting parity follows without a two-vertex-fiber premise. -/
theorem starExtended_cut_eq [Fintype V] [DecidableEq K]
    (G : Multigraph V E) (label : V → K)
    (C : Fin h → Finset E) (A : Finset E) (c : A → Fin h)
    (hinternal : ∀ e ∈ A, label (G.firstEnd e) = label (G.secondEnd e))
    (j : Fin h) (k : K) :
    G.cutOn (starExtendedClasses C A c j) (FourOdd.labelShore label {k}) =
      G.cutOn (C j) (FourOdd.labelShore label {k}) := by
  ext e
  simp only [Multigraph.mem_cutOn, starExtendedClasses, mem_union]
  constructor
  · rintro ⟨he | he, hcut⟩
    · exact ⟨he, hcut⟩
    · have hsame := hinternal e (coloredStarCopies_subset A c j he)
      have hmem : (G.firstEnd e ∈ FourOdd.labelShore label {k}) =
          (G.secondEnd e ∈ FourOdd.labelShore label {k}) := by
        simp only [FourOdd.mem_labelShore, hsame]
      exact (hcut hmem).elim
  · intro he
    exact ⟨Or.inl he.1, he.2⟩

variable [Fintype E]

/-- A concrete star extension with derived matching, exact copy coverage,
disjoint color classes, protected-color preservation and bounded growth. -/
theorem exists_star_extension_on_available (G : Multigraph V E)
    (C : Fin h → Finset E) (z : V) (U : Finset V)
    (A : Finset E) (F : Finset (Fin h)) (D b s : ℕ)
    (hA : A ⊆ AssignedParts.exceptionCorePool G z U)
    (hcard : A.card = F.card) (hlower : h - s - D ≤ A.card)
    (hb : b ≤ D) (hD : 128 * D ≤ h) (hs : 2 * s ≤ h)
    (hmatching : ∀ j, G.IsMatching (C j))
    (hdisjoint : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hAC : ∀ j, Disjoint A (C j))
    (hfree : ∀ j ∈ F, z ∉ G.edgeSupport (C j))
    (hload : ∀ v ∈ U, (F.filter (fun j => v ∈ G.edgeSupport (C j))).card ≤ D + b)
    (hweight : ∀ j ∈ F, WeightedPalette.starWeight G z U (C j) ≤ h / 8 + b) :
    ∃ f : A ≃ F,
      let B := starExtendedClasses C A (fun e => (f e).val)
      (∀ j, G.IsMatching (B j)) ∧
      Pairwise (fun i j => Disjoint (B i) (B j)) ∧
      univ.biUnion B = univ.biUnion C ∪ A ∧
      (∀ j, C j ⊆ B j) ∧
      (∀ j, (B j).card ≤ (C j).card + 1) ∧
      (∀ j, (G.edgeSupport (B j)).card ≤ (G.edgeSupport (C j)).card + 2) ∧
      (∀ j ∉ F, B j = C j) := by
  obtain ⟨f, hf⟩ := exists_star_choice_on_available G C z U A F D b s hA hcard hlower hb hD hs
    (fun j _ => hmatching j) hfree hload hweight
  have hc : Function.Injective (fun e => (f e).val) :=
    Subtype.val_injective.comp f.injective
  refine ⟨f, ?_, starExtended_disjoint C A _ hdisjoint hAC,
    starExtended_cover C A _, classes_subset_starExtended C A _,
    starExtended_card_le C A _ hc, starExtended_support_card_le G C A _ hc, ?_⟩
  · exact starExtended_isMatching G C A _ hc z
      (fun e he => (mem_filter.mp (hA he)).2.1) hmatching
      (fun e => hfree _ (f e).property) (fun e => (hf e).1)
  · intro j hj
    apply starExtended_eq_of_color_avoided C A _ j
    intro e he
    exact hj (he ▸ (f e).property)

/-- The global-load version follows by restricting to the available palette. -/
theorem exists_star_extension (G : Multigraph V E)
    (C : Fin h → Finset E) (z : V) (U : Finset V)
    (A : Finset E) (F : Finset (Fin h)) (D b s : ℕ)
    (hA : A ⊆ AssignedParts.exceptionCorePool G z U)
    (hcard : A.card = F.card) (hlower : h - s - D ≤ A.card)
    (hb : b ≤ D) (hD : 128 * D ≤ h) (hs : 2 * s ≤ h)
    (hmatching : ∀ j, G.IsMatching (C j))
    (hdisjoint : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hAC : ∀ j, Disjoint A (C j))
    (hfree : ∀ j ∈ F, z ∉ G.edgeSupport (C j))
    (hload : ∀ v ∈ U, (univ.filter (fun j => v ∈ G.edgeSupport (C j))).card ≤ D + b)
    (hweight : ∀ j ∈ F, WeightedPalette.starWeight G z U (C j) ≤ h / 8 + b) :
    ∃ f : A ≃ F,
      let B := starExtendedClasses C A (fun e => (f e).val)
      (∀ j, G.IsMatching (B j)) ∧
      Pairwise (fun i j => Disjoint (B i) (B j)) ∧
      univ.biUnion B = univ.biUnion C ∪ A ∧
      (∀ j, C j ⊆ B j) ∧
      (∀ j, (B j).card ≤ (C j).card + 1) ∧
      (∀ j, (G.edgeSupport (B j)).card ≤ (G.edgeSupport (C j)).card + 2) ∧
      (∀ j ∉ F, B j = C j) := by
  apply exists_star_extension_on_available G C z U A F D b s hA hcard hlower hb hD hs
    hmatching hdisjoint hAC hfree _ hweight
  intro v hv
  exact (card_le_card (filter_subset_filter _ (subset_univ F))).trans (hload v hv)

omit [Fintype E] in
/-- The construction retains the exact chosen original copy at its color. -/
theorem starExtended_contains_assigned_copy (C : Fin h → Finset E) (A : Finset E)
    (c : A → Fin h) (e : A) : e.val ∈ starExtendedClasses C A c (c e) :=
  mem_union_right _ (coloredStarCopies_contains A c e)

omit [Fintype E] in
/-- Every available color covers the star center after the bijective choice. -/
theorem starExtended_covers_available (G : Multigraph V E)
    (C : Fin h → Finset E) (A : Finset E) (F : Finset (Fin h)) (f : A ≃ F)
    (z : V) (hA : ∀ e ∈ A, z ∈ G.edge e) (j : Fin h) (hj : j ∈ F) :
    z ∈ G.edgeSupport (starExtendedClasses C A (fun e => (f e).val) j) := by
  let e := f.symm ⟨j, hj⟩
  have he : (f e).val = j := congrArg Subtype.val (f.apply_symm_apply ⟨j, hj⟩)
  apply (G.mem_edgeSupport _ z).mpr
  refine ⟨e.val, ?_, hA _ e.property⟩
  rw [← he]
  exact starExtended_contains_assigned_copy C A _ e

end Overfull.NativeStar
