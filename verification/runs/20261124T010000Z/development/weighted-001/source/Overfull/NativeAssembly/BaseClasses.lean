import Overfull.NativeStar.NativeBalance
import Overfull.NativeStar.TwoStars
import Overfull.ExceptionalPalette.ReserveInsertion

/-!
# Reserved classes with their actual internal exceptional bundle

The internal bundle is inserted only in colors outside the protected reserve
and the joining colors used at either exceptional endpoint.  Consequently the
actual remaining star palettes see exactly the original joining classes.  The
load and weighted obstruction bounds on those palettes are therefore inherited
without imposing a false global load bound on the protected reserve classes.
-/

noncomputable section

namespace Overfull.NativeAssembly

open Finset Classical AssignedParts FourOdd NativeReserve NativeStar WeightedPalette

variable {V E K I : Type*} [Fintype V] [Fintype E] [Fintype I] [DecidableEq K]
    {G : Multigraph V E} {label : V → K} {h D L b : ℕ} {p : K → ℕ}
    {C : JoiningPalette G label h D L p} {R : I → Finset E} {f : I → Fin h}

/-- Insert each actual internal exceptional copy into its prescribed color. -/
def bundleClasses (P : ReserveExtension C R f b) (B : Finset E)
    (c : B → Fin h) : Fin h → Finset E :=
  starExtendedClasses P.classes B c

/-- Outside protected colors, the actual reserve extension is the original
joining class, independently of the size of the protected boundaries. -/
theorem reserveExtension_eq_of_not_protected (P : ReserveExtension C R f b)
    (j : Fin h) (hj : j ∉ univ.image f) : P.classes j = C.classes j := by
  apply P.unchanged j
  rintro ⟨i, rfl⟩
  exact hj (mem_image_of_mem f (mem_univ i))

/-- A copy internal to its assigned label cannot occur in any joining class. -/
theorem internalCopies_disjoint_joining (B : Finset E)
    (hinternal : ∀ e ∈ B, label (G.firstEnd e) = label (G.secondEnd e)) :
    Disjoint B (joiningCopies G label) := by
  apply disjoint_left.mpr
  intro e he hj
  exact (mem_joiningCopies G label e).mp hj (hinternal e he)

/-- The actual bundle is disjoint from all reserve-extended classes once its
internal copies are absent from the prescribed boundaries. -/
theorem bundle_disjoint_reserveExtension (P : ReserveExtension C R f b)
    (B : Finset E)
    (hinternal : ∀ e ∈ B, label (G.firstEnd e) = label (G.secondEnd e))
    (hBR : ∀ i, Disjoint B (R i)) (j : Fin h) : Disjoint B (P.classes j) := by
  apply disjoint_left.mpr
  intro e heB heP
  have he : e ∈ joiningCopies G label ∪ univ.biUnion R := by
    rw [← P.cover]
    exact mem_biUnion.mpr ⟨j, mem_univ _, heP⟩
  rcases mem_union.mp he with heJ | heR
  · exact disjoint_left.mp (internalCopies_disjoint_joining B hinternal) heB heJ
  · obtain ⟨i, _, hei⟩ := mem_biUnion.mp heR
    exact disjoint_left.mp (hBR i) heB hei

/-- Free joining colors at both endpoints give an actual matching after the
internal bundle is inserted into the whole reserve extension. -/
theorem bundleClasses_matching (P : ReserveExtension C R f b)
    (B : Finset E) (c : B → Fin h) (hc : Function.Injective c) (x y : V)
    (hB : ∀ e ∈ B, G.edge e = s(x,y))
    (hprotected : ∀ e, c e ∉ univ.image f)
    (hfree : ∀ e, c e ∉ joiningUsedColors C x ∧ c e ∉ joiningUsedColors C y)
    (j : Fin h) : G.IsMatching (bundleClasses P B c j) := by
  apply starExtended_isMatching G P.classes B c hc x
  · intro e he
    rw [hB e he]
    simp
  · exact P.matching
  · intro e
    rw [reserveExtension_eq_of_not_protected P (c e) (hprotected e)]
    exact fun hx => (hfree e).1 ((mem_joiningUsedColors C x (c e)).mpr hx)
  · intro e
    rw [G.otherEnd_eq_of_edge e.val x y (hB e.val e.property),
      reserveExtension_eq_of_not_protected P (c e) (hprotected e)]
    exact fun hy => (hfree e).2 ((mem_joiningUsedColors C y (c e)).mpr hy)

theorem bundleClasses_disjoint (P : ReserveExtension C R f b)
    (B : Finset E) (c : B → Fin h)
    (hinternal : ∀ e ∈ B, label (G.firstEnd e) = label (G.secondEnd e))
    (hBR : ∀ i, Disjoint B (R i)) :
    Pairwise (fun i j => Disjoint (bundleClasses P B c i) (bundleClasses P B c j)) :=
  starExtended_disjoint P.classes B c P.disjoint
    (bundle_disjoint_reserveExtension P B hinternal hBR)

/-- Every original joining copy, selected boundary copy and internal bundle
copy occurs in the resulting family. -/
theorem bundleClasses_cover (P : ReserveExtension C R f b)
    (B : Finset E) (c : B → Fin h) :
    univ.biUnion (bundleClasses P B c) =
      joiningCopies G label ∪ univ.biUnion R ∪ B := by
  rw [bundleClasses, starExtended_cover, P.cover]

theorem bundleClasses_contains_reserve (P : ReserveExtension C R f b)
    (B : Finset E) (c : B → Fin h) (j : Fin h) :
    P.classes j ⊆ bundleClasses P B c j := subset_union_left

/-- No protected prescription is altered by insertion of the internal bundle. -/
theorem bundleClasses_prescribed (P : ReserveExtension C R f b)
    (B : Finset E) (c : B → Fin h)
    (hprotected : ∀ e, c e ∉ univ.image f) (i : I) :
    bundleClasses P B c (f i) = R i := by
  change starExtendedClasses P.classes B c (f i) = R i
  rw [starExtended_eq_of_color_avoided]
  · exact P.prescribed i
  · intro e he
    exact hprotected e (he ▸ mem_image_of_mem f (mem_univ i))

/-- An internal bundle leaves all assigned-fiber cut parities unchanged. -/
theorem bundleClasses_cut_parity (P : ReserveExtension C R f b)
    (B : Finset E) (c : B → Fin h)
    (hinternal : ∀ e ∈ B, label (G.firstEnd e) = label (G.secondEnd e))
    (j : Fin h) (k : K) :
    (G.cutOn (bundleClasses P B c j) (labelShore label {k})).card % 2 = p k := by
  rw [bundleClasses, starExtended_cut_eq G label P.classes B c hinternal]
  exact P.cut_parity j k

/-- The original palette is unchanged on the actual remaining colors of a
star: protected, joining-used and bundle-used colors have all been removed. -/
theorem bundleClasses_eq_on_remaining (P : ReserveExtension C R f b)
    (B : Finset E) (c : B → Fin h) (z : V) (j : Fin h)
    (hj : j ∈ remainingStarColors (univ.image f) (joiningUsedColors C z) (univ.image c)) :
    bundleClasses P B c j = C.classes j := by
  obtain ⟨hjQ, _, hjB⟩ := (mem_remainingStarColors _ _ _ j).mp hj
  change starExtendedClasses P.classes B c j = C.classes j
  rw [starExtended_eq_of_color_avoided]
  · exact reserveExtension_eq_of_not_protected P j hjQ
  · intro e he
    exact hjB (he ▸ mem_image_of_mem c (mem_univ e))

/-- Every actual remaining color is free at its exceptional center before
the star is inserted. -/
theorem bundleClasses_free_on_remaining (P : ReserveExtension C R f b)
    (B : Finset E) (c : B → Fin h) (z : V) (j : Fin h)
    (hj : j ∈ remainingStarColors (univ.image f) (joiningUsedColors C z) (univ.image c)) :
    z ∉ G.edgeSupport (bundleClasses P B c j) := by
  rw [bundleClasses_eq_on_remaining P B c z j hj]
  exact fun hz => ((mem_remainingStarColors _ _ _ j).mp hj).2.1
    ((mem_joiningUsedColors C z j).mpr hz)

/-- Available-only vertex loads remain bounded by the joining degree. -/
theorem bundleClasses_available_load_le (P : ReserveExtension C R f b)
    (B : Finset E) (c : B → Fin h) (z v : V) :
    ((remainingStarColors (univ.image f) (joiningUsedColors C z) (univ.image c)).filter
      (fun j => v ∈ G.edgeSupport (bundleClasses P B c j))).card ≤ D := by
  apply (card_le_card (show _ ⊆ univ.filter
    (fun j => v ∈ G.edgeSupport (C.classes j)) from ?_)).trans (C.vertex_load_le v)
  intro j hj
  obtain ⟨hjF,hv⟩ := mem_filter.mp hj
  rw [bundleClasses_eq_on_remaining P B c z j hjF] at hv
  exact mem_filter.mpr ⟨mem_univ _,hv⟩

/-- The actual weighted obstruction is inherited from the original whole
joining class on every color still available to the star. -/
theorem bundleClasses_available_weight_le (P : ReserveExtension C R f b)
    (B : Finset E) (c : B → Fin h) (z : V) (U : Finset V) (W : ℕ)
    (hweight : ∀ j, starWeight G z U (C.classes j) ≤ W) :
    ∀ j ∈ remainingStarColors (univ.image f) (joiningUsedColors C z) (univ.image c),
      starWeight G z U (bundleClasses P B c j) ≤ W := by
  intro j hj
  rw [bundleClasses_eq_on_remaining P B c z j hj]
  exact hweight j

/-- Every unavailable color already covers the center: it is a prescribed
reserve color, a joining-used color, or the color of an incident bundle copy. -/
theorem bundleClasses_covers_not_remaining (P : ReserveExtension C R f b)
    (B : Finset E) (c : B → Fin h) (z : V)
    (hprotected : ∀ e, c e ∉ univ.image f)
    (hreserve : ∀ i, z ∈ G.edgeSupport (R i))
    (hincident : ∀ e ∈ B, z ∈ G.edge e) (j : Fin h)
    (hj : j ∉ remainingStarColors (univ.image f) (joiningUsedColors C z) (univ.image c)) :
    z ∈ G.edgeSupport (bundleClasses P B c j) := by
  have hc : j ∈ univ.image f ∨ j ∈ joiningUsedColors C z ∨ j ∈ univ.image c := by
    simpa only [mem_remainingStarColors, not_and_or, not_not] using hj
  rcases hc with hjQ | hjJ | hjB
  · obtain ⟨i, _, rfl⟩ := mem_image.mp hjQ
    rw [bundleClasses_prescribed P B c hprotected]
    exact hreserve i
  · obtain ⟨e, he, hze⟩ := (G.mem_edgeSupport _ z).mp
      ((mem_joiningUsedColors C z j).mp hjJ)
    exact (G.mem_edgeSupport _ z).mpr
      ⟨e, bundleClasses_contains_reserve P B c j (P.contains_original j he), hze⟩
  · obtain ⟨e, _, rfl⟩ := mem_image.mp hjB
    exact (G.mem_edgeSupport _ z).mpr
      ⟨e.val, starExtended_contains_assigned_copy P.classes B c e,
        hincident e.val e.property⟩

/-- Deleting the prescribed reserve copies from a star leaves it disjoint
from every actual base class. -/
theorem remaining_star_disjoint_bundleClasses (P : ReserveExtension C R f b)
    (B S : Finset E) (c : B → Fin h)
    (hSJ : Disjoint S (joiningCopies G label)) (hSB : Disjoint S B) (j : Fin h) :
    Disjoint (S \ ((univ.biUnion R) ∩ S)) (bundleClasses P B c j) := by
  apply disjoint_left.mpr
  intro e heA heC
  obtain ⟨heS, heR⟩ := mem_sdiff.mp heA
  have he : e ∈ joiningCopies G label ∪ univ.biUnion R ∪ B := by
    rw [← bundleClasses_cover P B c]
    exact mem_biUnion.mpr ⟨j, mem_univ _, heC⟩
  rcases mem_union.mp he with he | heB
  · rcases mem_union.mp he with heJ | heR'
    · exact disjoint_left.mp hSJ heS heJ
    · exact heR (mem_inter.mpr ⟨heR',heS⟩)
  · exact disjoint_left.mp hSB heS heB

theorem bundleClasses_card_le (P : ReserveExtension C R f b)
    (B : Finset E) (c : B → Fin h) (hc : Function.Injective c) (j : Fin h) :
    (bundleClasses P B c j).card ≤ max (3*L) b + 1 :=
  (starExtended_card_le P.classes B c hc j).trans (Nat.add_le_add_right (P.card_le j) 1)

theorem bundleClasses_support_card_le (P : ReserveExtension C R f b)
    (B : Finset E) (c : B → Fin h) (hc : Function.Injective c) (j : Fin h) :
    (G.edgeSupport (bundleClasses P B c j)).card ≤ 2*max (3*L) b + 2 :=
  (starExtended_support_card_le G P.classes B c hc j).trans
    (Nat.add_le_add_right (P.support_card_le j) 2)

end Overfull.NativeAssembly
