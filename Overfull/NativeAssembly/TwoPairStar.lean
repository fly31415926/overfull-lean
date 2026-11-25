import Overfull.NativeAssembly.TwoPairStarBase

/-!
# Complete a separate assigned-core star together with two exceptional pairs

The remaining star/free-color balance follows from the actual degree and
incidence partition.  A single additional vertex in an assigned core fiber
supplies that partition, irrespective of the other four exceptional vertices.
Hall extension then completes every original star copy while preserving both
pair pools and every whole protected boundary.
-/

noncomputable section

namespace Overfull.NativeAssembly

open Finset Classical AssignedParts FourOdd NativeReserve NativeStar WeightedPalette
open scoped BigOperators

variable {V E I K : Type*} [Fintype V] [Fintype E] [Fintype I] [DecidableEq K]
    {G : Multigraph V E} {label : V → K} {h D L d : ℕ} {p : K → ℕ}
    {C : JoiningPalette G label h D L p} {U₀ U₁ : Finset V}
    {R : I → Finset E} {f : I → Fin h}

omit [Fintype V] in
/-- At a vertex of degree equal to the palette size, the uncolored actual
incidences and free colors have equal cardinality.  The supplied star may
already have some copies in the matching family. -/
theorem matching_family_remaining_star_balance (G : Multigraph V E)
    (F : Fin h → Finset E) (hm : ∀ j, G.IsMatching (F j))
    (hd : Pairwise (fun j k => Disjoint (F j) (F k)))
    (z : V) (S : Finset E) (hS : ∀ e ∈ S, z ∈ G.edge e)
    (hinc : ∀ e, z ∈ G.edge e → e ∈ univ.biUnion F ∨ e ∈ S)
    (hdegree : G.degree z = h) :
    (S \ univ.biUnion F).card =
      (univ.filter (fun j => z ∉ G.edgeSupport (F j))).card := by
  have hused : (univ.filter (fun j => z ∈ G.edgeSupport (F j))).card =
      G.degreeOn (univ.biUnion F) z := by
    have hone (j : Fin h) : G.degreeOn (F j) z =
        if z ∈ G.edgeSupport (F j) then 1 else 0 := by
      split_ifs with hz
      · have hlo := (G.degreeOn_pos_iff (F j) z).mpr hz
        have hhi := (G.isMatching_iff_incident_card_le_one _).mp (hm j) z
        change G.degreeOn (F j) z ≤ 1 at hhi
        omega
      · exact G.degreeOn_eq_zero_of_not_mem hz
    have hsum := removed_degreeOn G F univ (fun _ _ _ _ hij => hd hij) z
    change G.degreeOn (univ.biUnion F) z = _ at hsum
    simp only [hone, sum_boole] at hsum
    exact hsum.symm
  have heq : G.incidenceEdges z =
      ((univ.biUnion F).filter (fun e => z ∈ G.edge e)) ∪ (S \ univ.biUnion F) := by
    ext e
    simp only [Multigraph.mem_incidenceEdges, mem_union, mem_filter, mem_sdiff]
    constructor
    · intro he
      by_cases hF : e ∈ univ.biUnion F
      · exact Or.inl ⟨hF, he⟩
      · exact Or.inr ⟨(hinc e he).resolve_left hF, hF⟩
    · rintro (⟨_, he⟩ | ⟨he, _⟩)
      · exact he
      · exact hS e he
  have hdis : Disjoint ((univ.biUnion F).filter (fun e => z ∈ G.edge e))
      (S \ univ.biUnion F) := by
    apply disjoint_left.mpr
    intro e he hf
    exact (mem_sdiff.mp hf).2 (mem_filter.mp he).1
  have hdeg : G.degreeOn (univ.biUnion F) z + (S \ univ.biUnion F).card = h := by
    calc
      _ = G.degree z := by
        rw [Multigraph.degree, heq, card_union_of_disjoint hdis]
        rfl
      _ = h := hdegree
  have hc := filter_card_add_filter_neg_card_eq_card
    (s := (univ : Finset (Fin h))) (fun j => z ∈ G.edgeSupport (F j))
  rw [card_univ, Fintype.card_fin, hused] at hc
  omega

/-- One additional vertex in an assigned core fiber has no same-label
exceptional bundle: every incident copy is joining or goes to that core. -/
theorem single_added_fiber_star_incidence (z : V) (U : Finset V)
    (hfiber : labelShore label {label z} = insert z U) :
    (∀ e, z ∈ G.edge e → e ∈ joiningCopies G label ∨ e ∈ exceptionCorePool G z U) ∧
    ∀ e ∈ exceptionCorePool G z U, label (G.firstEnd e) = label (G.secondEnd e) := by
  have hlabel (v : V) (hv : v ∈ U) : label v = label z := by
    have hm : v ∈ labelShore label {label z} := hfiber.symm ▸ mem_insert_of_mem hv
    simpa only [mem_labelShore, mem_singleton] using hm
  constructor
  · intro e he
    by_cases hj : e ∈ joiningCopies G label
    · exact Or.inl hj
    · apply Or.inr
      have hs : label (G.otherEnd z e) = label z :=
        not_ne_iff.mp (fun hn => hj ((joining_iff_otherEnd_label_ne G label z e he).mpr hn))
      have ho : G.otherEnd z e ∈ insert z U := by
        rw [← hfiber]
        simpa only [mem_labelShore, mem_singleton] using hs
      have hU : G.otherEnd z e ∈ U :=
        (mem_insert.mp ho).resolve_left (G.otherEnd_ne z e he)
      exact mem_filter.mpr ⟨mem_univ _, he, hU⟩
  · intro e he
    have hz := (mem_filter.mp he).2.1
    have ho := hlabel _ (mem_filter.mp he).2.2
    have hn : e ∉ joiningCopies G label := by
      intro hj
      exact (joining_iff_otherEnd_label_ne G label z e hz).mp hj ho
    exact not_ne_iff.mp (fun hne => hn ((mem_joiningCopies G label e).mpr hne))

theorem noBundleColors_card_lower (C : JoiningPalette G label h D L p)
    (f : I → Fin h) (z : V) :
    h - Fintype.card I - D ≤ (noBundleColors C f z).card := by
  have hQ : (univ.image f).card ≤ Fintype.card I := by
    simpa only [card_univ] using card_image_le (s := (univ : Finset I)) (f := f)
  have hJ : (joiningUsedColors C z).card ≤ D := C.vertex_load_le z
  have hu := card_union_le (univ.image f) (joiningUsedColors C z)
  unfold noBundleColors remainingStarColors
  rw [union_empty, card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin]
  omega

theorem pairReserveClasses_available_support_iff (P : ReserveExtension C R f d)
    (B : TwoPairFiberCompletion C U₀ U₁) (z v : V)
    (hv : v ∉ U₀ ∪ U₁) (j : Fin h) (hj : j ∈ noBundleColors C f z) :
    v ∈ G.edgeSupport (pairReserveClasses P B j) ↔ v ∈ G.edgeSupport (C.classes j) := by
  rw [pairReserveClasses_support_outside_iff P B j v hv,
    reserve_eq_on_noBundleColors P z j hj]

theorem pairReserveClasses_available_weight_eq (P : ReserveExtension C R f d)
    (B : TwoPairFiberCompletion C U₀ U₁) (z : V) (U : Finset V)
    (hU : Disjoint U (U₀ ∪ U₁)) (j : Fin h) (hj : j ∈ noBundleColors C f z) :
    starWeight G z U (pairReserveClasses P B j) = starWeight G z U (C.classes j) := by
  unfold starWeight
  congr 1
  ext e
  simp only [mem_starBlockedCopies]
  constructor <;> rintro ⟨he, hv⟩ <;> refine ⟨he, ?_⟩
  · exact (pairReserveClasses_available_support_iff P B z _
      (fun ho => disjoint_left.mp hU (mem_filter.mp he).2.2 ho) j hj).mp hv
  · exact (pairReserveClasses_available_support_iff P B z _
      (fun ho => disjoint_left.mp hU (mem_filter.mp he).2.2 ho) j hj).mpr hv

set_option maxHeartbeats 800000 in
/-- Complete one assigned-core star alongside two completed pair pools.
The actual degree and single-added-vertex fiber derive the copy/color balance;
no global singleton assumption on the exceptional set is used. -/
theorem exists_two_pair_star_extension
    (P : ReserveExtension C R f d) (B : TwoPairFiberCompletion C U₀ U₁)
    (hprotected : ∀ i, B.classes (f i) ⊆ R i)
    (z : V) (U : Finset V) (hz : z ∉ U₀ ∪ U₁) (hU : Disjoint U (U₀ ∪ U₁))
    (hfiber : labelShore label {label z} = insert z U)
    (hdegree : G.degree z = h) (hreserve : ∀ i, z ∈ G.edgeSupport (R i))
    (hD : 128*D ≤ h) (hs : 2*Fintype.card I ≤ h)
    (hweight : ∀ j, starWeight G z U (C.classes j) ≤ h/8) :
    ∃ F : Fin h → Finset E,
      (∀ j, G.IsMatching (F j)) ∧
      Pairwise (fun j k => Disjoint (F j) (F k)) ∧
      univ.biUnion F = joiningCopies G label ∪ G.internalOn univ U₀ ∪
        G.internalOn univ U₁ ∪ univ.biUnion R ∪ exceptionCorePool G z U ∧
      (∀ j, C.classes j ⊆ F j) ∧
      (∀ i, F (f i) = R i) ∧
      (∀ j, U₀ ∪ U₁ ∪ {z} ⊆ G.edgeSupport (F j)) ∧
      (∀ j k, G.cutOn (F j) (labelShore label {k}) =
        G.cutOn (C.classes j) (labelShore label {k})) ∧
      (∀ j, (F j).card ≤ max (3*L+2) d + 1) ∧
      (∀ j, (G.edgeSupport (F j)).card ≤ 2*max (3*L+2) d + 2) := by
  let T := pairReserveClasses P B
  let S := exceptionCorePool G z U
  let A := S \ univ.biUnion T
  let Q := noBundleColors C f z
  have hm : ∀ j, G.IsMatching (T j) := pairReserveClasses_matching P B hprotected
  have hd : Pairwise (fun j k => Disjoint (T j) (T k)) := pairReserveClasses_disjoint P B hprotected
  have hstar := single_added_fiber_star_incidence (G := G) z U hfiber
  have hincS : ∀ e ∈ S, z ∈ G.edge e := fun e he => (mem_filter.mp he).2.1
  have hinc : ∀ e, z ∈ G.edge e → e ∈ univ.biUnion T ∨ e ∈ S := by
    intro e he
    rcases hstar.1 e he with heJ | heS
    · apply Or.inl
      rw [pairReserveClasses_cover P B]
      exact mem_union_left _ (mem_union_left _ (mem_union_left _ heJ))
    · exact Or.inr heS
  have hfree (j : Fin h) (hj : j ∈ Q) : z ∉ G.edgeSupport (T j) := by
    intro hzT
    have hzC := (pairReserveClasses_available_support_iff P B z z hz j hj).mp hzT
    exact ((mem_remainingStarColors _ _ _ _).mp hj).2.1
      ((mem_joiningUsedColors C z j).mpr hzC)
  have hcovered (j : Fin h) (hj : j ∉ Q) : z ∈ G.edgeSupport (T j) := by
    obtain ⟨e, he, hze⟩ := (G.mem_edgeSupport _ z).mp
      (reserve_covers_not_noBundleColors P z hreserve j hj)
    exact (G.mem_edgeSupport _ z).mpr ⟨e, mem_union_left _ he, hze⟩
  have hQ : Q = univ.filter (fun j => z ∉ G.edgeSupport (T j)) := by
    ext j
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · exact hfree j
    · intro hj
      by_contra hn
      exact hj (hcovered j hn)
  have hcard : A.card = Q.card := by
    rw [hQ]
    exact matching_family_remaining_star_balance G T hm hd z S hincS hinc hdegree
  have hlower : h - Fintype.card I - D ≤ A.card := by
    rw [hcard]
    exact noBundleColors_card_lower C f z
  have hAC : ∀ j, Disjoint A (T j) := by
    intro j
    apply disjoint_left.mpr
    intro e heA heT
    exact (mem_sdiff.mp heA).2 (mem_biUnion.mpr ⟨j, mem_univ _, heT⟩)
  have hload (v : V) (hv : v ∈ U) :
      (Q.filter (fun j => v ∈ G.edgeSupport (T j))).card ≤ D := by
    apply (card_le_card (show _ ⊆ univ.filter
      (fun j => v ∈ G.edgeSupport (C.classes j)) from ?_)).trans (C.vertex_load_le v)
    intro j hj
    obtain ⟨hjQ, hvT⟩ := mem_filter.mp hj
    exact mem_filter.mpr ⟨mem_univ _, (pairReserveClasses_available_support_iff P B z v
      (fun hpair => disjoint_left.mp hU hv hpair) j hjQ).mp hvT⟩
  have hwt (j : Fin h) (hj : j ∈ Q) : starWeight G z U (T j) ≤ h/8 := by
    rw [pairReserveClasses_available_weight_eq P B z U hU j hj]
    exact hweight j
  obtain ⟨g, hFm, hFd, hFcov, hFsub, hFc, hFs, hFother⟩ :=
    exists_star_extension_on_available G T z U A Q D 0 (Fintype.card I)
      sdiff_subset hcard hlower (Nat.zero_le _) hD hs hm hd hAC hfree
      (by simpa only [Nat.add_zero] using hload)
      (by simpa only [Nat.add_zero] using hwt)
  let F := starExtendedClasses T A (fun e => (g e).val)
  refine ⟨F, hFm, hFd, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hFcov]
    have heq : univ.biUnion T ∪ A = univ.biUnion T ∪ S := by
      ext e
      simp only [A, mem_union, mem_sdiff]
      tauto
    rw [heq, pairReserveClasses_cover P B]
  · intro j e he
    exact hFsub j (mem_union_left _ (P.contains_original j he))
  · intro i
    have hi : f i ∉ Q := by
      intro hi
      exact ((mem_remainingStarColors _ _ _ _).mp hi).1 (mem_image_of_mem f (mem_univ i))
    exact (hFother _ hi).trans (pairReserveClasses_prescribed P B hprotected i)
  · intro j v hv
    rcases mem_union.mp hv with hvPair | hvz
    · obtain ⟨e, he, hve⟩ := (G.mem_edgeSupport _ v).mp (pairReserveClasses_covers P B j hvPair)
      exact (G.mem_edgeSupport _ v).mpr ⟨e, hFsub j he, hve⟩
    · rw [mem_singleton] at hvz
      subst v
      by_cases hj : j ∈ Q
      · exact starExtended_covers_available G T A Q g z (fun e he => hincS e (mem_sdiff.mp he).1) j hj
      · obtain ⟨e, he, hze⟩ := (G.mem_edgeSupport _ z).mp (hcovered j hj)
        exact (G.mem_edgeSupport _ z).mpr ⟨e, hFsub j he, hze⟩
  · intro j k
    exact (starExtended_cut_eq G label T A _
      (fun e he => hstar.2 e (mem_sdiff.mp he).1) j k).trans (pairReserveClasses_cut_eq P B j k)
  · intro j
    exact (hFc j).trans (Nat.add_le_add_right (pairReserveClasses_card_le P B hprotected j) 1)
  · intro j
    exact (hFs j).trans (Nat.add_le_add_right (pairReserveClasses_support_card_le P B hprotected j) 2)

set_option maxHeartbeats 800000 in
/-- Construct the complete pair-and-star assembler from one joining palette
and the actual reserved boundaries.  Pair colorings, reserve insertion, the
remaining-star balance, and the matching extension are all constructed.
The explicit star-weight and numerical bounds remain inputs. -/
theorem exists_reserved_two_pair_star_completion
    (C : JoiningPalette G label h D L p) (k₀ k₁ : K) (hk : k₀ ≠ k₁)
    (U₀ U₁ : Finset V) (hcard₀ : U₀.card = 2) (hcard₁ : U₁.card = 2)
    (hfiber₀ : labelShore label {k₀} = U₀)
    (hfiber₁ : labelShore label {k₁} = U₁)
    (hp₀ : p k₀ = 0) (hp₁ : p k₁ = 0)
    (hregular₀ : ∀ v ∈ U₀, G.degree v = h)
    (hregular₁ : ∀ v ∈ U₁, G.degree v = h)
    (R : I → Finset E) (hR : ∀ i, G.IsMatching (R i))
    (hRd : Pairwise (fun i j => Disjoint (R i) (R j)))
    (hRcard : ∀ i, (R i).card ≤ d)
    (f : I → Fin h) (hf : Function.Injective f)
    (g₀ : I → G.internalOn univ U₀) (g₁ : I → G.internalOn univ U₁)
    (hg₀ : Function.Injective g₀) (hg₁ : Function.Injective g₁)
    (hmem₀ : ∀ i, (g₀ i).val ∈ R i) (hmem₁ : ∀ i, (g₁ i).val ∈ R i)
    (htrace : ∀ i, R i ∩ joiningCopies G label = C.classes (f i))
    (z : V) (U : Finset V) (hz₀ : label z ≠ k₀) (hz₁ : label z ≠ k₁)
    (hstarfiber : labelShore label {label z} = insert z U)
    (hdegree : G.degree z = h) (hreserve : ∀ i, z ∈ G.edgeSupport (R i))
    (hD : 128*D ≤ h) (hs : 2*Fintype.card I ≤ h)
    (hweight : ∀ j, starWeight G z U (C.classes j) ≤ h/8) :
    ∃ F : Fin h → Finset E,
      (∀ j, G.IsMatching (F j)) ∧
      Pairwise (fun j k => Disjoint (F j) (F k)) ∧
      univ.biUnion F = joiningCopies G label ∪ G.internalOn univ U₀ ∪
        G.internalOn univ U₁ ∪ univ.biUnion R ∪ exceptionCorePool G z U ∧
      (∀ j, C.classes j ⊆ F j) ∧
      (∀ i, F (f i) = R i) ∧
      (∀ j, U₀ ∪ U₁ ∪ {z} ⊆ G.edgeSupport (F j)) ∧
      (∀ j k, G.cutOn (F j) (labelShore label {k}) =
        G.cutOn (C.classes j) (labelShore label {k})) ∧
      (∀ j, (F j).card ≤ max (3*L+2) d + 1) ∧
      (∀ j, (G.edgeSupport (F j)).card ≤ 2*max (3*L+2) d + 2) := by
  obtain ⟨B, _hseed₀, _hseed₁, _hclass, hprotected⟩ :=
    exists_reserved_two_pair_completion_with_extra C k₀ k₁ hk U₀ U₁ hcard₀ hcard₁
      hfiber₀ hfiber₁ hp₀ hp₁ hregular₀ hregular₁ R hR f hf
      g₀ g₁ hg₀ hg₁ hmem₀ hmem₁ htrace
  let P : ReserveExtension C R f d := reserveExtension C R f hf hR hRd htrace hRcard
  have hz : z ∉ U₀ ∪ U₁ := by
    intro hz
    rcases mem_union.mp hz with hz | hz
    · rw [← hfiber₀] at hz
      exact hz₀ (by simpa only [mem_labelShore, mem_singleton] using hz)
    · rw [← hfiber₁] at hz
      exact hz₁ (by simpa only [mem_labelShore, mem_singleton] using hz)
  have hU : Disjoint U (U₀ ∪ U₁) := by
    apply disjoint_left.mpr
    intro v hv hp
    have hl : label v = label z := by
      have hm : v ∈ labelShore label {label z} := hstarfiber.symm ▸ mem_insert_of_mem hv
      simpa only [mem_labelShore, mem_singleton] using hm
    rcases mem_union.mp hp with hp | hp
    · rw [← hfiber₀] at hp
      have hk' : label v = k₀ := by simpa only [mem_labelShore, mem_singleton] using hp
      exact hz₀ (hl.symm.trans hk')
    · rw [← hfiber₁] at hp
      have hk' : label v = k₁ := by simpa only [mem_labelShore, mem_singleton] using hp
      exact hz₁ (hl.symm.trans hk')
  exact exists_two_pair_star_extension P B hprotected z U hz hU hstarfiber
    hdegree hreserve hD hs hweight

end Overfull.NativeAssembly
