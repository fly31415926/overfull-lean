import Overfull.NativeWeighted.TwoPairNative
import Overfull.NativeAssembly.TwoPairStarReserve
import Overfull.NativeAssembly.TwoPairBounds
import Overfull.AssignedParts.TwoPairOneStar
import Overfull.NativeCore.TwoPairParity
import Overfull.NativeCore.Coverage

/-!
# Complete native external assembly in the two-pair branch

The original matching and the five-exception bound construct either two
pairs alone or two pairs and one assigned-core star.  Actual retained core
degrees and the partner reserve construct the weighted joining palette,
the protected classes, and the entire exceptional extension.  No palette,
trace, star weight, or exceptional case split is supplied as an input.

The safe regular reserve-avoiding residual and its core/numerical budgets
remain the input to this external-assembly theorem.  Completing its classes
inside robust cores and factoring the terminal remainder are later steps.
-/

noncomputable section

namespace Overfull.NativeCore

open Finset Classical NativeReserve AssignedParts FourOdd WeightedPalette
  NativeWeighted NativeAssembly SmallCuts

variable {V E J : Type*} [Fintype V] [Fintype E]

set_option maxHeartbeats 1000000 in
/-- Construct the complete external matching family for two exceptional
pairs and at most one further exception, directly from the native residual
and retained cores.  All original joining and exceptional copies occur
exactly once, every exception is saturated in every color, selected whole
boundaries retain their original reserve indices, and the original cores
have even uncovered sets and their true core-deficit load bounds. -/
theorem exists_native_two_pair_external_palette
    (G : Multigraph V E) (U₀ U₁ Z : Finset V) {M : Finset E} {r : ℕ}
    (Q : PartnerBoundaryPacking G U₀ U₁ Z M r) (hM : G.IsPerfectMatching M)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 5)
    (e₀ e₁ : E) (he : e₀ ≠ e₁) (hpair : G.internalOn M Z = {e₀,e₁})
    (N : J → Finset E) (T : Finset J)
    (havoid : ∀ j ∈ T, Disjoint (N j) (removedCopies Q.boundary univ))
    {h D L t : ℕ} (hregular : ∀ v, (residualGraph G N T).degree v = h)
    (hno : ∀ X : Finset V, ¬ (residualGraph G N T).IsOverfull h X)
    (C₀ : Core (residualGraph G N T) U₀) (C₁ : Core (residualGraph G N T) U₁)
    (hcore₀ : ∀ v, (h : ℝ)-D ≤ (C₀.graph.degree v : ℝ))
    (hcore₁ : ∀ v, (h : ℝ)-D ≤ (C₁.graph.degree v : ℝ))
    (herror : h ≤ r+D) (q : Fin t → Fin r) (hq : Function.Injective q)
    (hh : 0 < h) (hDh : 128*D ≤ h) (ht : 2*t ≤ h) (hL : 0 < L)
    (hbudget : Fintype.card V*D ≤ 2*L*(h-t-40*D)) :
    let H := residualGraph G N T
    let label := twoPairAssignedLabel G M U₀ U₁ Z e₀
    ∃ (f : Fin t → Fin h) (F : Fin h → Finset {e : E // e ∉ removedCopies N T}),
      Function.Injective f ∧
      (∀ j, H.IsMatching (F j)) ∧
      Pairwise (fun i j => Disjoint (F i) (F j)) ∧
      (∀ i, F (f i) = Q.residualBoundary N T (q i)) ∧
      (∀ j, Z ⊆ H.edgeSupport (F j)) ∧
      (∀ j, Even (U₀ \ H.edgeSupport (F j)).card ∧
        Even (U₁ \ H.edgeSupport (F j)).card) ∧
      univ.biUnion F = joiningCopies H label ∪ exceptionalCopies H univ Z ∧
      (∀ j i, (H.cutOn (F j) (labelShore label {i})).card % 2 =
        (univ.filter (fun v => label v=i)).card % 2) ∧
      (∀ j, (F j).card ≤ 6*L+3) ∧
      (∀ j, (H.edgeSupport (F j)).card ≤ 12*L+6) ∧
      (∀ j, Disjoint (F j) (OneCore.coreEdges C₀)) ∧
      (∀ j, Disjoint (F j) (OneCore.coreEdges C₁)) ∧
      (∀ v : U₀, (univ.filter (fun j => v.val ∈ H.edgeSupport (F j))).card ≤ D) ∧
      (∀ v : U₁, (univ.filter (fun j => v.val ∈ H.edgeSupport (F j))).card ≤ D) := by
  let H := residualGraph G N T
  let label := twoPairAssignedLabel G M U₀ U₁ Z e₀
  let p := fun i : Fin 4 => (univ.filter (fun v => label v=i)).card % 2
  have hlabel₀ : ∀ v ∈ U₀, label v = 0 :=
    fun v hv => twoPairAssignedLabel_on_core₀ G M U₀ U₁ Z e₀ hv
  have hlabel₁ : ∀ v ∈ U₁, label v = 1 :=
    fun v hv => twoPairAssignedLabel_on_core₁ G (hM.isMatching G) U₀ U₁ Z h01 h0Z h1Z e₀ hv
  suffices hex : ∃ (C : JoiningPalette H label h D (2*L) p)
      (f : Fin t → Fin h) (F : Fin h → Finset {e : E // e ∉ removedCopies N T}),
      Function.Injective f ∧ (∀ j, H.IsMatching (F j)) ∧
      Pairwise (fun i j => Disjoint (F i) (F j)) ∧
      (∀ i, F (f i) = Q.residualBoundary N T (q i)) ∧
      (∀ j, Z ⊆ H.edgeSupport (F j)) ∧
      (∀ j i, H.cutOn (F j) (labelShore label {i}) = H.cutOn (C.classes j) (labelShore label {i})) ∧
      (∀ j, (F j).card ≤ 6*L+3) ∧
      (∀ j, (H.edgeSupport (F j)).card ≤ 12*L+6) ∧
      univ.biUnion F = joiningCopies H label ∪ exceptionalCopies H univ Z by
    obtain ⟨C,f,F,hf,hm,hd,hpres,hcovers,hcuts,hcard,hsupport,hcov⟩ := hex
    have hsub (j : Fin h) : F j ⊆ joiningCopies H label ∪ exceptionalCopies H univ Z := by
      intro e heF
      rw [← hcov]
      exact mem_biUnion.mpr ⟨j,mem_univ _,heF⟩
    have heven := old_core_parity_of_twoPair_joining_cuts G H hM U₀ U₁ Z
      h01 h0Z h1Z hcover e₀ e₁ he hpair C F hm hcovers hcuts
    refine ⟨f,F,hf,hm,hd,hpres,hcovers,heven,hcov,?_,hcard,hsupport,?_,?_,?_,?_⟩
    · intro j i
      rw [hcuts j i,C.cut_parity j i]
    · intro j
      exact (joining_exceptional_disjoint_core H label U₀ Z C₀ h0Z 0 hlabel₀).mono_left (hsub j)
    · intro j
      exact (joining_exceptional_disjoint_core H label U₁ Z C₁ h1Z 1 hlabel₁).mono_left (hsub j)
    · intro v
      have hload := external_family_load_le_error H label U₀ Z C₀ h0Z 0 hlabel₀ h D
        hregular hcore₀ F hd hsub v
      exact_mod_cast hload
    · intro v
      have hload := external_family_load_le_error H label U₁ Z C₁ h1Z 1 hlabel₁ h D
        hregular hcore₁ F hd hsub v
      exact_mod_cast hload
  have hfibers := twoPairAssignedLabel_fibers G hM U₀ U₁ Z
    h01 h0Z h1Z hcover e₀ e₁ he hpair
  rcases twoPair_zero_or_one_star_geometry G hM U₀ U₁ Z h01 h0Z h1Z hcover hZ
      e₀ e₁ he hpair with hnone | ⟨z,hzZ,_hzPair,hZeq,hstar⟩
  · have hbudget' : Fintype.card V*D ≤ 2*L*(h-8*D-t) :=
      hbudget.trans (Nat.mul_le_mul_left (2*L) (by omega))
    obtain ⟨C,f,hf,B,hpres⟩ := exists_partner_twoPair_protected_completion_of_core_degrees
      Q hM h01 h0Z h1Z hcover e₀ e₁ he hpair hnone N T havoid
      hregular hno C₀ C₁ hcore₀ hcore₁ herror q hq hL (by omega) hbudget'
    have hcovers (j : Fin h) : Z ⊆ H.edgeSupport (B.classes j) := by
      simpa only [hnone] using B.covers j
    have hsub (j : Fin h) : B.classes j ⊆ joiningCopies H label ∪ exceptionalCopies H univ Z := by
      intro e heB
      have hall : e ∈ joiningCopies H label ∪ H.internalOn univ (exceptionalPairPart G e₀) ∪
          H.internalOn univ (exceptionalPairPart G e₁) := by
        rw [← B.cover]
        exact mem_biUnion.mpr ⟨j,mem_univ _,heB⟩
      rcases mem_union.mp hall with hj | hi
      · rcases mem_union.mp hj with hj | hi
        · exact mem_union_left _ hj
        · apply mem_union_right
          apply (mem_exceptionalCopies H univ Z e).mpr
          refine ⟨mem_univ _,Or.inl ?_⟩
          rw [hnone]
          exact mem_union_left _ (mem_filter.mp hi).2.1
      · apply mem_union_right
        apply (mem_exceptionalCopies H univ Z e).mpr
        refine ⟨mem_univ _,Or.inl ?_⟩
        rw [hnone]
        exact mem_union_right _ (mem_filter.mp hi).2.1
    have hjoining : joiningCopies H label ⊆ univ.biUnion B.classes := by
      intro e heJ
      rw [← C.cover] at heJ
      obtain ⟨j,_,hj⟩ := mem_biUnion.mp heJ
      exact mem_biUnion.mpr ⟨j,mem_univ _,B.contains_joining j hj⟩
    have hcov := external_union_eq_of_saturation H label h B.classes Z B.disjoint
      (fun v _ => hregular v) hcovers hjoining hsub
    refine ⟨C,f,B.classes,hf,B.matching,B.disjoint,hpres,hcovers,B.cut_eq,?_,?_,hcov⟩
    · intro j
      have hbound := B.card_le j
      omega
    · intro j
      have hbound := B.support_card_le j
      omega
  · obtain ⟨C,f,hf,hweight,htrace⟩ := exists_native_twoPair_weighted_protected_palette
      G U₀ U₁ Z Q hM h01 h0Z h1Z hcover e₀ e₁ he hpair N T havoid
      hregular hno C₀ C₁ hcore₀ hcore₁ herror q hq
      (fun _ : Fin 1 => (⟨z,hzZ⟩ : Z)) (by decide) hh hDh ht hL hbudget
    let a₀ : G.internalOn M Z := ⟨e₀,by rw [hpair]; exact mem_insert_self _ _⟩
    let a₁ : G.internalOn M Z := ⟨e₁,by rw [hpair]; exact mem_insert_of_mem (mem_singleton_self _)⟩
    have hp₂ : p 2 = 0 := by
      change (univ.filter (fun v => label v=2)).card % 2 = 0
      have hs : labelShore label {2} = exceptionalPairPart G e₀ := hfibers.2.2.1
      change (labelShore label {2}).card % 2 = 0
      rw [hs,exceptionalPairPart_card]
    have hp₃ : p 3 = 0 := by
      change (labelShore label {3}).card % 2 = 0
      rw [hfibers.2.2.2,exceptionalPairPart_card]
    have hstarcase : ∃ U : Finset V,
        label z ≠ 2 ∧ label z ≠ 3 ∧ labelShore label {label z} = insert z U ∧
        ∀ j, starWeight H z U (C.classes j) ≤ h/8 := by
      rcases hstar with ⟨hz0,hfiber,_⟩ | ⟨hz1,hfiber,_⟩
      · refine ⟨U₀,by rw [hz0]; decide,by rw [hz0]; decide,?_,?_⟩
        · simpa only [hz0] using hfiber
        · intro j
          exact (starWeight_mono_core H z U₀ (U₀ ∪ U₁) subset_union_left (C.classes j)).trans
            (hweight 0 j)
      · refine ⟨U₁,by rw [hz1]; decide,by rw [hz1]; decide,?_,?_⟩
        · simpa only [hz1] using hfiber
        · intro j
          exact (starWeight_mono_core H z U₁ (U₀ ∪ U₁) subset_union_right (C.classes j)).trans
            (hweight 0 j)
    obtain ⟨U,hz₂,hz₃,hstarfiber,hstarweight⟩ := hstarcase
    obtain ⟨F,hm,hd,hcov,_hsub,hpres,hcovers,hcuts,hcard,hsupport⟩ :=
      exists_partner_two_pair_star_completion Q hM a₀ a₁ ⟨z,hzZ⟩ U hZeq N T havoid
        C 2 3 (by decide) hfibers.2.2.1 hfibers.2.2.2 hp₂ hp₃ hz₂ hz₃ hstarfiber
        0 1 (by decide) h01 hlabel₀ hlabel₁ hregular q f hq hf htrace hDh
        (by simpa only [Fintype.card_fin] using ht) hstarweight
    refine ⟨C,f,F,hf,hm,hd,hpres,hcovers,hcuts,?_,?_,hcov⟩
    · intro j
      have hbound := hcard j
      have hmax : max (3*(2*L)+2) (Z.card+1) = 6*L+2 := by omega
      rw [hmax] at hbound
      exact hbound
    · intro j
      have hbound := hsupport j
      have hmax : max (3*(2*L)+2) (Z.card+1) = 6*L+2 := by omega
      rw [hmax] at hbound
      omega

end Overfull.NativeCore
