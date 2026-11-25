import Overfull.NativeAssembly.TwoPairGeneralProtected
import Overfull.NativeWeighted.FourJoining
import Overfull.NativeCore.Incidence

/-!
# Actual native weighted protected palettes with two exceptional pairs

The retained cores bound both joining degrees and exceptional-to-core
parallel multiplicities. Actual partner-reserve traces give the protected
empty or singleton classes. Weighted grouping then constructs all star
budgets in the full palette, allowing unpaired exceptions in either core.

The reserve-avoiding residual's regularity and no-overfull safety remain
explicit inputs. Neither a weighted palette nor its protected trace is
assumed.
-/

noncomputable section

namespace Overfull.NativeWeighted

open Finset Classical NativeReserve AssignedParts FourOdd WeightedPalette NativeAssembly

variable {V E J κ : Type*} [Fintype V] [Fintype E] [Fintype κ] {r : ℕ}

omit [Fintype V] [Fintype κ] in
/-- Actual retained core deficits bound every exceptional-to-core parallel
bundle by the same integer used for the native joining budget. -/
theorem two_core_exception_parallel_bound
    (H : Multigraph V E) (U₀ U₁ Z : Finset V)
    (C₀ : SmallCuts.Core H U₀) (C₁ : SmallCuts.Core H U₁)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z) (h D : ℕ)
    (hregular : ∀ v, H.degree v = h)
    (hcore₀ : ∀ v, (h : ℝ)-D ≤ (C₀.graph.degree v : ℝ))
    (hcore₁ : ∀ v, (h : ℝ)-D ≤ (C₁.graph.degree v : ℝ)) :
    ∀ z ∈ Z, ∀ v ∈ U₀ ∪ U₁, (H.parallelEdges z v).card ≤ D := by
  intro z hz v hv
  rcases mem_union.mp hv with hv | hv
  · have hb := NativeCore.outside_parallel_le_core_error H U₀ C₀ h D hregular hcore₀
      z (fun hmem => disjoint_left.mp h0Z hmem hz) ⟨v,hv⟩
    exact_mod_cast hb
  · have hb := NativeCore.outside_parallel_le_core_error H U₁ C₁ h D hregular hcore₁
      z (fun hmem => disjoint_left.mp h1Z hmem hz) ⟨v,hv⟩
    exact_mod_cast hb

/-- Construct the native four-label protected palette and all actual
old-core star-weight bounds from the retained cores and partner reserve.
The resource centers are exceptional vertices; extra unpaired exceptions
are allowed and the original reserve indices are retained. -/
theorem exists_native_twoPair_weighted_protected_palette
    (G : Multigraph V E) (U₀ U₁ Z : Finset V) {M : Finset E}
    (Q : PartnerBoundaryPacking G U₀ U₁ Z M r) (hM : G.IsPerfectMatching M)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (e₀ e₁ : E) (he : e₀ ≠ e₁) (hpair : G.internalOn M Z = {e₀,e₁})
    (N : J → Finset E) (T : Finset J)
    (havoid : ∀ j ∈ T, Disjoint (N j) (removedCopies Q.boundary univ))
    {h D L t : ℕ} (hregular : ∀ v, (residualGraph G N T).degree v = h)
    (hno : ∀ X : Finset V, ¬ (residualGraph G N T).IsOverfull h X)
    (C₀ : SmallCuts.Core (residualGraph G N T) U₀)
    (C₁ : SmallCuts.Core (residualGraph G N T) U₁)
    (hcore₀ : ∀ v, (h : ℝ)-D ≤ (C₀.graph.degree v : ℝ))
    (hcore₁ : ∀ v, (h : ℝ)-D ≤ (C₁.graph.degree v : ℝ))
    (herror : h ≤ r+D) (q : Fin t → Fin r) (hq : Function.Injective q)
    (z : κ → Z) (hresources : Fintype.card κ ≤ 2)
    (hh : 0 < h) (hDh : 128*D ≤ h) (ht : 2*t ≤ h) (hL : 0 < L)
    (hbudget : Fintype.card V*D ≤ 2*L*(h-t-40*D)) :
    ∃ C : JoiningPalette (residualGraph G N T) (twoPairAssignedLabel G M U₀ U₁ Z e₀)
      h D (2*L) (fun i => (univ.filter
        (fun v => twoPairAssignedLabel G M U₀ U₁ Z e₀ v = i)).card % 2),
      ∃ f : Fin t → Fin h, Function.Injective f ∧
        (∀ i j, starWeight (residualGraph G N T) (z i).val (U₀ ∪ U₁) (C.classes j) ≤ h/8) ∧
        (∀ i, Q.residualBoundary N T (q i) ∩
          joiningCopies (residualGraph G N T) (twoPairAssignedLabel G M U₀ U₁ Z e₀) =
            C.classes (f i)) := by
  let H := residualGraph G N T
  let label := twoPairAssignedLabel G M U₀ U₁ Z e₀
  have hdegree : ∀ v, H.degreeOn (joiningCopies H label) v ≤ D :=
    partner_twoPair_joining_degree_bound_general Q hM h01 h0Z h1Z hcover e₀ e₁ he hpair
      N T havoid hregular C₀ C₁ hcore₀ hcore₁ herror
  have hparallel : ∀ i, ∀ v ∈ U₀ ∪ U₁, (H.parallelEdges (z i).val v).card ≤ D := by
    intro i v hv
    exact two_core_exception_parallel_bound H U₀ U₁ Z C₀ C₁ h0Z h1Z h D hregular
      hcore₀ hcore₁ (z i).val (z i).property v hv
  have hdeg (v : V) : (joiningGraph H label).degree v ≤ D := by
    rw [joiningGraph_degree_eq]
    exact hdegree v
  have hfibers := twoPairAssignedLabel_fibers G hM U₀ U₁ Z
    h01 h0Z h1Z hcover e₀ e₁ he hpair
  rcases twoPairAssignedLabel_parity G hM U₀ U₁ Z h01 h0Z h1Z hcover
      e₀ e₁ he hpair with heven | hodd
  · have hcore : (corePart G M Z U₀).card % 2 = 0 := by
      rw [← hfibers.1]
      simpa only [labelShore, mem_singleton] using heven 0
    let f : Fin t → Fin h := fun i => ⟨i.val, by omega⟩
    have hf : Function.Injective f := by
      intro i j hij
      exact Fin.ext (congrArg Fin.val hij)
    let A := univ.image f
    have hAcard : A.card = t := by rw [card_image_of_injective _ hf, card_univ, Fintype.card_fin]
    obtain ⟨P⟩ := exists_fourJoining_decomposition_of_even_fibers H label
      (by decide) hregular hno heven
    obtain ⟨C, hweight, hprotected⟩ := P.exists_star_weighted_palette H label
      A (fun i => (z i).val) (fun _ => U₀ ∪ U₁) hresources hdegree hparallel
      (fun i => (hregular (z i).val).le) (le_refl D) hh hDh
      (by rw [hAcard]; exact ht) (by rw [hAcard]; exact hbudget)
    refine ⟨C.congr_parity (fun i => (heven i).symm), f, hf, hweight, ?_⟩
    intro i
    change Q.residualBoundary N T (q i) ∩ joiningCopies H label = C.classes (f i)
    rw [hprotected _ (mem_image_of_mem f (mem_univ i))]
    exact Q.residualBoundary_twoPair_joining_trace_empty_general hM h01 h0Z h1Z hcover
      e₀ e₁ he hpair hcore N T havoid (q i)
  · have hcore : (corePart G M Z U₀).card % 2 = 1 := by
      rw [← hfibers.1]
      simpa only [labelShore, mem_singleton, if_pos (Or.inl rfl)] using hodd 0
    obtain ⟨g, hg, htrace, hends⟩ := Q.exists_twoPair_residual_joining_singletons_general
      hM h01 h0Z h1Z hcover e₀ e₁ he hpair hcore N T havoid
    let g' := fun i : Fin t => g (q i)
    have hg' : Function.Injective g' := hg.comp hq
    let A := univ.image g'
    have hAcard : A.card = t := by rw [card_image_of_injective _ hg', card_univ, Fintype.card_fin]
    have hA : A.card ≤ h := by rw [hAcard]; omega
    have hD : D ≤ h-A.card := by rw [hAcard]; omega
    have hpairA : ∀ e ∈ A, (joiningQuotient H label).edge e = s(0,1) := by
      intro e heA
      obtain ⟨i, _, rfl⟩ := mem_image.mp heA
      exact hends (q i)
    obtain ⟨P, hforced⟩ := exists_fourTwoOddJoining_decomposition_with_reserved_primary
      H label 0 1 (by decide) h D (by decide) hregular hno hodd A hpairA hA hdeg hD
    let S := A.image (fun e => ({e.val} : Finset {e : E // e ∉ removedCopies N T}))
    have hScard : S.card = t := by
      rw [card_image_of_injective]
      · exact hAcard
      · intro e f hef
        exact Subtype.ext (singleton_inj.mp hef)
    have hSP : S ⊆ P.primary := by
      intro B hB
      obtain ⟨e, heA, rfl⟩ := mem_image.mp hB
      exact hforced e heA
    obtain ⟨C, hweight, hprotected⟩ := P.exists_star_weighted_protected_palette H label
      S hSP (fun i => (z i).val) (fun _ => U₀ ∪ U₁) hresources hdegree hparallel
      (fun i => (hregular (z i).val).le) (le_refl D) hh hDh hL
      (by rw [hScard]; exact ht) (by rw [hScard]; exact hbudget)
    have hex : ∀ i : Fin t, ∃ j, C.classes j = {(g' i).val} := by
      intro i
      apply hprotected
      exact mem_image.mpr ⟨g' i, mem_image.mpr ⟨i, mem_univ _, rfl⟩, rfl⟩
    choose f hf using hex
    have hfinj : Function.Injective f := by
      intro i j hij
      apply hg'
      apply Subtype.ext
      exact singleton_inj.mp ((hf i).symm.trans ((congrArg C.classes hij).trans (hf j)))
    refine ⟨C.congr_parity (fun i => (hodd i).symm), f, hfinj, hweight, ?_⟩
    intro i
    exact (htrace (q i)).trans (hf i).symm

end Overfull.NativeWeighted
