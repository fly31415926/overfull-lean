import Overfull.NativeReserve.PartnerGeneralTraces
import Overfull.NativeAssembly.TwoPairBounds

/-!
# Native protected joining palettes with unpaired exceptions

The actual partner code preserves both exceptional pairs and all assigned
core incidences. Exact native traces and joining-degree bounds therefore
extend to unpaired exceptions. The final pair-only completion is not claimed
here: its additional assigned-core stars require their separate completion.
-/

noncomputable section

namespace Overfull.NativeReserve.PartnerBoundaryPacking

open Finset Classical AssignedParts FourOdd

variable {V E J : Type*} [Fintype V] [Fintype E]
    {G : Multigraph V E} {U₀ U₁ Z : Finset V} {M : Finset E} {r : ℕ}
    (Q : PartnerBoundaryPacking G U₀ U₁ Z M r)

/-- All exceptional vertices, paired or unpaired, retain `r` distinct
internal assigned incidences and hence have joining degree at most `h-r`. -/
theorem residual_twoPair_exceptional_joining_degree_general
    (hM : G.IsPerfectMatching M)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (e₀ e₁ : E) (he : e₀ ≠ e₁) (hpair : G.internalOn M Z = {e₀,e₁})
    (N : J → Finset E) (T : Finset J)
    (havoid : ∀ j ∈ T, Disjoint (N j) (removedCopies Q.boundary univ))
    (h : ℕ) (hregular : ∀ v, (residualGraph G N T).degree v = h)
    {z : V} (hz : z ∈ Z) :
    (joiningGraph (residualGraph G N T) (twoPairAssignedLabel G M U₀ U₁ Z e₀)).degree z ≤ h-r := by
  have hcount := residual_joining_degree_add_reserved_le G
    (twoPairAssignedLabel G M U₀ U₁ Z e₀)
    (removedCopies N T) (removedCopies Q.boundary univ)
    (Q.reserved_disjoint_removed N T havoid) z (by
      intro e heR hze
      obtain ⟨i, _, heB⟩ := (mem_removedCopies Q.boundary univ e).mp heR
      have heZ := mem_exceptionalCopies_of_incident G
        (compressedBoundary_subset G (Q.parent i) U₀ U₁ Z heB) hz hze
      exact Q.exceptionalCopies_twoPair_label_eq hM h01 h0Z h1Z hcover
        e₀ e₁ he hpair i heZ)
  change (joiningGraph (residualGraph G N T)
    (twoPairAssignedLabel G M U₀ U₁ Z e₀)).degree z +
      G.degreeOn (removedCopies Q.boundary univ) z ≤ (residualGraph G N T).degree z at hcount
  rw [Q.reserved_exceptional_degree hz, hregular] at hcount
  omega

end Overfull.NativeReserve.PartnerBoundaryPacking

namespace Overfull.NativeAssembly

open Finset Classical AssignedParts FourOdd NativeReserve

variable {V E J : Type*} [Fintype V] [Fintype E]
    {G : Multigraph V E} {U₀ U₁ Z : Finset V} {M : Finset E} {r : ℕ}

/-- Construct exact native protected traces for the actual four-fiber
assignment, permitting unpaired exceptions assigned to either core. -/
theorem exists_partner_twoPair_protected_palette_general
    (Q : PartnerBoundaryPacking G U₀ U₁ Z M r) (hM : G.IsPerfectMatching M)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (e₀ e₁ : E) (he : e₀ ≠ e₁) (hpair : G.internalOn M Z = {e₀,e₁})
    (N : J → Finset E) (T : Finset J)
    (havoid : ∀ j ∈ T, Disjoint (N j) (removedCopies Q.boundary univ))
    {h D L t : ℕ} (hregular : ∀ v, (residualGraph G N T).degree v = h)
    (hno : ∀ X : Finset V, ¬ (residualGraph G N T).IsOverfull h X)
    (q : Fin t → Fin r) (hq : Function.Injective q)
    (hdegree : ∀ v, (residualGraph G N T).degreeOn
      (joiningCopies (residualGraph G N T) (twoPairAssignedLabel G M U₀ U₁ Z e₀)) v ≤ D)
    (hL : 0 < L) (hmargin : 8*D+t < h)
    (hbudget : Fintype.card V*D ≤ 2*L*(h-8*D-t)) :
    ∃ C : JoiningPalette (residualGraph G N T) (twoPairAssignedLabel G M U₀ U₁ Z e₀)
      h D (2*L) (fun i => (univ.filter
        (fun v => twoPairAssignedLabel G M U₀ U₁ Z e₀ v = i)).card % 2),
      ∃ f : Fin t → Fin h, Function.Injective f ∧
        ∀ i, Q.residualBoundary N T (q i) ∩
          joiningCopies (residualGraph G N T) (twoPairAssignedLabel G M U₀ U₁ Z e₀) =
            C.classes (f i) := by
  let label := twoPairAssignedLabel G M U₀ U₁ Z e₀
  have hfibers := twoPairAssignedLabel_fibers G hM U₀ U₁ Z
    h01 h0Z h1Z hcover e₀ e₁ he hpair
  rcases twoPairAssignedLabel_parity G hM U₀ U₁ Z h01 h0Z h1Z hcover
      e₀ e₁ he hpair with heven | hodd
  · have hcore : (corePart G M Z U₀).card % 2 = 0 := by
      rw [← hfibers.1]
      simpa only [labelShore, mem_singleton] using heven 0
    obtain ⟨P⟩ := exists_fourJoining_decomposition_of_even_fibers
      (residualGraph G N T) label (by decide) hregular hno heven
    obtain ⟨C, f, hf, hprotected⟩ := NativeReserve.FourJoiningDecomposition.exists_palette_with_reserved_empty
      (residualGraph G N T) label P hdegree hL hmargin hbudget
    refine ⟨C.congr_parity (fun i => (heven i).symm), f, hf, ?_⟩
    intro i
    change Q.residualBoundary N T (q i) ∩ joiningCopies (residualGraph G N T) label =
      C.classes (f i)
    rw [hprotected i, Q.residualBoundary_twoPair_joining_trace_empty_general
      hM h01 h0Z h1Z hcover e₀ e₁ he hpair hcore N T havoid (q i)]
  · have hcore : (corePart G M Z U₀).card % 2 = 1 := by
      rw [← hfibers.1]
      simpa only [labelShore, mem_singleton, if_pos (Or.inl rfl)] using hodd 0
    obtain ⟨g, hg, htrace, hends⟩ := Q.exists_twoPair_residual_joining_singletons_general
      hM h01 h0Z h1Z hcover e₀ e₁ he hpair hcore N T havoid
    obtain ⟨C, f, hf, hprotected⟩ := exists_four_protected_singleton_palette
      (residualGraph G N T) label 0 1 (by decide) h D L t (by decide)
      hregular hno hodd (fun i => g (q i)) (hg.comp hq) (fun i => hends (q i))
      hdegree hL hmargin hbudget
    refine ⟨C.congr_parity (fun i => (hodd i).symm), f, hf, ?_⟩
    intro i
    exact (htrace (q i)).trans (hprotected i).symm

/-- Retained core degrees and partner reserve incidences bound every
joining degree, with unpaired exceptions included in their assigned fibers. -/
theorem partner_twoPair_joining_degree_bound_general
    (Q : PartnerBoundaryPacking G U₀ U₁ Z M r) (hM : G.IsPerfectMatching M)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (e₀ e₁ : E) (he : e₀ ≠ e₁) (hpair : G.internalOn M Z = {e₀,e₁})
    (N : J → Finset E) (T : Finset J)
    (havoid : ∀ j ∈ T, Disjoint (N j) (removedCopies Q.boundary univ))
    {h D : ℕ} (hregular : ∀ v, (residualGraph G N T).degree v = h)
    (C₀ : SmallCuts.Core (residualGraph G N T) U₀)
    (C₁ : SmallCuts.Core (residualGraph G N T) U₁)
    (hcore₀ : ∀ v, (h : ℝ)-D ≤ (C₀.graph.degree v : ℝ))
    (hcore₁ : ∀ v, (h : ℝ)-D ≤ (C₁.graph.degree v : ℝ))
    (herror : h ≤ r+D) :
    ∀ v, (residualGraph G N T).degreeOn
      (joiningCopies (residualGraph G N T) (twoPairAssignedLabel G M U₀ U₁ Z e₀)) v ≤ D := by
  intro v
  rw [← joiningGraph_degree_eq]
  rcases hcover v with hv | hv | hv
  · have hb := joining_degree_le_core_error (residualGraph G N T)
      (twoPairAssignedLabel G M U₀ U₁ Z e₀) U₀ C₀ 0
      (fun _ hw => twoPairAssignedLabel_on_core₀ G M U₀ U₁ Z e₀ hw)
      h D hregular hcore₀ ⟨v,hv⟩
    exact_mod_cast hb
  · have hb := joining_degree_le_core_error (residualGraph G N T)
      (twoPairAssignedLabel G M U₀ U₁ Z e₀) U₁ C₁ 1
      (fun _ hw => twoPairAssignedLabel_on_core₁ G (hM.isMatching G) U₀ U₁ Z h01 h0Z h1Z e₀ hw)
      h D hregular hcore₁ ⟨v,hv⟩
    exact_mod_cast hb
  · have hb := Q.residual_twoPair_exceptional_joining_degree_general hM h01 h0Z h1Z hcover
      e₀ e₁ he hpair N T havoid h hregular hv
    omega

/-- Construct the actual native protected palette directly from the two
retained cores and the partner reserve, allowing unpaired exceptions. -/
theorem exists_partner_twoPair_protected_palette_of_core_degrees_general
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
    (hL : 0 < L) (hmargin : 8*D+t < h)
    (hbudget : Fintype.card V*D ≤ 2*L*(h-8*D-t)) :
    ∃ C : JoiningPalette (residualGraph G N T) (twoPairAssignedLabel G M U₀ U₁ Z e₀)
      h D (2*L) (fun i => (univ.filter
        (fun v => twoPairAssignedLabel G M U₀ U₁ Z e₀ v = i)).card % 2),
      ∃ f : Fin t → Fin h, Function.Injective f ∧
        ∀ i, Q.residualBoundary N T (q i) ∩
          joiningCopies (residualGraph G N T) (twoPairAssignedLabel G M U₀ U₁ Z e₀) =
            C.classes (f i) := by
  exact exists_partner_twoPair_protected_palette_general Q hM h01 h0Z h1Z hcover
    e₀ e₁ he hpair N T havoid hregular hno q hq
    (partner_twoPair_joining_degree_bound_general Q hM h01 h0Z h1Z hcover e₀ e₁ he hpair
      N T havoid hregular C₀ C₁ hcore₀ hcore₁ herror) hL hmargin hbudget

end Overfull.NativeAssembly
