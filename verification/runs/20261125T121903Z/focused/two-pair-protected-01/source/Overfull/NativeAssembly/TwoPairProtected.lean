import Overfull.NativeReserve.PartnerTraces
import Overfull.ResidualPalette.FourProtectedPalette
import Overfull.AssignedParts.TwoPairPalette
import Overfull.NativeAssembly.TwoPairReserve

/-!
# Native two-pair completion with constructed protected traces

The actual partner reserve supplies the native joining traces.  The host's
regularity, absence of overfull sets, and joining budget construct one palette
with those exact traces, including the empty all-even classes.  Completing
both internal pair pools then preserves each selected whole boundary.

The host is an explicitly supplied reserve-avoiding residual; constructing
its safety and degree budgets is a separate obligation.
-/

noncomputable section

namespace Overfull.NativeAssembly

open Finset Classical AssignedParts FourOdd NativeReserve

variable {V E J : Type*} [Fintype V] [Fintype E]
    {G : Multigraph V E} {U₀ U₁ Z : Finset V} {M : Finset E} {r : ℕ}

/-- Construct the joining palette and injective protected colors from the
actual two-pair reserve. No palette, primary selection, or trace equality
is supplied as a hypothesis. -/
theorem exists_partner_twoPair_protected_palette
    (Q : PartnerBoundaryPacking G U₀ U₁ Z M r) (hM : G.IsPerfectMatching M)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (e₀ e₁ : E) (he : e₀ ≠ e₁) (hpair : G.internalOn M Z = {e₀,e₁})
    (hZ : Z = exceptionalPairPart G e₀ ∪ exceptionalPairPart G e₁)
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
    obtain ⟨C, f, hf, hprotected⟩ := P.exists_palette_with_reserved_empty
      (residualGraph G N T) label hdegree hL hmargin hbudget
    refine ⟨C.congr_parity (fun i => (heven i).symm), f, hf, ?_⟩
    intro i
    change Q.residualBoundary N T (q i) ∩ joiningCopies (residualGraph G N T) label =
      C.classes (f i)
    rw [hprotected i, Q.residualBoundary_twoPair_joining_trace_empty
      hM h01 h0Z h1Z hcover e₀ e₁ he hpair hZ hcore N T havoid (q i)]
  · have hcore : (corePart G M Z U₀).card % 2 = 1 := by
      rw [← hfibers.1]
      simpa only [labelShore, mem_singleton, if_pos (Or.inl rfl)] using hodd 0
    obtain ⟨g, hg, htrace, hends⟩ := Q.exists_twoPair_residual_joining_singletons
      hM h01 h0Z h1Z hcover e₀ e₁ he hpair hZ hcore N T havoid
    obtain ⟨C, f, hf, hprotected⟩ := exists_four_protected_singleton_palette
      (residualGraph G N T) label 0 1 (by decide) h D L t (by decide)
      hregular hno hodd (fun i => g (q i)) (hg.comp hq) (fun i => hends (q i))
      hdegree hL hmargin hbudget
    refine ⟨C.congr_parity (fun i => (hodd i).symm), f, hf, ?_⟩
    intro i
    exact (htrace (q i)).trans (hprotected i).symm

/-- Construct both internal pair completions together with their joining
palette and protected colors, preserving each whole selected native boundary.
The only residual inputs are safety, regularity, and explicit degree budgets. -/
theorem exists_partner_twoPair_protected_completion
    (Q : PartnerBoundaryPacking G U₀ U₁ Z M r) (hM : G.IsPerfectMatching M)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (e₀ e₁ : E) (he : e₀ ≠ e₁) (hpair : G.internalOn M Z = {e₀,e₁})
    (hZ : Z = exceptionalPairPart G e₀ ∪ exceptionalPairPart G e₁)
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
        ∃ B : TwoPairFiberCompletion C (exceptionalPairPart G e₀) (exceptionalPairPart G e₁),
          ∀ i, B.classes (f i) = Q.residualBoundary N T (q i) := by
  obtain ⟨C, f, hf, htrace⟩ := exists_partner_twoPair_protected_palette Q hM
    h01 h0Z h1Z hcover e₀ e₁ he hpair hZ N T havoid hregular hno q hq
    hdegree hL hmargin hbudget
  have hfibers := twoPairAssignedLabel_fibers G hM U₀ U₁ Z
    h01 h0Z h1Z hcover e₀ e₁ he hpair
  let a₀ : G.internalOn M Z := ⟨e₀, by rw [hpair]; exact mem_insert_self _ _⟩
  let a₁ : G.internalOn M Z := ⟨e₁, by rw [hpair]; exact mem_insert_of_mem (mem_singleton_self _)⟩
  have hp₂ : (univ.filter
      (fun v => twoPairAssignedLabel G M U₀ U₁ Z e₀ v = 2)).card % 2 = 0 := by
    have hh : (labelShore (twoPairAssignedLabel G M U₀ U₁ Z e₀) {2}).card % 2 = 0 := by
      rw [hfibers.2.2.1, exceptionalPairPart_card]
      decide
    simpa only [labelShore, mem_singleton] using hh
  have hp₃ : (univ.filter
      (fun v => twoPairAssignedLabel G M U₀ U₁ Z e₀ v = 3)).card % 2 = 0 := by
    have hh : (labelShore (twoPairAssignedLabel G M U₀ U₁ Z e₀) {3}).card % 2 = 0 := by
      rw [hfibers.2.2.2, exceptionalPairPart_card]
      decide
    simpa only [labelShore, mem_singleton] using hh
  obtain ⟨B, hB⟩ := exists_partner_two_pair_completion_of_no_unpaired Q hM
    a₀ a₁ hZ h01 N T havoid C 0 1 (by decide)
    (fun v hv => twoPairAssignedLabel_on_core₀ G M U₀ U₁ Z e₀ hv)
    (fun v hv => twoPairAssignedLabel_on_core₁ G (hM.isMatching G) U₀ U₁ Z h01 h0Z h1Z e₀ hv)
    2 3 (by decide) hfibers.2.2.1 hfibers.2.2.2 hp₂ hp₃ hregular q f hq hf htrace
  exact ⟨C, f, hf, B, hB⟩

end Overfull.NativeAssembly
