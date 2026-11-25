import Overfull.NativeAssembly.TwoPairProtected

/-!
# Joining-degree bounds for the actual native two-pair residual

Every exceptional vertex retains one distinct internal incidence from each
reserved boundary. Old-core copies remain internal under the actual four
labels. These actual copy bounds derive the joining degree used by the
protected palette and simultaneous pair completion.
-/

noncomputable section

namespace Overfull.NativeReserve.PartnerBoundaryPacking

open Finset Classical AssignedParts FourOdd
open scoped BigOperators

variable {V E J : Type*}
    {G : Multigraph V E} {U₀ U₁ Z : Finset V} {M : Finset E} {r : ℕ}
    (Q : PartnerBoundaryPacking G U₀ U₁ Z M r)

/-- The union of the actual partner-preserving boundaries contains exactly
one distinct incidence per reserve index at each exceptional vertex. -/
theorem reserved_exceptional_degree {z : V} (hz : z ∈ Z) :
    G.degreeOn (removedCopies Q.boundary univ) z = r := by
  rw [removed_degreeOn G Q.boundary univ (fun _ _ _ _ hij => Q.disjoint hij)]
  simp only [Q.exceptional_degree _ hz, sum_const, card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one]

/-- Avoidance by each removed copy set preserves the whole native reserve. -/
theorem reserved_disjoint_removed (N : J → Finset E) (T : Finset J)
    (havoid : ∀ j ∈ T, Disjoint (N j) (removedCopies Q.boundary univ)) :
    Disjoint (removedCopies Q.boundary univ) (removedCopies N T) := by
  apply disjoint_left.mpr
  intro e heR heN
  obtain ⟨j, hj, he⟩ := (mem_removedCopies N T e).mp heN
  exact disjoint_left.mp (havoid j hj) he heR

variable [Fintype V] [Fintype E]

/-- In the no-unpaired two-pair branch, all `r` reserved exceptional
incidences survive internally. Joining incidences therefore have degree
at most the residual degree minus `r`. -/
theorem residual_twoPair_exceptional_joining_degree
    (hM : G.IsPerfectMatching M)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (e₀ e₁ : E) (he : e₀ ≠ e₁) (hpair : G.internalOn M Z = {e₀,e₁})
    (hZ : Z = exceptionalPairPart G e₀ ∪ exceptionalPairPart G e₁)
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
      have hnot := Q.exceptionalCopies_not_joining_twoPair hM h01 h0Z h1Z hcover
        e₀ e₁ he hpair hZ i heZ
      exact not_not.mp (by simpa only [mem_joiningCopies, ne_eq] using hnot))
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

/-- High retained simple-core degrees and the actual `r` internal reserve
incidences imply the complete native joining-degree bound. -/
theorem partner_twoPair_joining_degree_bound
    (Q : PartnerBoundaryPacking G U₀ U₁ Z M r) (hM : G.IsPerfectMatching M)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (e₀ e₁ : E) (he : e₀ ≠ e₁) (hpair : G.internalOn M Z = {e₀,e₁})
    (hZ : Z = exceptionalPairPart G e₀ ∪ exceptionalPairPart G e₁)
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
  · have hb := Q.residual_twoPair_exceptional_joining_degree hM h01 h0Z h1Z hcover
      e₀ e₁ he hpair hZ N T havoid h hregular hv
    omega

/-- The native protected palette needs no supplied joining-degree bound
when the two retained cores and actual partner reserve give it directly. -/
theorem exists_partner_twoPair_protected_palette_of_core_degrees
    (Q : PartnerBoundaryPacking G U₀ U₁ Z M r) (hM : G.IsPerfectMatching M)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (e₀ e₁ : E) (he : e₀ ≠ e₁) (hpair : G.internalOn M Z = {e₀,e₁})
    (hZ : Z = exceptionalPairPart G e₀ ∪ exceptionalPairPart G e₁)
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
  exact exists_partner_twoPair_protected_palette Q hM h01 h0Z h1Z hcover
    e₀ e₁ he hpair hZ N T havoid hregular hno q hq
    (partner_twoPair_joining_degree_bound Q hM h01 h0Z h1Z hcover e₀ e₁ he hpair hZ
      N T havoid hregular C₀ C₁ hcore₀ hcore₁ herror) hL hmargin hbudget

/-- Derive the joining budget from both retained cores and the surviving
partner reserve, then construct the protected simultaneous pair completion. -/
theorem exists_partner_twoPair_protected_completion_of_core_degrees
    (Q : PartnerBoundaryPacking G U₀ U₁ Z M r) (hM : G.IsPerfectMatching M)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (e₀ e₁ : E) (he : e₀ ≠ e₁) (hpair : G.internalOn M Z = {e₀,e₁})
    (hZ : Z = exceptionalPairPart G e₀ ∪ exceptionalPairPart G e₁)
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
        ∃ B : TwoPairFiberCompletion C (exceptionalPairPart G e₀) (exceptionalPairPart G e₁),
          ∀ i, B.classes (f i) = Q.residualBoundary N T (q i) := by
  exact exists_partner_twoPair_protected_completion Q hM h01 h0Z h1Z hcover
    e₀ e₁ he hpair hZ N T havoid hregular hno q hq
    (partner_twoPair_joining_degree_bound Q hM h01 h0Z h1Z hcover e₀ e₁ he hpair hZ
      N T havoid hregular C₀ C₁ hcore₀ hcore₁ herror) hL hmargin hbudget

end Overfull.NativeAssembly
