import Overfull.NativeAssembly.TwoPairStar
import Overfull.NativeReserve.PartnerResidual

/-!
# Native two-pair and fifth-vertex assembly

Actual partner-preserving boundaries supply the pair injections, disjoint
reserved classes, and coverage of the fifth vertex.  With the stated native
fiber geometry and joining palette, the assembler covers exactly every
joining or exceptional copy and saturates the whole exceptional set in every
color.  Residual construction, protected traces, and star-weight budgets are
explicit inputs at this interface.
-/

noncomputable section

namespace Overfull.NativeAssembly

open Finset Classical AssignedParts FourOdd NativeReserve NativeStar WeightedPalette

variable {V E I J K : Type*} [Fintype V] [Fintype E] [Fintype I] [DecidableEq K]

/-- Two actual pair fibers and one additional vertex account for every
nonjoining exceptional copy: it is internal to one pair or belongs to the
last vertex's assigned-core star. -/
theorem exceptional_two_pair_star_cover (H : Multigraph V E) (label : V → K)
    (k₀ k₁ : K) (U₀ U₁ Z : Finset V) (z : V) (U : Finset V)
    (hZ : Z = U₀ ∪ U₁ ∪ {z})
    (hfiber₀ : labelShore label {k₀} = U₀)
    (hfiber₁ : labelShore label {k₁} = U₁)
    (hstarfiber : labelShore label {label z} = insert z U) :
    joiningCopies H label ∪ exceptionalCopies H univ Z =
      joiningCopies H label ∪ H.internalOn univ U₀ ∪ H.internalOn univ U₁ ∪
        exceptionCorePool H z U := by
  have hzZ : z ∈ Z := by rw [hZ]; exact mem_union_right _ (mem_singleton_self _)
  have hclass (e : E) (v : V) (hv : v ∈ Z) (hve : v ∈ H.edge e)
      (hn : e ∉ joiningCopies H label) :
      e ∈ H.internalOn univ U₀ ∨ e ∈ H.internalOn univ U₁ ∨ e ∈ exceptionCorePool H z U := by
    have hsame : label (H.otherEnd v e) = label v :=
      not_ne_iff.mp (fun hne => hn ((joining_iff_otherEnd_label_ne H label v e hve).mpr hne))
    rw [hZ] at hv
    rcases mem_union.mp hv with hv | hv
    · rcases mem_union.mp hv with hv₀ | hv₁
      · apply Or.inl
        have hvlabel : label v = k₀ := by
          rw [← hfiber₀] at hv₀
          simpa only [mem_labelShore, mem_singleton] using hv₀
        have ho : H.otherEnd v e ∈ U₀ := by
          rw [← hfiber₀]
          simpa only [mem_labelShore, mem_singleton] using hsame.trans hvlabel
        exact H.mem_internalOn_of_incident_otherEnd (mem_univ _) hve hv₀ ho
      · apply Or.inr ∘ Or.inl
        have hvlabel : label v = k₁ := by
          rw [← hfiber₁] at hv₁
          simpa only [mem_labelShore, mem_singleton] using hv₁
        have ho : H.otherEnd v e ∈ U₁ := by
          rw [← hfiber₁]
          simpa only [mem_labelShore, mem_singleton] using hsame.trans hvlabel
        exact H.mem_internalOn_of_incident_otherEnd (mem_univ _) hve hv₁ ho
    · have hvz := mem_singleton.mp hv
      subst v
      exact Or.inr (Or.inr (((single_added_fiber_star_incidence (G := H)
        z U hstarfiber).1 e hve).resolve_left hn))
  apply subset_antisymm
  · intro e he
    rcases mem_union.mp he with hj | he
    · exact mem_union_left _ (mem_union_left _ (mem_union_left _ hj))
    · by_cases hj : e ∈ joiningCopies H label
      · exact mem_union_left _ (mem_union_left _ (mem_union_left _ hj))
      · obtain ⟨_, hv | hv⟩ := (mem_exceptionalCopies H univ Z e).mp he
        · rcases hclass e (H.firstEnd e) hv ((H.incident_iff e _).mpr (Or.inl rfl)) hj with h₀ | h₁ | hs
          · exact mem_union_left _ (mem_union_left _ (mem_union_right _ h₀))
          · exact mem_union_left _ (mem_union_right _ h₁)
          · exact mem_union_right _ hs
        · rcases hclass e (H.secondEnd e) hv ((H.incident_iff e _).mpr (Or.inr rfl)) hj with h₀ | h₁ | hs
          · exact mem_union_left _ (mem_union_left _ (mem_union_right _ h₀))
          · exact mem_union_left _ (mem_union_right _ h₁)
          · exact mem_union_right _ hs
  · intro e he
    rcases mem_union.mp he with he | hs
    · rcases mem_union.mp he with he | h₁
      · rcases mem_union.mp he with hj | h₀
        · exact mem_union_left _ hj
        · apply mem_union_right
          apply (mem_exceptionalCopies H univ Z e).mpr
          refine ⟨mem_univ _, Or.inl ?_⟩
          rw [hZ]
          exact mem_union_left _ (mem_union_left _ (mem_filter.mp h₀).2.1)
      · apply mem_union_right
        apply (mem_exceptionalCopies H univ Z e).mpr
        refine ⟨mem_univ _, Or.inl ?_⟩
        rw [hZ]
        exact mem_union_left _ (mem_union_right _ (mem_filter.mp h₁).2.1)
    · apply mem_union_right
      apply (mem_exceptionalCopies H univ Z e).mpr
      refine ⟨mem_univ _, ?_⟩
      rcases (H.incident_iff e z).mp (mem_filter.mp hs).2.1 with hz | hz
      · exact Or.inl (hz.symm ▸ hzZ)
      · exact Or.inr (hz.symm ▸ hzZ)

set_option maxHeartbeats 800000 in
/-- Native actual pair injections and whole compressed boundaries supply
the complete two-pair-plus-star assembler in a reserve-avoiding residual.
Its union is exactly all joining and exceptional copies, and every color
saturates all five exceptional vertices when the displayed partition has
that size. -/
theorem exists_partner_two_pair_star_completion
    {G : Multigraph V E} {A₀ A₁ Z : Finset V} {M : Finset E} {r : ℕ}
    (Q : PartnerBoundaryPacking G A₀ A₁ Z M r) (hM : G.IsPerfectMatching M)
    (e₀ e₁ : G.internalOn M Z) (z : Z) (U : Finset V)
    (hZ : Z = (G.edge e₀.val).toFinset ∪ (G.edge e₁.val).toFinset ∪ {z.val})
    (N : J → Finset E) (T : Finset J)
    (havoid : ∀ j ∈ T, Disjoint (N j) (removedCopies Q.boundary univ))
    {label : V → K} {h D L : ℕ} {p : K → ℕ}
    (C : JoiningPalette (residualGraph G N T) label h D L p)
    (k₀ k₁ : K) (hk : k₀ ≠ k₁)
    (hfiber₀ : labelShore label {k₀} = (G.edge e₀.val).toFinset)
    (hfiber₁ : labelShore label {k₁} = (G.edge e₁.val).toFinset)
    (hp₀ : p k₀ = 0) (hp₁ : p k₁ = 0)
    (hz₀ : label z.val ≠ k₀) (hz₁ : label z.val ≠ k₁)
    (hstarfiber : labelShore label {label z.val} = insert z.val U)
    (a₀ a₁ : K) (ha : a₀ ≠ a₁) (h01 : Disjoint A₀ A₁)
    (hlabel₀ : ∀ v ∈ A₀, label v = a₀) (hlabel₁ : ∀ v ∈ A₁, label v = a₁)
    (hregular : ∀ v, (residualGraph G N T).degree v = h)
    (q : I → Fin r) (f : I → Fin h)
    (hq : Function.Injective q) (hf : Function.Injective f)
    (htrace : ∀ i, Q.residualBoundary N T (q i) ∩
      joiningCopies (residualGraph G N T) label = C.classes (f i))
    (hD : 128*D ≤ h) (hs : 2*Fintype.card I ≤ h)
    (hweight : ∀ j, starWeight (residualGraph G N T) z.val U (C.classes j) ≤ h/8) :
    ∃ F : Fin h → Finset {e : E // e ∉ removedCopies N T},
      (∀ j, (residualGraph G N T).IsMatching (F j)) ∧
      Pairwise (fun j k => Disjoint (F j) (F k)) ∧
      univ.biUnion F = joiningCopies (residualGraph G N T) label ∪
        exceptionalCopies (residualGraph G N T) univ Z ∧
      (∀ j, C.classes j ⊆ F j) ∧
      (∀ i, F (f i) = Q.residualBoundary N T (q i)) ∧
      (∀ j, Z ⊆ (residualGraph G N T).edgeSupport (F j)) ∧
      (∀ j k, (residualGraph G N T).cutOn (F j) (labelShore label {k}) =
        (residualGraph G N T).cutOn (C.classes j) (labelShore label {k})) ∧
      (∀ j, (F j).card ≤ max (3*L+2) (Z.card+1) + 1) ∧
      (∀ j, ((residualGraph G N T).edgeSupport (F j)).card ≤ 2*max (3*L+2) (Z.card+1) + 2) := by
  let H := residualGraph G N T
  let R : I → Finset {e : E // e ∉ removedCopies N T} := fun i => Q.residualBoundary N T (q i)
  obtain ⟨g₀, hg₀, hgR₀⟩ := Q.exists_residual_pair_injection hM e₀ N T havoid q hq
  obtain ⟨g₁, hg₁, hgR₁⟩ := Q.exists_residual_pair_injection hM e₁ N T havoid q hq
  have hcard₀ : (G.edge e₀.val).toFinset.card = 2 :=
    Sym2.card_toFinset_of_not_isDiag _ (G.loopless e₀.val)
  have hcard₁ : (G.edge e₁.val).toFinset.card = 2 :=
    Sym2.card_toFinset_of_not_isDiag _ (G.loopless e₁.val)
  obtain ⟨F, hm, hd, hcov, hsub, hpres, hcovers, hcuts, hcard, hsupp⟩ :=
    exists_reserved_two_pair_star_completion C k₀ k₁ hk
      (G.edge e₀.val).toFinset (G.edge e₁.val).toFinset hcard₀ hcard₁ hfiber₀ hfiber₁ hp₀ hp₁
      (fun v _ => hregular v) (fun v _ => hregular v)
      R (fun i => Q.residualBoundary_matching N T (q i))
      (fun i j hij => Q.residualBoundary_disjoint N T (fun heq => hij (hq heq)))
      (fun i => Q.residualBoundary_card_le N T havoid (q i))
      f hf g₀ g₁ hg₀ hg₁ (fun i => (hgR₀ i).1) (fun i => (hgR₁ i).1)
      (by
        intro i
        ext e
        simpa only [R, mem_inter] using Finset.ext_iff.mp (htrace i) e)
      z.val U hz₀ hz₁ hstarfiber (hregular z.val)
      (fun i => Q.residualBoundary_covers_exceptional N T havoid (q i) z.property)
      hD hs hweight
  have hRsub : univ.biUnion R ⊆ joiningCopies H label ∪ exceptionalCopies H univ Z := by
    intro e he
    obtain ⟨i, _, hei⟩ := mem_biUnion.mp he
    exact Q.residualBoundary_subset_joining_exceptional N T label a₀ a₁ ha h01 hlabel₀ hlabel₁ (q i) hei
  have hext := exceptional_two_pair_star_cover H label k₀ k₁
    (G.edge e₀.val).toFinset (G.edge e₁.val).toFinset Z z.val U hZ hfiber₀ hfiber₁ hstarfiber
  refine ⟨F, hm, hd, ?_, hsub, hpres, ?_, hcuts, hcard, hsupp⟩
  · ext e
    have hcE := Finset.ext_iff.mp hcov e
    have heE := Finset.ext_iff.mp hext e
    simp only [mem_biUnion, mem_univ, true_and, mem_union] at hcE heE ⊢
    constructor
    · intro he
      rcases hcE.mp he with (he | heR) | heS
      · exact heE.mpr (Or.inl he)
      · obtain ⟨i, hi⟩ := heR
        exact mem_union.mp (hRsub (mem_biUnion.mpr ⟨i, mem_univ _, hi⟩))
      · exact heE.mpr (Or.inr heS)
    · intro he
      rcases heE.mp he with he | heS
      · exact hcE.mpr (Or.inl (Or.inl he))
      · exact hcE.mpr (Or.inr heS)
  · intro j
    simpa only [hZ] using hcovers j

end Overfull.NativeAssembly
