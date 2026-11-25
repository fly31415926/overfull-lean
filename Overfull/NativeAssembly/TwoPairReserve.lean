import Overfull.NativeReserve.PartnerResidual
import Overfull.NativeAssembly.TwoPairs

/-!
# Complete two actual native pair reserves in the residual graph

The partner-preserving packing supplies the two injections of surviving
parallel copies. The original reserve and protected-color indices are
retained. When the exceptional set is exactly the two endpoint pairs,
distinct constant old-core labels also supply the boundary containment.
-/

noncomputable section

namespace Overfull.NativeAssembly

open Finset Classical AssignedParts FourOdd NativeReserve

variable {V E J I K : Type*} [Fintype V] [Fintype E] [Fintype I] [DecidableEq K]
    {G : Multigraph V E} {A₀ A₁ Z : Finset V} {M : Finset E} {r : ℕ}

/-- Actual surviving copies from one partner-preserving native reserve
construct the two-pair completion and retain each whole selected boundary. -/
theorem exists_partner_two_pair_completion
    (Q : PartnerBoundaryPacking G A₀ A₁ Z M r) (hM : G.IsPerfectMatching M)
    (e₀ e₁ : G.internalOn M Z) (N : J → Finset E) (T : Finset J)
    (havoid : ∀ j ∈ T, Disjoint (N j) (removedCopies Q.boundary univ))
    {label : V → K} {h D L : ℕ} {p : K → ℕ}
    (C : JoiningPalette (residualGraph G N T) label h D L p)
    (k₀ k₁ : K) (hk : k₀ ≠ k₁)
    (hfiber₀ : labelShore label {k₀} = (G.edge e₀.val).toFinset)
    (hfiber₁ : labelShore label {k₁} = (G.edge e₁.val).toFinset)
    (hp₀ : p k₀ = 0) (hp₁ : p k₁ = 0)
    (hregular : ∀ v, (residualGraph G N T).degree v = h)
    (q : I → Fin r) (f : I → Fin h)
    (hq : Function.Injective q) (hf : Function.Injective f)
    (hsubset : ∀ i, Q.residualBoundary N T (q i) ⊆
      joiningCopies (residualGraph G N T) label ∪
        exceptionalCopies (residualGraph G N T) univ
          ((G.edge e₀.val).toFinset ∪ (G.edge e₁.val).toFinset))
    (htrace : ∀ i, Q.residualBoundary N T (q i) ∩
      joiningCopies (residualGraph G N T) label = C.classes (f i)) :
    ∃ B : TwoPairFiberCompletion C (G.edge e₀.val).toFinset (G.edge e₁.val).toFinset,
      ∀ i, B.classes (f i) = Q.residualBoundary N T (q i) := by
  obtain ⟨g₀, hg₀, hgR₀⟩ := Q.exists_residual_pair_injection hM e₀ N T havoid q hq
  obtain ⟨g₁, hg₁, hgR₁⟩ := Q.exists_residual_pair_injection hM e₁ N T havoid q hq
  have hcard₀ : (G.edge e₀.val).toFinset.card = 2 :=
    Sym2.card_toFinset_of_not_isDiag _ (G.loopless e₀.val)
  have hcard₁ : (G.edge e₁.val).toFinset.card = 2 :=
    Sym2.card_toFinset_of_not_isDiag _ (G.loopless e₁.val)
  obtain ⟨B, _hcolor₀, _hcolor₁, hB⟩ := exists_reserved_two_pair_completion C
    k₀ k₁ hk (G.edge e₀.val).toFinset (G.edge e₁.val).toFinset
    hcard₀ hcard₁ hfiber₀ hfiber₁ hp₀ hp₁
    (fun v _ => hregular v) (fun v _ => hregular v)
    (fun i => Q.residualBoundary N T (q i))
    (fun i => Q.residualBoundary_matching N T (q i)) f hf g₀ g₁ hg₀ hg₁
    (fun i => (hgR₀ i).1) (fun i => (hgR₁ i).1)
    (by
      intro i e he
      simpa only [mem_union] using hsubset i he)
    (by
      intro i
      ext e
      simpa only [mem_inter] using Finset.ext_iff.mp (htrace i) e)
  exact ⟨B, hB⟩

/-- If the two actual pair edges cover all exceptions, the native reserve
needs no assumed containment certificate. Distinct constant old-core labels
derive it from the actual compressed boundaries. -/
theorem exists_partner_two_pair_completion_of_no_unpaired
    (Q : PartnerBoundaryPacking G A₀ A₁ Z M r) (hM : G.IsPerfectMatching M)
    (e₀ e₁ : G.internalOn M Z)
    (hZ : Z = (G.edge e₀.val).toFinset ∪ (G.edge e₁.val).toFinset)
    (h01 : Disjoint A₀ A₁) (N : J → Finset E) (T : Finset J)
    (havoid : ∀ j ∈ T, Disjoint (N j) (removedCopies Q.boundary univ))
    {label : V → K} {h D L : ℕ} {p : K → ℕ}
    (C : JoiningPalette (residualGraph G N T) label h D L p)
    (a₀ a₁ : K) (ha : a₀ ≠ a₁)
    (hlabel₀ : ∀ v ∈ A₀, label v = a₀) (hlabel₁ : ∀ v ∈ A₁, label v = a₁)
    (k₀ k₁ : K) (hk : k₀ ≠ k₁)
    (hfiber₀ : labelShore label {k₀} = (G.edge e₀.val).toFinset)
    (hfiber₁ : labelShore label {k₁} = (G.edge e₁.val).toFinset)
    (hp₀ : p k₀ = 0) (hp₁ : p k₁ = 0)
    (hregular : ∀ v, (residualGraph G N T).degree v = h)
    (q : I → Fin r) (f : I → Fin h)
    (hq : Function.Injective q) (hf : Function.Injective f)
    (htrace : ∀ i, Q.residualBoundary N T (q i) ∩
      joiningCopies (residualGraph G N T) label = C.classes (f i)) :
    ∃ B : TwoPairFiberCompletion C (G.edge e₀.val).toFinset (G.edge e₁.val).toFinset,
      ∀ i, B.classes (f i) = Q.residualBoundary N T (q i) := by
  apply exists_partner_two_pair_completion Q hM e₀ e₁ N T havoid C
    k₀ k₁ hk hfiber₀ hfiber₁ hp₀ hp₁ hregular q f hq hf
  · intro i
    have hs := Q.residualBoundary_subset_joining_exceptional N T label
      a₀ a₁ ha h01 hlabel₀ hlabel₁ (q i)
    simpa only [hZ] using hs
  · exact htrace

end Overfull.NativeAssembly
