import Overfull.AssignedParts.PartnerSignatures
import Overfull.AssignedParts.TwoPairs

/-!
# The four assigned labels are fixed by the full partner code

An explicit enumeration of the representative's two exceptional pairs is
transported to actual parallel copies in every matching with the same partner
code.  The transported copies exhaust its internal exceptional matching and
have exactly the same two endpoint pairs.  Thus one fixed four-label function
works throughout the code class, without identifying different parallel copies.
-/

noncomputable section

namespace Overfull.AssignedParts

open Finset Classical FourOdd

variable {V E : Type*} (G : Multigraph V E)

/-- Equal full partner codes preserve the number of internal matching copies,
although the copies themselves may be different parallel representatives. -/
theorem internalOn_card_eq_of_partnerSignature_eq {M N : Finset E}
    (hM : G.IsPerfectMatching M) (hN : G.IsPerfectMatching N)
    (U₀ Z : Finset V)
    (hcode : partnerSignature G M U₀ Z = partnerSignature G N U₀ Z) :
    (G.internalOn M Z).card = (G.internalOn N Z).card := by
  have hc := congrArg Finset.card (pairPart_eq_of_partnerSignature_eq G hM hN U₀ Z hcode)
  rw [pairPart_card G (hM.isMatching G) Z, pairPart_card G (hN.isMatching G) Z] at hc
  omega

/-- Both explicit exceptional pairs have distinct actual parallel copies in
every matching with the same full code, and these are all its internal copies. -/
theorem exists_two_parallel_pairs_of_partnerSignature_eq {M N : Finset E}
    (hM : G.IsPerfectMatching M) (hN : G.IsPerfectMatching N)
    (U₀ Z : Finset V)
    (hcode : partnerSignature G M U₀ Z = partnerSignature G N U₀ Z)
    (e₀ e₁ : E) (he : e₀ ≠ e₁) (hpair : G.internalOn M Z = {e₀, e₁}) :
    ∃ f₀ f₁ : E, f₀ ≠ f₁ ∧ G.internalOn N Z = {f₀, f₁} ∧
      G.edge f₀ = G.edge e₀ ∧ G.edge f₁ = G.edge e₁ ∧
      exceptionalPairPart G f₀ = exceptionalPairPart G e₀ ∧
      exceptionalPairPart G f₁ = exceptionalPairPart G e₁ := by
  have he₀ : e₀ ∈ G.internalOn M Z := by rw [hpair]; exact mem_insert_self _ _
  have he₁ : e₁ ∈ G.internalOn M Z := by
    rw [hpair]
    exact mem_insert_of_mem (mem_singleton_self _)
  obtain ⟨f₀, hf₀, hedge₀⟩ :=
    exists_parallel_of_partnerSignature_eq G hM hN U₀ Z hcode he₀
  obtain ⟨f₁, hf₁, hedge₁⟩ :=
    exists_parallel_of_partnerSignature_eq G hM hN U₀ Z hcode he₁
  have hf : f₀ ≠ f₁ := by
    intro h
    have hedge : G.edge e₀ = G.edge e₁ :=
      hedge₀.symm.trans ((congrArg G.edge h).trans hedge₁)
    have hv₀ : G.firstEnd e₀ ∈ G.edge e₀ :=
      (G.incident_iff e₀ _).mpr (Or.inl rfl)
    have hv₁ : G.firstEnd e₀ ∈ G.edge e₁ := hedge ▸ hv₀
    exact he ((hM.isMatching G) e₀ (mem_filter.mp he₀).1 e₁ (mem_filter.mp he₁).1
      (G.firstEnd e₀) hv₀ hv₁)
  have hcard : (G.internalOn N Z).card = 2 := by
    rw [← internalOn_card_eq_of_partnerSignature_eq G hM hN U₀ Z hcode, hpair]
    simp [he]
  have hsub : ({f₀, f₁} : Finset E) ⊆ G.internalOn N Z := by
    intro f hfmem
    rcases mem_insert.mp hfmem with rfl | hfmem
    · exact hf₀
    · exact (mem_singleton.mp hfmem).symm ▸ hf₁
  have hfull : G.internalOn N Z = {f₀, f₁} :=
    (eq_of_subset_of_card_le hsub (by rw [hcard]; simp [hf])).symm
  exact ⟨f₀, f₁, hf, hfull, hedge₀, hedge₁,
    exceptionalPairPart_eq_of_edge_eq G hedge₀, exceptionalPairPart_eq_of_edge_eq G hedge₁⟩

/-- Equal partner codes and an aligned actual parallel representative give
the identical four-label function on the original vertex type. -/
theorem twoPairAssignedLabel_eq_of_partnerSignature_eq {M N : Finset E}
    (hM : G.IsPerfectMatching M) (hN : G.IsPerfectMatching N)
    (U₀ U₁ Z : Finset V) (h01 : Disjoint U₀ U₁)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (hcode : partnerSignature G M U₀ Z = partnerSignature G N U₀ Z)
    (e f : E) (hedge : G.edge f = G.edge e) :
    twoPairAssignedLabel G M U₀ U₁ Z e = twoPairAssignedLabel G N U₀ U₁ Z f := by
  have hp := assignedParts_eq_of_partnerSignature_eq G hM hN U₀ U₁ Z
    h01 h0Z h1Z hcover hcode
  exact twoPairAssignedLabel_eq_of_parts G U₀ U₁ Z e f hp.1 hp.2.1
    (exceptionalPairPart_eq_of_edge_eq G hedge).symm

variable [Fintype V]

/-- Transport the two actual pair representatives and every assigned fiber
while retaining one fixed label function throughout the full code class. -/
theorem exists_two_pair_assigned_label_transfer {M N : Finset E}
    (hM : G.IsPerfectMatching M) (hN : G.IsPerfectMatching N)
    (U₀ U₁ Z : Finset V) (h01 : Disjoint U₀ U₁)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (hcode : partnerSignature G M U₀ Z = partnerSignature G N U₀ Z)
    (e₀ e₁ : E) (he : e₀ ≠ e₁) (hpair : G.internalOn M Z = {e₀, e₁}) :
    ∃ f₀ f₁ : E, f₀ ≠ f₁ ∧ G.internalOn N Z = {f₀, f₁} ∧
      G.edge f₀ = G.edge e₀ ∧ G.edge f₁ = G.edge e₁ ∧
      twoPairAssignedLabel G M U₀ U₁ Z e₀ = twoPairAssignedLabel G N U₀ U₁ Z f₀ ∧
      labelShore (twoPairAssignedLabel G M U₀ U₁ Z e₀) {0} = corePart G N Z U₀ ∧
      labelShore (twoPairAssignedLabel G M U₀ U₁ Z e₀) {1} = corePart G N Z U₁ ∧
      labelShore (twoPairAssignedLabel G M U₀ U₁ Z e₀) {2} = exceptionalPairPart G f₀ ∧
      labelShore (twoPairAssignedLabel G M U₀ U₁ Z e₀) {3} = exceptionalPairPart G f₁ := by
  obtain ⟨f₀, f₁, hf, hfull, hedge₀, hedge₁, _hp₀, _hp₁⟩ :=
    exists_two_parallel_pairs_of_partnerSignature_eq G hM hN U₀ Z hcode e₀ e₁ he hpair
  have hlabel := twoPairAssignedLabel_eq_of_partnerSignature_eq G hM hN
    U₀ U₁ Z h01 h0Z h1Z hcover hcode e₀ f₀ hedge₀
  have hfibers := twoPairAssignedLabel_fibers G hN U₀ U₁ Z h01 h0Z h1Z hcover
    f₀ f₁ hf hfull
  refine ⟨f₀, f₁, hf, hfull, hedge₀, hedge₁, hlabel, ?_⟩
  simpa only [hlabel] using hfibers

end Overfull.AssignedParts
