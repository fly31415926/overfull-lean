import Overfull.AssignedParts.Signatures

/-!
# Actual-copy pools required by a common assignment signature

Each pool consists of original edge copies. In particular an internal
exceptional endpoint pair may have many parallel copies in its pool.
The witnesses below give pool usage, not disjoint reserve selection or
residual no-overfull safety.
-/

noncomputable section

namespace Overfull.AssignedParts

open Finset Classical

variable {V E : Type*} (G : Multigraph V E) [Fintype E]

/-- All original copies from this exception to the specified original core. -/
def exceptionCorePool (z : V) (U : Finset V) : Finset E :=
  univ.filter (fun e => z ∈ G.edge e ∧ G.otherEnd z e ∈ U)

/-- All original copies joining the two disjoint original cores. -/
def coreCrossingPool (U₀ U₁ : Finset V) : Finset E :=
  G.cutOn univ U₀ ∩ G.cutOn univ U₁

/-- Every sample with the internal-pair signature uses one actual copy in
the full exceptional internal pool. -/
theorem signature_none_uses_internalPool (M : Finset E) (U₀ Z : Finset V)
    (hcode : coarseSignature G M U₀ Z = none) :
    (M ∩ G.internalOn univ Z).Nonempty := by
  obtain ⟨e, he⟩ := (coarseSignature_eq_none_iff G M U₀ Z).mp hcode
  exact ⟨e, mem_inter.mpr ⟨(mem_filter.mp he).1,
    mem_filter.mpr ⟨mem_univ _, (mem_filter.mp he).2⟩⟩⟩

/-- A specified original copy gives the required nonempty pool intersection. -/
theorem uses_exceptionCorePool_of_witness (M : Finset E) (z : V) (U : Finset V)
    (hw : ∃ e ∈ M, z ∈ G.edge e ∧ G.otherEnd z e ∈ U) :
    (M ∩ exceptionCorePool G z U).Nonempty := by
  obtain ⟨e, he, hz, ho⟩ := hw
  exact ⟨e, mem_inter.mpr ⟨he, mem_filter.mpr ⟨mem_univ _, hz, ho⟩⟩⟩

/-- Every unpaired exception uses a copy to the core recorded in
its signature, for the original matching whose code is supplied. -/
theorem signature_some_uses_exceptionCorePool {M : Finset E}
    (hM : G.IsPerfectMatching M) (U₀ U₁ Z : Finset V)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (σ : ↥Z → Fin 2) (hcode : coarseSignature G M U₀ Z = some σ) (z : ↥Z) :
    (M ∩ exceptionCorePool G z.val (if σ z = 0 then U₀ else U₁)).Nonempty := by
  obtain ⟨hi, hchoice⟩ := (coarseSignature_eq_some_iff G M U₀ Z σ).mp hcode
  by_cases hz0 : σ z = 0
  · rw [if_pos hz0]
    apply uses_exceptionCorePool_of_witness G
    apply (exceptional_corePart_iff G M U₀ Z h0Z z.property).mp
    apply (assignmentChoice_eq_zero_iff G M U₀ Z z).mp
    rw [hchoice, hz0]
  · rw [if_neg hz0]
    apply uses_exceptionCorePool_of_witness G
    apply (exceptional_corePart_iff G M U₁ Z h1Z z.property).mp
    have hn0 : z.val ∉ corePart G M Z U₀ := by
      intro hm
      have hc := (assignmentChoice_eq_zero_iff G M U₀ Z z).mpr hm
      rw [hchoice] at hc
      exact hz0 hc
    have hnp : z.val ∉ pairPart G M Z := by
      rw [pairPart_eq_empty_of_internal_eq_empty G M Z hi]
      simp
    rcases coreParts_cover G hM U₀ U₁ Z hcover z.val with h0 | h1 | hp
    · exact (hn0 h0).elim
    · exact h1
    · exact (hnp hp).elim

/-- A selected old-core crossing is a member of the original copy pool. -/
theorem uses_coreCrossingPool_of_nonempty (M : Finset E) (U₀ U₁ : Finset V)
    (hc : (G.cutOn M U₀ ∩ G.cutOn M U₁).Nonempty) :
    (M ∩ coreCrossingPool G U₀ U₁).Nonempty := by
  obtain ⟨e, he⟩ := hc
  obtain ⟨he0, he1⟩ := mem_inter.mp he
  obtain ⟨heM, h0⟩ := (G.mem_cutOn M U₀ e).mp he0
  have h1 := ((G.mem_cutOn M U₁ e).mp he1).2
  exact ⟨e, mem_inter.mpr ⟨heM, mem_inter.mpr
    ⟨(G.mem_cutOn univ U₀ e).mpr ⟨mem_univ _, h0⟩,
      (G.mem_cutOn univ U₁ e).mpr ⟨mem_univ _, h1⟩⟩⟩⟩

/-- An odd crossing parity of one representative forces every matching
with that same signature to use the original cross-core copy pool. -/
theorem signature_uses_coreCrossingPool_of_odd {M N : Finset E}
    (hM : G.IsPerfectMatching M) (hN : G.IsPerfectMatching N)
    (U₀ U₁ Z : Finset V) (h01 : Disjoint U₀ U₁)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2)
    (hcode : coarseSignature G M U₀ Z = coarseSignature G N U₀ Z)
    (hodd : (G.cutOn M U₀ ∩ G.cutOn M U₁).card % 2 = 1) :
    (N ∩ coreCrossingPool G U₀ U₁).Nonempty := by
  have hp := coreCrossing_parity_eq_of_signature_eq G hM hN
    U₀ U₁ Z h01 h0Z h1Z hcover hZ hcode
  apply uses_coreCrossingPool_of_nonempty G
  apply card_pos.mp
  omega

end Overfull.AssignedParts
