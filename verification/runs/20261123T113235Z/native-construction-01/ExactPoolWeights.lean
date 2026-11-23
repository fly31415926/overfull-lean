import Overfull.AssignedParts.HeavySignature

/-!
# Exact signature weights of exceptional-to-core copy pools

For a fixed exceptional vertex and either original core, the total weight
of signatures assigning that vertex to that core equals the cardinality
of the actual copy pool. Each selected matching uses zero or one of those
copies, and its signature records that usage exactly. Parallel copies
contribute separately. These identities do not select reserves or assert
any property of a residual graph.
-/

noncomputable section

namespace Overfull.AssignedParts

open Finset Classical
open NativeWeights
open Overfull.CircuitPatterns (aggregateWeight_statistic)
open scoped BigOperators

variable {V E : Type*} (G : Multigraph V E)

/-- The signature assigns this exceptional vertex to this original core. -/
def signatureAssignsCore {Z : Finset V} (p : AssignmentSignature Z)
    (z : ↥Z) (i : Fin 2) : Prop :=
  ∃ σ : ↥Z → Fin 2, p = some σ ∧ σ z = i

/-- The native code records the exact assigned-core membership of each
exception. The internal-pair case assigns it to neither old core. -/
theorem signatureAssignsCore_iff_corePart {M : Finset E}
    (hM : G.IsPerfectMatching M) (U₀ U₁ Z : Finset V)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2)
    (z : ↥Z) (i : Fin 2) :
    signatureAssignsCore (coarseSignature G M U₀ Z) z i ↔
      z.val ∈ corePart G M Z (if i = 0 then U₀ else U₁) := by
  cases hc : coarseSignature G M U₀ Z with
  | none =>
    have hi := (coarseSignature_eq_none_iff G M U₀ Z).mp hc
    have hp := (pairPart_eq_exceptions_of_internal G (hM.isMatching G) Z hZ hi).1
    have hUZ : Disjoint (if i = 0 then U₀ else U₁) Z := by
      split_ifs <;> assumption
    have hn : z.val ∉ corePart G M Z (if i = 0 then U₀ else U₁) := by
      rw [corePart_eq_original_of_pairPart_eq G (hM.isMatching G) _ Z hUZ hp]
      exact fun hz => disjoint_left.mp hUZ hz z.property
    simp [signatureAssignsCore, hn]
  | some σ =>
    obtain ⟨hi, hchoice⟩ := (coarseSignature_eq_some_iff G M U₀ Z σ).mp hc
    fin_cases i
    · have hiff : σ z = 0 ↔ z.val ∈ corePart G M Z U₀ := by
        rw [← hchoice]
        exact assignmentChoice_eq_zero_iff G M U₀ Z z
      simpa [signatureAssignsCore] using hiff
    · have hiff : σ z = 1 ↔ z.val ∈ corePart G M Z U₁ := by
        constructor
        · intro hz
          have hn0 : z.val ∉ corePart G M Z U₀ := by
            apply (assignmentChoice_eq_one_iff G M U₀ Z z).mp
            rw [hchoice]
            exact hz
          have hnp : z.val ∉ pairPart G M Z := by
            rw [pairPart_eq_empty_of_internal_eq_empty G M Z hi]
            simp
          rcases coreParts_cover G hM U₀ U₁ Z hcover z.val with h0 | h1 | hp
          · exact (hn0 h0).elim
          · exact h1
          · exact (hnp hp).elim
        · intro hz
          have hn0 : z.val ∉ corePart G M Z U₀ := fun h0 =>
            disjoint_left.mp (coreParts_disjoint G (hM.isMatching G)
              U₀ U₁ Z h01 h0Z h1Z) h0 hz
          have h := (assignmentChoice_eq_one_iff G M U₀ Z z).mpr hn0
          simpa only [hchoice] using h
      simpa [signatureAssignsCore] using hiff

variable [Fintype E]

/-- A matching uses at most one actual copy in a fixed exceptional pool. -/
theorem exceptionCorePool_matching_card_le_one {M : Finset E}
    (hM : G.IsMatching M) (z : V) (U : Finset V) :
    (M ∩ exceptionCorePool G z U).card ≤ 1 := by
  apply card_le_one.mpr
  intro e he f hf
  obtain ⟨heM, heA⟩ := mem_inter.mp he
  obtain ⟨hfM, hfA⟩ := mem_inter.mp hf
  exact hM e heM f hfM z (mem_filter.mp heA).2.1 (mem_filter.mp hfA).2.1

/-- Pool use at an exceptional vertex is exactly membership in its actual
assigned core part. No matching hypothesis is needed for this equivalence. -/
theorem exceptionCorePool_nonempty_iff_corePart (M : Finset E)
    (U Z : Finset V) (hUZ : Disjoint U Z) (z : ↥Z) :
    (M ∩ exceptionCorePool G z.val U).Nonempty ↔ z.val ∈ corePart G M Z U := by
  rw [exceptional_corePart_iff G M U Z hUZ z.property]
  constructor
  · rintro ⟨e, he⟩
    obtain ⟨heM, heA⟩ := mem_inter.mp he
    exact ⟨e, heM, (mem_filter.mp heA).2⟩
  · intro hw
    exact uses_exceptionCorePool_of_witness G M z.val U hw

/-- The code's zero-or-one statistic is the exact usage of the actual
exceptional-to-core pool in this same perfect matching. -/
theorem exceptionCorePool_usage_eq_assignment {M : Finset E}
    (hM : G.IsPerfectMatching M) (U₀ U₁ Z : Finset V)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2)
    (z : ↥Z) (i : Fin 2) :
    (M ∩ exceptionCorePool G z.val (if i = 0 then U₀ else U₁)).card =
      if signatureAssignsCore (coarseSignature G M U₀ Z) z i then 1 else 0 := by
  have hUZ : Disjoint (if i = 0 then U₀ else U₁) Z := by
    split_ifs <;> assumption
  have huse := exceptionCorePool_nonempty_iff_corePart G M
    (if i = 0 then U₀ else U₁) Z hUZ z
  have hcode := signatureAssignsCore_iff_corePart G hM U₀ U₁ Z
    h01 h0Z h1Z hcover hZ z i
  have hle := exceptionCorePool_matching_card_le_one G (hM.isMatching G)
    z.val (if i = 0 then U₀ else U₁)
  by_cases ha : signatureAssignsCore (coarseSignature G M U₀ Z) z i
  · rw [if_pos ha]
    have hpos := (huse.mpr (hcode.mp ha)).card_pos
    omega
  · rw [if_neg ha]
    have hn : ¬ (M ∩ exceptionCorePool G z.val (if i = 0 then U₀ else U₁)).Nonempty := by
      intro hu
      exact ha (hcode.mpr (huse.mp hu))
    exact card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hn)

variable {S : Type*} [Fintype S] {k : ℕ}
  (D : MultigraphMatchingProbability.Distribution G k S)

/-- The total scaled weight of signatures sending one exception to either
specified core is exactly the size of that original actual-copy pool. -/
theorem signature_assignment_weight_eq_pool (hk : 0 < k)
    (U₀ U₁ Z : Finset V) (h01 : Disjoint U₀ U₁)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2)
    (z : ↥Z) (i : Fin 2) :
    (∑ p ∈ univ.filter (fun p : AssignmentSignature Z => signatureAssignsCore p z i),
      signatureWeight D U₀ Z p) =
      (exceptionCorePool G z.val (if i = 0 then U₀ else U₁)).card := by
  calc
    _ = ∑ p, signatureWeight D U₀ Z p *
        (if signatureAssignsCore p z i then (1 : ℝ) else 0) := by
      simp [sum_filter, mul_ite]
    _ = ∑ s, scaledWeight D s *
        (if signatureAssignsCore (coarseSignature G (D.matching s) U₀ Z) z i
          then (1 : ℝ) else 0) :=
      aggregateWeight_statistic _ _ _
    _ = ∑ s, scaledWeight D s *
        ((D.matching s ∩ exceptionCorePool G z.val (if i = 0 then U₀ else U₁)).card : ℝ) := by
      apply sum_congr rfl
      intro s _
      rw [exceptionCorePool_usage_eq_assignment G (D.perfect s)
        U₀ U₁ Z h01 h0Z h1Z hcover hZ z i]
      split_ifs <;> simp
    _ = _ := scaled_matching_pool_eq D hk _

end Overfull.AssignedParts
