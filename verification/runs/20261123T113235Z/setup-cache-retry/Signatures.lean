import Overfull.AssignedParts.MatchedCuts

/-!
# Native assignment signatures with at most two exceptional vertices

The signature keeps an internal exceptional pair, including when its selected
copy belongs to a parallel bundle. Otherwise it records the original core to
which each exceptional vertex is matched. Equal signatures determine the same
actual assigned vertex parts and the same parity of the old-core crossing
count. They do not determine the exact crossing count or selected edge copies.
-/

noncomputable section

namespace Overfull.AssignedParts

open Finset Classical

variable {V E : Type*} (G : Multigraph V E)

/-- A possible internal pair, or the matched-core choice of every exception. -/
abbrev AssignmentSignature (Z : Finset V) := Option (↥Z → Fin 2)

/-- Zero records membership in the first actual assigned core part. -/
def assignmentChoice (M : Finset E) (U₀ Z : Finset V) (z : ↥Z) : Fin 2 :=
  if z.val ∈ corePart G M Z U₀ then 0 else 1

/-- The code is attached to the supplied original matching, not to a newly
chosen replacement. The internal-pair case forgets only which parallel copy
realizes that pair. -/
def coarseSignature (M : Finset E) (U₀ Z : Finset V) : AssignmentSignature Z :=
  if (G.internalOn M Z).Nonempty then none else some (assignmentChoice G M U₀ Z)

@[simp] theorem assignmentChoice_eq_zero_iff (M : Finset E) (U₀ Z : Finset V)
    (z : ↥Z) : assignmentChoice G M U₀ Z z = 0 ↔ z.val ∈ corePart G M Z U₀ := by
  by_cases h : z.val ∈ corePart G M Z U₀ <;> simp [assignmentChoice, h]

@[simp] theorem assignmentChoice_eq_one_iff (M : Finset E) (U₀ Z : Finset V)
    (z : ↥Z) : assignmentChoice G M U₀ Z z = 1 ↔ z.val ∉ corePart G M Z U₀ := by
  by_cases h : z.val ∈ corePart G M Z U₀ <;> simp [assignmentChoice, h]

@[simp] theorem coarseSignature_eq_none_iff (M : Finset E) (U₀ Z : Finset V) :
    coarseSignature G M U₀ Z = none ↔ (G.internalOn M Z).Nonempty := by
  by_cases h : (G.internalOn M Z).Nonempty <;> simp [coarseSignature, h]

theorem coarseSignature_eq_some_iff (M : Finset E) (U₀ Z : Finset V)
    (σ : ↥Z → Fin 2) : coarseSignature G M U₀ Z = some σ ↔
      G.internalOn M Z = ∅ ∧ assignmentChoice G M U₀ Z = σ := by
  by_cases h : (G.internalOn M Z).Nonempty
  · have hn : G.internalOn M Z ≠ ∅ := h.ne_empty
    simp [coarseSignature, h, hn]
  · have he : G.internalOn M Z = ∅ := not_nonempty_iff_eq_empty.mp h
    simp [coarseSignature, h, he]

/-- With at most two exceptions, one selected internal copy uses all of them. -/
theorem pairPart_eq_exceptions_of_internal {M : Finset E} (hM : G.IsMatching M)
    (Z : Finset V) (hZ : Z.card ≤ 2) (hi : (G.internalOn M Z).Nonempty) :
    pairPart G M Z = Z ∧ Z.card = 2 := by
  have hc := pairPart_card G hM Z
  have hp := hi.card_pos
  have hsub := pairPart_subset G M Z
  have hle := card_le_card hsub
  have he : (pairPart G M Z).card = Z.card := by omega
  exact ⟨eq_of_subset_of_card_le hsub he.ge, by omega⟩

/-- A full exceptional pair leaves both original core parts unchanged. -/
theorem corePart_eq_original_of_pairPart_eq {M : Finset E} (hM : G.IsMatching M)
    (U Z : Finset V) (hUZ : Disjoint U Z) (hp : pairPart G M Z = Z) :
    corePart G M Z U = U := by
  apply subset_antisymm
  · intro v hv
    rcases (mem_corePart G M Z U v).mp hv with hU | ⟨hZ, _⟩
    · exact hU
    · have hd := corePart_pairPart_disjoint G hM U Z hUZ
      rw [hp] at hd
      exact (disjoint_left.mp hd hv hZ).elim
  · exact core_subset_corePart G M Z U

theorem pairPart_eq_empty_of_internal_eq_empty (M : Finset E) (Z : Finset V)
    (hi : G.internalOn M Z = ∅) : pairPart G M Z = ∅ := by
  ext v
  simp [pairPart, hi, Multigraph.mem_edgeSupport]

/-- The signature contains enough information to recover the optional pair
part even when that pair has many possible parallel copies. -/
theorem pairPart_eq_of_signature_eq {M N : Finset E}
    (hM : G.IsMatching M) (hN : G.IsMatching N)
    (U₀ Z : Finset V) (hZ : Z.card ≤ 2)
    (hcode : coarseSignature G M U₀ Z = coarseSignature G N U₀ Z) :
    pairPart G M Z = pairPart G N Z := by
  by_cases hiM : (G.internalOn M Z).Nonempty
  · have hcM : coarseSignature G M U₀ Z = none :=
      (coarseSignature_eq_none_iff G M U₀ Z).mpr hiM
    have hiN := (coarseSignature_eq_none_iff G N U₀ Z).mp (hcode.symm.trans hcM)
    rw [(pairPart_eq_exceptions_of_internal G hM Z hZ hiM).1,
      (pairPart_eq_exceptions_of_internal G hN Z hZ hiN).1]
  · have hiN : ¬ (G.internalOn N Z).Nonempty := by
      intro hiN
      have hcN := (coarseSignature_eq_none_iff G N U₀ Z).mpr hiN
      exact hiM ((coarseSignature_eq_none_iff G M U₀ Z).mp (hcode.trans hcN))
    rw [pairPart_eq_empty_of_internal_eq_empty G M Z
        (not_nonempty_iff_eq_empty.mp hiM),
      pairPart_eq_empty_of_internal_eq_empty G N Z (not_nonempty_iff_eq_empty.mp hiN)]

/-- Equal signatures determine the first actual assigned core part. -/
theorem firstCorePart_eq_of_signature_eq {M N : Finset E}
    (hM : G.IsMatching M) (hN : G.IsMatching N)
    (U₀ Z : Finset V) (h0Z : Disjoint U₀ Z) (hZ : Z.card ≤ 2)
    (hcode : coarseSignature G M U₀ Z = coarseSignature G N U₀ Z) :
    corePart G M Z U₀ = corePart G N Z U₀ := by
  by_cases hiM : (G.internalOn M Z).Nonempty
  · have hcM := (coarseSignature_eq_none_iff G M U₀ Z).mpr hiM
    have hiN := (coarseSignature_eq_none_iff G N U₀ Z).mp (hcode.symm.trans hcM)
    rw [corePart_eq_original_of_pairPart_eq G hM U₀ Z h0Z
        (pairPart_eq_exceptions_of_internal G hM Z hZ hiM).1,
      corePart_eq_original_of_pairPart_eq G hN U₀ Z h0Z
        (pairPart_eq_exceptions_of_internal G hN Z hZ hiN).1]
  · have hiN : ¬ (G.internalOn N Z).Nonempty := by
      intro hiN
      have hcN := (coarseSignature_eq_none_iff G N U₀ Z).mpr hiN
      exact hiM ((coarseSignature_eq_none_iff G M U₀ Z).mp (hcode.trans hcN))
    have hchoice : assignmentChoice G M U₀ Z = assignmentChoice G N U₀ Z := by
      simpa [coarseSignature, hiM, hiN] using hcode
    ext v
    by_cases hvZ : v ∈ Z
    · have hv := congrFun hchoice ⟨v, hvZ⟩
      exact (assignmentChoice_eq_zero_iff G M U₀ Z ⟨v, hvZ⟩).symm.trans
        ((congrArg (fun x : Fin 2 => x = 0) hv).to_iff.trans
          (assignmentChoice_eq_zero_iff G N U₀ Z ⟨v, hvZ⟩))
    · simp [mem_corePart, hvZ]

/-- For disjoint covering assigned parts, fixing the first and pair parts
also fixes the second part. -/
theorem secondCorePart_eq_of_other_parts_eq {M N : Finset E}
    (hM : G.IsPerfectMatching M) (hN : G.IsPerfectMatching N)
    (U₀ U₁ Z : Finset V) (h01 : Disjoint U₀ U₁)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (hfirst : corePart G M Z U₀ = corePart G N Z U₀)
    (hpair : pairPart G M Z = pairPart G N Z) :
    corePart G M Z U₁ = corePart G N Z U₁ := by
  have hM01 := coreParts_disjoint G (hM.isMatching G) U₀ U₁ Z h01 h0Z h1Z
  have hN01 := coreParts_disjoint G (hN.isMatching G) U₀ U₁ Z h01 h0Z h1Z
  have hM1p := corePart_pairPart_disjoint G (hM.isMatching G) U₁ Z h1Z
  have hN1p := corePart_pairPart_disjoint G (hN.isMatching G) U₁ Z h1Z
  ext v
  constructor
  · intro hv
    rcases coreParts_cover G hN U₀ U₁ Z hcover v with h0 | h1 | hp
    · exact (disjoint_left.mp hM01 (hfirst ▸ h0) hv).elim
    · exact h1
    · exact (disjoint_left.mp hM1p hv (hpair ▸ hp)).elim
  · intro hv
    rcases coreParts_cover G hM U₀ U₁ Z hcover v with h0 | h1 | hp
    · exact (disjoint_left.mp hN01 (hfirst.symm ▸ h0) hv).elim
    · exact h1
    · exact (disjoint_left.mp hN1p hv (hpair.symm ▸ hp)).elim

/-- Every actual assigned part is constant on a native coarse signature. -/
theorem assignedParts_eq_of_signature_eq {M N : Finset E}
    (hM : G.IsPerfectMatching M) (hN : G.IsPerfectMatching N)
    (U₀ U₁ Z : Finset V) (h01 : Disjoint U₀ U₁)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2)
    (hcode : coarseSignature G M U₀ Z = coarseSignature G N U₀ Z) :
    corePart G M Z U₀ = corePart G N Z U₀ ∧
      corePart G M Z U₁ = corePart G N Z U₁ ∧ pairPart G M Z = pairPart G N Z := by
  have hfirst := firstCorePart_eq_of_signature_eq G
    (hM.isMatching G) (hN.isMatching G) U₀ Z h0Z hZ hcode
  have hpair := pairPart_eq_of_signature_eq G
    (hM.isMatching G) (hN.isMatching G) U₀ Z hZ hcode
  exact ⟨hfirst, secondCorePart_eq_of_other_parts_eq G hM hN U₀ U₁ Z
    h01 h0Z h1Z hcover hfirst hpair, hpair⟩

theorem assignedLabel_eq_of_signature_eq {M N : Finset E}
    (hM : G.IsPerfectMatching M) (hN : G.IsPerfectMatching N)
    (U₀ U₁ Z : Finset V) (h01 : Disjoint U₀ U₁)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2)
    (hcode : coarseSignature G M U₀ Z = coarseSignature G N U₀ Z) :
    assignedLabel G M U₀ U₁ Z = assignedLabel G N U₀ U₁ Z := by
  obtain ⟨hfirst, hsecond, _⟩ := assignedParts_eq_of_signature_eq G hM hN
    U₀ U₁ Z h01 h0Z h1Z hcover hZ hcode
  unfold assignedLabel
  rw [hfirst, hsecond]

/-- The old-core crossing parity is fixed, without identifying the exact
number of selected crossing copies across the entire signature class. -/
theorem coreCrossing_parity_eq_of_signature_eq {M N : Finset E}
    (hM : G.IsPerfectMatching M) (hN : G.IsPerfectMatching N)
    (U₀ U₁ Z : Finset V) (h01 : Disjoint U₀ U₁)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2)
    (hcode : coarseSignature G M U₀ Z = coarseSignature G N U₀ Z) :
    (G.cutOn M U₀ ∩ G.cutOn M U₁).card % 2 =
      (G.cutOn N U₀ ∩ G.cutOn N U₁).card % 2 := by
  rw [← corePart_card_parity G hM U₀ U₁ Z h01 h0Z h1Z hcover,
    ← corePart_card_parity G hN U₀ U₁ Z h01 h0Z h1Z hcover]
  rw [firstCorePart_eq_of_signature_eq G
    (hM.isMatching G) (hN.isMatching G) U₀ Z h0Z hZ hcode]

omit G in
theorem card_assignmentSignature (Z : Finset V) :
    Fintype.card (AssignmentSignature Z) = 2 ^ Z.card + 1 := by
  simp [AssignmentSignature, Fintype.card_fun]

omit G in
/-- This upper bound includes unrealizable signatures, which cause no harm
in the weighted pigeonhole argument. -/
theorem card_assignmentSignature_le_five (Z : Finset V) (hZ : Z.card ≤ 2) :
    Fintype.card (AssignmentSignature Z) ≤ 5 := by
  rw [card_assignmentSignature]
  have hpow : 2 ^ Z.card ≤ 2 ^ 2 := Nat.pow_le_pow_right (by omega) hZ
  omega

end Overfull.AssignedParts
