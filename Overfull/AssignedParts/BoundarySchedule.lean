import Overfull.AssignedParts.NativePatternConstruction
import Overfull.CircuitPatterns.Realization

/-!
# A simultaneous native boundary schedule

Fix two disjoint original cores `U₀,U₁` and an exceptional set `Z` with at
most two vertices. A round is prescribed by a native assignment signature
(`AssignmentSignature Z`). It needs one actual copy inside `Z` for the
internal-pair signature, one copy from each exception to its assigned core
otherwise, and one copy between the two cores exactly when the signature's
crossing parity is odd. This is the boundary of a compressed matching in
Step 2 of the proof of Lemma 4.4 of the manuscript.

The main theorem chooses all these copies at once. Distinct rounds use
distinct original copies; in particular, rounds sharing an exceptional
endpoint pair use distinct parallel copies of that pair. Every round is a
matching covering `Z`, leaves an even number of vertices uncovered in each
core, and has the prescribed crossing count. Each core vertex lies in at
most `a` rounds, and the copies used from every pool are counted exactly.

The hypotheses are an outside-degree bound `a` at every core vertex and a
strict capacity inequality for every pool that some round uses. The
construction applies the graph-independent greedy selection
`CircuitPatternRealization.exists_pool_selection`.

This module does not choose the multiplicities of the signatures, complete
the rounds inside the cores, or prove that a residual graph has no overfull
set.
-/

noncomputable section

namespace Overfull.AssignedParts

open Finset Classical
open scoped BigOperators

variable {V E : Type*}

/-! ### Pools, slots and their demands -/

/-- The three kinds of native boundary pools for two cores. -/
inductive NativePool (Z : Finset V) where
  /-- Copies with both ends in the exceptional set. -/
  | internal : NativePool Z
  /-- Copies from one exception to the indicated original core. -/
  | toCore : ↥Z → Fin 2 → NativePool Z
  /-- Copies between the two original cores. -/
  | crossing : NativePool Z

/-- Slot tags of a round: `none` is the optional crossing slot, `some none`
the internal exceptional pair, and `some (some z)` the slot at `z`. -/
abbrev SlotTag (Z : Finset V) := Option (Option ↥Z)

/-- The parity of the old-core crossing count prescribed by a signature:
the parity of the order of its first assigned core part. -/
def signatureCrossingBit (U₀ Z : Finset V) : AssignmentSignature Z → ℕ
  | none => U₀.card % 2
  | some σ => (U₀.card + (univ.filter (fun z : ↥Z => σ z = 0)).card) % 2

/-- The slots needed by a round with the given signature. -/
def SlotDemanded (U₀ Z : Finset V) (p : AssignmentSignature Z) : SlotTag Z → Prop
  | none => signatureCrossingBit U₀ Z p = 1
  | some none => p = none
  | some (some _) => p ≠ none

/-- The pool supplying a slot. -/
def slotPool {Z : Finset V} (p : AssignmentSignature Z) : SlotTag Z → NativePool Z
  | none => .crossing
  | some none => .internal
  | some (some z) => .toCore z (p.elim 0 (fun σ => σ z))

/-- The number of core endpoints of a copy in each pool. -/
def nativePoolArity {Z : Finset V} : NativePool Z → ℕ
  | .internal => 0
  | .toCore _ _ => 1
  | .crossing => 2

/-- The number of core endpoints of the copy filling a slot. -/
def slotArity {Z : Finset V} : SlotTag Z → ℕ
  | none => 2
  | some none => 0
  | some (some _) => 1

/-- A round with the given signature takes one copy from this pool. -/
def RoundUses (U₀ Z : Finset V) (p : AssignmentSignature Z) (b : NativePool Z) : Prop :=
  ∃ t, SlotDemanded U₀ Z p t ∧ slotPool p t = b

theorem signatureCrossingBit_lt_two (U₀ Z : Finset V) (p : AssignmentSignature Z) :
    signatureCrossingBit U₀ Z p < 2 := by
  cases p <;> exact Nat.mod_lt _ (by decide)

theorem slotPool_injective {Z : Finset V} (p : AssignmentSignature Z) :
    Function.Injective (slotPool p) := by
  intro t t' h
  rcases t with _ | _ | z <;> rcases t' with _ | _ | z' <;> simp_all [slotPool]

theorem nativePoolArity_slotPool {Z : Finset V} (p : AssignmentSignature Z)
    (t : SlotTag Z) : nativePoolArity (slotPool p t) = slotArity t := by
  rcases t with _ | _ | z <;> rfl

theorem sum_slotArity (Z : Finset V) : ∑ t : SlotTag Z, slotArity t = Z.card + 2 := by
  rw [Fintype.sum_option, Fintype.sum_option]
  simp only [slotArity, sum_const, card_univ, Fintype.card_coe, smul_eq_mul, mul_one]
  omega

theorem roundUses_crossing_iff (U₀ Z : Finset V) (p : AssignmentSignature Z) :
    RoundUses U₀ Z p .crossing ↔ signatureCrossingBit U₀ Z p = 1 := by
  constructor
  · rintro ⟨t, ht, hp⟩
    rcases t with _ | _ | z
    · exact ht
    · simp [slotPool] at hp
    · simp [slotPool] at hp
  · intro h
    exact ⟨none, h, rfl⟩

theorem roundUses_internal_iff (U₀ Z : Finset V) (p : AssignmentSignature Z) :
    RoundUses U₀ Z p .internal ↔ p = none := by
  constructor
  · rintro ⟨t, ht, hp⟩
    rcases t with _ | _ | z
    · simp [slotPool] at hp
    · exact ht
    · simp [slotPool] at hp
  · intro h
    exact ⟨some none, h, rfl⟩

theorem roundUses_toCore_iff (U₀ Z : Finset V) (p : AssignmentSignature Z)
    (z : ↥Z) (i : Fin 2) :
    RoundUses U₀ Z p (.toCore z i) ↔ ∃ σ, p = some σ ∧ σ z = i := by
  constructor
  · rintro ⟨t, ht, hp⟩
    rcases t with _ | _ | z'
    · simp [slotPool] at hp
    · simp [slotPool] at hp
    · rcases p with _ | σ
      · simp [SlotDemanded] at ht
      · simp only [slotPool, Option.elim, NativePool.toCore.injEq] at hp
        obtain ⟨rfl, hi⟩ := hp
        exact ⟨σ, rfl, hi⟩
  · rintro ⟨σ, rfl, hi⟩
    refine ⟨some (some z), ?_, ?_⟩
    · simp [SlotDemanded]
    · simp [slotPool, hi]

/-- The exceptional-to-core pools used by a signature are exactly the
assignments recorded by `signatureAssignsCore`, whose total weight is the
pool size (`signature_assignment_weight_eq_pool`). -/
theorem roundUses_toCore_iff_signatureAssignsCore (U₀ Z : Finset V)
    (p : AssignmentSignature Z) (z : ↥Z) (i : Fin 2) :
    RoundUses U₀ Z p (.toCore z i) ↔ signatureAssignsCore p z i :=
  roundUses_toCore_iff U₀ Z p z i

/-! ### The actual copies in each pool -/

variable (G : Multigraph V E) [Fintype E]

/-- The original copies forming each native boundary pool. -/
def nativePool (U₀ U₁ Z : Finset V) : NativePool Z → Finset E
  | .internal => G.internalOn univ Z
  | .toCore z i => exceptionCorePool G z.val (if i = 0 then U₀ else U₁)
  | .crossing => coreCrossingPool G U₀ U₁

/-- The endpoints of an actual copy lying in one of the two original cores. -/
def nativeCoreEnds (U₀ U₁ : Finset V) (e : E) : Finset V :=
  ({G.firstEnd e, G.secondEnd e} : Finset V).filter (fun v => v ∈ U₀ ∨ v ∈ U₁)

omit [Fintype E] in
theorem mem_nativeCoreEnds (U₀ U₁ : Finset V) (e : E) (v : V) :
    v ∈ nativeCoreEnds G U₀ U₁ e ↔ v ∈ G.edge e ∧ (v ∈ U₀ ∨ v ∈ U₁) := by
  rw [nativeCoreEnds, mem_filter, G.incident_iff, mem_insert, mem_singleton]
  constructor
  · rintro ⟨h | h, hv⟩
    · exact ⟨Or.inl h.symm, hv⟩
    · exact ⟨Or.inr h.symm, hv⟩
  · rintro ⟨h | h, hv⟩
    · exact ⟨Or.inl h.symm, hv⟩
    · exact ⟨Or.inr h.symm, hv⟩

omit [Fintype E] in
theorem nativeCoreEnds_card_le_two (U₀ U₁ : Finset V) (e : E) :
    (nativeCoreEnds G U₀ U₁ e).card ≤ 2 :=
  (card_filter_le _ _).trans ((card_insert_le _ _).trans (by simp))

theorem mem_internalPool_iff (Z : Finset V) (e : E) :
    e ∈ G.internalOn univ Z ↔ G.firstEnd e ∈ Z ∧ G.secondEnd e ∈ Z := by
  simp [Multigraph.internalOn]

theorem mem_exceptionCorePool_iff (z : V) (U : Finset V) (e : E) :
    e ∈ exceptionCorePool G z U ↔ z ∈ G.edge e ∧ G.otherEnd z e ∈ U := by
  simp [exceptionCorePool]

/-- An actual copy between the two disjoint cores has one end in each. -/
theorem exists_ends_of_mem_coreCrossingPool {U₀ U₁ : Finset V} (h01 : Disjoint U₀ U₁)
    {e : E} (he : e ∈ coreCrossingPool G U₀ U₁) :
    ∃ x y, G.edge e = s(x, y) ∧ x ∈ U₀ ∧ y ∈ U₁ := by
  have h := (mem_coreCrossings_iff G univ U₀ U₁ h01 e).mp he
  rcases h.2 with ⟨h0, h1⟩ | ⟨h1, h0⟩
  · exact ⟨_, _, (G.edge_eq e).symm, h0, h1⟩
  · exact ⟨_, _, (G.edge_eq e).symm.trans Sym2.eq_swap, h0, h1⟩

/-- The two endpoints of an internal exceptional copy. -/
theorem ends_of_mem_internalPool {Z : Finset V} {e : E} (he : e ∈ G.internalOn univ Z) :
    G.edge e = s(G.firstEnd e, G.secondEnd e) ∧ G.firstEnd e ∈ Z ∧ G.secondEnd e ∈ Z :=
  ⟨(G.edge_eq e).symm, (mem_internalPool_iff G Z e).mp he⟩

omit [Fintype E] in
/-- The endpoint and the other end of a copy given by an explicit pair. -/
theorem mem_pair_cases {e : E} {x y v : V} (he : G.edge e = s(x, y))
    (hv : v ∈ G.edge e) :
    (v = x ∧ G.otherEnd v e = y) ∨ (v = y ∧ G.otherEnd v e = x) := by
  rw [he, Sym2.mem_iff] at hv
  rcases hv with rfl | rfl
  · exact Or.inl ⟨rfl, G.otherEnd_eq_of_edge e _ _ he⟩
  · exact Or.inr ⟨rfl, G.otherEnd_eq_of_edge e _ _ (he.trans Sym2.eq_swap)⟩

omit [Fintype E] in
/-- A copy given by an explicit pair crosses a shore exactly when its two
specified ends do. -/
theorem crosses_iff_of_edge_eq {e : E} {x y : V} (he : G.edge e = s(x, y))
    (X : Finset V) :
    ((G.firstEnd e ∈ X) ≠ (G.secondEnd e ∈ X)) ↔ ((x ∈ X) ≠ (y ∈ X)) := by
  have h := (G.edge_eq e).trans he
  rcases Sym2.eq_iff.mp h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · rw [h₁, h₂]
  · rw [h₁, h₂]
    exact ne_comm

section Pools

variable {U₀ U₁ Z : Finset V}

/-- The unique exceptional endpoint of a copy from an exception to a core. -/
theorem exceptional_end_of_mem_exceptionCorePool {U : Finset V} (hUZ : Disjoint U Z)
    {z w : V} {e : E} (he : e ∈ exceptionCorePool G z U) (hw : w ∈ G.edge e)
    (hwZ : w ∈ Z) : w = z := by
  obtain ⟨hz, ho⟩ := (mem_exceptionCorePool_iff G z U e).mp he
  rw [G.edge_eq_otherEnd z e hz, Sym2.mem_iff] at hw
  rcases hw with h | h
  · exact h
  · have hwU : w ∈ U := by rw [h]; exact ho
    exact (disjoint_left.mp hUZ hwU hwZ).elim

theorem mem_core_of_toCore {i : Fin 2} {o : V}
    (ho : o ∈ (if i = 0 then U₀ else U₁)) : o ∈ U₀ ∨ o ∈ U₁ := by
  split_ifs at ho
  · exact Or.inl ho
  · exact Or.inr ho

/-- A vertex of the `i`th core lies in the `j`th core exactly when `i = j`. -/
theorem mem_coreSet_iff (h01 : Disjoint U₀ U₁) {i j : Fin 2} {o : V}
    (ho : o ∈ (if i = 0 then U₀ else U₁)) :
    o ∈ (if j = 0 then U₀ else U₁) ↔ i = j := by
  constructor
  · intro hj
    by_contra hij
    by_cases hi : i = 0
    · have hj0 : j ≠ 0 := fun h => hij (hi.trans h.symm)
      rw [if_pos hi] at ho
      rw [if_neg hj0] at hj
      exact disjoint_left.mp h01 ho hj
    · by_cases hj0 : j = 0
      · rw [if_neg hi] at ho
        rw [if_pos hj0] at hj
        exact disjoint_left.mp h01 hj ho
      · exact hij ((Fin.eq_one_of_ne_zero i hi).trans (Fin.eq_one_of_ne_zero j hj0).symm)
  · rintro rfl
    exact ho

theorem coreSet_disjoint (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z) (i : Fin 2) :
    Disjoint (if i = 0 then U₀ else U₁) Z := by
  split_ifs
  · exact h0Z
  · exact h1Z

/-- Every endpoint of a pool copy is exceptional or lies in a core. -/
theorem nativePool_endpoint (h01 : Disjoint U₀ U₁) {b : NativePool Z} {e : E}
    (he : e ∈ nativePool G U₀ U₁ Z b) {w : V} (hw : w ∈ G.edge e) :
    w ∈ Z ∨ w ∈ U₀ ∨ w ∈ U₁ := by
  cases b with
  | internal =>
      change e ∈ G.internalOn univ Z at he
      obtain ⟨hxy, hx, hy⟩ := ends_of_mem_internalPool G he
      rw [hxy, Sym2.mem_iff] at hw
      rcases hw with rfl | rfl
      · exact Or.inl hx
      · exact Or.inl hy
  | toCore z i =>
      change e ∈ exceptionCorePool G z.val (if i = 0 then U₀ else U₁) at he
      obtain ⟨hz, ho⟩ := (mem_exceptionCorePool_iff G _ _ e).mp he
      rw [G.edge_eq_otherEnd z.val e hz, Sym2.mem_iff] at hw
      rcases hw with rfl | rfl
      · exact Or.inl z.property
      · exact Or.inr (mem_core_of_toCore ho)
  | crossing =>
      change e ∈ coreCrossingPool G U₀ U₁ at he
      obtain ⟨x, y, hxy, hx, hy⟩ := exists_ends_of_mem_coreCrossingPool G h01 he
      rw [hxy, Sym2.mem_iff] at hw
      rcases hw with rfl | rfl
      · exact Or.inr (Or.inl hx)
      · exact Or.inr (Or.inr hy)

/-- A pool copy at a core vertex leaves that vertex's core. -/
theorem nativePool_otherEnd_not_mem (h01 : Disjoint U₀ U₁)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    {b : NativePool Z} {e : E} (he : e ∈ nativePool G U₀ U₁ Z b) {v : V}
    (hv : v ∈ G.edge e) :
    (v ∈ U₀ → G.otherEnd v e ∉ U₀) ∧ (v ∈ U₁ → G.otherEnd v e ∉ U₁) := by
  have n0 : ∀ x, x ∈ U₀ → x ∈ Z → False := fun x h hz => disjoint_left.mp h0Z h hz
  have n1 : ∀ x, x ∈ U₁ → x ∈ Z → False := fun x h hz => disjoint_left.mp h1Z h hz
  have n01 : ∀ x, x ∈ U₀ → x ∈ U₁ → False := fun x h h' => disjoint_left.mp h01 h h'
  cases b with
  | internal =>
      change e ∈ G.internalOn univ Z at he
      obtain ⟨hxy, hx, hy⟩ := ends_of_mem_internalPool G he
      rcases mem_pair_cases G hxy hv with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact ⟨fun h => (n0 _ h hx).elim, fun h => (n1 _ h hx).elim⟩
      · exact ⟨fun h => (n0 _ h hy).elim, fun h => (n1 _ h hy).elim⟩
  | toCore z i =>
      change e ∈ exceptionCorePool G z.val (if i = 0 then U₀ else U₁) at he
      obtain ⟨hz, ho⟩ := (mem_exceptionCorePool_iff G _ _ e).mp he
      rcases mem_pair_cases G (G.edge_eq_otherEnd z.val e hz) hv with
        ⟨rfl, _⟩ | ⟨rfl, hother⟩
      · exact ⟨fun h => (n0 _ h z.property).elim, fun h => (n1 _ h z.property).elim⟩
      · rw [hother]
        exact ⟨fun _ h => n0 _ h z.property, fun _ h => n1 _ h z.property⟩
  | crossing =>
      change e ∈ coreCrossingPool G U₀ U₁ at he
      obtain ⟨x, y, hxy, hx, hy⟩ := exists_ends_of_mem_coreCrossingPool G h01 he
      rcases mem_pair_cases G hxy hv with ⟨rfl, hother⟩ | ⟨rfl, hother⟩
      · rw [hother]
        exact ⟨fun _ h => n01 _ h hy, fun h => (n01 _ hx h).elim⟩
      · rw [hother]
        exact ⟨fun h => (n01 _ h hy).elim, fun _ h => n01 _ hx h⟩

/-- Distinct pool kinds consist of distinct original copies. -/
theorem nativePool_disjoint (h01 : Disjoint U₀ U₁)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z) (b c : NativePool Z) (hbc : b ≠ c) :
    Disjoint (nativePool G U₀ U₁ Z b) (nativePool G U₀ U₁ Z c) := by
  have n0 : ∀ x, x ∈ U₀ → x ∈ Z → False := fun x h hz => disjoint_left.mp h0Z h hz
  have n1 : ∀ x, x ∈ U₁ → x ∈ Z → False := fun x h hz => disjoint_left.mp h1Z h hz
  -- The exceptional endpoints of copies in each pool.
  have hint : ∀ {e : E}, e ∈ nativePool G U₀ U₁ Z .internal →
      G.firstEnd e ∈ Z ∧ G.secondEnd e ∈ Z := fun he =>
    (mem_internalPool_iff G Z _).mp he
  have hcr : ∀ {e : E}, e ∈ nativePool G U₀ U₁ Z .crossing →
      ∃ x y, G.edge e = s(x, y) ∧ x ∈ U₀ ∧ y ∈ U₁ := fun he =>
    exists_ends_of_mem_coreCrossingPool G h01 he
  have htc : ∀ {e : E} {z : ↥Z} {i : Fin 2}, e ∈ nativePool G U₀ U₁ Z (.toCore z i) →
      G.edge e = s(z.val, G.otherEnd z.val e) ∧
        G.otherEnd z.val e ∈ (if i = 0 then U₀ else U₁) := by
    intro e z i he
    obtain ⟨hz, ho⟩ := (mem_exceptionCorePool_iff G _ _ e).mp he
    exact ⟨G.edge_eq_otherEnd z.val e hz, ho⟩
  apply disjoint_left.mpr
  intro e heb hec
  cases b with
  | internal =>
      obtain ⟨hx, hy⟩ := hint heb
      cases c with
      | internal => exact hbc rfl
      | toCore z i =>
          obtain ⟨hxy, ho⟩ := htc hec
          have hoZ : G.otherEnd z.val e ∈ Z := by
            have hmem : G.otherEnd z.val e ∈ G.edge e := by rw [hxy]; simp
            rcases (G.incident_iff e _).mp hmem with h | h
            · rw [← h]; exact hx
            · rw [← h]; exact hy
          rcases mem_core_of_toCore ho with h | h
          · exact n0 _ h hoZ
          · exact n1 _ h hoZ
      | crossing =>
          obtain ⟨x, y, hxy, hx', _⟩ := hcr hec
          have hxe : x ∈ G.edge e := by rw [hxy]; simp
          have hxZ : x ∈ Z := by
            rcases (G.incident_iff e x).mp hxe with h | h
            · rw [← h]; exact hx
            · rw [← h]; exact hy
          exact n0 _ hx' hxZ
  | toCore z i =>
      obtain ⟨hxy, ho⟩ := htc heb
      cases c with
      | internal =>
          obtain ⟨hx, hy⟩ := hint hec
          have hoZ : G.otherEnd z.val e ∈ Z := by
            have hmem : G.otherEnd z.val e ∈ G.edge e := by rw [hxy]; simp
            rcases (G.incident_iff e _).mp hmem with h | h
            · rw [← h]; exact hx
            · rw [← h]; exact hy
          rcases mem_core_of_toCore ho with h | h
          · exact n0 _ h hoZ
          · exact n1 _ h hoZ
      | toCore z' i' =>
          obtain ⟨hxy', ho'⟩ := htc hec
          have hz' : z'.val ∈ G.edge e := by rw [hxy']; simp
          have hzz : z'.val = z.val := by
            rw [hxy, Sym2.mem_iff] at hz'
            rcases hz' with h | h
            · exact h
            · rcases mem_core_of_toCore ho with h' | h'
              · have hz0 : z'.val ∈ U₀ := by rw [h]; exact h'
                exact (n0 _ hz0 z'.property).elim
              · have hz1 : z'.val ∈ U₁ := by rw [h]; exact h'
                exact (n1 _ hz1 z'.property).elim
          have hzeq : z' = z := Subtype.ext hzz
          subst hzeq
          have hii : i = i' := (mem_coreSet_iff h01 ho).mp ho'
          exact hbc (by rw [hii])
      | crossing =>
          obtain ⟨x, y, hxy', hx, hy⟩ := hcr hec
          have hz : z.val ∈ G.edge e := by rw [hxy]; simp
          rw [hxy', Sym2.mem_iff] at hz
          rcases hz with h | h
          · have hz0 : z.val ∈ U₀ := by rw [h]; exact hx
            exact n0 _ hz0 z.property
          · have hz1 : z.val ∈ U₁ := by rw [h]; exact hy
            exact n1 _ hz1 z.property
  | crossing =>
      obtain ⟨x, y, hxy, hx, hy⟩ := hcr heb
      cases c with
      | internal =>
          obtain ⟨hx', hy'⟩ := hint hec
          have hxe : x ∈ G.edge e := by rw [hxy]; simp
          have hxZ : x ∈ Z := by
            rcases (G.incident_iff e x).mp hxe with h | h
            · rw [← h]; exact hx'
            · rw [← h]; exact hy'
          exact n0 _ hx hxZ
      | toCore z i =>
          obtain ⟨hxy', _⟩ := htc hec
          have hz : z.val ∈ G.edge e := by rw [hxy']; simp
          rw [hxy, Sym2.mem_iff] at hz
          rcases hz with h | h
          · have hz0 : z.val ∈ U₀ := by rw [h]; exact hx
            exact n0 _ hz0 z.property
          · have hz1 : z.val ∈ U₁ := by rw [h]; exact hy
            exact n1 _ hz1 z.property
      | crossing => exact hbc rfl

/-- The number of core endpoints of a pool copy is at most its arity. -/
theorem nativeCoreEnds_card_le_arity (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (b : NativePool Z) (e : E) (he : e ∈ nativePool G U₀ U₁ Z b) :
    (nativeCoreEnds G U₀ U₁ e).card ≤ nativePoolArity b := by
  cases b with
  | internal =>
      change e ∈ G.internalOn univ Z at he
      obtain ⟨hxy, hx, hy⟩ := ends_of_mem_internalPool G he
      have hempty : nativeCoreEnds G U₀ U₁ e = ∅ := by
        apply eq_empty_of_forall_notMem
        intro v hv
        obtain ⟨hve, hcore⟩ := (mem_nativeCoreEnds G U₀ U₁ e v).mp hv
        have hvZ : v ∈ Z := by
          rw [hxy, Sym2.mem_iff] at hve
          rcases hve with rfl | rfl
          · exact hx
          · exact hy
        rcases hcore with h0 | h1
        · exact disjoint_left.mp h0Z h0 hvZ
        · exact disjoint_left.mp h1Z h1 hvZ
      simp [hempty, nativePoolArity]
  | toCore z i =>
      change e ∈ exceptionCorePool G z.val (if i = 0 then U₀ else U₁) at he
      obtain ⟨hz, _⟩ := (mem_exceptionCorePool_iff G _ _ e).mp he
      have hsub : nativeCoreEnds G U₀ U₁ e ⊆ {G.otherEnd z.val e} := by
        intro v hv
        obtain ⟨hve, hcore⟩ := (mem_nativeCoreEnds G U₀ U₁ e v).mp hv
        rw [G.edge_eq_otherEnd z.val e hz, Sym2.mem_iff] at hve
        rcases hve with rfl | rfl
        · rcases hcore with h0 | h1
          · exact (disjoint_left.mp h0Z h0 z.property).elim
          · exact (disjoint_left.mp h1Z h1 z.property).elim
        · exact mem_singleton_self _
      exact (card_le_card hsub).trans (by simp [nativePoolArity])
  | crossing =>
      exact (nativeCoreEnds_card_le_two G U₀ U₁ e).trans (by simp [nativePoolArity])

variable [Fintype V]

/-- Each core vertex is a core endpoint of at most `a` copies of each pool. -/
theorem nativePool_coreEnds_card_le (h01 : Disjoint U₀ U₁)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z) {a : ℕ}
    (hout₀ : ∀ v ∈ U₀, (G.edgesTo v U₀ᶜ).card ≤ a)
    (hout₁ : ∀ v ∈ U₁, (G.edgesTo v U₁ᶜ).card ≤ a) (b : NativePool Z) (v : V) :
    ((nativePool G U₀ U₁ Z b).filter (fun e => v ∈ nativeCoreEnds G U₀ U₁ e)).card ≤ a := by
  by_cases h0 : v ∈ U₀
  · refine (card_le_card ?_).trans (hout₀ v h0)
    intro e he
    obtain ⟨heb, hv⟩ := mem_filter.mp he
    have hve := ((mem_nativeCoreEnds G U₀ U₁ e v).mp hv).1
    exact (G.mem_edgesTo v U₀ᶜ e).mpr ⟨hve, mem_compl.mpr
      ((nativePool_otherEnd_not_mem G h01 h0Z h1Z heb hve).1 h0)⟩
  · by_cases h1 : v ∈ U₁
    · refine (card_le_card ?_).trans (hout₁ v h1)
      intro e he
      obtain ⟨heb, hv⟩ := mem_filter.mp he
      have hve := ((mem_nativeCoreEnds G U₀ U₁ e v).mp hv).1
      exact (G.mem_edgesTo v U₁ᶜ e).mpr ⟨hve, mem_compl.mpr
        ((nativePool_otherEnd_not_mem G h01 h0Z h1Z heb hve).2 h1)⟩
    · have hempty : (nativePool G U₀ U₁ Z b).filter
          (fun e => v ∈ nativeCoreEnds G U₀ U₁ e) = ∅ := by
        apply filter_false_of_mem
        intro e _ hv
        rcases ((mem_nativeCoreEnds G U₀ U₁ e v).mp hv).2 with h | h
        · exact h0 h
        · exact h1 h
      rw [hempty, card_empty]
      exact Nat.zero_le a

end Pools

/-! ### One round -/

section Round

variable {U₀ U₁ Z : Finset V}

/-- Three vertices of a set with at most two elements are not distinct. -/
theorem eq_or_eq_of_card_le_two {x y z : V} (hxy : x ≠ y) (hx : x ∈ Z) (hy : y ∈ Z)
    (hZ : Z.card ≤ 2) (hz : z ∈ Z) : z = x ∨ z = y := by
  have hsub : ({x, y} : Finset V) ⊆ Z := by
    intro v hv
    rcases mem_insert.mp hv with h | h
    · rw [h]; exact hx
    · rw [mem_singleton.mp h]; exact hy
  have heq := eq_of_subset_of_card_le hsub (by rw [card_pair hxy]; exact hZ)
  rw [← heq] at hz
  simpa using hz

/-- Two distinct slots of one signature have no common exceptional endpoint. -/
theorem slot_exceptional_ends_distinct (h01 : Disjoint U₀ U₁)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    {p p' : AssignmentSignature Z} {t t' : SlotTag Z} (ht : SlotDemanded U₀ Z p t)
    (ht' : SlotDemanded U₀ Z p' t') (hpp : p = p') (htt : t ≠ t') {e f : E}
    (he : e ∈ nativePool G U₀ U₁ Z (slotPool p t))
    (hf : f ∈ nativePool G U₀ U₁ Z (slotPool p' t'))
    {w : V} (hwZ : w ∈ Z) (hwe : w ∈ G.edge e) (hwf : w ∈ G.edge f) : False := by
  subst hpp
  have hnotcross : ∀ {g : E}, g ∈ nativePool G U₀ U₁ Z .crossing → w ∈ G.edge g → False := by
    intro g hg hwg
    obtain ⟨x, y, hxy, hx, hy⟩ := exists_ends_of_mem_coreCrossingPool G h01 hg
    rw [hxy, Sym2.mem_iff] at hwg
    rcases hwg with h | h
    · rw [h] at hwZ
      exact disjoint_left.mp h0Z hx hwZ
    · rw [h] at hwZ
      exact disjoint_left.mp h1Z hy hwZ
  rcases t with _ | _ | z <;> rcases t' with _ | _ | z'
  · exact htt rfl
  · exact hnotcross he hwe
  · exact hnotcross he hwe
  · exact hnotcross hf hwf
  · exact htt rfl
  · exact ht' ht
  · exact hnotcross hf hwf
  · exact ht ht'
  · change e ∈ exceptionCorePool G z.val
      (if p.elim 0 (fun σ => σ z) = 0 then U₀ else U₁) at he
    change f ∈ exceptionCorePool G z'.val
      (if p.elim 0 (fun σ => σ z') = 0 then U₀ else U₁) at hf
    have hze := exceptional_end_of_mem_exceptionCorePool G
      (coreSet_disjoint h0Z h1Z _) he hwe hwZ
    have hzf := exceptional_end_of_mem_exceptionCorePool G
      (coreSet_disjoint h0Z h1Z _) hf hwf hwZ
    have hzz : z = z' := Subtype.ext (hze.symm.trans hzf)
    exact htt (by rw [hzz])

/-- A pool copy from an exception to its `i`th core crosses the `j`th core
exactly when `i = j`. -/
theorem toCore_crosses_iff (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z)
    (h1Z : Disjoint U₁ Z) {z : ↥Z} {i : Fin 2} {e : E}
    (he : e ∈ nativePool G U₀ U₁ Z (.toCore z i)) (j : Fin 2) :
    ((G.firstEnd e ∈ (if j = 0 then U₀ else U₁)) ≠
      (G.secondEnd e ∈ (if j = 0 then U₀ else U₁))) ↔ i = j := by
  change e ∈ exceptionCorePool G z.val (if i = 0 then U₀ else U₁) at he
  obtain ⟨hz, ho⟩ := (mem_exceptionCorePool_iff G _ _ e).mp he
  rw [crosses_iff_of_edge_eq G (G.edge_eq_otherEnd z.val e hz)]
  have hzj : z.val ∉ (if j = 0 then U₀ else U₁) := fun h =>
    disjoint_left.mp (coreSet_disjoint h0Z h1Z j) h z.property
  rw [← mem_coreSet_iff h01 ho]
  constructor
  · intro h
    by_contra hno
    exact h (propext (iff_of_false hzj hno))
  · intro h heq
    exact hzj (Eq.mpr heq h)

/-- A copy between the two cores crosses each of them. -/
theorem crossing_crosses {e : E}
    (he : e ∈ coreCrossingPool G U₀ U₁) (j : Fin 2) :
    (G.firstEnd e ∈ (if j = 0 then U₀ else U₁)) ≠
      (G.secondEnd e ∈ (if j = 0 then U₀ else U₁)) := by
  obtain ⟨he0, he1⟩ := mem_inter.mp he
  split_ifs
  · exact ((G.mem_cutOn univ U₀ e).mp he0).2
  · exact ((G.mem_cutOn univ U₁ e).mp he1).2

/-- The cut of a round at either core consists of its crossing copy and its
copies from exceptions assigned to that core. -/
theorem round_cut_card (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    {p : AssignmentSignature Z} {F : Finset E}
    (hmem : ∀ e ∈ F, ∃ b, RoundUses U₀ Z p b ∧ e ∈ nativePool G U₀ U₁ Z b)
    (hcard : ∀ b, (F ∩ nativePool G U₀ U₁ Z b).card =
      if RoundUses U₀ Z p b then 1 else 0)
    (j : Fin 2) :
    (G.cutOn F (if j = 0 then U₀ else U₁)).card =
      signatureCrossingBit U₀ Z p +
        (univ.filter (fun z : ↥Z => RoundUses U₀ Z p (.toCore z j))).card := by
  set X := if j = 0 then U₀ else U₁
  have hsplit : G.cutOn F X = (F ∩ nativePool G U₀ U₁ Z .crossing) ∪
      (univ : Finset ↥Z).biUnion (fun z => F ∩ nativePool G U₀ U₁ Z (.toCore z j)) := by
    ext e
    rw [Multigraph.mem_cutOn, mem_union, mem_biUnion]
    constructor
    · rintro ⟨heF, hcross⟩
      obtain ⟨b, _, heb⟩ := hmem e heF
      cases b with
      | internal =>
          exfalso
          change e ∈ G.internalOn univ Z at heb
          obtain ⟨hx, hy⟩ := (mem_internalPool_iff G Z e).mp heb
          have hxX : G.firstEnd e ∉ X := fun h =>
            disjoint_left.mp (coreSet_disjoint h0Z h1Z j) h hx
          have hyX : G.secondEnd e ∉ X := fun h =>
            disjoint_left.mp (coreSet_disjoint h0Z h1Z j) h hy
          exact hcross (propext (iff_of_false hxX hyX))
      | toCore z i =>
          have hij := (toCore_crosses_iff G h01 h0Z h1Z heb j).mp hcross
          rw [hij] at heb
          exact Or.inr ⟨z, mem_univ _, mem_inter.mpr ⟨heF, heb⟩⟩
      | crossing =>
          exact Or.inl (mem_inter.mpr ⟨heF, heb⟩)
    · rintro (h | ⟨z, _, h⟩)
      · obtain ⟨heF, heb⟩ := mem_inter.mp h
        exact ⟨heF, crossing_crosses G heb j⟩
      · obtain ⟨heF, heb⟩ := mem_inter.mp h
        exact ⟨heF, (toCore_crosses_iff G h01 h0Z h1Z heb j).mpr rfl⟩
  have hdisj : Disjoint (F ∩ nativePool G U₀ U₁ Z .crossing)
      ((univ : Finset ↥Z).biUnion (fun z => F ∩ nativePool G U₀ U₁ Z (.toCore z j))) := by
    rw [disjoint_biUnion_right]
    intro z _
    exact (nativePool_disjoint G h01 h0Z h1Z _ _ (by simp)).mono
      inter_subset_right inter_subset_right
  rw [hsplit, card_union_of_disjoint hdisj, card_biUnion]
  · congr 1
    · rw [hcard]
      have hlt := signatureCrossingBit_lt_two U₀ Z p
      split_ifs with hu
      · exact ((roundUses_crossing_iff U₀ Z p).mp hu).symm
      · have hne := (roundUses_crossing_iff U₀ Z p).not.mp hu
        omega
    · rw [card_filter]
      apply sum_congr rfl
      intro z _
      exact hcard _
  · intro z _ z' _ hzz
    change Disjoint (F ∩ nativePool G U₀ U₁ Z (.toCore z j))
      (F ∩ nativePool G U₀ U₁ Z (.toCore z' j))
    exact (nativePool_disjoint G h01 h0Z h1Z _ _ (by simpa using hzz)).mono
      inter_subset_right inter_subset_right

/-- A round of a schedule leaves an even number of vertices uncovered in each core. -/
theorem round_uncovered_even (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z)
    (h1Z : Disjoint U₁ Z) (hZ : Z.card ≤ 2) (heven : Even (U₀.card + U₁.card + Z.card))
    {p : AssignmentSignature Z} {F : Finset E} (hF : G.IsMatching F)
    (hmem : ∀ e ∈ F, ∃ b, RoundUses U₀ Z p b ∧ e ∈ nativePool G U₀ U₁ Z b)
    (hcard : ∀ b, (F ∩ nativePool G U₀ U₁ Z b).card =
      if RoundUses U₀ Z p b then 1 else 0) :
    Even (U₀ \ G.edgeSupport F).card ∧ Even (U₁ \ G.edgeSupport F).card := by
  have hc0 := round_cut_card G h01 h0Z h1Z hmem hcard 0
  have hc1 := round_cut_card G h01 h0Z h1Z hmem hcard 1
  rw [if_pos rfl] at hc0
  rw [if_neg (show (1 : Fin 2) ≠ 0 by decide)] at hc1
  rw [hF.uncovered_even_iff_cut_parity G U₀, hF.uncovered_even_iff_cut_parity G U₁, hc0, hc1]
  have hev := Nat.even_iff.mp heven
  cases hp : p with
  | none =>
      have hfilter : ∀ j : Fin 2,
          (univ.filter (fun z : ↥Z => RoundUses U₀ Z none (.toCore z j))).card = 0 := by
        intro j
        rw [card_eq_zero]
        apply filter_false_of_mem
        intro z _ hz
        obtain ⟨σ, hσ, _⟩ := (roundUses_toCore_iff U₀ Z none z j).mp hz
        cases hσ
      rw [hfilter 0, hfilter 1]
      -- the internal pair uses both exceptional vertices
      have hint := hcard .internal
      rw [if_pos ((roundUses_internal_iff U₀ Z p).mpr hp)] at hint
      have hpos : 0 < (F ∩ nativePool G U₀ U₁ Z .internal).card := by
        rw [hint]; exact Nat.one_pos
      obtain ⟨e, he⟩ := card_pos.mp hpos
      have heb : e ∈ G.internalOn univ Z := (mem_inter.mp he).2
      obtain ⟨hx, hy⟩ := (mem_internalPool_iff G Z e).mp heb
      have hpair : ({G.firstEnd e, G.secondEnd e} : Finset V) ⊆ Z := by
        intro v hv
        rcases mem_insert.mp hv with h | h
        · rw [h]; exact hx
        · rw [mem_singleton.mp h]; exact hy
      have h2 := card_le_card hpair
      rw [card_pair (G.endpoints_distinct e)] at h2
      simp only [signatureCrossingBit]
      constructor <;> omega
  | some σ =>
      have hfilter : ∀ j : Fin 2,
          (univ.filter (fun z : ↥Z => RoundUses U₀ Z (some σ) (.toCore z j))) =
            univ.filter (fun z : ↥Z => σ z = j) := by
        intro j
        apply filter_congr
        intro z _
        rw [roundUses_toCore_iff]
        constructor
        · rintro ⟨σ', hσ', hz⟩
          cases hσ'
          exact hz
        · intro hz
          exact ⟨σ, rfl, hz⟩
      rw [hfilter 0, hfilter 1]
      have hsplit := filter_card_add_filter_neg_card_eq_card
        (s := (univ : Finset ↥Z)) (fun z : ↥Z => σ z = 0)
      have hneg : (univ : Finset ↥Z).filter (fun z => ¬ σ z = 0) =
          univ.filter (fun z => σ z = 1) := by
        apply filter_congr
        intro z _
        constructor
        · exact Fin.eq_one_of_ne_zero _
        · intro h h0
          rw [h0] at h
          exact absurd h (by decide)
      rw [hneg, card_univ, Fintype.card_coe] at hsplit
      simp only [signatureCrossingBit]
      constructor <;> omega

end Round

/-! ### The slots of all rounds -/

/-- The slots of all rounds, each with its tag. -/
abbrev ScheduleSlot (U₀ Z : Finset V) {R : Type*} (sig : R → AssignmentSignature Z) :=
  {x : R × SlotTag Z // SlotDemanded U₀ Z (sig x.1) x.2}

theorem scheduleSlot_arity_sum_le {U₀ Z : Finset V} {R : Type*} [Fintype R]
    (sig : R → AssignmentSignature Z) (r : R) :
    ∑ s ∈ (univ : Finset (ScheduleSlot U₀ Z sig)).filter (fun s => s.val.1 = r),
      nativePoolArity (slotPool (sig s.val.1) s.val.2) ≤ Z.card + 2 := by
  calc
    _ = ∑ s ∈ (univ : Finset (ScheduleSlot U₀ Z sig)).filter (fun s => s.val.1 = r),
          slotArity s.val.2 :=
        sum_congr rfl (fun s _ => nativePoolArity_slotPool _ _)
    _ = ∑ t ∈ ((univ : Finset (ScheduleSlot U₀ Z sig)).filter
          (fun s => s.val.1 = r)).image (fun s => s.val.2), slotArity t := by
        rw [sum_image]
        intro s hs s' hs' h
        apply Subtype.ext
        apply Prod.ext
        · exact (mem_filter.mp hs).2.trans (mem_filter.mp hs').2.symm
        · exact h
    _ ≤ ∑ t : SlotTag Z, slotArity t := sum_le_sum_of_subset (subset_univ _)
    _ = Z.card + 2 := sum_slotArity Z

theorem scheduleSlot_demand_le {U₀ Z : Finset V} {R : Type*} [Fintype R]
    (sig : R → AssignmentSignature Z) (b : NativePool Z) :
    CircuitPatternRealization.demandCount
        (fun s : ScheduleSlot U₀ Z sig => slotPool (sig s.val.1) s.val.2) b ≤
      (univ.filter (fun r => RoundUses U₀ Z (sig r) b)).card := by
  unfold CircuitPatternRealization.demandCount
  apply card_le_card_of_injOn (fun s => s.val.1)
  · intro s hs
    exact mem_filter.mpr ⟨mem_univ _, s.val.2, s.property, (mem_filter.mp hs).2⟩
  · intro s hs s' hs' h
    have h' : s.val.1 = s'.val.1 := h
    have h1 : slotPool (sig s.val.1) s.val.2 = b := (mem_filter.mp hs).2
    have h2 : slotPool (sig s'.val.1) s'.val.2 = b := (mem_filter.mp hs').2
    apply Subtype.ext
    apply Prod.ext h'
    apply slotPool_injective (sig s.val.1)
    rw [h1, h']
    exact h2.symm

/-! ### The schedule -/

/-- A family of boundary rounds realizing prescribed native signatures by
pairwise disjoint sets of actual original copies. -/
structure NativeBoundarySchedule (U₀ U₁ Z : Finset V) {R : Type*} [Fintype R]
    (sig : R → AssignmentSignature Z) (a : ℕ) where
  /-- The actual copies used in each round. -/
  copies : R → Finset E
  /-- Every round is a matching of original copies. -/
  isMatching : ∀ r, G.IsMatching (copies r)
  /-- Distinct rounds use distinct original copies. -/
  disjoint : ∀ r r', r ≠ r' → Disjoint (copies r) (copies r')
  /-- Every copy of a round comes from a pool used by its signature. -/
  mem_pool : ∀ r, ∀ e ∈ copies r, ∃ b, RoundUses U₀ Z (sig r) b ∧ e ∈ nativePool G U₀ U₁ Z b
  /-- A round takes exactly one copy from each pool it uses, and none from the others. -/
  pool_card : ∀ r b, (copies r ∩ nativePool G U₀ U₁ Z b).card =
    if RoundUses U₀ Z (sig r) b then 1 else 0
  /-- Every round covers every exceptional vertex. -/
  covers : ∀ r, ∀ z ∈ Z, ∃ e ∈ copies r, z ∈ G.edge e
  /-- The crossing count is the prescribed parity. -/
  crossing_card : ∀ r, (copies r ∩ coreCrossingPool G U₀ U₁).card =
    signatureCrossingBit U₀ Z (sig r)
  /-- Every round leaves an even number of vertices uncovered in each core. -/
  uncovered_even : ∀ r, Even (U₀ \ G.edgeSupport (copies r)).card ∧
    Even (U₁ \ G.edgeSupport (copies r)).card
  /-- Every core vertex lies in at most `a` rounds. -/
  load : ∀ v ∈ U₀ ∪ U₁, (univ.filter (fun r => v ∈ G.edgeSupport (copies r))).card ≤ a
  /-- Exact accounting of the copies used from each pool. -/
  accounting : ∀ b, (nativePool G U₀ U₁ Z b ∩ univ.biUnion copies).card =
    (univ.filter (fun r => RoundUses U₀ Z (sig r) b)).card

/-- **Simultaneous native boundary schedule.** For two disjoint cores and at
most two exceptional vertices, any finite family of rounds prescribed by
native signatures is realized by pairwise disjoint matchings of actual
original copies. The hypotheses bound the copies leaving each core at every
core vertex by `a`, and require every used pool to exceed its demand by more
than `(|Z|+2)a`. -/
theorem exists_native_boundary_schedule [Fintype V] {U₀ U₁ Z : Finset V}
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hZ : Z.card ≤ 2) (heven : Even (U₀.card + U₁.card + Z.card))
    {R : Type*} [Fintype R] (sig : R → AssignmentSignature Z) (a : ℕ)
    (hout₀ : ∀ v ∈ U₀, (G.edgesTo v U₀ᶜ).card ≤ a)
    (hout₁ : ∀ v ∈ U₁, (G.edgesTo v U₁ᶜ).card ≤ a)
    (hcap : ∀ b : NativePool Z, (∃ r, RoundUses U₀ Z (sig r) b) →
      (univ.filter (fun r => RoundUses U₀ Z (sig r) b)).card + (Z.card + 2) * a <
        (nativePool G U₀ U₁ Z b).card) :
    Nonempty (NativeBoundarySchedule G U₀ U₁ Z sig a) := by
  obtain ⟨pick, hpick, hinj, hdisj⟩ := CircuitPatternRealization.exists_pool_selection
    (nativePool G U₀ U₁ Z)
    (fun s : ScheduleSlot U₀ Z sig => slotPool (sig s.val.1) s.val.2)
    (fun s => s.val.1) (nativeCoreEnds G U₀ U₁) nativePoolArity a (Z.card + 2)
    (nativePool_disjoint G h01 h0Z h1Z)
    (nativeCoreEnds_card_le_arity G h0Z h1Z)
    (fun b v => by convert nativePool_coreEnds_card_le G h01 h0Z h1Z hout₀ hout₁ b v)
    (fun r => by convert scheduleSlot_arity_sum_le (U₀ := U₀) sig r)
    (fun s => lt_of_le_of_lt
      (Nat.add_le_add_right (scheduleSlot_demand_le (U₀ := U₀) sig _) _)
      (hcap _ ⟨s.val.1, s.val.2, s.property, rfl⟩))
  let F : R → Finset E := fun r =>
    ((univ : Finset (ScheduleSlot U₀ Z sig)).filter (fun s => s.val.1 = r)).image pick
  have hmemF : ∀ r e, e ∈ F r ↔
      ∃ s : ScheduleSlot U₀ Z sig, s.val.1 = r ∧ pick s = e := by
    intro r e
    simp only [F, mem_image, mem_filter, mem_univ, true_and]
  have hpick' : ∀ s : ScheduleSlot U₀ Z sig,
      pick s ∈ nativePool G U₀ U₁ Z (slotPool (sig s.val.1) s.val.2) := hpick
  have hkind : ∀ (s : ScheduleSlot U₀ Z sig) b, pick s ∈ nativePool G U₀ U₁ Z b →
      slotPool (sig s.val.1) s.val.2 = b := by
    intro s b hb
    by_contra hne
    exact disjoint_left.mp (nativePool_disjoint G h01 h0Z h1Z _ _ hne) (hpick' s) hb
  -- Every round is a matching.
  have hmatch : ∀ r, G.IsMatching (F r) := by
    intro r e he f hf w hwe hwf
    obtain ⟨s, hs, rfl⟩ := (hmemF r e).mp he
    obtain ⟨s', hs', rfl⟩ := (hmemF r f).mp hf
    by_contra hne
    have hss : s ≠ s' := fun h => hne (by rw [h])
    have hround : s.val.1 = s'.val.1 := hs.trans hs'.symm
    have hcore := hdisj s s' hss hround
    rcases nativePool_endpoint G h01 (hpick' s) hwe with hwZ | hw0 | hw1
    · obtain ⟨⟨r₁, t⟩, ht⟩ := s
      obtain ⟨⟨r₂, t'⟩, ht'⟩ := s'
      have hr : r₁ = r₂ := hround
      have htt : t ≠ t' := fun h => hss (Subtype.ext (Prod.ext hr h))
      exact slot_exceptional_ends_distinct G h01 h0Z h1Z ht ht' (by rw [hr]) htt
        (hpick' ⟨(r₁, t), ht⟩) (hpick' ⟨(r₂, t'), ht'⟩) hwZ hwe hwf
    · exact disjoint_left.mp hcore
        ((mem_nativeCoreEnds G U₀ U₁ _ w).mpr ⟨hwe, Or.inl hw0⟩)
        ((mem_nativeCoreEnds G U₀ U₁ _ w).mpr ⟨hwf, Or.inl hw0⟩)
    · exact disjoint_left.mp hcore
        ((mem_nativeCoreEnds G U₀ U₁ _ w).mpr ⟨hwe, Or.inr hw1⟩)
        ((mem_nativeCoreEnds G U₀ U₁ _ w).mpr ⟨hwf, Or.inr hw1⟩)
  -- Distinct rounds are disjoint.
  have hdisjF : ∀ r r', r ≠ r' → Disjoint (F r) (F r') := by
    intro r r' hrr
    apply disjoint_left.mpr
    intro e he he'
    obtain ⟨s, hs, rfl⟩ := (hmemF r e).mp he
    obtain ⟨s', hs', hss⟩ := (hmemF r' _).mp he'
    have h1 : s' = s := hinj hss
    subst h1
    exact hrr (hs.symm.trans hs')
  -- Every copy comes from a used pool.
  have hmemPool : ∀ r, ∀ e ∈ F r,
      ∃ b, RoundUses U₀ Z (sig r) b ∧ e ∈ nativePool G U₀ U₁ Z b := by
    intro r e he
    obtain ⟨s, hs, rfl⟩ := (hmemF r e).mp he
    refine ⟨slotPool (sig s.val.1) s.val.2, ?_, hpick' s⟩
    rw [← hs]
    exact ⟨s.val.2, s.property, rfl⟩
  -- Exactly one copy from each used pool.
  have hpoolCard : ∀ r b, (F r ∩ nativePool G U₀ U₁ Z b).card =
      if RoundUses U₀ Z (sig r) b then 1 else 0 := by
    intro r b
    split_ifs with hu
    · obtain ⟨t, ht, hb⟩ := hu
      let s₀ : ScheduleSlot U₀ Z sig := ⟨(r, t), ht⟩
      apply card_eq_one.mpr
      refine ⟨pick s₀, ?_⟩
      ext e
      rw [mem_inter, mem_singleton]
      constructor
      · rintro ⟨he, heb⟩
        obtain ⟨s, hs, rfl⟩ := (hmemF r e).mp he
        have hk : slotPool (sig r) s.val.2 = b := by
          rw [← hs]; exact hkind s b heb
        have hst : s = s₀ := by
          apply Subtype.ext
          apply Prod.ext hs
          exact slotPool_injective (sig r) (hk.trans hb.symm)
        rw [hst]
      · rintro rfl
        refine ⟨(hmemF r _).mpr ⟨s₀, rfl, rfl⟩, ?_⟩
        rw [← hb]
        exact hpick' s₀
    · apply card_eq_zero.mpr
      apply eq_empty_of_forall_notMem
      intro e he
      obtain ⟨he, heb⟩ := mem_inter.mp he
      obtain ⟨s, hs, rfl⟩ := (hmemF r e).mp he
      apply hu
      rw [← hs]
      exact ⟨s.val.2, s.property, hkind s b heb⟩
  -- Every round covers the exceptional vertices.
  have hcovers : ∀ r, ∀ z ∈ Z, ∃ e ∈ F r, z ∈ G.edge e := by
    intro r z hz
    cases hp : sig r with
    | none =>
        let s₀ : ScheduleSlot U₀ Z sig := ⟨(r, some none), hp⟩
        have he : pick s₀ ∈ G.internalOn univ Z := hpick' s₀
        obtain ⟨hx, hy⟩ := (mem_internalPool_iff G Z _).mp he
        refine ⟨pick s₀, (hmemF r _).mpr ⟨s₀, rfl, rfl⟩, ?_⟩
        rcases eq_or_eq_of_card_le_two (G.endpoints_distinct (pick s₀)) hx hy hZ hz with
          h | h
        · exact (G.incident_iff _ _).mpr (Or.inl h.symm)
        · exact (G.incident_iff _ _).mpr (Or.inr h.symm)
    | some σ =>
        have hdem : SlotDemanded U₀ Z (sig r) (some (some ⟨z, hz⟩)) := by
          change sig r ≠ none
          rw [hp]
          exact Option.some_ne_none σ
        let s₀ : ScheduleSlot U₀ Z sig := ⟨(r, some (some ⟨z, hz⟩)), hdem⟩
        have he := hpick' s₀
        change pick s₀ ∈ exceptionCorePool G z _ at he
        exact ⟨pick s₀, (hmemF r _).mpr ⟨s₀, rfl, rfl⟩,
          ((mem_exceptionCorePool_iff G _ _ _).mp he).1⟩
  -- The crossing count.
  have hcrossCard : ∀ r, (F r ∩ coreCrossingPool G U₀ U₁).card =
      signatureCrossingBit U₀ Z (sig r) := by
    intro r
    have h := hpoolCard r .crossing
    change (F r ∩ coreCrossingPool G U₀ U₁).card = _ at h
    rw [h]
    have hlt := signatureCrossingBit_lt_two U₀ Z (sig r)
    split_ifs with hu
    · exact ((roundUses_crossing_iff U₀ Z (sig r)).mp hu).symm
    · have hne := (roundUses_crossing_iff U₀ Z (sig r)).not.mp hu
      omega
  -- The load at a core vertex.
  have hload : ∀ v ∈ U₀ ∪ U₁,
      (univ.filter (fun r => v ∈ G.edgeSupport (F r))).card ≤ a := by
    intro v hv
    have key : ∀ X : Finset V, (G.edgesTo v Xᶜ).card ≤ a →
        (∀ b, ∀ e ∈ nativePool G U₀ U₁ Z b, v ∈ G.edge e → G.otherEnd v e ∉ X) →
        (univ.filter (fun r => v ∈ G.edgeSupport (F r))).card ≤ a := by
      intro X hX hleave
      have h1 : (univ.filter (fun r => v ∈ G.edgeSupport (F r))).card ≤
          ((univ.filter (fun r => v ∈ G.edgeSupport (F r))).biUnion
            (fun r => F r ∩ G.edgesTo v Xᶜ)).card := by
        apply card_le_card_biUnion
        · intro r _ r' _ hrr
          change Disjoint (F r ∩ G.edgesTo v Xᶜ) (F r' ∩ G.edgesTo v Xᶜ)
          exact (hdisjF r r' hrr).mono inter_subset_left inter_subset_left
        · intro r hr
          obtain ⟨e, he, hve⟩ := (G.mem_edgeSupport _ v).mp (mem_filter.mp hr).2
          obtain ⟨b, _, heb⟩ := hmemPool r e he
          exact ⟨e, mem_inter.mpr ⟨he, (G.mem_edgesTo v Xᶜ e).mpr
            ⟨hve, mem_compl.mpr (hleave b e heb hve)⟩⟩⟩
      have h2 : ((univ.filter (fun r => v ∈ G.edgeSupport (F r))).biUnion
          (fun r => F r ∩ G.edgesTo v Xᶜ)).card ≤ (G.edgesTo v Xᶜ).card := by
        apply card_le_card
        intro e he
        obtain ⟨r, _, her⟩ := mem_biUnion.mp he
        exact (mem_inter.mp her).2
      exact h1.trans (h2.trans hX)
    rcases mem_union.mp hv with h0 | h1
    · exact key U₀ (hout₀ v h0) (fun b e he hve =>
        (nativePool_otherEnd_not_mem G h01 h0Z h1Z he hve).1 h0)
    · exact key U₁ (hout₁ v h1) (fun b e he hve =>
        (nativePool_otherEnd_not_mem G h01 h0Z h1Z he hve).2 h1)
  -- Exact accounting.
  have hacc : ∀ b, (nativePool G U₀ U₁ Z b ∩ univ.biUnion F).card =
      (univ.filter (fun r => RoundUses U₀ Z (sig r) b)).card := by
    intro b
    have heq : nativePool G U₀ U₁ Z b ∩ univ.biUnion F =
        (univ.filter (fun r => RoundUses U₀ Z (sig r) b)).biUnion
          (fun r => F r ∩ nativePool G U₀ U₁ Z b) := by
      ext e
      simp only [mem_inter, mem_biUnion, mem_univ, true_and, mem_filter]
      constructor
      · rintro ⟨heb, r, her⟩
        refine ⟨r, ?_, her, heb⟩
        obtain ⟨b', hb', heb'⟩ := hmemPool r e her
        have hbb : b' = b := by
          by_contra hne
          exact disjoint_left.mp (nativePool_disjoint G h01 h0Z h1Z _ _ hne) heb' heb
        rw [← hbb]
        exact hb'
      · rintro ⟨r, _, her, heb⟩
        exact ⟨heb, r, her⟩
    rw [heq, card_biUnion]
    · calc
        ∑ r ∈ univ.filter (fun r => RoundUses U₀ Z (sig r) b),
            (F r ∩ nativePool G U₀ U₁ Z b).card
            = ∑ r ∈ univ.filter (fun r => RoundUses U₀ Z (sig r) b), 1 := by
              apply sum_congr rfl
              intro r hr
              rw [hpoolCard r b, if_pos (mem_filter.mp hr).2]
        _ = _ := (card_eq_sum_ones _).symm
    · intro r _ r' _ hrr
      change Disjoint (F r ∩ nativePool G U₀ U₁ Z b) (F r' ∩ nativePool G U₀ U₁ Z b)
      exact (hdisjF r r' hrr).mono inter_subset_left inter_subset_left
  exact ⟨⟨F, hmatch, hdisjF, hmemPool, hpoolCard, hcovers, hcrossCard,
    fun r => round_uncovered_even G h01 h0Z h1Z hZ heven (hmatch r) (hmemPool r)
      (hpoolCard r),
    hload, hacc⟩⟩

/-! ### Rounds given by signature multiplicities -/

/-- With `m p` rounds of each signature `p`, the demand on a pool is the
total multiplicity of the signatures using it. -/
theorem card_roundUses_sigma (U₀ Z : Finset V) (m : AssignmentSignature Z → ℕ)
    (b : NativePool Z) :
    (univ.filter (fun r : (Σ p : AssignmentSignature Z, Fin (m p)) =>
        RoundUses U₀ Z r.1 b)).card =
      ∑ p ∈ univ.filter (fun p => RoundUses U₀ Z p b), m p := by
  have heq : (univ.filter (fun r : (Σ p : AssignmentSignature Z, Fin (m p)) =>
      RoundUses U₀ Z r.1 b)) =
      (univ.filter (fun p => RoundUses U₀ Z p b)).sigma (fun _ => univ) := by
    ext ⟨p, j⟩
    simp only [mem_filter, mem_univ, true_and, mem_sigma, and_true]
  rw [heq, card_sigma]
  apply sum_congr rfl
  intro p _
  rw [card_univ, Fintype.card_fin]

/-- **Native boundary schedule for prescribed multiplicities.** Realize
`m p` rounds of every signature `p` simultaneously. -/
theorem exists_native_boundary_schedule_of_multiplicity [Fintype V] {U₀ U₁ Z : Finset V}
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hZ : Z.card ≤ 2) (heven : Even (U₀.card + U₁.card + Z.card))
    (m : AssignmentSignature Z → ℕ) (a : ℕ)
    (hout₀ : ∀ v ∈ U₀, (G.edgesTo v U₀ᶜ).card ≤ a)
    (hout₁ : ∀ v ∈ U₁, (G.edgesTo v U₁ᶜ).card ≤ a)
    (hcap : ∀ b : NativePool Z, (∃ p, 0 < m p ∧ RoundUses U₀ Z p b) →
      (∑ p ∈ univ.filter (fun p => RoundUses U₀ Z p b), m p) + (Z.card + 2) * a <
        (nativePool G U₀ U₁ Z b).card) :
    Nonempty (NativeBoundarySchedule G U₀ U₁ Z
      (fun r : (Σ p : AssignmentSignature Z, Fin (m p)) => r.1) a) := by
  apply exists_native_boundary_schedule G h01 h0Z h1Z hZ heven _ a hout₀ hout₁
  intro b hb
  obtain ⟨⟨p, j⟩, hp⟩ := hb
  rw [card_roundUses_sigma U₀ Z m b]
  exact hcap b ⟨p, lt_of_le_of_lt (Nat.zero_le _) j.isLt, hp⟩

/-- Proportional demand leaves the slack required by `hcap`: if every
multiplicity is at most a `(1-η)` fraction of a weight, and the weights
of the signatures using a pool sum to at most its size `c`, then the demand
plus any `L < η c` is below `c`. -/
theorem capacity_of_proportional_demand {P : Type*} (S : Finset P) (m : P → ℕ)
    (w : P → ℝ) (η : ℝ) (c L : ℕ) (hη : η ≤ 1)
    (hm : ∀ p ∈ S, (m p : ℝ) ≤ (1 - η) * w p) (hw : ∑ p ∈ S, w p ≤ c)
    (hL : (L : ℝ) < η * c) :
    ∑ p ∈ S, m p + L < c := by
  have hsum : ((∑ p ∈ S, m p : ℕ) : ℝ) ≤ (1 - η) * c := by
    push_cast
    calc
      ∑ p ∈ S, (m p : ℝ) ≤ ∑ p ∈ S, (1 - η) * w p := sum_le_sum hm
      _ = (1 - η) * ∑ p ∈ S, w p := (mul_sum _ _ _).symm
      _ ≤ (1 - η) * c := mul_le_mul_of_nonneg_left hw (by linarith)
  have hreal : ((∑ p ∈ S, m p : ℕ) : ℝ) + L < c := by linarith
  exact_mod_cast hreal

/-! ### The crossing parity of an actual representative -/

omit [Fintype E] in
/-- For an actual perfect matching, the crossing parity prescribed by its
own signature is the parity of its number of old-core crossing copies. -/
theorem signatureCrossingBit_coarseSignature {M : Finset E}
    (hM : G.IsPerfectMatching M) {U₀ U₁ Z : Finset V} (h01 : Disjoint U₀ U₁)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2) :
    signatureCrossingBit U₀ Z (coarseSignature G M U₀ Z) =
      (G.cutOn M U₀ ∩ G.cutOn M U₁).card % 2 := by
  rw [← corePart_card_parity G hM U₀ U₁ Z h01 h0Z h1Z hcover]
  by_cases hi : (G.internalOn M Z).Nonempty
  · rw [(coarseSignature_eq_none_iff G M U₀ Z).mpr hi]
    have hpair := (pairPart_eq_exceptions_of_internal G (hM.isMatching G) Z hZ hi).1
    rw [corePart_eq_original_of_pairPart_eq G (hM.isMatching G) U₀ Z h0Z hpair]
    rfl
  · have he : G.internalOn M Z = ∅ := not_nonempty_iff_eq_empty.mp hi
    have hc : coarseSignature G M U₀ Z = some (assignmentChoice G M U₀ Z) :=
      (coarseSignature_eq_some_iff G M U₀ Z _).mpr ⟨he, rfl⟩
    rw [hc]
    have hdisj : Disjoint U₀ (assignedExceptions G M Z U₀) := by
      apply disjoint_left.mpr
      intro v hv hvA
      exact disjoint_left.mp h0Z hv ((mem_assignedExceptions G M Z U₀ v).mp hvA).1
    have hcard : (assignedExceptions G M Z U₀).card =
        (univ.filter (fun z : ↥Z => assignmentChoice G M U₀ Z z = 0)).card := by
      rw [← card_map (Function.Embedding.subtype (· ∈ Z))]
      congr 1
      ext v
      simp only [mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coe_subtype]
      constructor
      · intro hv
        have hvZ := ((mem_assignedExceptions G M Z U₀ v).mp hv).1
        refine ⟨⟨v, hvZ⟩, ?_, rfl⟩
        rw [assignmentChoice_eq_zero_iff]
        exact (mem_corePart G M Z U₀ v).mpr
          (Or.inr ((mem_assignedExceptions G M Z U₀ v).mp hv))
      · rintro ⟨z, hz, rfl⟩
        rw [assignmentChoice_eq_zero_iff] at hz
        rcases (mem_corePart G M Z U₀ z.val).mp hz with h | h
        · exact (disjoint_left.mp h0Z h z.property).elim
        · exact (mem_assignedExceptions G M Z U₀ z.val).mpr h
    simp only [signatureCrossingBit, corePart, card_union_of_disjoint hdisj, hcard]

/-! ### Capacity from the native signature weights -/

section Weights

open NativeWeights

variable {S : Type*} [Fintype S] {k : ℕ}

/-- Every sample whose signature uses a pool contains a copy of that pool. -/
theorem matching_meets_nativePool (D : MultigraphMatchingProbability.Distribution G k S)
    {U₀ U₁ Z : Finset V} (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z)
    (h1Z : Disjoint U₁ Z) (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2)
    (s : S) (b : NativePool Z)
    (hu : RoundUses U₀ Z (coarseSignature G (D.matching s) U₀ Z) b) :
    (D.matching s ∩ nativePool G U₀ U₁ Z b).Nonempty := by
  cases b with
  | internal =>
      exact signature_none_uses_internalPool G (D.matching s) U₀ Z
        ((roundUses_internal_iff U₀ Z _).mp hu)
  | toCore z i =>
      obtain ⟨σ, hσ, hi⟩ := (roundUses_toCore_iff U₀ Z _ z i).mp hu
      have h := signature_some_uses_exceptionCorePool G (D.perfect s)
        U₀ U₁ Z h0Z h1Z hcover σ hσ z
      rw [hi] at h
      exact h
  | crossing =>
      have hbit := (roundUses_crossing_iff U₀ Z _).mp hu
      rw [signatureCrossingBit_coarseSignature G (D.perfect s) h01 h0Z h1Z hcover hZ] at hbit
      have hpos : 0 < (G.cutOn (D.matching s) U₀ ∩ G.cutOn (D.matching s) U₁).card := by
        omega
      exact uses_coreCrossingPool_of_nonempty G (D.matching s) U₀ U₁ (card_pos.mp hpos)

/-- The signatures using a pool have total weight at most its number of
original copies. Parallel copies are counted separately. -/
theorem signatureWeight_roundUses_le_pool
    (D : MultigraphMatchingProbability.Distribution G k S) (hk : 0 < k)
    {U₀ U₁ Z : Finset V} (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z)
    (h1Z : Disjoint U₁ Z) (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2)
    (b : NativePool Z) :
    ∑ p ∈ univ.filter (fun p => RoundUses U₀ Z p b), signatureWeight D U₀ Z p ≤
      (nativePool G U₀ U₁ Z b).card := by
  have h := aggregate_capacity D hk (fun s => coarseSignature G (D.matching s) U₀ Z)
    D.matching (fun _ => subset_refl _) (nativePool G U₀ U₁ Z b)
    (fun p => if RoundUses U₀ Z p b then 1 else 0) (by
      intro s
      dsimp only
      split_ifs with hu
      · exact Nat.succ_le_of_lt (card_pos.mpr
          (matching_meets_nativePool G D h01 h0Z h1Z hcover hZ s b hu))
      · exact Nat.zero_le _)
  calc
    ∑ p ∈ univ.filter (fun p => RoundUses U₀ Z p b), signatureWeight D U₀ Z p
        = ∑ p, signatureWeight D U₀ Z p *
            (((if RoundUses U₀ Z p b then 1 else 0 : ℕ)) : ℝ) := by
          rw [sum_filter]
          apply sum_congr rfl
          intro p _
          split_ifs <;> simp
    _ ≤ _ := h

/-- **Native boundary schedule from weights.** If every multiplicity is at
most a `(1-η)` fraction of the native weight of its signature, and every
pool used by a realized signature is larger than `(|Z|+2)a/η`, then all
rounds can be realized simultaneously. -/
theorem exists_native_boundary_schedule_of_weights [Fintype V]
    (D : MultigraphMatchingProbability.Distribution G k S) (hk : 0 < k)
    {U₀ U₁ Z : Finset V} (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z)
    (h1Z : Disjoint U₁ Z) (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2)
    (m : AssignmentSignature Z → ℕ) (a : ℕ) (η : ℝ) (hη : η ≤ 1)
    (hout₀ : ∀ v ∈ U₀, (G.edgesTo v U₀ᶜ).card ≤ a)
    (hout₁ : ∀ v ∈ U₁, (G.edgesTo v U₁ᶜ).card ≤ a)
    (hm : ∀ p, (m p : ℝ) ≤ (1 - η) * signatureWeight D U₀ Z p)
    (hlarge : ∀ b : NativePool Z, (∃ p, 0 < m p ∧ RoundUses U₀ Z p b) →
      (((Z.card + 2) * a : ℕ) : ℝ) < η * ((nativePool G U₀ U₁ Z b).card : ℝ)) :
    Nonempty (NativeBoundarySchedule G U₀ U₁ Z
      (fun r : (Σ p : AssignmentSignature Z, Fin (m p)) => r.1) a) := by
  have hne : (univ : Finset S).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    have h1 := D.sum_one
    rw [h, sum_empty] at h1
    exact zero_ne_one h1
  obtain ⟨s, -⟩ := hne
  have heven : Even (U₀.card + U₁.card + Z.card) := by
    have hev := (D.perfect s).even_card G
    have hunion : (univ : Finset V) = U₀ ∪ U₁ ∪ Z := by
      ext v
      simp only [mem_univ, mem_union, true_iff]
      rcases hcover v with h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
    rw [← card_univ, hunion, card_union_of_disjoint (disjoint_union_left.mpr ⟨h0Z, h1Z⟩),
      card_union_of_disjoint h01] at hev
    exact hev
  apply exists_native_boundary_schedule_of_multiplicity G h01 h0Z h1Z hZ heven m a
    hout₀ hout₁
  intro b hb
  exact capacity_of_proportional_demand _ m (signatureWeight D U₀ Z) η _ _ hη
    (fun p _ => hm p)
    (signatureWeight_roundUses_le_pool G D hk h01 h0Z h1Z hcover hZ b) (hlarge b hb)

end Weights

end Overfull.AssignedParts
