import Overfull.NativeReserve.Greedy

/-!
# Scheduling the actual slots of representative boundaries

The representative boundaries may overlap. Only their demand slots are
used; fresh pairwise disjoint original copies are selected outside the
given reserve, with the same exact pool use in each round.
-/

noncomputable section

namespace Overfull.NativeReserve

open Finset Classical AssignedParts
open scoped BigOperators

variable {V E R : Type*} [Fintype R] (G : Multigraph V E)

abbrev BoundarySlots (B : R → Finset E) := (r : R) × ↥(B r)

theorem boundarySlots_round_card (B : R → Finset E) (r : R) :
    (univ.filter (fun x : BoundarySlots B => x.1 = r)).card = (B r).card := by
  simp only [card_eq_sum_ones, sum_filter, Fintype.sum_sigma]
  simp

theorem boundarySlots_pool_card (B : R → Finset E) {P : Type*}
    (kind : BoundarySlots B → P) (pool : P → Finset E)
    (hkind : ∀ x p, kind x = p ↔ x.2.val ∈ pool p) (p : P) :
    CircuitPatternRealization.demandCount kind p = ∑ r, (B r ∩ pool p).card := by
  simp only [CircuitPatternRealization.demandCount, card_eq_sum_ones, sum_filter,
    Fintype.sum_sigma, hkind]
  apply sum_congr rfl
  intro r _
  simp [Finset.sum_coe_sort, ← Finset.filter_mem_eq_inter]

theorem boundarySlots_round_pool_card (B : R → Finset E) {P : Type*}
    (kind : BoundarySlots B → P) (pool : P → Finset E)
    (hkind : ∀ x p, kind x = p ↔ x.2.val ∈ pool p) (r : R) (p : P) :
    ((univ.filter (fun x : BoundarySlots B => x.1 = r)).filter
      (fun x => kind x = p)).card = (B r ∩ pool p).card := by
  simp only [card_eq_sum_ones, sum_filter, Fintype.sum_sigma, hkind]
  simp [Finset.sum_coe_sort, ← Finset.filter_mem_eq_inter]

variable [Fintype E]

theorem exists_family_avoiding_with_representative_pools
    (U₀ U₁ Z : Finset V) (C₀ : SmallCuts.Core G U₀) (C₁ : SmallCuts.Core G U₁)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 2)
    (k : ℕ) (a η : ℝ) (ha : 0 < a)
    (hregular : ∀ v, G.degree v = k)
    (hdegree₀ : ∀ v, (k : ℝ)-a ≤ (C₀.graph.degree v : ℝ))
    (hdegree₁ : ∀ v, (k : ℝ)-a ≤ (C₁.graph.degree v : ℝ))
    (B : R → Finset E) (hmatching : ∀ r, G.IsMatching (B r))
    (hcoverZ : ∀ r, Z ⊆ G.edgeSupport (B r)) (hcard : ∀ r, (B r).card ≤ 3)
    (hB : ∀ r, ∀ e ∈ B r, ∃ p, e ∈ poolCopies G U₀ U₁ Z p)
    (A : Finset E)
    (huse : ∀ p, ((∑ r, (B r ∩ poolCopies G U₀ U₁ Z p).card : ℕ) : ℝ) ≤
      (1-η) * (poolCopies G U₀ U₁ Z p \ A).card)
    (hslack : ∀ p, (∃ r, (B r ∩ poolCopies G U₀ U₁ Z p).Nonempty) →
      8*a ≤ η * (poolCopies G U₀ U₁ Z p \ A).card) :
    ∃ F : R → Finset E,
      (∀ r, G.IsMatching (F r)) ∧
      (∀ r r', r ≠ r' → Disjoint (F r) (F r')) ∧
      (∀ r, Disjoint (F r) A) ∧
      (∀ r, Z ⊆ G.edgeSupport (F r)) ∧
      (∀ r, ∀ e ∈ F r, ∃ p, e ∈ poolCopies G U₀ U₁ Z p) ∧
      (∀ r, (F r).card = (B r).card) ∧
      (∀ r p, (F r ∩ poolCopies G U₀ U₁ Z p).card =
        (B r ∩ poolCopies G U₀ U₁ Z p).card) := by
  let pool := poolCopies G U₀ U₁ Z
  let kind : BoundarySlots B → PoolKind Z := fun x => (hB x.1 x.2.val x.2.property).choose
  have hkind_mem (x : BoundarySlots B) : x.2.val ∈ pool (kind x) :=
    (hB x.1 x.2.val x.2.property).choose_spec
  have hpools := poolCopies_pairwiseDisjoint G U₀ U₁ Z h01 h0Z h1Z hZ
  have hkind (x : BoundarySlots B) (p : PoolKind Z) :
      kind x = p ↔ x.2.val ∈ pool p := by
    constructor
    · intro h; exact h ▸ hkind_mem x
    · intro h
      by_contra hn
      exact disjoint_left.mp (hpools hn) (hkind_mem x) h
  let available := fun p => pool p \ A
  have havail : ∀ p q, p ≠ q → Disjoint (available p) (available q) :=
    fun p q hpq => (hpools hpq).mono sdiff_subset sdiff_subset
  have hinc (p : PoolKind Z) (v : V) :
      ((available p).filter (fun e => v ∈ coreEnds G Z e)).card ≤ ⌊a⌋₊ := by
    apply Nat.le_floor
    by_cases hvZ : v ∈ Z
    · have heq : (available p).filter (fun e => v ∈ coreEnds G Z e) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro e he
        exact (mem_coreEnds G Z e v).mp (mem_filter.mp he).2 |>.2 hvZ
      rw [heq, card_empty, Nat.cast_zero]
      exact le_of_lt ha
    · have hle : ((available p).filter (fun e => v ∈ coreEnds G Z e)).card ≤
          G.degreeOn (pool p) v := by
        apply card_le_card
        intro e he
        obtain ⟨he, hv⟩ := mem_filter.mp he
        exact mem_filter.mpr ⟨(mem_sdiff.mp he).1, (mem_coreEnds G Z e v).mp hv |>.1⟩
      rcases hcover v with hv | hv | hv
      · exact (Nat.cast_le.mpr hle).trans
          (pool_core_incidence_le_error G C₀ (pool p)
            (poolCopies_disjoint_core G U₀ U₁ Z U₀ h01 h0Z h1Z (Or.inl rfl) C₀ p)
            k a hregular hdegree₀ ⟨v,hv⟩)
      · exact (Nat.cast_le.mpr hle).trans
          (pool_core_incidence_le_error G C₁ (pool p)
            (poolCopies_disjoint_core G U₀ U₁ Z U₁ h01 h0Z h1Z (Or.inr rfl) C₁ p)
            k a hregular hdegree₁ ⟨v,hv⟩)
      · exact (hvZ hv).elim
  have hround (r : R) :
      ∑ _x ∈ univ.filter (fun x : BoundarySlots B => x.1 = r), 2 ≤ 6 := by
    have := hcard r
    simp only [sum_const, nsmul_eq_mul, boundarySlots_round_card]
    omega
  have hcap (x : BoundarySlots B) :
      CircuitPatternRealization.demandCount kind (kind x) + 6 * ⌊a⌋₊ <
        (available (kind x)).card := by
    have hu := huse (kind x)
    have hs := hslack (kind x) ⟨x.1, x.2.val, mem_inter.mpr ⟨x.2.property, hkind_mem x⟩⟩
    have hf := Nat.floor_le (le_of_lt ha)
    rw [boundarySlots_pool_card B kind pool hkind]
    have hh : ((∑ r, (B r ∩ pool (kind x)).card : ℕ) : ℝ) +
        6 * (⌊a⌋₊ : ℝ) < (available (kind x)).card := by
      change _ ≤ (1-η) * (available (kind x)).card at hu
      change 8*a ≤ η * (available (kind x)).card at hs
      nlinarith
    exact_mod_cast hh
  obtain ⟨pick, hpick, hinj, hcore⟩ := CircuitPatternRealization.exists_pool_selection
    available kind (fun x : BoundarySlots B => x.1) (coreEnds G Z) (fun _ => 2)
    ⌊a⌋₊ 6 havail (fun _ e _ => coreEnds_card_le_two G Z e) hinc hround hcap
  have hpickPool (x : BoundarySlots B) : pick x ∈ pool (kind x) :=
    (mem_sdiff.mp (hpick x)).1
  have hsame (x : BoundarySlots B) :
      specialEnds G Z (pick x) = specialEnds G Z x.2.val := by
    rw [poolCopies_specialEnds G U₀ U₁ Z h01 h0Z h1Z hZ (kind x) _ (hpickPool x),
      poolCopies_specialEnds G U₀ U₁ Z h01 h0Z h1Z hZ (kind x) _ (hkind_mem x)]
  have hspecial (i j : BoundarySlots B) (hij : i ≠ j) (hr : i.1 = j.1) :
      Disjoint (specialEnds G Z (pick i)) (specialEnds G Z (pick j)) := by
    rw [hsame, hsame]
    apply disjoint_left.mpr
    intro v hi hj
    rcases i with ⟨r,e⟩
    rcases j with ⟨s,f⟩
    dsimp at hr
    subst s
    have heq := hmatching r e.val e.property f.val f.property v
      ((mem_specialEnds G Z _ _).mp hi).1 ((mem_specialEnds G Z _ _).mp hj).1
    apply hij
    congr 1
    exact Subtype.ext heq
  let F : R → Finset E := chosenRound (fun x : BoundarySlots B => x.1) pick
  refine ⟨F, fun r => chosenRound_isMatching G Z _ pick hspecial hcore r,
    fun r s hrs => chosenRound_pairwiseDisjoint _ pick hinj hrs, ?_, ?_, ?_, ?_, ?_⟩
  · intro r
    apply disjoint_left.mpr
    intro e he heA
    obtain ⟨x, _, rfl⟩ := (mem_chosenRound _ pick r e).mp he
    exact (mem_sdiff.mp (hpick x)).2 heA
  · intro r v hv
    obtain ⟨e, he, hev⟩ := (G.mem_edgeSupport (B r) v).mp (hcoverZ r hv)
    let x : BoundarySlots B := ⟨r, ⟨e, he⟩⟩
    have hspec : v ∈ specialEnds G Z (pick x) := by
      rw [hsame]
      exact (mem_specialEnds G Z e v).mpr ⟨hev, hv⟩
    exact (G.mem_edgeSupport (F r) v).mpr
      ⟨pick x, (mem_chosenRound _ pick r _).mpr ⟨x,rfl,rfl⟩,
        ((mem_specialEnds G Z _ _).mp hspec).1⟩
  · intro r e he
    obtain ⟨x, _, rfl⟩ := (mem_chosenRound _ pick r e).mp he
    exact ⟨kind x, hpickPool x⟩
  · intro r
    change ((univ.filter (fun x : BoundarySlots B => x.1 = r)).image pick).card = _
    rw [card_image_of_injective _ hinj, boundarySlots_round_card]
  · intro r p
    change ((univ.filter (fun x : BoundarySlots B => x.1 = r)).image pick ∩ pool p).card = _
    rw [← filter_mem_eq_inter]
    rw [CircuitPatternRealization.chosen_pool_card pool kind pick hpickPool hinj
      (fun p q hpq => hpools hpq)]
    exact boundarySlots_round_pool_card B kind pool hkind r p

end Overfull.NativeReserve
