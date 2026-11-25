import Overfull.AssignedParts.Basic
import Overfull.TerminalFour.Parity

/-!
# Four actual assigned parts from two exceptional matching pairs

The two internal matching copies determine separate two-vertex parts.  Their
order is an explicit enumeration, not an unproved canonical choice of copies.
The vertex parts depend only on the endpoint pairs, so parallel replacements
with the same endpoints do not change them.  The actual assigned core parts
receive labels zero and one and the separate pair parts receive two and three.

This constructs the native assigned parts and their parity alternatives.  It
does not construct reserves, star extensions, or a coloring of the host.
-/

noncomputable section

namespace Overfull.AssignedParts

open Finset Classical FourOdd

variable {V E : Type*} (G : Multigraph V E)

/-- The actual endpoint pair of one original edge copy. -/
def exceptionalPairPart (e : E) : Finset V := (G.edge e).toFinset

@[simp] theorem mem_exceptionalPairPart (e : E) (v : V) :
    v ∈ exceptionalPairPart G e ↔ v ∈ G.edge e := by
  exact Sym2.mem_toFinset

/-- Every original loopless copy contributes exactly two distinct vertices. -/
theorem exceptionalPairPart_card (e : E) :
    (exceptionalPairPart G e).card = 2 :=
  Sym2.card_toFinset_of_not_isDiag _ (G.loopless e)

/-- Replacing a parallel copy leaves its actual endpoint pair unchanged. -/
theorem exceptionalPairPart_eq_of_edge_eq {e f : E}
    (h : G.edge e = G.edge f) :
    exceptionalPairPart G e = exceptionalPairPart G f := by
  exact congrArg Sym2.toFinset h

/-- A selected internal exceptional copy has all its endpoints in the old
pair part.  This assertion uses actual copies, including their multiplicity. -/
theorem exceptionalPairPart_subset_pairPart {M : Finset E} {Z : Finset V}
    {e : E} (he : e ∈ G.internalOn M Z) :
    exceptionalPairPart G e ⊆ pairPart G M Z := by
  intro v hv
  exact (G.mem_edgeSupport _ v).mpr ⟨e, he, (mem_exceptionalPairPart G e v).mp hv⟩

theorem exceptionalPairPart_subset_exceptions {M : Finset E} {Z : Finset V}
    {e : E} (he : e ∈ G.internalOn M Z) :
    exceptionalPairPart G e ⊆ Z :=
  (exceptionalPairPart_subset_pairPart G he).trans (pairPart_subset G M Z)

/-- Distinct copies of an actual matching give disjoint endpoint pairs. -/
theorem exceptionalPairParts_disjoint {M : Finset E} (hM : G.IsMatching M)
    {e f : E} (he : e ∈ M) (hf : f ∈ M) (hef : e ≠ f) :
    Disjoint (exceptionalPairPart G e) (exceptionalPairPart G f) := by
  apply disjoint_left.mpr
  intro v hve hvf
  exact hef (hM e he f hf v ((mem_exceptionalPairPart G e v).mp hve)
    ((mem_exceptionalPairPart G f v).mp hvf))

/-- A core assigned by the original matching misses each separate pair part. -/
theorem corePart_exceptionalPairPart_disjoint {M : Finset E}
    (hM : G.IsMatching M) (U Z : Finset V) (hUZ : Disjoint U Z)
    {e : E} (he : e ∈ G.internalOn M Z) :
    Disjoint (corePart G M Z U) (exceptionalPairPart G e) := by
  apply disjoint_left.mpr
  intro v hvU hvP
  exact disjoint_left.mp (corePart_pairPart_disjoint G hM U Z hUZ) hvU
    (exceptionalPairPart_subset_pairPart G he hvP)

/-- Enumerating exactly two internal matching copies splits the old pair
part into their actual endpoint sets. -/
theorem pairPart_eq_two_pair_union {M : Finset E} {Z : Finset V}
    (e f : E) (hpair : G.internalOn M Z = {e, f}) :
    pairPart G M Z = exceptionalPairPart G e ∪ exceptionalPairPart G f := by
  ext v
  simp only [pairPart, Multigraph.mem_edgeSupport, hpair, mem_insert,
    mem_singleton, mem_union, mem_exceptionalPairPart]
  aesop

/-- The original matching assigns every vertex to one of the two core
parts or one of the two separate endpoint pairs. -/
theorem twoPairParts_cover {M : Finset E} (hM : G.IsPerfectMatching M)
    (U₀ U₁ Z : Finset V)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (e f : E) (hpair : G.internalOn M Z = {e, f}) (v : V) :
    v ∈ corePart G M Z U₀ ∨ v ∈ corePart G M Z U₁ ∨
      v ∈ exceptionalPairPart G e ∨ v ∈ exceptionalPairPart G f := by
  have hv := coreParts_cover G hM U₀ U₁ Z hcover v
  rw [pairPart_eq_two_pair_union G e f hpair, mem_union] at hv
  exact hv

/-- Five exceptional vertices permit at most two internal matching copies. -/
theorem internalOn_card_le_two {M : Finset E} (hM : G.IsMatching M)
    (Z : Finset V) (hZ : Z.card ≤ 5) :
    (G.internalOn M Z).card ≤ 2 := by
  have h := card_le_card (pairPart_subset G M Z)
  rw [pairPart_card G hM Z] at h
  omega

/-- If both exceptional pairs occur, at most one exception remains unpaired. -/
theorem unpaired_card_le_one_of_two_pairs {M : Finset E} (hM : G.IsMatching M)
    (Z : Finset V) (hZ : Z.card ≤ 5)
    (hpair : (G.internalOn M Z).card = 2) :
    (Z \ pairPart G M Z).card ≤ 1 := by
  rw [card_sdiff_of_subset (pairPart_subset G M Z), pairPart_card G hM Z, hpair]
  omega

/-- Distinct labels for the actual assigned cores and the first explicit
endpoint pair; the covering second pair receives the remaining label. -/
def twoPairAssignedLabel (M : Finset E) (U₀ U₁ Z : Finset V) (e : E) (v : V) :
    Fin 4 :=
  if v ∈ corePart G M Z U₀ then 0
  else if v ∈ corePart G M Z U₁ then 1
  else if v ∈ exceptionalPairPart G e then 2 else 3

/-- The explicit labeling depends on the assigned core vertex sets and on
the first endpoint pair, not on which parallel copy represents that pair. -/
theorem twoPairAssignedLabel_eq_of_parts {M N : Finset E}
    (U₀ U₁ Z : Finset V) (e f : E)
    (h0 : corePart G M Z U₀ = corePart G N Z U₀)
    (h1 : corePart G M Z U₁ = corePart G N Z U₁)
    (hp : exceptionalPairPart G e = exceptionalPairPart G f) :
    twoPairAssignedLabel G M U₀ U₁ Z e = twoPairAssignedLabel G N U₀ U₁ Z f := by
  funext v
  simp only [twoPairAssignedLabel, h0, h1, hp]

variable [Fintype V]

/-- All four fibers are exactly the original assigned parts.  Neither pair
is merged with the other, even though their union is the old pair part. -/
theorem twoPairAssignedLabel_fibers {M : Finset E} (hM : G.IsPerfectMatching M)
    (U₀ U₁ Z : Finset V) (h01 : Disjoint U₀ U₁)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (e f : E) (hef : e ≠ f) (hpair : G.internalOn M Z = {e, f}) :
    labelShore (twoPairAssignedLabel G M U₀ U₁ Z e) {0} = corePart G M Z U₀ ∧
    labelShore (twoPairAssignedLabel G M U₀ U₁ Z e) {1} = corePart G M Z U₁ ∧
    labelShore (twoPairAssignedLabel G M U₀ U₁ Z e) {2} = exceptionalPairPart G e ∧
    labelShore (twoPairAssignedLabel G M U₀ U₁ Z e) {3} = exceptionalPairPart G f := by
  have he : e ∈ G.internalOn M Z := by rw [hpair]; exact mem_insert_self e {f}
  have hf : f ∈ G.internalOn M Z := by
    rw [hpair]
    exact mem_insert_of_mem (mem_singleton_self f)
  have hd01 := coreParts_disjoint G (hM.isMatching G) U₀ U₁ Z h01 h0Z h1Z
  have hd0e := corePart_exceptionalPairPart_disjoint G (hM.isMatching G) U₀ Z h0Z he
  have hd0f := corePart_exceptionalPairPart_disjoint G (hM.isMatching G) U₀ Z h0Z hf
  have hd1e := corePart_exceptionalPairPart_disjoint G (hM.isMatching G) U₁ Z h1Z he
  have hd1f := corePart_exceptionalPairPart_disjoint G (hM.isMatching G) U₁ Z h1Z hf
  have hdef := exceptionalPairParts_disjoint G (hM.isMatching G)
    (mem_filter.mp he).1 (mem_filter.mp hf).1 hef
  have hc := twoPairParts_cover G hM U₀ U₁ Z hcover e f hpair
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext v
    simp only [mem_labelShore, mem_singleton, twoPairAssignedLabel]
    split_ifs <;> simp_all
  · ext v
    simp only [mem_labelShore, mem_singleton, twoPairAssignedLabel]
    by_cases hv0 : v ∈ corePart G M Z U₀
    · have hv1 : v ∉ corePart G M Z U₁ := fun hh => disjoint_left.mp hd01 hv0 hh
      simp [hv0, hv1]
    · split_ifs <;> simp_all
  · ext v
    simp only [mem_labelShore, mem_singleton, twoPairAssignedLabel]
    by_cases hv0 : v ∈ corePart G M Z U₀
    · have hve : v ∉ exceptionalPairPart G e := fun hh => disjoint_left.mp hd0e hv0 hh
      simp [hv0, hve]
    · by_cases hv1 : v ∈ corePart G M Z U₁
      · have hve : v ∉ exceptionalPairPart G e := fun hh => disjoint_left.mp hd1e hv1 hh
        simp [hv0, hv1, hve]
      · simp [hv0, hv1]
  · ext v
    simp only [mem_labelShore, mem_singleton, twoPairAssignedLabel]
    by_cases hv0 : v ∈ corePart G M Z U₀
    · have hvf : v ∉ exceptionalPairPart G f := fun hh => disjoint_left.mp hd0f hv0 hh
      simp [hv0, hvf]
    · by_cases hv1 : v ∈ corePart G M Z U₁
      · have hvf : v ∉ exceptionalPairPart G f := fun hh => disjoint_left.mp hd1f hv1 hh
        simp [hv0, hv1, hvf]
      · by_cases hve : v ∈ exceptionalPairPart G e
        · have hvf : v ∉ exceptionalPairPart G f := fun hh => disjoint_left.mp hdef hve hh
          simp [hv0, hv1, hve, hvf]
        · have hvf : v ∈ exceptionalPairPart G f := by
            rcases hc v with hv | hv | hv | hv
            · exact (hv0 hv).elim
            · exact (hv1 hv).elim
            · exact (hve hv).elim
            · exact hv
          simp [hv0, hv1, hve, hvf]

/-- With two even pair fibers and even total order, the two assigned core
fibers have the same parity. -/
theorem core_fiber_parity_eq_of_two_even_pairs (label : V → Fin 4)
    (hV : Even (Fintype.card V))
    (h2 : Even (labelShore label {2}).card)
    (h3 : Even (labelShore label {3}).card) :
    (labelShore label {0}).card % 2 = (labelShore label {1}).card % 2 := by
  have hs := TerminalFour.fiber_card_sum_four label
  have ht := Nat.even_iff.mp hV
  have hp2 := Nat.even_iff.mp h2
  have hp3 := Nat.even_iff.mp h3
  simp only [labelShore, mem_singleton] at hp2 hp3 ⊢
  omega

/-- The two explicit pair fibers rule out every odd-fiber alternative
except simultaneous oddness of the two assigned cores. -/
theorem fiber_parity_cases_of_two_even_pairs (label : V → Fin 4)
    (hV : Even (Fintype.card V))
    (h2 : Even (labelShore label {2}).card)
    (h3 : Even (labelShore label {3}).card) :
    (∀ i, (labelShore label {i}).card % 2 = 0) ∨
      (∀ i, (labelShore label {i}).card % 2 = if i = 0 ∨ i = 1 then 1 else 0) := by
  have h01 := core_fiber_parity_eq_of_two_even_pairs label hV h2 h3
  have hp2 := Nat.even_iff.mp h2
  have hp3 := Nat.even_iff.mp h3
  by_cases h0 : (labelShore label {0}).card % 2 = 0
  · left
    intro i
    fin_cases i
    · exact h0
    · exact h01.symm.trans h0
    · exact hp2
    · exact hp3
  · have h0odd : (labelShore label {0}).card % 2 = 1 := by omega
    right
    intro i
    fin_cases i
    · simpa using h0odd
    · simpa using h01.symm.trans h0odd
    · simpa using hp2
    · simpa using hp3

/-- A perfect matching with two internal exceptional copies constructs four
distinct assigned fibers with the required all-even or two-odd parity. -/
theorem exists_two_pair_assigned_labels {M : Finset E} (hM : G.IsPerfectMatching M)
    (U₀ U₁ Z : Finset V) (h01 : Disjoint U₀ U₁)
    (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z)
    (hpair : (G.internalOn M Z).card = 2) :
    ∃ (e f : E) (label : V → Fin 4), e ≠ f ∧ G.internalOn M Z = {e, f} ∧
      labelShore label {0} = corePart G M Z U₀ ∧
      labelShore label {1} = corePart G M Z U₁ ∧
      labelShore label {2} = exceptionalPairPart G e ∧
      labelShore label {3} = exceptionalPairPart G f ∧
      (labelShore label {2}).card = 2 ∧ (labelShore label {3}).card = 2 ∧
      (labelShore label {0}).card % 2 = (labelShore label {1}).card % 2 ∧
      ((∀ i, (labelShore label {i}).card % 2 = 0) ∨
        (∀ i, (labelShore label {i}).card % 2 = if i = 0 ∨ i = 1 then 1 else 0)) := by
  obtain ⟨e, f, hef, hparts⟩ := card_eq_two.mp hpair
  let label := twoPairAssignedLabel G M U₀ U₁ Z e
  have hfibers := twoPairAssignedLabel_fibers G hM U₀ U₁ Z h01 h0Z h1Z hcover e f hef hparts
  have hc2 : (labelShore label {2}).card = 2 := by
    rw [hfibers.2.2.1]
    exact exceptionalPairPart_card G e
  have hc3 : (labelShore label {3}).card = 2 := by
    rw [hfibers.2.2.2]
    exact exceptionalPairPart_card G f
  have he2 : Even (labelShore label {2}).card := by rw [hc2]; decide
  have he3 : Even (labelShore label {3}).card := by rw [hc3]; decide
  refine ⟨e, f, label, hef, hparts, hfibers.1, hfibers.2.1,
    hfibers.2.2.1, hfibers.2.2.2, hc2, hc3, ?_, ?_⟩
  · exact core_fiber_parity_eq_of_two_even_pairs label (hM.even_card G) he2 he3
  · exact fiber_parity_cases_of_two_even_pairs label (hM.even_card G) he2 he3

end Overfull.AssignedParts
