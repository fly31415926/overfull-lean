import Overfull.AssignedParts.TwoPairPalette

/-!
# The actual remaining vertex after two exceptional pairs

The five-exception bound leaves either no unpaired exception or one actual
vertex.  In the latter case its assigned fiber is exactly its old core plus
that vertex, and the other assigned core has no added vertex.  The conclusion
is derived from the original perfect matching and four-fiber assignment.
-/

noncomputable section

namespace Overfull.AssignedParts

open Finset Classical FourOdd

variable {V E : Type*} (G : Multigraph V E)

/-- If at most one specified vertex lies outside the paired support, every
assigned core lies in its old core together with that vertex. -/
theorem corePart_subset_insert_of_single_unpaired {M : Finset E}
    (hM : G.IsMatching M) (U Z : Finset V) (hUZ : Disjoint U Z)
    (z : V) (hZ : Z ⊆ pairPart G M Z ∪ {z}) :
    corePart G M Z U ⊆ insert z U := by
  intro v hv
  rcases (mem_corePart G M Z U v).mp hv with hvU | hvZ
  · exact mem_insert_of_mem hvU
  · have hn : v ∉ pairPart G M Z :=
      fun hp => disjoint_left.mp (corePart_pairPart_disjoint G hM U Z hUZ) hv hp
    have hz : v ∈ ({z} : Finset V) := (mem_union.mp (hZ hvZ.1)).resolve_left hn
    exact mem_insert.mpr (Or.inl (mem_singleton.mp hz))

/-- The unique unpaired vertex gives an exact insert when it is assigned
to the indicated core. -/
theorem corePart_eq_insert_of_single_unpaired {M : Finset E}
    (hM : G.IsMatching M) (U Z : Finset V) (hUZ : Disjoint U Z)
    (z : V) (hZ : Z ⊆ pairPart G M Z ∪ {z})
    (hz : z ∈ corePart G M Z U) :
    corePart G M Z U = insert z U := by
  apply subset_antisymm (corePart_subset_insert_of_single_unpaired G hM U Z hUZ z hZ)
  exact insert_subset hz (core_subset_corePart G M Z U)

/-- A core not assigned the unique unpaired vertex remains its old core. -/
theorem corePart_eq_core_of_single_unpaired {M : Finset E}
    (hM : G.IsMatching M) (U Z : Finset V) (hUZ : Disjoint U Z)
    (z : V) (hZ : Z ⊆ pairPart G M Z ∪ {z})
    (hz : z ∉ corePart G M Z U) :
    corePart G M Z U = U := by
  apply subset_antisymm
  · intro v hv
    have hm := corePart_subset_insert_of_single_unpaired G hM U Z hUZ z hZ hv
    rcases mem_insert.mp hm with heq | hm
    · exact (hz (heq ▸ hv)).elim
    · exact hm
  · exact core_subset_corePart G M Z U

variable [Fintype V]

/-- The original five-exception hypothesis constructs the complete
zero-or-one-star geometry for two actual exceptional matching pairs. -/
theorem twoPair_zero_or_one_star_geometry {M : Finset E}
    (hM : G.IsPerfectMatching M) (U₀ U₁ Z : Finset V)
    (h01 : Disjoint U₀ U₁) (h0Z : Disjoint U₀ Z) (h1Z : Disjoint U₁ Z)
    (hcover : ∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) (hZ : Z.card ≤ 5)
    (e₀ e₁ : E) (he : e₀ ≠ e₁) (hpair : G.internalOn M Z = {e₀,e₁}) :
    Z = exceptionalPairPart G e₀ ∪ exceptionalPairPart G e₁ ∨
      ∃ z, z ∈ Z ∧ z ∉ exceptionalPairPart G e₀ ∪ exceptionalPairPart G e₁ ∧
        Z = exceptionalPairPart G e₀ ∪ exceptionalPairPart G e₁ ∪ {z} ∧
        ((twoPairAssignedLabel G M U₀ U₁ Z e₀ z = 0 ∧
          labelShore (twoPairAssignedLabel G M U₀ U₁ Z e₀) {0} = insert z U₀ ∧
          corePart G M Z U₁ = U₁) ∨
         (twoPairAssignedLabel G M U₀ U₁ Z e₀ z = 1 ∧
          labelShore (twoPairAssignedLabel G M U₀ U₁ Z e₀) {1} = insert z U₁ ∧
          corePart G M Z U₀ = U₀)) := by
  have hpairs := pairPart_eq_two_pair_union G e₀ e₁ hpair
  have hcount : (G.internalOn M Z).card = 2 := by
    rw [hpair,card_insert_of_notMem (by simpa using he),card_singleton]
  have hrem := unpaired_card_le_one_of_two_pairs G (hM.isMatching G) Z hZ hcount
  by_cases hnone : Z \ pairPart G M Z = ∅
  · left
    have hsub : Z ⊆ pairPart G M Z := sdiff_eq_empty_iff_subset.mp hnone
    exact (subset_antisymm hsub (pairPart_subset G M Z)).trans hpairs
  · obtain ⟨z,hz⟩ := nonempty_iff_ne_empty.mpr hnone
    have hzZ := (mem_sdiff.mp hz).1
    have hzP := (mem_sdiff.mp hz).2
    have hremEq : Z \ pairPart G M Z = {z} := by
      ext v
      constructor
      · intro hv
        exact mem_singleton.mpr ((card_le_one.mp hrem) hv hz)
      · intro hv
        exact (mem_singleton.mp hv).symm ▸ hz
    have hZeq : Z = pairPart G M Z ∪ {z} := by
      rw [← hremEq,union_sdiff_of_subset (pairPart_subset G M Z)]
    have hZsub : Z ⊆ pairPart G M Z ∪ {z} := hZeq.le
    have hparts := coreParts_disjoint G (hM.isMatching G) U₀ U₁ Z h01 h0Z h1Z
    have hfibers := twoPairAssignedLabel_fibers G hM U₀ U₁ Z
      h01 h0Z h1Z hcover e₀ e₁ he hpair
    refine Or.inr ⟨z,hzZ,by simpa only [hpairs] using hzP,
      by simpa only [hpairs] using hZeq,?_⟩
    rcases coreParts_cover G hM U₀ U₁ Z hcover z with hz0 | hz1 | hzPair
    · have hn1 : z ∉ corePart G M Z U₁ := fun hh => disjoint_left.mp hparts hz0 hh
      have heq0 := corePart_eq_insert_of_single_unpaired G (hM.isMatching G)
        U₀ Z h0Z z hZsub hz0
      have heq1 := corePart_eq_core_of_single_unpaired G (hM.isMatching G)
        U₁ Z h1Z z hZsub hn1
      refine Or.inl ⟨?_,hfibers.1.trans heq0,heq1⟩
      simp only [twoPairAssignedLabel,if_pos hz0]
    · have hn0 : z ∉ corePart G M Z U₀ := fun hh => disjoint_left.mp hparts hh hz1
      have heq1 := corePart_eq_insert_of_single_unpaired G (hM.isMatching G)
        U₁ Z h1Z z hZsub hz1
      have heq0 := corePart_eq_core_of_single_unpaired G (hM.isMatching G)
        U₀ Z h0Z z hZsub hn0
      refine Or.inr ⟨?_,hfibers.2.1.trans heq1,heq0⟩
      simp only [twoPairAssignedLabel,if_neg hn0,if_pos hz1]
    · exact (hzP hzPair).elim

end Overfull.AssignedParts
