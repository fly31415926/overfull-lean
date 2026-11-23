import Overfull.ResidualPalette.PaletteGrouping

/-!
# Palette grouping with protected primary classes

A protected primary label receives no surplus piece. This follows by adding
conflicts between every surplus index and every protected primary index.
The extension preserves one primary per palette and all original-copy
matching, coverage, footprint, and load bounds. It does not assert the
existence or alignment of the protected original crossing copies.
-/

noncomputable section

namespace Overfull.NativeReserve

open Finset Classical

variable {V E I : Type*} [Fintype I]

/-- In addition to actual endpoint conflicts, surplus indices conflict with
all protected primary indices. -/
def protectedPieceConflict (G : Multigraph V E) (M : I → Finset E)
    (P Q : Finset I) (i j : I) : Prop :=
  pieceConflict G M i j ∨ (i ∈ Q ∧ j ∉ P) ∨ (j ∈ Q ∧ i ∉ P)

omit [Fintype I] in
/-- The augmented conflict relation is symmetric. -/
theorem protectedPieceConflict_symm (G : Multigraph V E) (M : I → Finset E)
    (P Q : Finset I) : Symmetric (protectedPieceConflict G M P Q) := by
  intro i j hij
  rcases hij with hh | hh | hh
  · exact Or.inl ⟨hh.1.symm, fun hd => hh.2 hd.symm⟩
  · exact Or.inr (Or.inr hh)
  · exact Or.inr (Or.inl hh)

omit [Fintype I] in
/-- Protection introduces no loop because every protected index is primary. -/
theorem protectedPieceConflict_irrefl (G : Multigraph V E) (M : I → Finset E)
    (P Q : Finset I) (hQP : Q ⊆ P) : Irreflexive (protectedPieceConflict G M P Q) := by
  intro i hii
  rcases hii with hh | hh | hh
  · exact hh.1 rfl
  · exact hh.2 (hQP hh.1)
  · exact hh.2 (hQP hh.1)

/-- At an uncolored surplus index, the only new possible neighbors are the
protected primary indices. The bound counts actual copy endpoint conflicts. -/
theorem protectedPieceConflict_card_le (G : Multigraph V E) (M : I → Finset E)
    (S : Finset E) (P Q : Finset I) (hQP : Q ⊆ P) (D : ℕ)
    (hsize : ∀ i, (M i).card ≤ 3)
    (hdisjoint : Pairwise (fun i j => Disjoint (M i) (M j)))
    (hsubset : ∀ i, M i ⊆ S) (hdegree : ∀ v, G.degreeOn S v ≤ D)
    (i : I) (hi : i ∉ P) :
    (univ.filter (protectedPieceConflict G M P Q i)).card ≤ 6*D+Q.card := by
  have hsub : univ.filter (protectedPieceConflict G M P Q i) ⊆
      univ.filter (pieceConflict G M i) ∪ Q := by
    intro j hj
    rcases (mem_filter.mp hj).2 with hh | hh | hh
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _,hh⟩)
    · exact (hi (hQP hh.1)).elim
    · exact mem_union_right _ hh.1
  exact (card_le_card hsub).trans ((card_union_le _ _).trans
    (Nat.add_le_add_right (pieceConflict_card_le G M S D hsize hdisjoint hsubset hdegree i) _))

/-- Construct a bounded matching grouping whose protected primary classes
remain exactly their original pieces, without any added surplus. -/
theorem exists_protected_matching_grouping {h D L : ℕ}
    (G : Multigraph V E) (M : I → Finset E) (S : Finset E)
    (P Q : Finset I) (hQP : Q ⊆ P) (hP : P.card = h)
    (hM : ∀ i, G.IsMatching (M i)) (hsize : ∀ i, (M i).card ≤ 3)
    (hdisjoint : Pairwise (fun i j => Disjoint (M i) (M j)))
    (hsubset : ∀ i, M i ⊆ S) (hdegree : ∀ v, G.degreeOn S v ≤ D)
    (hL : 0 < L) (hDh : 6*D+Q.card < h)
    (hbudget : Fintype.card I ≤ L*(h-6*D-Q.card)) :
    ∃ c : I → Fin h,
      (∀ i, ∃! j : P, c j.val = i) ∧
      (∀ p ∈ Q, groupedCopies M c (c p) = M p) ∧
      (∀ i, (univ.filter (fun j => c j = i)).card ≤ L) ∧
      (∀ i, G.IsMatching (groupedCopies M c i)) ∧
      Pairwise (fun i j => Disjoint (groupedCopies M c i) (groupedCopies M c j)) ∧
      univ.biUnion (groupedCopies M c) = univ.biUnion M ∧
      (∀ i, (groupedCopies M c i).card ≤ 3*L) ∧
      (∀ i, (G.edgeSupport (groupedCopies M c i)).card ≤ 6*L) ∧
      (∀ v, (univ.filter (fun i => v ∈ G.edgeSupport (groupedCopies M c i))).card ≤ D) := by
  have hpos : 0 < h := lt_of_le_of_lt (Nat.zero_le _) hDh
  let c₀ := primarySeed P hP hpos
  have hinj : Set.InjOn c₀ P := primarySeed_injective P hP hpos
  have hp : ∀ i ∈ P, ∀ j ∈ P, protectedPieceConflict G M P Q i j → c₀ i ≠ c₀ j := by
    intro i hi j hj hij heq
    have hs := hinj hi hj heq
    subst j
    exact protectedPieceConflict_irrefl G M P Q hQP i hij
  have hl : ∀ i, (P.filter (fun j => c₀ j = i)).card ≤ L := by
    intro i
    have hh : (P.filter (fun j => c₀ j = i)).card ≤ 1 := by
      apply card_le_one.mpr
      intro j hj k hk
      exact hinj (mem_filter.mp hj).1 (mem_filter.mp hk).1
        ((mem_filter.mp hj).2.trans (mem_filter.mp hk).2.symm)
    omega
  obtain ⟨c,hcP,hcproper,hcload⟩ := exists_bounded_palette_extension
    (protectedPieceConflict G M P Q) (protectedPieceConflict_symm G M P Q)
    (protectedPieceConflict_irrefl G M P Q hQP) univ P (subset_univ _) c₀ hp hl
    (fun i hi => protectedPieceConflict_card_le G M S P Q hQP D
      hsize hdisjoint hsubset hdegree i (mem_sdiff.mp hi).2)
    hDh (by simpa only [card_univ, Nat.sub_sub] using hbudget)
  have hcp : ∀ i j, protectedPieceConflict G M P Q i j → c i ≠ c j :=
    fun i j => hcproper i (mem_univ _) j (mem_univ _)
  refine ⟨c,primarySeed_extension_unique P hP hpos c hcP,?_,hcload,
    groupedCopies_isMatching G M c hM (fun i j hij => hcp i j (Or.inl hij)),
    groupedCopies_disjoint M c hdisjoint,groupedCopies_cover M c,
    groupedCopies_card_le M c hsize hcload,
    groupedCopies_support_card_le G M c hsize hcload,
    groupedCopies_support_load_le G M c S hdisjoint hsubset hdegree⟩
  intro p hpQ
  ext e
  rw [mem_groupedCopies]
  constructor
  · rintro ⟨j,hj,he⟩
    have hjp : j = p := by
      by_cases hjP : j ∈ P
      · apply hinj hjP (hQP hpQ)
        rw [← hcP j hjP,← hcP p (hQP hpQ)]
        exact hj
      · exact (hcp p j (Or.inr (Or.inl ⟨hpQ,hjP⟩)) hj.symm).elim
    simpa only [hjp] using he
  · intro he
    exact ⟨p,rfl,he⟩

/-- The incidence budget gives one common protected-group capacity before
choosing any particular piece coloring. -/
theorem protected_palette_capacity_of_incidence_budget [Fintype V]
    {h D L : ℕ} (G : Multigraph V E) (M : I → Finset E) (S : Finset E)
    (Q : Finset I) (hne : ∀ i, (M i).Nonempty)
    (hdisjoint : Pairwise (fun i j => Disjoint (M i) (M j)))
    (hsubset : ∀ i, M i ⊆ S) (hdegree : ∀ v, G.degreeOn S v ≤ D)
    (hbudget : Fintype.card V*D ≤ 2*L*(h-6*D-Q.card)) :
    Fintype.card I ≤ L*(h-6*D-Q.card) := by
  have hh := twice_piece_count_le_order_mul_degree G M S D hne hdisjoint hsubset hdegree
  nlinarith

end Overfull.NativeReserve
