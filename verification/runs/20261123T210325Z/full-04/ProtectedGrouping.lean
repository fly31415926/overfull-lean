import Overfull.ResidualPalette.JoiningGrouping

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

namespace Overfull.FourOdd

open Finset Classical NativeReserve

variable {V E K : Type*} [Fintype V] [Fintype E] [DecidableEq K]
    (G : Multigraph V E) (label : V → K)

/-- Construct an actual parity-correct joining palette while preserving every
protected primary piece as an entire palette class. In particular, protected
singleton primaries receive no additional joining copy. -/
theorem TwoOddJoiningDecomposition.exists_protected_palette {a b : K} {h D L : ℕ}
    (P : TwoOddJoiningDecomposition G label a b h) (Q : Finset (Finset E))
    (hQP : Q ⊆ P.primary)
    (hdegree : ∀ v, G.degreeOn (joiningCopies G label) v ≤ D)
    (hL : 0 < L) (hDh : 6*D+Q.card < h)
    (hbudget : Fintype.card V*D ≤ 2*L*(h-6*D-Q.card)) :
    ∃ C : JoiningPalette G label h D L (fun i => if i=a ∨ i=b then 1 else 0),
      ∀ N ∈ Q, ∃ j, C.classes j = N := by
  let T := P.primary ∪ P.surplus
  let M : T → Finset E := Subtype.val
  let A : Finset T := univ.filter (fun j => j.val ∈ P.primary)
  let B : Finset T := univ.filter (fun j => j.val ∈ Q)
  have hBA : B ⊆ A := by
    intro j hj
    exact mem_filter.mpr ⟨mem_univ _,hQP (mem_filter.mp hj).2⟩
  have hM : ∀ j, G.IsMatching (M j) := fun j => P.matching _ j.property
  have hsize : ∀ j, (M j).card ≤ 3 := by
    intro j
    rcases mem_union.mp j.property with hj | hj
    · exact (P.primary_card_le _ hj).trans (by omega)
    · exact P.surplus_card_le _ hj
  have hdis : Pairwise (fun i j => Disjoint (M i) (M j)) := by
    intro i j hij
    exact P.disjoint _ i.property _ j.property (fun hh => hij (Subtype.ext hh))
  have hsubset : ∀ j, M j ⊆ joiningCopies G label := by
    intro j e he
    rw [← P.cover]
    exact mem_biUnion.mpr ⟨j.val, j.property, he⟩
  have hA : A.card = h := by
    have himage : A.image Subtype.val = P.primary := by
      ext N
      simp only [mem_image, A, mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨j,hj,rfl⟩
        exact hj
      · intro hN
        exact ⟨⟨N,mem_union_left _ hN⟩,hN,rfl⟩
    have hc := card_image_of_injective A Subtype.val_injective
    rw [himage,P.primary_card] at hc
    exact hc.symm
  have hB : B.card = Q.card := by
    have himage : B.image Subtype.val = Q := by
      ext N
      simp only [mem_image,B,mem_filter,mem_univ,true_and]
      constructor
      · rintro ⟨j,hj,rfl⟩
        exact hj
      · intro hN
        exact ⟨⟨N,mem_union_left _ (hQP hN)⟩,hN,rfl⟩
    have hc := card_image_of_injective B Subtype.val_injective
    rw [himage] at hc
    exact hc.symm
  have hcount : Fintype.card T ≤ L*(h-6*D-B.card) :=
    protected_palette_capacity_of_incidence_budget G M (joiningCopies G label) B
      (fun j => P.nonempty _ j.property) hdis hsubset hdegree (by simpa only [hB] using hbudget)
  obtain ⟨c,hunique,hprotected,hcload,hmatching,hgroups,hcover,hcard,hsupport,hload⟩ :=
    exists_protected_matching_grouping G M (joiningCopies G label) A B hBA hA
      hM hsize hdis hsubset hdegree hL (by simpa only [hB] using hDh) hcount
  have hcoverM : univ.biUnion M = joiningCopies G label := by
    rw [← P.cover]
    ext e
    simp only [mem_biUnion,mem_univ,true_and]
    exact ⟨fun ⟨j,hj⟩ => ⟨j.val,j.property,hj⟩,
      fun ⟨N,hN,he⟩ => ⟨⟨N,hN⟩,he⟩⟩
  have hparity : ∀ j i, (G.cutOn (groupedCopies M c j) (labelShore label {i})).card % 2 =
      if i=a ∨ i=b then 1 else 0 := by
    intro j i
    obtain ⟨p,hp,honly⟩ := hunique j
    have hpA : p.val.val ∈ P.primary := (mem_filter.mp p.property).2
    have hpclass : p.val ∈ univ.filter (fun q => c q = j) := mem_filter.mpr ⟨mem_univ _,hp⟩
    have heven : ∀ q ∈ univ.filter (fun q => c q = j), q ≠ p.val →
        Even ((G.cutOn (M q) (labelShore label {i})).card) := by
      intro q hq hqp
      have hqnot : q.val ∉ P.primary := by
        intro hqP
        have hqA : q ∈ A := mem_filter.mpr ⟨mem_univ _,hqP⟩
        have heq := honly ⟨q,hqA⟩ (mem_filter.mp hq).2
        exact hqp (congrArg Subtype.val heq)
      exact P.surplus_even_cut _ ((mem_union.mp q.property).resolve_left hqnot) i
    have hcut := cutOn_biUnion_mod_two_of_one_primary G
      (univ.filter (fun q => c q = j)) M (fun q _ r _ hqr => hdis hqr)
      (labelShore label {i}) p.val hpclass heven
    change (G.cutOn ((univ.filter (fun q => c q = j)).biUnion M)
      (labelShore label {i})).card % 2 = _
    rw [hcut]
    have hpodd := P.primary_odd_cut_iff _ hpA i
    by_cases hi : i=a ∨ i=b
    · rw [if_pos hi]
      exact Nat.odd_iff.mp (hpodd.mpr hi)
    · rw [if_neg hi]
      apply Nat.even_iff.mp
      exact Nat.not_odd_iff_even.mp (fun hh => hi (hpodd.mp hh))
  let C : JoiningPalette G label h D L (fun i => if i=a ∨ i=b then 1 else 0) := {
    classes := groupedCopies M c
    matching := hmatching
    disjoint := hgroups
    cover := hcover.trans hcoverM
    cut_parity := hparity
    card_le := hcard
    support_card_le := hsupport
    vertex_load_le := hload
  }
  refine ⟨C,?_⟩
  intro N hN
  let j : T := ⟨N,mem_union_left _ (hQP hN)⟩
  have hj : j ∈ B := mem_filter.mpr ⟨mem_univ _,hN⟩
  exact ⟨c j,hprotected j hj⟩

end Overfull.FourOdd
