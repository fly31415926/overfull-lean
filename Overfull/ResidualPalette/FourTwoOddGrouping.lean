import Overfull.ResidualPalette.FourProtectedGrouping
import Overfull.ResidualPalette.FourJoiningGrouping

/-!
# Protected and unprotected four-label two-odd joining palettes

Primary pieces contain at most three original copies and surplus pieces at
most four.  A protected primary remains an entire color class.  The grouping
has at most `4*L` copies and `8*L` support vertices per class; it is stored in
`JoiningPalette` at capacity `2*L`, as in the all-even four-label interface.
-/

noncomputable section

namespace Overfull.FourOdd

open Finset Classical NativeReserve

variable {V E K : Type*} [Fintype V] [Fintype E] [DecidableEq K]
    (G : Multigraph V E) (label : V → K)

/-- Construct an actual parity-correct joining palette while preserving every
protected primary piece as an entire palette class. In particular, protected
singleton primaries receive no additional joining copy. -/
theorem FourTwoOddJoiningDecomposition.exists_protected_palette {a b : K} {h D L : ℕ}
    (P : FourTwoOddJoiningDecomposition G label a b h) (Q : Finset (Finset E))
    (hQP : Q ⊆ P.primary)
    (hdegree : ∀ v, G.degreeOn (joiningCopies G label) v ≤ D)
    (hL : 0 < L) (hDh : 8*D+Q.card < h)
    (hbudget : Fintype.card V*D ≤ 2*L*(h-8*D-Q.card)) :
    ∃ C : JoiningPalette G label h D (2*L) (fun i => if i=a ∨ i=b then 1 else 0),
      ∀ N ∈ Q, ∃ j, C.classes j = N := by
  let T := P.primary ∪ P.surplus
  let M : T → Finset E := Subtype.val
  let A : Finset T := univ.filter (fun j => j.val ∈ P.primary)
  let B : Finset T := univ.filter (fun j => j.val ∈ Q)
  have hBA : B ⊆ A := by
    intro j hj
    exact mem_filter.mpr ⟨mem_univ _,hQP (mem_filter.mp hj).2⟩
  have hM : ∀ j, G.IsMatching (M j) := fun j => P.matching _ j.property
  have hsize : ∀ j, (M j).card ≤ 4 := by
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
  have hcount : Fintype.card T ≤ L*(h-8*D-B.card) :=
    protected_palette_capacity_of_incidence_budget_of_size (s := 4) G M (joiningCopies G label) B
      (fun j => P.nonempty _ j.property) hdis hsubset hdegree (by simpa only [hB] using hbudget)
  obtain ⟨c,hunique,hprotected,hcload,hmatching,hgroups,hcover,hcard,hsupport,hload⟩ :=
    exists_protected_matching_grouping_of_size (s := 4) G M (joiningCopies G label) A B hBA hA
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
  let C : JoiningPalette G label h D (2*L) (fun i => if i=a ∨ i=b then 1 else 0) := {
    classes := groupedCopies M c
    matching := hmatching
    disjoint := hgroups
    cover := hcover.trans hcoverM
    cut_parity := hparity
    card_le := fun j => by have hh := hcard j; omega
    support_card_le := fun j => by have hh := hsupport j; omega
    vertex_load_le := hload
  }
  refine ⟨C,?_⟩
  intro N hN
  let j : T := ⟨N,mem_union_left _ (hQP hN)⟩
  have hj : j ∈ B := mem_filter.mpr ⟨mem_univ _,hN⟩
  exact ⟨c j,hprotected j hj⟩

/-- The actual four-label two-odd decomposition always gives a complete
joining palette under its incidence and capacity margins, with no protected
piece supplied or coloring assumed. -/
theorem FourTwoOddJoiningDecomposition.exists_palette {a b : K} {h D L : ℕ}
    (P : FourTwoOddJoiningDecomposition G label a b h)
    (hdegree : ∀ v, G.degreeOn (joiningCopies G label) v ≤ D)
    (hL : 0 < L) (hDh : 8*D < h)
    (hbudget : Fintype.card V*D ≤ 2*L*(h-8*D)) :
    Nonempty (JoiningPalette G label h D (2*L) (fun i => if i=a ∨ i=b then 1 else 0)) := by
  obtain ⟨C, _⟩ := P.exists_protected_palette G label ∅ (empty_subset _) hdegree hL
    (by simpa only [card_empty, Nat.add_zero] using hDh)
    (by simpa only [card_empty, Nat.sub_zero] using hbudget)
  exact ⟨C⟩

end Overfull.FourOdd
