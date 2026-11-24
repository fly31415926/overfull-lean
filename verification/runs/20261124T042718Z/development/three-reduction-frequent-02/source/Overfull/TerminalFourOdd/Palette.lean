import Overfull.TerminalFourOdd.Decomposition
import Overfull.Terminal.Palette

/-!
# Completing selected four-odd primary colors

Every surplus pair is grouped with one of the chosen primary pieces. The
other primary matchings remain intact, retaining their original forest
profiles and singleton/triple cut counts.
-/

noncomputable section

namespace Overfull.TerminalFourOdd

open Finset Classical FourOdd NativeReserve Terminal

variable {V E : Type*} [Fintype V] [Fintype E]

set_option maxHeartbeats 800000 in
/-- Choose exactly `r` primary pieces as seeds, put every surplus circuit in
those colors, and retain precisely the other `h-r` original primary pieces. -/
theorem exists_prefix_palette_of_selected (G : Multigraph V E) (label : V → Fin 4)
    {h r D L : ℕ} (P : JoiningDecomposition G label h)
    (S : Finset (Finset E)) (hSP : S ⊆ P.primary) (hS : S.card = r)
    (hdegree : ∀ v, G.degreeOn (joiningCopies G label) v ≤ D)
    (hL : 0 < L) (hDr : 6*D < r)
    (hbudget : Fintype.card V*D ≤ 2*L*(r-6*D)) :
    ∃ B : PrefixPalette G label r L (fun _ => 1),
      B.remaining = P.primary \ S ∧ B.remaining.card = h-r := by
  let T := S ∪ P.surplus
  let M : T → Finset E := Subtype.val
  let A : Finset T := univ.filter (fun j => j.val ∈ S)
  have hT : T ⊆ P.primary ∪ P.surplus :=
    union_subset (hSP.trans subset_union_left) subset_union_right
  have hM : ∀ j, G.IsMatching (M j) := fun j => P.matching _ (hT j.property)
  have hsize : ∀ j, (M j).card ≤ 3 := by
    intro j
    rcases mem_union.mp (hT j.property) with hj | hj
    · exact P.primary_card_le _ hj
    · rw [P.surplus_card_eq _ hj]
      decide
  have hdis : Pairwise (fun i j => Disjoint (M i) (M j)) := by
    intro i j hij
    exact P.disjoint _ (hT i.property) _ (hT j.property)
      (fun hh => hij (Subtype.ext hh))
  have hsubset : ∀ j, M j ⊆ joiningCopies G label := by
    intro j e he
    rw [← P.cover]
    exact mem_biUnion.mpr ⟨j.val, hT j.property, he⟩
  have hcount : Fintype.card T ≤ L*(r-6*D) :=
    palette_capacity_of_incidence_budget G M (joiningCopies G label)
      (fun j => P.nonempty _ (hT j.property)) hdis hsubset hdegree hbudget
  have hA : A.card = r := by
    have himage : A.image Subtype.val = S := by
      ext N
      simp only [mem_image, A, mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨j, hj, rfl⟩
        exact hj
      · intro hN
        exact ⟨⟨N, mem_union_left _ hN⟩, hN, rfl⟩
    have hc := card_image_of_injective A Subtype.val_injective
    rw [himage, hS] at hc
    exact hc.symm
  have hpos : 0 < r := lt_of_le_of_lt (Nat.zero_le _) hDr
  obtain ⟨c, hcA, _hcload, hmatching, hgroups, hcover, _hcard, hsupport⟩ :=
    exists_bounded_matching_grouping G M (joiningCopies G label) A (primarySeed A hA hpos)
      (primarySeed_injective A hA hpos) hM hsize hdis hsubset hdegree hL hDr hcount
  have hcoverM : univ.biUnion M = T.biUnion id := by
    ext e
    simp only [mem_biUnion, mem_univ, true_and]
    exact ⟨fun ⟨j, hj⟩ => ⟨j.val, j.property, hj⟩,
      fun ⟨N, hN, he⟩ => ⟨⟨N, hN⟩, he⟩⟩
  have hremain : ∀ N ∈ P.primary \ S, N ∈ P.primary ∪ P.surplus :=
    fun _ hN => mem_union_left _ (mem_sdiff.mp hN).1
  have hcross : ∀ j, ∀ N ∈ P.primary \ S, Disjoint (groupedCopies M c j) N := by
    intro j N hN
    apply disjoint_left.mpr
    intro e he heN
    obtain ⟨p, _, hep⟩ := (mem_groupedCopies M c j e).mp he
    have hpN : p.val ≠ N := by
      intro heq
      have hp := p.property
      change p.val ∈ S ∪ P.surplus at hp
      rw [heq] at hp
      rcases mem_union.mp hp with hp | hp
      · exact (mem_sdiff.mp hN).2 hp
      · exact disjoint_left.mp P.families_disjoint (mem_sdiff.mp hN).1 hp
    exact disjoint_left.mp
      (P.disjoint _ (hT p.property) _ (hremain N hN) hpN) hep heN
  have hall : univ.biUnion (groupedCopies M c) ∪ (P.primary \ S).biUnion id =
      joiningCopies G label := by
    rw [hcover, hcoverM]
    have hunion : T.biUnion id ∪ (P.primary \ S).biUnion id =
        (T ∪ (P.primary \ S)).biUnion id := by
      ext e
      simp only [mem_union, mem_biUnion]
      aesop
    rw [hunion]
    have hsets : T ∪ (P.primary \ S) = P.primary ∪ P.surplus := by
      ext N
      simp only [T, mem_union, mem_sdiff]
      have := fun hN => hSP (a := N) hN
      tauto
    rw [hsets, P.cover]
  have hparity : ∀ j i,
      (G.cutOn (groupedCopies M c j) (labelShore label {i})).card % 2 =
        1 := by
    intro j i
    obtain ⟨p, hp, hunique⟩ := primarySeed_extension_unique A hA hpos c hcA j
    have hpS : p.val.val ∈ S := (mem_filter.mp p.property).2
    have hpclass : p.val ∈ univ.filter (fun q => c q = j) := mem_filter.mpr ⟨mem_univ _, hp⟩
    have heven : ∀ q ∈ univ.filter (fun q => c q = j), q ≠ p.val →
        Even ((G.cutOn (M q) (labelShore label {i})).card) := by
      intro q hq hqp
      have hqnot : q.val ∉ S := by
        intro hqS
        have hqA : q ∈ A := mem_filter.mpr ⟨mem_univ _, hqS⟩
        have heq := hunique ⟨q, hqA⟩ (mem_filter.mp hq).2
        exact hqp (congrArg Subtype.val heq)
      exact P.surplus_even_cut _ ((mem_union.mp q.property).resolve_left hqnot) i
    have hpmod := cutOn_biUnion_mod_two_of_one_primary G
      (univ.filter (fun q => c q = j)) M (fun q _ s _ hqs => hdis hqs)
      (labelShore label {i}) p.val hpclass heven
    change (G.cutOn ((univ.filter (fun q => c q = j)).biUnion M)
      (labelShore label {i})).card % 2 = _
    rw [hpmod]
    exact Nat.odd_iff.mp ((P.primary_profile _ (hSP hpS)).odd_cut i)
  refine ⟨{
    boundary := groupedCopies M c
    remaining := P.primary \ S
    matching := hmatching
    disjoint := hgroups
    remaining_nonempty := fun N hN => P.nonempty N (hremain N hN)
    remaining_matching := fun N hN => P.matching N (hremain N hN)
    remaining_disjoint := fun N hN Q hQ hNQ =>
      P.disjoint N (hremain N hN) Q (hremain Q hQ) hNQ
    cross_disjoint := hcross
    cover := hall
    cut_parity := hparity
    support_card_le := hsupport
  }, rfl, ?_⟩
  rw [card_sdiff_of_subset hSP, P.primary_card, hS]


/-- Select a short prefix, assigning every surplus pair to that prefix and
retaining exactly the other original primary forests. -/
theorem exists_prefix_palette (G : Multigraph V E) (label : V → Fin 4)
    {h r D L : ℕ} (P : JoiningDecomposition G label h)
    (hrh : r ≤ h) (hdegree : ∀ v, G.degreeOn (joiningCopies G label) v ≤ D)
    (hL : 0 < L) (hDr : 6*D < r)
    (hbudget : Fintype.card V*D ≤ 2*L*(r-6*D)) :
    ∃ B : PrefixPalette G label r L (fun _ => 1),
      B.remaining.card = h-r ∧ B.remaining ⊆ P.primary := by
  obtain ⟨S, hSP, hS⟩ := exists_subset_card_eq (show r ≤ P.primary.card by
    rw [P.primary_card]
    exact hrh)
  obtain ⟨B, hB, hc⟩ := exists_prefix_palette_of_selected G label P S hSP hS
    hdegree hL hDr hbudget
  exact ⟨B, hc, by rw [hB]; exact sdiff_subset⟩

end Overfull.TerminalFourOdd
