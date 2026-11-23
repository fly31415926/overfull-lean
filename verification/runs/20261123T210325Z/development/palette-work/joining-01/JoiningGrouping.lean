import Overfull.ResidualPalette.PaletteGrouping
import Overfull.ResidualPalette.PaletteParity

/-!
# Actual parity-preserving palette classes for joining copies

The even and two-odd circuit decompositions are grouped into actual matching
color classes. The construction preserves all edge copies, retains each
fiber's required parity, and bounds both whole-class footprints and the
number of classes meeting any vertex. It does not align reserved crossing
copies or provide the later robust perfect-matching completions.
-/

noncomputable section

namespace Overfull.NativeReserve

open Finset Classical

variable {V E K : Type*} [Fintype V] [Fintype E] [DecidableEq K]

/-- A complete matching palette for all actual joining copies, with explicit
cut parity and the whole-class size/load bounds needed for later completion. -/
structure JoiningPalette (G : Multigraph V E) (label : V → K)
    (h D L : ℕ) (parity : K → ℕ) where
  classes : Fin h → Finset E
  matching : ∀ j, G.IsMatching (classes j)
  disjoint : Pairwise (fun i j => Disjoint (classes i) (classes j))
  cover : univ.biUnion classes = FourOdd.joiningCopies G label
  cut_parity : ∀ j i, (G.cutOn (classes j) (FourOdd.labelShore label {i})).card % 2 = parity i
  card_le : ∀ j, (classes j).card ≤ 3*L
  support_card_le : ∀ j, (G.edgeSupport (classes j)).card ≤ 6*L
  vertex_load_le : ∀ v, (univ.filter (fun j => v ∈ G.edgeSupport (classes j))).card ≤ D

end Overfull.NativeReserve

namespace Overfull.FourOdd

open Finset Classical NativeReserve

variable {V E K : Type*} [Fintype V] [Fintype E] [DecidableEq K]
    (G : Multigraph V E) (label : V → K)

/-- Group every all-even joining circuit into an actual matching palette
while retaining each fiber's even cut certificate. -/
theorem EvenJoiningDecomposition.exists_palette
    (P : EvenJoiningDecomposition G label) {h D L : ℕ}
    (hdegree : ∀ v, G.degreeOn (joiningCopies G label) v ≤ D)
    (hL : 0 < L) (hDh : 6*D < h)
    (hbudget : Fintype.card V*D ≤ 2*L*(h-6*D)) :
    Nonempty (JoiningPalette G label h D L (fun _ => 0)) := by
  let M : P.parts → Finset E := Subtype.val
  have hM : ∀ j, G.IsMatching (M j) := fun j => P.matching _ j.property
  have hsize : ∀ j, (M j).card ≤ 3 := fun j => P.card_le _ j.property
  have hdis : Pairwise (fun i j => Disjoint (M i) (M j)) := by
    intro i j hij
    exact P.disjoint _ i.property _ j.property (fun hh => hij (Subtype.ext hh))
  have hsubset : ∀ j, M j ⊆ joiningCopies G label := by
    intro j e he
    rw [← P.cover]
    exact mem_biUnion.mpr ⟨j.val, j.property, he⟩
  have hcount : Fintype.card P.parts ≤ L*(h-6*D) :=
    palette_capacity_of_incidence_budget G M (joiningCopies G label)
      (fun j => P.nonempty _ j.property) hdis hsubset hdegree hbudget
  have hpos : 0 < h := lt_of_le_of_lt (Nat.zero_le _) hDh
  obtain ⟨c, _, hcload, hmatching, hgroups, hcover, hcard, hsupport⟩ :=
    exists_bounded_matching_grouping G M (joiningCopies G label) ∅ (fun _ => ⟨0,hpos⟩)
      (by simp) hM hsize hdis hsubset hdegree hL hDh hcount
  have hcoverM : univ.biUnion M = joiningCopies G label := by
    rw [← P.cover]
    ext e
    simp only [mem_biUnion, mem_univ, true_and]
    exact ⟨fun ⟨j,hj⟩ => ⟨j.val,j.property,hj⟩,
      fun ⟨N,hN,he⟩ => ⟨⟨N,hN⟩,he⟩⟩
  refine ⟨{
    classes := groupedCopies M c
    matching := hmatching
    disjoint := hgroups
    cover := hcover.trans hcoverM
    cut_parity := ?_
    card_le := hcard
    support_card_le := hsupport
    vertex_load_le := groupedCopies_support_load_le G M c _ hdis hsubset hdegree
  }⟩
  intro j i
  apply Nat.even_iff.mp
  apply cutOn_biUnion_even G _ M _ _
  · intro a _ b _ hab
    exact hdis hab
  · intro a _
    exact P.even_cut _ a.property i

/-- Group two-odd joining pieces after prescribing the `h` primary pieces
bijectively to the `h` labels. Every whole class has exactly the target cut
parity because all its additional pieces have even cuts. -/
theorem TwoOddJoiningDecomposition.exists_palette {a b : K} {h D L : ℕ}
    (P : TwoOddJoiningDecomposition G label a b h)
    (hdegree : ∀ v, G.degreeOn (joiningCopies G label) v ≤ D)
    (hL : 0 < L) (hDh : 6*D < h)
    (hbudget : Fintype.card V*D ≤ 2*L*(h-6*D)) :
    Nonempty (JoiningPalette G label h D L (fun i => if i=a ∨ i=b then 1 else 0)) := by
  let T := P.primary ∪ P.surplus
  let M : T → Finset E := Subtype.val
  let A : Finset T := univ.filter (fun j => j.val ∈ P.primary)
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
  have hcount : Fintype.card T ≤ L*(h-6*D) :=
    palette_capacity_of_incidence_budget G M (joiningCopies G label)
      (fun j => P.nonempty _ j.property) hdis hsubset hdegree hbudget
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
    rw [himage, P.primary_card] at hc
    exact hc.symm
  have hpos : 0 < h := lt_of_le_of_lt (Nat.zero_le _) hDh
  obtain ⟨c, hcA, hcload, hmatching, hgroups, hcover, hcard, hsupport⟩ :=
    exists_bounded_matching_grouping G M (joiningCopies G label) A (primarySeed A hA hpos)
      (primarySeed_injective A hA hpos) hM hsize hdis hsubset hdegree hL hDh hcount
  have hcoverM : univ.biUnion M = joiningCopies G label := by
    rw [← P.cover]
    ext e
    simp only [mem_biUnion, mem_univ, true_and]
    exact ⟨fun ⟨j,hj⟩ => ⟨j.val,j.property,hj⟩,
      fun ⟨N,hN,he⟩ => ⟨⟨N,hN⟩,he⟩⟩
  refine ⟨{
    classes := groupedCopies M c
    matching := hmatching
    disjoint := hgroups
    cover := hcover.trans hcoverM
    cut_parity := ?_
    card_le := hcard
    support_card_le := hsupport
    vertex_load_le := groupedCopies_support_load_le G M c _ hdis hsubset hdegree
  }⟩
  intro j i
  obtain ⟨p,hp,hunique⟩ := primarySeed_extension_unique A hA hpos c hcA j
  have hpA : p.val.val ∈ P.primary := (mem_filter.mp p.property).2
  have hpclass : p.val ∈ univ.filter (fun q => c q = j) := mem_filter.mpr ⟨mem_univ _,hp⟩
  have heven : ∀ q ∈ univ.filter (fun q => c q = j), q ≠ p.val →
      Even ((G.cutOn (M q) (labelShore label {i})).card) := by
    intro q hq hqp
    have hqnot : q.val ∉ P.primary := by
      intro hqP
      have hqA : q ∈ A := mem_filter.mpr ⟨mem_univ _,hqP⟩
      have heq := hunique ⟨q,hqA⟩ (mem_filter.mp hq).2
      exact hqp (congrArg Subtype.val heq)
    exact P.surplus_even_cut _ ((mem_union.mp q.property).resolve_left hqnot) i
  have hparity := cutOn_biUnion_mod_two_of_one_primary G
    (univ.filter (fun q => c q = j)) M (fun q _ r _ hqr => hdis hqr)
    (labelShore label {i}) p.val hpclass heven
  change (G.cutOn ((univ.filter (fun q => c q = j)).biUnion M)
    (labelShore label {i})).card % 2 = _
  rw [hparity]
  have hpodd := P.primary_odd_cut_iff _ hpA i
  by_cases hi : i=a ∨ i=b
  · rw [if_pos hi]
    exact Nat.odd_iff.mp (hpodd.mpr hi)
  · rw [if_neg hi]
    apply Nat.even_iff.mp
    exact Nat.not_odd_iff_even.mp (fun hh => hi (hpodd.mp hh))

end Overfull.FourOdd
