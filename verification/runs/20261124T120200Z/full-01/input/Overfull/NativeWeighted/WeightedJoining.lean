import Overfull.WeightedPalette.Grouping
import Overfull.ResidualPalette.ProtectedGrouping

/-!
# Weighted palettes for the actual joining decompositions

The even and two-odd decompositions are grouped in the original palette of
`h` colors while controlling at most two actual old-core star resources.
The empty or injective primary seed supplies its own weight certificate;
protected labels receive no surplus piece. Fiber-cut parity and every
original joining copy are retained.
-/

noncomputable section

namespace Overfull.NativeWeighted

open Finset Classical NativeReserve WeightedPalette
open scoped BigOperators

variable {I : Type*} {h : ℕ}

/-- An injective prescribed coloring puts at most one seed in each color. -/
theorem injective_seed_count_le_one (P : Finset I) (c : I → Fin h)
    (hc : Set.InjOn c P) (j : Fin h) :
    (P.filter (fun i => c i = j)).card ≤ 1 := by
  apply card_le_one.mpr
  intro i hi k hk
  exact hc (mem_filter.mp hi).1 (mem_filter.mp hk).1
    ((mem_filter.mp hi).2.trans (mem_filter.mp hk).2.symm)

/-- The seed resource load is at most the weight of one prescribed piece. -/
theorem injective_seed_weight_le (P : Finset I) (c : I → Fin h)
    (hc : Set.InjOn c P) (w : I → ℕ) (W : ℕ)
    (hw : ∀ i ∈ P, w i ≤ W) (j : Fin h) :
    paletteWeight P c w j ≤ W := by
  unfold paletteWeight
  calc
    _ ≤ ∑ _i ∈ P.filter (fun i => c i = j), W :=
      sum_le_sum (fun i hi => hw i (mem_filter.mp hi).1)
    _ = (P.filter (fun i => c i = j)).card * W := by simp
    _ ≤ 1 * W := Nat.mul_le_mul_right W (injective_seed_count_le_one P c hc j)
    _ = W := Nat.one_mul W

/-- The actual incidence count discharges the weighted palette capacity. -/
theorem weighted_capacity_of_incidence_budget
    {V E : Type*} [Fintype V] [Fintype I]
    (G : Multigraph V E) (M : I → Finset E) (S : Finset E)
    (D h s L : ℕ) (hne : ∀ i, (M i).Nonempty)
    (hdisjoint : Pairwise (fun i j => Disjoint (M i) (M j)))
    (hsubset : ∀ i, M i ⊆ S) (hdegree : ∀ v, G.degreeOn S v ≤ D)
    (hbudget : Fintype.card V * D ≤ 2 * L * (h - s - 32 * D)) :
    Fintype.card I ≤ L * (h - s - 32 * D) := by
  have hcount := twice_piece_count_le_order_mul_degree G M S D
    hne hdisjoint hsubset hdegree
  nlinarith

end Overfull.NativeWeighted

namespace Overfull.FourOdd

open Finset Classical NativeReserve WeightedPalette NativeWeighted

variable {V E K κ : Type*} [Fintype V] [Fintype E] [DecidableEq K]
    [Fintype κ] (G : Multigraph V E) (label : V → K)

/-- Group all-even joining circuits with empty protected colors, actual
star weights at most `h/8`, and their original fiber-cut certificates.
The weighted threshold uses the full palette `h` throughout. -/
theorem EvenJoiningDecomposition.exists_star_weighted_palette
    (P : EvenJoiningDecomposition G label) {h D b L : ℕ}
    (Q : Finset (Fin h)) (z : κ → V) (U : κ → Finset V)
    (hresources : Fintype.card κ ≤ 2)
    (hdegree : ∀ v, G.degreeOn (joiningCopies G label) v ≤ D)
    (hparallel : ∀ r, ∀ v ∈ U r, (G.parallelEdges (z r) v).card ≤ b)
    (hexception : ∀ r, G.degree (z r) ≤ h)
    (hbD : b ≤ D) (hh : 0 < h) (hDh : 128 * D ≤ h)
    (hQ : 2 * Q.card ≤ h)
    (hbudget : Fintype.card V * D ≤ 2 * L * (h - Q.card - 32 * D)) :
    ∃ C : JoiningPalette G label h D L (fun _ => 0),
      (∀ r j, starWeight G (z r) (U r) (C.classes j) ≤ h / 8) ∧
      (∀ j ∈ Q, C.classes j = ∅) := by
  let M : P.parts → Finset E := Subtype.val
  have hM : ∀ j, G.IsMatching (M j) := fun j => P.matching _ j.property
  have hsize : ∀ j, (M j).card ≤ 3 := fun j => P.card_le _ j.property
  have hdis : Pairwise (fun i j => Disjoint (M i) (M j)) := by
    intro i j hij
    exact P.disjoint _ i.property _ j.property (fun heq => hij (Subtype.ext heq))
  have hsubset : ∀ j, M j ⊆ joiningCopies G label := by
    intro j e he
    rw [← P.cover]
    exact mem_biUnion.mpr ⟨j.val, j.property, he⟩
  have hcount : Fintype.card P.parts ≤ L * (h - Q.card - 32 * D) :=
    weighted_capacity_of_incidence_budget G M (joiningCopies G label) D h Q.card L
      (fun j => P.nonempty _ j.property) hdis hsubset hdegree hbudget
  obtain ⟨c, _hseed, _hproper, _havoid, hprotected, _hcload, _hweight,
      hstar, hmatching, hgroups, hcover, hcard, hsupport, hload⟩ :=
    exists_star_weighted_matching_grouping G M (joiningCopies G label)
      ∅ (fun _ => ⟨0, hh⟩) Q z U hresources (by simp) (by simp) (by simp)
      hM hsize hdis hsubset hdegree hparallel hexception hbD hh hDh hQ hcount
  have hcoverM : univ.biUnion M = joiningCopies G label := by
    rw [← P.cover]
    ext e
    simp only [mem_biUnion, mem_univ, true_and]
    exact ⟨fun ⟨j,hj⟩ => ⟨j.val,j.property,hj⟩,
      fun ⟨N,hN,he⟩ => ⟨⟨N,hN⟩,he⟩⟩
  let C : JoiningPalette G label h D L (fun _ => 0) := {
    classes := groupedCopies M c
    matching := hmatching
    disjoint := hgroups
    cover := hcover.trans hcoverM
    cut_parity := by
      intro j i
      apply Nat.even_iff.mp
      exact cutOn_biUnion_even G (univ.filter (fun q => c q = j)) M
        (fun a _ b _ hab => hdis hab) (labelShore label {i})
        (fun a _ => P.even_cut _ a.property i)
    card_le := hcard
    support_card_le := hsupport
    vertex_load_le := hload
  }
  refine ⟨C, hstar, ?_⟩
  intro j hj
  simpa only [filter_empty, biUnion_empty] using hprotected j hj

/-- Group two-odd joining pieces with one genuine primary in every
color, retaining each protected primary as its whole color class and
bounding all actual old-core star weights by `h/8`. -/
theorem TwoOddJoiningDecomposition.exists_star_weighted_protected_palette
    {a a' : K} {h D b L : ℕ}
    (P : TwoOddJoiningDecomposition G label a a' h)
    (Q : Finset (Finset E)) (hQP : Q ⊆ P.primary)
    (z : κ → V) (U : κ → Finset V) (hresources : Fintype.card κ ≤ 2)
    (hdegree : ∀ v, G.degreeOn (joiningCopies G label) v ≤ D)
    (hparallel : ∀ r, ∀ v ∈ U r, (G.parallelEdges (z r) v).card ≤ b)
    (hexception : ∀ r, G.degree (z r) ≤ h)
    (hbD : b ≤ D) (hh : 0 < h) (hDh : 128 * D ≤ h)
    (hL : 0 < L) (hQ : 2 * Q.card ≤ h)
    (hbudget : Fintype.card V * D ≤ 2 * L * (h - Q.card - 32 * D)) :
    ∃ C : JoiningPalette G label h D L (fun i => if i=a ∨ i=a' then 1 else 0),
      (∀ r j, starWeight G (z r) (U r) (C.classes j) ≤ h / 8) ∧
      (∀ N ∈ Q, ∃ j, C.classes j = N) := by
  let T := P.primary ∪ P.surplus
  let M : T → Finset E := Subtype.val
  let A : Finset T := univ.filter (fun j => j.val ∈ P.primary)
  let B : Finset T := univ.filter (fun j => j.val ∈ Q)
  have hBA : B ⊆ A := by
    intro j hj
    exact mem_filter.mpr ⟨mem_univ _, hQP (mem_filter.mp hj).2⟩
  have hM : ∀ j, G.IsMatching (M j) := fun j => P.matching _ j.property
  have hsize : ∀ j, (M j).card ≤ 3 := by
    intro j
    rcases mem_union.mp j.property with hj | hj
    · exact (P.primary_card_le _ hj).trans (by omega)
    · exact P.surplus_card_le _ hj
  have hdis : Pairwise (fun i j => Disjoint (M i) (M j)) := by
    intro i j hij
    exact P.disjoint _ i.property _ j.property (fun heq => hij (Subtype.ext heq))
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
    rw [himage, P.primary_card] at hc
    exact hc.symm
  have hB : B.card = Q.card := by
    have himage : B.image Subtype.val = Q := by
      ext N
      simp only [mem_image, B, mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨j,hj,rfl⟩
        exact hj
      · intro hN
        exact ⟨⟨N,mem_union_left _ (hQP hN)⟩,hN,rfl⟩
    have hc := card_image_of_injective B Subtype.val_injective
    rw [himage] at hc
    exact hc.symm
  let c₀ := primarySeed A hA hh
  have hinj : Set.InjOn c₀ A := primarySeed_injective A hA hh
  let F := B.image c₀
  have hF : F.card = Q.card := (card_image_of_injOn (hinj.mono hBA)).trans hB
  have hseedProper : ∀ i ∈ A, ∀ j ∈ A, pieceConflict G M i j → c₀ i ≠ c₀ j := by
    intro i hi j hj hij heq
    exact hij.1 (hinj hi hj heq)
  have hseedCount : ∀ j, (A.filter (fun i => c₀ i = j)).card ≤ L := by
    intro j
    exact (injective_seed_count_le_one A c₀ hinj j).trans hL
  have hseedWeight : ∀ r j,
      paletteWeight A c₀ (fun i => starWeight G (z r) (U r) (M i)) j ≤ h / 8 := by
    intro r j
    apply injective_seed_weight_le A c₀ hinj _ (h / 8) _ j
    intro i hi
    apply (starWeight_le_four_mul G (z r) (U r) (M i) b (hparallel r)
      (P.primary_card_le _ (mem_filter.mp hi).2)).trans
    omega
  have hcount : Fintype.card T ≤ L * (h - F.card - 32 * D) :=
    weighted_capacity_of_incidence_budget G M (joiningCopies G label) D h F.card L
      (fun j => P.nonempty _ j.property) hdis hsubset hdegree
      (by simpa only [hF] using hbudget)
  obtain ⟨c, hcA, _hproper, _havoid, hprotected, _hcload, _hweight,
      hstar, hmatching, hgroups, hcover, hcard, hsupport, hload⟩ :=
    exists_star_weighted_matching_grouping G M (joiningCopies G label) A c₀ F z U
      hresources hseedProper hseedCount hseedWeight hM hsize hdis hsubset
      hdegree hparallel hexception hbD hh hDh (by simpa only [hF] using hQ) hcount
  have hcoverM : univ.biUnion M = joiningCopies G label := by
    rw [← P.cover]
    ext e
    simp only [mem_biUnion, mem_univ, true_and]
    exact ⟨fun ⟨j,hj⟩ => ⟨j.val,j.property,hj⟩,
      fun ⟨N,hN,he⟩ => ⟨⟨N,hN⟩,he⟩⟩
  let C : JoiningPalette G label h D L (fun i => if i=a ∨ i=a' then 1 else 0) := {
    classes := groupedCopies M c
    matching := hmatching
    disjoint := hgroups
    cover := hcover.trans hcoverM
    cut_parity := by
      intro j i
      obtain ⟨p,hp,honly⟩ := primarySeed_extension_unique A hA hh c hcA j
      have hpA : p.val.val ∈ P.primary := (mem_filter.mp p.property).2
      have hpclass : p.val ∈ univ.filter (fun q => c q = j) :=
        mem_filter.mpr ⟨mem_univ _, hp⟩
      have heven : ∀ q ∈ univ.filter (fun q => c q = j), q ≠ p.val →
          Even ((G.cutOn (M q) (labelShore label {i})).card) := by
        intro q hq hqp
        have hqnot : q.val ∉ P.primary := by
          intro hqP
          have hqA : q ∈ A := mem_filter.mpr ⟨mem_univ _, hqP⟩
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
      by_cases hi : i=a ∨ i=a'
      · rw [if_pos hi]
        exact Nat.odd_iff.mp (hpodd.mpr hi)
      · rw [if_neg hi]
        apply Nat.even_iff.mp
        exact Nat.not_odd_iff_even.mp (fun hi' => hi (hpodd.mp hi'))
    card_le := hcard
    support_card_le := hsupport
    vertex_load_le := hload
  }
  refine ⟨C, hstar, ?_⟩
  intro N hN
  let q : T := ⟨N, mem_union_left _ (hQP hN)⟩
  have hqB : q ∈ B := mem_filter.mpr ⟨mem_univ _, hN⟩
  have hqA := hBA hqB
  have hqF : c₀ q ∈ F := mem_image_of_mem c₀ hqB
  have hsingle : A.filter (fun i => c₀ i = c₀ q) = {q} := by
    ext i
    constructor
    · intro hi
      exact mem_singleton.mpr (hinj (mem_filter.mp hi).1 hqA (mem_filter.mp hi).2)
    · intro hi
      rcases mem_singleton.mp hi with rfl
      exact mem_filter.mpr ⟨hqA,rfl⟩
  refine ⟨c₀ q, ?_⟩
  change groupedCopies M c (c₀ q) = N
  rw [hprotected _ hqF, hsingle, singleton_biUnion]

end Overfull.FourOdd
