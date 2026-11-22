import Overfull.FourOdd.Capping
import Overfull.FourOdd.Matching
import Overfull.FourOdd.OriginalGraph

/-!
# Constructing the canonical matching decomposition from actual pools

The four crossing pools are capped by ordinary bipartite edge coloring.
Their parity and the half-incidence condition survive truncation. The two
distinguished pools then supply the exact singleton counts required by
the minority-pairing assembly, while every discarded copy remains in an
actual parallel-pair matching.
-/

noncomputable section

namespace Overfull.FourOdd

open Finset Classical Compression CircuitPatterns
open scoped BigOperators

def matchingForest : Finset LabelPair := {matchingLeftPair, matchingRightPair}

def matchingOffPairs : Finset LabelPair := univ \ matchingForest

theorem matchingForest_shape : LabelForestShape matchingForest :=
  matching_left_right_shape

theorem matchingOffPairs_card : matchingOffPairs.card = 4 := by decide

theorem matchingOffPairs_crosses : ∀ p : LabelPair,
    p ∈ matchingOffPairs ↔ (p.val ∩ {0, 1}).card = 1 := by decide

theorem matchingOffPairs_ne_left : matchingLeftPair ∉ matchingOffPairs := by decide

theorem matchingOffPairs_ne_right : matchingRightPair ∉ matchingOffPairs := by decide

variable {V E : Type*} [Fintype E]

theorem matchingOffPools_eq_cut (Q : Multigraph (Fin 4) E) :
    matchingOffPairs.biUnion (pairPool Q) = Q.cutOn univ {0, 1} := by
  rw [biUnion_pairPool]
  ext e
  simp only [mem_filter, mem_univ, true_and, Multigraph.mem_cutOn]
  exact (matchingOffPairs_crosses (Q.edgeLabelPair e)).trans
    (Q.edgeLabelPair_crosses e {0, 1})

omit [Fintype E] in
private theorem degreeOn_union_disjoint (Q : Multigraph V E)
    {C D : Finset E} (hCD : Disjoint C D) (v : V) :
    Q.degreeOn (C ∪ D) v = Q.degreeOn C v + Q.degreeOn D v := by
  unfold Multigraph.degreeOn
  rw [filter_union, card_union_of_disjoint
    (hCD.mono (filter_subset _ _) (filter_subset _ _))]

omit [Fintype E] in
private theorem degreeOn_card_le (G : Multigraph V E) (X : Finset E) (v : V) :
    G.degreeOn X v ≤ X.card := by
  unfold Multigraph.degreeOn
  exact card_le_card (filter_subset _ _)

namespace CappedPools

variable {G : Multigraph V E} {Q : Multigraph (Fin 4) E} {B : ℕ}
    (P : CappedPools G Q matchingForest B)

def matchingCross : Finset E := matchingOffPairs.biUnion P.kept

theorem matchingCross_subset_cut : P.matchingCross ⊆ Q.cutOn univ {0, 1} := by
  rw [← matchingOffPools_eq_cut]
  intro e he
  obtain ⟨p, hp, he⟩ := mem_biUnion.mp he
  exact mem_biUnion.mpr ⟨p, hp, P.subset p he⟩

theorem matchingCross_card : P.matchingCross.card =
    ∑ p ∈ matchingOffPairs, (P.kept p).card := by
  apply card_biUnion
  intro p _ q _ hpq
  exact P.kept_disjoint hpq

theorem matchingCross_card_le : P.matchingCross.card ≤ 4 * (B + 1) := by
  rw [P.matchingCross_card]
  have h := sum_le_sum (s := matchingOffPairs)
    (f := fun p => (P.kept p).card) (g := fun _ => B + 1)
    (fun p hp => P.cap_bound p (mem_sdiff.mp hp).2)
  simpa [matchingOffPairs_card] using h

theorem matchingCross_parity : P.matchingCross.card % 2 =
    (Q.cutOn univ {0, 1}).card % 2 := by
  rw [P.matchingCross_card, ← matchingOffPools_eq_cut,
    card_biUnion (fun p _ q _ hpq => pairPool_disjoint Q hpq)]
  rw [sum_nat_mod _ 2 (fun p => (P.kept p).card),
    sum_nat_mod _ 2 (fun p => (pairPool Q p).card)]
  congr 1
  exact sum_congr rfl (fun p _ => P.parity p)

theorem matchingCross_full_or_large :
    P.matchingCross = Q.cutOn univ {0, 1} ∨ B ≤ P.matchingCross.card := by
  by_cases hall : ∀ p ∈ matchingOffPairs, P.kept p = pairPool Q p
  · left
    rw [← matchingOffPools_eq_cut]
    apply biUnion_congr rfl
    exact hall
  · right
    push_neg at hall
    obtain ⟨p, hp, hchanged⟩ := hall
    have hlarge := (P.full_or_large p).resolve_left hchanged
    exact hlarge.trans (card_le_card (subset_biUnion_of_mem P.kept hp))

theorem matchingCross_half_degree {D : ℕ}
    (hdegree : ∀ v, G.degree v ≤ D) (hB : 2 * D ≤ B)
    (hcut : ∀ v, G.degreeOn (Q.cutOn univ {0, 1}) v ≤
      (Q.cutOn univ {0, 1}).card / 2) (v : V) :
    G.degreeOn P.matchingCross v ≤ P.matchingCross.card / 2 := by
  rcases P.matchingCross_full_or_large with hfull | hlarge
  · rw [hfull]
    exact hcut v
  · have hd := (degreeOn_le_degree G P.matchingCross v).trans (hdegree v)
    omega

theorem matchingCross_disjoint_left : Disjoint P.matchingCross (pairPool Q matchingLeftPair) := by
  apply disjoint_left.mpr
  intro e he hl
  obtain ⟨p, hp, hep⟩ := mem_biUnion.mp he
  have hpl := ((mem_pairPool Q p e).mp (P.subset p hep)).symm.trans
    ((mem_pairPool Q matchingLeftPair e).mp hl)
  exact matchingOffPairs_ne_left (hpl ▸ hp)

theorem matchingCross_disjoint_right : Disjoint P.matchingCross (pairPool Q matchingRightPair) := by
  apply disjoint_left.mpr
  intro e he hr
  obtain ⟨p, hp, hep⟩ := mem_biUnion.mp he
  have hpr := ((mem_pairPool Q p e).mp (P.subset p hep)).symm.trans
    ((mem_pairPool Q matchingRightPair e).mp hr)
  exact matchingOffPairs_ne_right (hpr ▸ hp)

theorem matching_retained_eq : P.retained =
    P.matchingCross ∪ pairPool Q matchingLeftPair ∪ pairPool Q matchingRightPair := by
  have hL := P.fixed matchingLeftPair (by simp [matchingForest])
  have hR := P.fixed matchingRightPair (by simp [matchingForest])
  ext e
  constructor
  · intro he
    obtain ⟨p, _, hep⟩ := mem_biUnion.mp he
    by_cases hp : p ∈ matchingForest
    · simp only [matchingForest, mem_insert, mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact mem_union_left _ (mem_union_right _ (hL ▸ hep))
      · exact mem_union_right _ (hR ▸ hep)
    · exact mem_union_left _ (mem_union_left _
        (mem_biUnion.mpr ⟨p, mem_sdiff.mpr ⟨mem_univ _, hp⟩, hep⟩))
  · intro he
    rcases mem_union.mp he with he | he
    · rcases mem_union.mp he with he | he
      · obtain ⟨p, _, hep⟩ := mem_biUnion.mp he
        exact mem_biUnion.mpr ⟨p, mem_univ _, hep⟩
      · exact mem_biUnion.mpr ⟨matchingLeftPair, mem_univ _, hL.symm ▸ he⟩
    · exact mem_biUnion.mpr ⟨matchingRightPair, mem_univ _, hR.symm ▸ he⟩

theorem matching_retained_degree (i : Fin 4) :
    Q.degreeOn P.retained i = Q.degreeOn P.matchingCross i +
      if i.val < 2 then (pairPool Q matchingLeftPair).card
      else (pairPool Q matchingRightPair).card := by
  rw [P.matching_retained_eq,
    degreeOn_union_disjoint _ (disjoint_union_left.mpr
      ⟨P.matchingCross_disjoint_right, pairPool_disjoint Q matching_left_ne_right⟩),
    degreeOn_union_disjoint _ P.matchingCross_disjoint_left,
    degreeOn_pairPool, degreeOn_pairPool]
  fin_cases i <;> simp [matchingLeftPair, matchingRightPair]

end CappedPools

/-- The preserved singleton-label cuts determine a feasible exact number
of distinguished-pool singletons, including its necessary parity. -/
theorem matching_singleton_count_bounds {n a b x h D : ℕ}
    (ha : a ≤ x) (hb : b ≤ x) (hroom : x + 4 * D ≤ h)
    (hlower0 : h ≤ a + n) (hlower1 : h ≤ b + n)
    (hpar0 : (a + n) % 2 = h % 2) (hpar1 : (b + n) % 2 = h % 2) :
    let q := h - min a b
    q + min a b = h ∧ q ≤ n ∧ n % 2 = q % 2 ∧ 4 * D ≤ q := by
  dsimp
  by_cases hab : a ≤ b
  · rw [min_eq_left hab]
    omega
  · rw [min_eq_right (by omega)]
    omega

/-- Actual copies and the complete surplus decomposition prepared for the
canonical minority-pairing assembly. -/
structure MatchingPreparation (G : Multigraph V E) (Q : Multigraph (Fin 4) E)
    (h D : ℕ) where
  cross : Finset E
  left : Finset E
  right : Finset E
  cross_subset : cross ⊆ Q.cutOn univ {0, 1}
  left_subset : left ⊆ pairPool Q matchingLeftPair
  right_subset : right ⊆ pairPool Q matchingRightPair
  cross_even : cross.card % 2 = 0
  cross_half : ∀ v, G.degreeOn cross v ≤ cross.card / 2
  cross_room : cross.card + 4 * D ≤ h
  left_count : left.card + min (Q.degreeOn cross 0) (Q.degreeOn cross 1) = h
  right_count : right.card + min (Q.degreeOn cross 2) (Q.degreeOn cross 3) = h
  surplus : Decomposition G Q.edgeLabelPair (univ \ (cross ∪ left ∪ right)) 0

private theorem matching_surplus_cover (X L R S0 S1 : Finset E)
    (hS0 : S0 ⊆ L) (hS1 : S1 ⊆ R)
    (hXL : Disjoint X L) (hXR : Disjoint X R) (hLR : Disjoint L R) :
    ((L \ S0) ∪ (R \ S1)) ∪ (univ \ (X ∪ L ∪ R)) =
      univ \ (X ∪ S0 ∪ S1) := by
  ext e
  have hsl : e ∈ S0 → e ∈ L := fun he => hS0 he
  have hsr : e ∈ S1 → e ∈ R := fun he => hS1 he
  have hxl : ¬ (e ∈ X ∧ e ∈ L) := fun he => disjoint_left.mp hXL he.1 he.2
  have hxr : ¬ (e ∈ X ∧ e ∈ R) := fun he => disjoint_left.mp hXR he.1 he.2
  have hlr : ¬ (e ∈ L ∧ e ∈ R) := fun he => disjoint_left.mp hLR he.1 he.2
  simp only [mem_union, mem_sdiff, mem_univ, true_and]
  tauto

/-- Cap the actual crossing pools and split the unchanged distinguished
pools into exactly the required singleton and parallel-pair copies. -/
theorem exists_matchingPreparation [Fintype V] (G : Multigraph V E)
    (label : V → Fin 4)
    (hjoin : ∀ e, label (G.firstEnd e) ≠ label (G.secondEnd e))
    {h D r0 : ℕ} (hD : 0 < D) (hsmall : 1000 * D ≤ h)
    (hsupply : 999 * h ≤ 1000 * r0) (hdegree : ∀ v, G.degree v ≤ D)
    (hlower : ∀ i, h ≤ (G.labelQuotient label hjoin).degree i)
    (hpar : ∀ i, (G.labelQuotient label hjoin).degree i % 2 = h % 2)
    (hleft : r0 ≤ (pairPool (G.labelQuotient label hjoin) matchingLeftPair).card)
    (hright : r0 ≤ (pairPool (G.labelQuotient label hjoin) matchingRightPair).card)
    (hcut_even : ((G.labelQuotient label hjoin).cutOn univ {0, 1}).card % 2 = 0)
    (hcut_half : ∀ v, G.degreeOn ((G.labelQuotient label hjoin).cutOn univ {0, 1}) v ≤
      ((G.labelQuotient label hjoin).cutOn univ {0, 1}).card / 2) :
    Nonempty (MatchingPreparation G (G.labelQuotient label hjoin) h D) := by
  let Q := G.labelQuotient label hjoin
  let B := 2 * D + (h - r0)
  obtain ⟨hB, hreserve, hroom⟩ := matching_parameter_bounds hD hsmall hsupply
  change 2 * D ≤ B at hB
  change h ≤ r0 + B at hreserve
  change 8 * (B + 1) + 4 * D ≤ h at hroom
  obtain ⟨P⟩ := exists_cappedPools G label hjoin matchingForest B
    (fun v => (hdegree v).trans (by omega))
  let X := P.matchingCross
  let L := pairPool Q matchingLeftPair
  let R := pairPool Q matchingRightPair
  have hsupplyF : ∀ p ∈ matchingForest, r0 ≤ (pairPool Q p).card := by
    intro p hp
    simp only [matchingForest, mem_insert, mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact hleft
    · exact hright
  have hl (i : Fin 4) : h ≤ Q.degreeOn X i +
      if i.val < 2 then L.card else R.card := by
    rw [← P.matching_retained_degree]
    exact P.degree_lower matchingForest_shape hsupplyF hlower hreserve i
  have hp (i : Fin 4) : (Q.degreeOn X i +
      if i.val < 2 then L.card else R.card) % 2 = h % 2 := by
    rw [← P.matching_retained_degree]
    exact (P.degree_parity i).trans (hpar i)
  have hxcard : X.card ≤ 4 * (B + 1) := P.matchingCross_card_le
  have hxroom : X.card + 4 * D ≤ h := by omega
  have hxd (i : Fin 4) : Q.degreeOn X i ≤ X.card := degreeOn_card_le Q X i
  let q0 := h - min (Q.degreeOn X 0) (Q.degreeOn X 1)
  let q1 := h - min (Q.degreeOn X 2) (Q.degreeOn X 3)
  have hq0 := matching_singleton_count_bounds (hxd 0) (hxd 1) hxroom
    (show h ≤ Q.degreeOn X 0 + L.card by simpa using hl 0)
    (show h ≤ Q.degreeOn X 1 + L.card by simpa using hl 1)
    (show (Q.degreeOn X 0 + L.card) % 2 = h % 2 by simpa using hp 0)
    (show (Q.degreeOn X 1 + L.card) % 2 = h % 2 by simpa using hp 1)
  have hq1 := matching_singleton_count_bounds (hxd 2) (hxd 3) hxroom
    (show h ≤ Q.degreeOn X 2 + R.card by simpa using hl 2)
    (show h ≤ Q.degreeOn X 3 + R.card by simpa using hl 3)
    (show (Q.degreeOn X 2 + R.card) % 2 = h % 2 by simpa using hp 2)
    (show (Q.degreeOn X 3 + R.card) % 2 = h % 2 by simpa using hp 3)
  change q0 + _ = h ∧ q0 ≤ L.card ∧ L.card % 2 = q0 % 2 ∧ 4 * D ≤ q0 at hq0
  change q1 + _ = h ∧ q1 ≤ R.card ∧ R.card % 2 = q1 % 2 ∧ 4 * D ≤ q1 at hq1
  obtain ⟨S0, hS0, hcard0, ⟨T0⟩⟩ := exists_singletons_and_pairs_on G L
    (pairPool_bipartite G label hjoin matchingLeftPair) q0 hq0.2.1 hq0.2.2.1
    (fun v => (restrictEdges_degree_le_original G L v).trans ((hdegree v).trans (by omega)))
  obtain ⟨S1, hS1, hcard1, ⟨T1⟩⟩ := exists_singletons_and_pairs_on G R
    (pairPool_bipartite G label hjoin matchingRightPair) q1 hq1.2.1 hq1.2.2.1
    (fun v => (restrictEdges_degree_le_original G R v).trans ((hdegree v).trans (by omega)))
  let A0 : Decomposition G Q.edgeLabelPair (L \ S0) 0 :=
    Decomposition.ofPairPartition T0 (by
      intro M hM e he f hf
      exact ((mem_pairPool Q matchingLeftPair e).mp
        (mem_sdiff.mp (T0.part_subset hM he)).1).trans
        ((mem_pairPool Q matchingLeftPair f).mp
          (mem_sdiff.mp (T0.part_subset hM hf)).1).symm)
  let A1 : Decomposition G Q.edgeLabelPair (R \ S1) 0 :=
    Decomposition.ofPairPartition T1 (by
      intro M hM e he f hf
      exact ((mem_pairPool Q matchingRightPair e).mp
        (mem_sdiff.mp (T1.part_subset hM he)).1).trans
        ((mem_pairPool Q matchingRightPair f).mp
          (mem_sdiff.mp (T1.part_subset hM hf)).1).symm)
  have hLR : Disjoint L R := pairPool_disjoint Q matching_left_ne_right
  have hXR : Disjoint X R := P.matchingCross_disjoint_right
  have hXL : Disjoint X L := P.matchingCross_disjoint_left
  have hretained : P.retained = X ∪ L ∪ R := P.matching_retained_eq
  have hremain : Disjoint ((L \ S0) ∪ (R \ S1)) (univ \ P.retained) := by
    apply disjoint_left.mpr
    intro e he hr
    apply (mem_sdiff.mp hr).2
    rw [hretained]
    rcases mem_union.mp he with he | he
    · exact mem_union_left _ (mem_union_right _ (mem_sdiff.mp he).1)
    · exact mem_union_right _ (mem_sdiff.mp he).1
  let A := (A0.union A1 (hLR.mono sdiff_subset sdiff_subset)).union
    P.discardedDecomposition hremain
  have hcover : ((L \ S0) ∪ (R \ S1)) ∪ (univ \ P.retained) =
      univ \ (X ∪ S0 ∪ S1) := by
    rw [hretained]
    exact matching_surplus_cover X L R S0 S1 hS0 hS1 hXL hXR hLR
  refine ⟨{
    cross := X
    left := S0
    right := S1
    cross_subset := P.matchingCross_subset_cut
    left_subset := hS0
    right_subset := hS1
    cross_even := P.matchingCross_parity.trans hcut_even
    cross_half := P.matchingCross_half_degree hdegree hB hcut_half
    cross_room := hxroom
    left_count := by rw [hcard0]; exact hq0.1
    right_count := by rw [hcard1]; exact hq1.1
    surplus := A.cast hcover rfl }⟩

private theorem matchingSide_ne_iff_cut : ∀ a b : Fin 4,
    matchingSide a ≠ matchingSide b ↔
      (a ∈ ({0, 1} : Finset (Fin 4))) ≠ (b ∈ ({0, 1} : Finset (Fin 4))) := by
  decide

/-- Complete the prepared actual copies by contracting the two minority
classes, pairing the crossing copies, and inserting the exact singletons. -/
theorem MatchingPreparation.toDecomposition [Fintype V] (G : Multigraph V E)
    (label : V → Fin 4)
    (hjoin : ∀ e, label (G.firstEnd e) ≠ label (G.secondEnd e))
    {h D : ℕ} (T : MatchingPreparation G (G.labelQuotient label hjoin) h D)
    (hdegree : ∀ v, G.degree v ≤ D) :
    Nonempty (Decomposition G (G.labelQuotient label hjoin).edgeLabelPair univ h) := by
  let Q := G.labelQuotient label hjoin
  let H := G.restrictEdges T.cross
  let k := T.cross.card / 2
  let side := matchingSide ∘ label
  let refinement := matchingRefinement ∘ label
  have hcross (e : T.cross) :
      matchingSide (label (G.firstEnd e.val)) ≠ matchingSide (label (G.secondEnd e.val)) := by
    apply (matchingSide_ne_iff_cut _ _).mpr
    exact ((labelQuotient_mem_cutOn_iff G label hjoin univ {0, 1} e.val).mp
      (T.cross_subset e.property)).2
  have hcard : Fintype.card T.cross = 2 * k := by
    rw [Fintype.card_coe]
    have heven := T.cross_even
    dsimp [k]
    omega
  have hhalf (v : V) : H.degree v ≤ k := by
    rw [restrictEdges_degree_eq_degreeOn]
    exact T.cross_half v
  obtain ⟨P⟩ := exists_minorityPairing H side refinement hcross k hcard hhalf
  have hprojection (e : T.cross) : Q.edgeLabelPair e.val =
      matchingCrossPair (sideLabel H side refinement false e)
        (sideLabel H side refinement true e) :=
    matching_cross_projection H label (fun e => hjoin e.val) hcross e
  have hcount0 : T.left.card + (univ.filter (P.Mixed false)).card = h := by
    rw [P.mixed_card]
    change T.left.card + min
      (sideEdges (G.restrictEdges T.cross) (matchingSide ∘ label)
        (matchingRefinement ∘ label) false false).card
      (sideEdges (G.restrictEdges T.cross) (matchingSide ∘ label)
        (matchingRefinement ∘ label) false true).card = h
    rw [matching_sideEdges_card G label hjoin T.cross hcross false false,
      matching_sideEdges_card G label hjoin T.cross hcross false true]
    exact T.left_count
  have hcount1 : T.right.card + (univ.filter (P.Mixed true)).card = h := by
    rw [P.mixed_card]
    change T.right.card + min
      (sideEdges (G.restrictEdges T.cross) (matchingSide ∘ label)
        (matchingRefinement ∘ label) true false).card
      (sideEdges (G.restrictEdges T.cross) (matchingSide ∘ label)
        (matchingRefinement ∘ label) true true).card = h
    rw [matching_sideEdges_card G label hjoin T.cross hcross true false,
      matching_sideEdges_card G label hjoin T.cross hcross true true]
    exact T.right_count
  have hsize : 2 * k + 4 * D ≤ h := by
    have hc : T.cross.card = 2 * k := by simpa using hcard
    rw [← hc]
    exact T.cross_room
  obtain ⟨R⟩ := exists_matching_assembly G H Subtype.val Subtype.val_injective
    (fun _ => rfl) label Q.edgeLabelPair
    (fun e v hv => (Q.mem_edgeLabelPair e (label v)).mpr
      (G.label_incident_of_incident label hjoin hv))
    side refinement P hprojection T.left T.right
    (fun e he => (mem_pairPool Q matchingLeftPair e).mp (T.left_subset he))
    (fun e he => (mem_pairPool Q matchingRightPair e).mp (T.right_subset he))
    hdegree hcount0 hcount1 hsize
  have himage : (univ : Finset T.cross).image Subtype.val = T.cross := by
    ext e
    simp only [mem_image, mem_univ, true_and]
    exact ⟨fun ⟨f, hf⟩ => hf ▸ f.property, fun he => ⟨⟨e, he⟩, rfl⟩⟩
  let R' := R.cast (by rw [himage]) rfl
  have hdisjoint : Disjoint (T.cross ∪ T.left ∪ T.right)
      (univ \ (T.cross ∪ T.left ∪ T.right)) :=
    disjoint_left.mpr (fun _ he hf => (mem_sdiff.mp hf).2 he)
  have hcover : (T.cross ∪ T.left ∪ T.right) ∪
      (univ \ (T.cross ∪ T.left ∪ T.right)) = univ := by
    ext e
    simp
  exact ⟨(R'.union T.surplus hdisjoint).cast hcover (by omega)⟩

/-- The complete canonical matching case, with no assumed pairing,
singleton selection, cap choice, or decomposition. -/
theorem exists_matching_decomposition [Fintype V] (G : Multigraph V E)
    (label : V → Fin 4)
    (hjoin : ∀ e, label (G.firstEnd e) ≠ label (G.secondEnd e))
    {h D r0 : ℕ} (hD : 0 < D) (hsmall : 1000 * D ≤ h)
    (hsupply : 999 * h ≤ 1000 * r0) (hdegree : ∀ v, G.degree v ≤ D)
    (hlower : ∀ i, h ≤ (G.labelQuotient label hjoin).degree i)
    (hpar : ∀ i, (G.labelQuotient label hjoin).degree i % 2 = h % 2)
    (hleft : r0 ≤ (pairPool (G.labelQuotient label hjoin) matchingLeftPair).card)
    (hright : r0 ≤ (pairPool (G.labelQuotient label hjoin) matchingRightPair).card)
    (hcut_even : ((G.labelQuotient label hjoin).cutOn univ {0, 1}).card % 2 = 0)
    (hcut_half : ∀ v, G.degreeOn ((G.labelQuotient label hjoin).cutOn univ {0, 1}) v ≤
      ((G.labelQuotient label hjoin).cutOn univ {0, 1}).card / 2) :
    Nonempty (Decomposition G (G.labelQuotient label hjoin).edgeLabelPair univ h) := by
  obtain ⟨T⟩ := exists_matchingPreparation G label hjoin hD hsmall hsupply hdegree
    hlower hpar hleft hright hcut_even hcut_half
  exact T.toDecomposition G label hjoin hdegree

end Overfull.FourOdd
