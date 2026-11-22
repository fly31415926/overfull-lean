import Overfull.FourOdd.MatchingShapes
import Overfull.FourOdd.Allocation

/-!
# Exact assembly in the canonical matching case

The minority pairing supplies the two-copy pieces and their exact savings.
Distinct singleton copies extend same-row and same-column pieces to stars;
the remaining singletons pair into perfect matchings.  Every copy is used
once and the number of primary pieces is exactly the requested degree.
-/

noncomputable section

namespace Overfull.FourOdd

open Finset Classical Compression CircuitPatterns
open scoped BigOperators

variable {V E F : Type*} [Fintype E] [Fintype F]

omit [Fintype E] [Fintype F] in
private theorem pair_matching_of_label_disjoint (G : Multigraph V E)
    (vertexLabel : V → Fin 4) (label : E → LabelPair)
    (hincident : ∀ e v, v ∈ G.edge e → vertexLabel v ∈ (label e).val)
    {e f : E} (hdisj : Disjoint (label e).val (label f).val) :
    G.IsMatching {e, f} := by
  intro x hx y hy v hxv hyv
  simp only [mem_insert, mem_singleton] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · rfl
  · exact (disjoint_left.mp hdisj (hincident _ _ hxv) (hincident _ _ hyv)).elim
  · exact (disjoint_left.mp hdisj (hincident _ _ hyv) (hincident _ _ hxv)).elim
  · rfl

omit [Fintype E] [Fintype F] in
/-- A finite set of singleton copies of one distinguished pair matches
bijectively with an equally sized set of the other distinguished pair. -/
private theorem exists_left_right_decomposition (G : Multigraph V E)
    (vertexLabel : V → Fin 4) (label : E → LabelPair)
    (hincident : ∀ e v, v ∈ G.edge e → vertexLabel v ∈ (label e).val)
    (L R : Finset E) (hL : ∀ e ∈ L, label e = matchingLeftPair)
    (hR : ∀ e ∈ R, label e = matchingRightPair) (hcard : L.card = R.card) :
    Nonempty (Decomposition G label (L ∪ R) L.card) := by
  let f : L ≃ R := Fintype.equivOfCardEq (by simpa using hcard)
  let M : L → Finset E := fun e => {e.val, (f e).val}
  have hLR : Disjoint L R := by
    apply disjoint_left.mpr
    intro e he hf
    exact matching_left_ne_right ((hL e he).symm.trans (hR e hf))
  have hmatch (e : L) : G.IsMatching (M e) := by
    apply pair_matching_of_label_disjoint G vertexLabel label hincident
    rw [hL e.val e.property, hR (f e).val (f e).property]
    decide
  have hshape (e : L) : IsPrimary label (M e) :=
    primary_left_right (hL e.val e.property) (hR (f e).val (f e).property)
  have hdisj : Pairwise (fun e e' : L => Disjoint (M e) (M e')) := by
    intro e e' hne
    apply disjoint_left.mpr
    intro x hx hy
    simp only [M, mem_insert, mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with h | h
    · exact hne (Subtype.ext h)
    · exact disjoint_left.mp hLR e.property (h ▸ (f e').property)
    · exact disjoint_left.mp hLR (h ▸ e'.property) (f e).property
    · exact hne (f.injective (Subtype.ext h))
  let P := Decomposition.ofPrimaryFamily G label M hmatch hshape hdisj
  have hcover : univ.biUnion M = L ∪ R := by
    ext e
    simp only [mem_biUnion, mem_univ, true_and, M, mem_insert, mem_singleton, mem_union]
    constructor
    · rintro ⟨x, rfl | h⟩
      · exact Or.inl x.property
      · exact Or.inr (h ▸ (f x).property)
    · rintro (he | he)
      · exact ⟨⟨e, he⟩, Or.inl rfl⟩
      · obtain ⟨x, hx⟩ := f.surjective ⟨e, he⟩
        exact ⟨x, Or.inr (congrArg Subtype.val hx).symm⟩
  exact ⟨P.cast hcover (by simp)⟩

/-- Augment every shared-row or shared-column pair by a distinct compatible
singleton. Opposite pairs are already primary, and parallel pairs remain
surplus circuits. The used singleton counts are exact. -/
theorem exists_augmented_cross_decomposition
    (G : Multigraph V E) (H : Multigraph V F) (copy : F → E)
    (hcopy : Function.Injective copy) (hedge : ∀ e, G.edge (copy e) = H.edge e)
    (label : E → LabelPair) (side refinement : V → Bool) {k D : ℕ}
    (P : MinorityPairing H side refinement k)
    (hlabel : ∀ e, label (copy e) = matchingCrossPair
      (sideLabel H side refinement false e) (sideLabel H side refinement true e))
    (S0 S1 : Finset E)
    (hS0 : ∀ e ∈ S0, label e = matchingLeftPair)
    (hS1 : ∀ e ∈ S1, label e = matchingRightPair)
    (hdegree : ∀ v, G.degree v ≤ D)
    (hsize0 : P.sameRowPairs.card + 4 * D ≤ S0.card)
    (hsize1 : P.sameColumnPairs.card + 4 * D ≤ S1.card) :
    ∃ U0 U1 : Finset E, U0 ⊆ S0 ∧ U1 ⊆ S1 ∧
      U0.card = P.sameRowPairs.card ∧ U1.card = P.sameColumnPairs.card ∧
      Nonempty (Decomposition G label ((univ.image copy) ∪ U0 ∪ U1)
        (P.oppositePairs.card + P.sameRowPairs.card + P.sameColumnPairs.card)) := by
  let X : Finset E := univ.image copy
  let M : Fin k → Finset E := fun i => (P.pair i).image copy
  have hMX (i : Fin k) : M i ⊆ X := Finset.image_subset_image (subset_univ _)
  have hMcard (i : Fin k) : (M i).card = 2 := by
    rw [Finset.card_image_of_injective _ hcopy]
    exact P.card_pair i
  have hMmatch (i : Fin k) : G.IsMatching (M i) := by
    intro x hx y hy v hxv hyv
    obtain ⟨e, he, rfl⟩ := mem_image.mp hx
    obtain ⟨f, hf, rfl⟩ := mem_image.mp hy
    rw [hedge] at hxv hyv
    exact congrArg copy (P.pair_isMatching i e he f hf v hxv hyv)
  have hMdisj : Pairwise (fun i j => Disjoint (M i) (M j)) := by
    intro i j hij
    apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨e, he, hxe⟩ := mem_image.mp hx
    obtain ⟨f, hf, hxf⟩ := mem_image.mp hy
    have hef := hcopy (hxe.trans hxf.symm)
    subst f
    exact disjoint_left.mp (P.pair_disjoint hij) he hf
  have hMcover : univ.biUnion M = X := by
    change (univ.biUnion (fun i => (P.pair i).image copy)) = univ.image copy
    rw [← Finset.biUnion_image, P.pair_cover]
  have hXS0 : Disjoint X S0 := by
    apply disjoint_left.mpr
    intro x hx hs
    obtain ⟨e, _, rfl⟩ := mem_image.mp hx
    exact matching_cross_ne_left _ _ ((hlabel e).symm.trans (hS0 (copy e) hs))
  have hXS1 : Disjoint X S1 := by
    apply disjoint_left.mpr
    intro x hx hs
    obtain ⟨e, _, rfl⟩ := mem_image.mp hx
    exact matching_cross_ne_right _ _ ((hlabel e).symm.trans (hS1 (copy e) hs))
  have hS01 : Disjoint S0 S1 := by
    apply disjoint_left.mpr
    intro e he hf
    exact matching_left_ne_right ((hS0 e he).symm.trans (hS1 e hf))
  let R := P.sameRowPairs
  let C := P.sameColumnPairs
  have hR (i : Fin k) : i ∈ R ↔ ¬ P.Mixed false i ∧ P.Mixed true i := by
    simp [R, MinorityPairing.sameRowPairs]
  have hC (i : Fin k) : i ∈ C ↔ P.Mixed false i ∧ ¬ P.Mixed true i := by
    simp [C, MinorityPairing.sameColumnPairs]
  obtain ⟨f0, hf0⟩ := exists_matching_singleton_injection G (fun i : R => M i.val) S0 D
    (fun i => hMmatch i.val) (fun i => (hMcard i.val).le) hdegree (by simpa [R] using hsize0)
  obtain ⟨f1, hf1⟩ := exists_matching_singleton_injection G (fun i : C => M i.val) S1 D
    (fun i => hMmatch i.val) (fun i => (hMcard i.val).le) hdegree (by simpa [C] using hsize1)
  let A0 : Fin k → Finset E := fun i => if hi : i ∈ R then {(f0 ⟨i, hi⟩).val} else ∅
  let A1 : Fin k → Finset E := fun i => if hi : i ∈ C then {(f1 ⟨i, hi⟩).val} else ∅
  have hA0sub (i : Fin k) : A0 i ⊆ S0 := by
    dsimp [A0]
    split_ifs with hi
    · exact singleton_subset_iff.mpr (f0 ⟨i, hi⟩).property
    · exact empty_subset _
  have hA1sub (i : Fin k) : A1 i ⊆ S1 := by
    dsimp [A1]
    split_ifs with hi
    · exact singleton_subset_iff.mpr (f1 ⟨i, hi⟩).property
    · exact empty_subset _
  have hA0disj : Pairwise (fun i j => Disjoint (A0 i) (A0 j)) := by
    intro i j hij
    dsimp [A0]
    split_ifs with hi hj <;> try simp only [disjoint_empty_left, disjoint_empty_right]
    apply disjoint_singleton.mpr
    intro h
    exact hij (congrArg Subtype.val (f0.injective (Subtype.ext h)))
  have hA1disj : Pairwise (fun i j => Disjoint (A1 i) (A1 j)) := by
    intro i j hij
    dsimp [A1]
    split_ifs with hi hj <;> try simp only [disjoint_empty_left, disjoint_empty_right]
    apply disjoint_singleton.mpr
    intro h
    exact hij (congrArg Subtype.val (f1.injective (Subtype.ext h)))
  let U0 := univ.biUnion A0
  let U1 := univ.biUnion A1
  have hU0sub : U0 ⊆ S0 := by
    intro e he
    obtain ⟨i, _, hi⟩ := mem_biUnion.mp he
    exact hA0sub i hi
  have hU1sub : U1 ⊆ S1 := by
    intro e he
    obtain ⟨i, _, hi⟩ := mem_biUnion.mp he
    exact hA1sub i hi
  have hU0card : U0.card = R.card := by
    have hA0card (i : Fin k) : (A0 i).card = if i ∈ R then 1 else 0 := by
      by_cases hi : i ∈ R <;> simp [A0, hi]
    dsimp [U0]
    rw [card_biUnion (fun i _ j _ hij => hA0disj hij)]
    simp_rw [hA0card]
    simp
  have hU1card : U1.card = C.card := by
    have hA1card (i : Fin k) : (A1 i).card = if i ∈ C then 1 else 0 := by
      by_cases hi : i ∈ C <;> simp [A1, hi]
    dsimp [U1]
    rw [card_biUnion (fun i _ j _ hij => hA1disj hij)]
    simp_rw [hA1card]
    simp
  let N : Fin k → Finset E := fun i => M i ∪ A0 i ∪ A1 i
  let count : Fin k → ℕ := fun i => if P.Mixed false i ∨ P.Mixed true i then 1 else 0
  have hNdisj : Pairwise (fun i j => Disjoint (N i) (N j)) := by
    intro i j hij
    have hbb := hMdisj hij
    have hb0 := hXS0.mono (hMX i) (hA0sub j)
    have hb1 := hXS1.mono (hMX i) (hA1sub j)
    have h0b := (hXS0.mono (hMX j) (hA0sub i)).symm
    have h1b := (hXS1.mono (hMX j) (hA1sub i)).symm
    have h00 := hA0disj hij
    have h11 := hA1disj hij
    have h01 := hS01.mono (hA0sub i) (hA1sub j)
    have h10 := (hS01.mono (hA0sub j) (hA1sub i)).symm
    simp only [N, disjoint_union_left, disjoint_union_right]
    tauto
  have hpart (i : Fin k) : Nonempty (Decomposition G label (N i) (count i)) := by
    by_cases hr : P.Mixed false i <;> by_cases hc : P.Mixed true i
    · have hir : i ∉ R := by simp [hR, hr]
      have hic : i ∉ C := by simp [hC, hc]
      have hN : N i = M i := by simp [N, A0, A1, hir, hic]
      rw [hN]
      have hn : count i = 1 := by simp [count, hr]
      rw [hn]
      exact ⟨Decomposition.singlePrimary G label (M i) (hMmatch i)
        (P.opposite_primary copy label hlabel i hr hc)⟩
    · have hir : i ∉ R := by simp [hR, hr]
      have hic : i ∈ C := (hC i).mpr ⟨hr, hc⟩
      have hN : N i = M i ∪ {(f1 ⟨i, hic⟩).val} := by simp [N, A0, A1, hir, hic]
      rw [hN]
      have hn : count i = 1 := by simp [count, hr]
      rw [hn]
      exact ⟨Decomposition.singlePrimary G label _ (hf1 ⟨i, hic⟩)
        (P.sameColumn_primary copy label hlabel i hr hc
          (hS1 _ (f1 ⟨i, hic⟩).property))⟩
    · have hir : i ∈ R := (hR i).mpr ⟨hr, hc⟩
      have hic : i ∉ C := by simp [hC, hr]
      have hN : N i = M i ∪ {(f0 ⟨i, hir⟩).val} := by simp [N, A0, A1, hir, hic]
      rw [hN]
      have hn : count i = 1 := by simp [count, hc]
      rw [hn]
      exact ⟨Decomposition.singlePrimary G label _ (hf0 ⟨i, hir⟩)
        (P.sameRow_primary copy label hlabel i hr hc
          (hS0 _ (f0 ⟨i, hir⟩).property))⟩
    · have hir : i ∉ R := by simp [hR, hc]
      have hic : i ∉ C := by simp [hC, hr]
      have hN : N i = M i := by simp [N, A0, A1, hir, hic]
      rw [hN]
      have hn : count i = 0 := by simp [count, hr, hc]
      rw [hn]
      exact ⟨Decomposition.singlePair G label (M i) (hMmatch i)
        (P.parallel_pair copy label hlabel hcopy i hr hc)⟩
  have hNcover : univ.biUnion N = X ∪ U0 ∪ U1 := by
    calc
      _ = (univ.biUnion M) ∪ (univ.biUnion A0) ∪ (univ.biUnion A1) := by
        ext e
        simp only [N, mem_biUnion, mem_univ, true_and, mem_union, exists_or]
      _ = _ := by rw [hMcover]
  have hcount : (∑ i : Fin k, count i) =
      P.oppositePairs.card + R.card + C.card := by
    have h := filter_card_add_filter_neg_card_eq_card
      (s := (univ : Finset (Fin k))) (fun i => P.Mixed false i ∨ P.Mixed true i)
    have hn : univ.filter (fun i => ¬ (P.Mixed false i ∨ P.Mixed true i)) = P.parallelPairs := by
      ext i
      simp [MinorityPairing.parallelPairs, not_or]
    rw [hn] at h
    simp only [card_univ, Fintype.card_fin] at h
    have hall := P.pair_shapes_card
    dsimp [count]
    rw [sum_boole]
    dsimp [R, C]
    omega
  obtain ⟨Q⟩ := Decomposition.exists_biUnion univ N count
    (fun i => Classical.choice (hpart i)) (fun i _ j _ hij => hNdisj hij)
  refine ⟨U0, U1, hU0sub, hU1sub, hU0card, hU1card, ?_⟩
  exact ⟨Q.cast hNcover hcount⟩

/-- Complete the canonical matching case after the two distinguished pools
have supplied their exact singleton quotas.  The output uses every retained
copy exactly once and has precisely `h` primary matching pieces. -/
theorem exists_matching_assembly
    (G : Multigraph V E) (H : Multigraph V F) (copy : F → E)
    (hcopy : Function.Injective copy) (hedge : ∀ e, G.edge (copy e) = H.edge e)
    (vertexLabel : V → Fin 4) (label : E → LabelPair)
    (hincident : ∀ e v, v ∈ G.edge e → vertexLabel v ∈ (label e).val)
    (side refinement : V → Bool) {k D h : ℕ}
    (P : MinorityPairing H side refinement k)
    (hlabel : ∀ e, label (copy e) = matchingCrossPair
      (sideLabel H side refinement false e) (sideLabel H side refinement true e))
    (S0 S1 : Finset E)
    (hS0 : ∀ e ∈ S0, label e = matchingLeftPair)
    (hS1 : ∀ e ∈ S1, label e = matchingRightPair)
    (hdegree : ∀ v, G.degree v ≤ D)
    (hcount0 : S0.card + (univ.filter (P.Mixed false)).card = h)
    (hcount1 : S1.card + (univ.filter (P.Mixed true)).card = h)
    (hsize : 2 * k + 4 * D ≤ h) :
    Nonempty (Decomposition G label ((univ.image copy) ∪ S0 ∪ S1) h) := by
  have hrowle : (univ.filter (P.Mixed false)).card ≤ k := by
    simpa using card_le_univ (univ.filter (P.Mixed false))
  have hcolumnle : (univ.filter (P.Mixed true)).card ≤ k := by
    simpa using card_le_univ (univ.filter (P.Mixed true))
  have hRle : P.sameRowPairs.card ≤ k := by simpa using card_le_univ P.sameRowPairs
  have hCle : P.sameColumnPairs.card ≤ k := by simpa using card_le_univ P.sameColumnPairs
  have hsize0 : P.sameRowPairs.card + 4 * D ≤ S0.card := by omega
  have hsize1 : P.sameColumnPairs.card + 4 * D ≤ S1.card := by omega
  obtain ⟨U0, U1, hU0, hU1, hU0card, hU1card, ⟨Q⟩⟩ :=
    exists_augmented_cross_decomposition G H copy hcopy hedge label side refinement P hlabel
      S0 S1 hS0 hS1 hdegree hsize0 hsize1
  have hrow : P.oppositePairs.card + P.sameColumnPairs.card =
      (univ.filter (P.Mixed false)).card := by
    rw [P.mixed_card]
    exact P.opposite_add_sameColumn_card
  have hcolumn : P.oppositePairs.card + P.sameRowPairs.card =
      (univ.filter (P.Mixed true)).card := by
    rw [P.mixed_card]
    exact P.opposite_add_sameRow_card
  have hrem0 := card_sdiff_add_card_eq_card hU0
  have hrem1 := card_sdiff_add_card_eq_card hU1
  have hremcard : (S0 \ U0).card = (S1 \ U1).card := by omega
  have htotal : P.oppositePairs.card + P.sameRowPairs.card + P.sameColumnPairs.card +
      (S0 \ U0).card = h := by omega
  obtain ⟨R⟩ := exists_left_right_decomposition G vertexLabel label hincident
    (S0 \ U0) (S1 \ U1)
    (fun e he => hS0 e (mem_sdiff.mp he).1)
    (fun e he => hS1 e (mem_sdiff.mp he).1) hremcard
  let X : Finset E := univ.image copy
  have hXS0 : Disjoint X S0 := by
    apply disjoint_left.mpr
    intro x hx hs
    obtain ⟨e, _, rfl⟩ := mem_image.mp hx
    exact matching_cross_ne_left _ _ ((hlabel e).symm.trans (hS0 (copy e) hs))
  have hXS1 : Disjoint X S1 := by
    apply disjoint_left.mpr
    intro x hx hs
    obtain ⟨e, _, rfl⟩ := mem_image.mp hx
    exact matching_cross_ne_right _ _ ((hlabel e).symm.trans (hS1 (copy e) hs))
  have hS01 : Disjoint S0 S1 := by
    apply disjoint_left.mpr
    intro e he hf
    exact matching_left_ne_right ((hS0 e he).symm.trans (hS1 e hf))
  have hU0rem : Disjoint U0 (S0 \ U0) :=
    disjoint_left.mpr (fun e he hf => (mem_sdiff.mp hf).2 he)
  have hU1rem : Disjoint U1 (S1 \ U1) :=
    disjoint_left.mpr (fun e he hf => (mem_sdiff.mp hf).2 he)
  have hblocks : Disjoint (X ∪ U0 ∪ U1) ((S0 \ U0) ∪ (S1 \ U1)) := by
    have hx0 := hXS0.mono (subset_refl X) (sdiff_subset : S0 \ U0 ⊆ S0)
    have hx1 := hXS1.mono (subset_refl X) (sdiff_subset : S1 \ U1 ⊆ S1)
    have h01 := hS01.mono hU0 (sdiff_subset : S1 \ U1 ⊆ S1)
    have h10 := hS01.symm.mono hU1 (sdiff_subset : S0 \ U0 ⊆ S0)
    simp only [disjoint_union_left, disjoint_union_right]
    tauto
  have hcover : (X ∪ U0 ∪ U1) ∪ ((S0 \ U0) ∪ (S1 \ U1)) = X ∪ S0 ∪ S1 := by
    ext e
    have hs0 : e ∈ U0 → e ∈ S0 := fun he => hU0 he
    have hs1 : e ∈ U1 → e ∈ S1 := fun he => hU1 he
    simp only [mem_union, mem_sdiff]
    tauto
  exact ⟨(Q.union R hblocks).cast hcover htotal⟩

end Overfull.FourOdd
