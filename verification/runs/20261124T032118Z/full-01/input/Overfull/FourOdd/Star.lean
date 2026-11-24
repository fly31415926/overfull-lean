import Overfull.FourOdd.StarAssembly
import Overfull.FourOdd.Capping

/-!
# Complete canonical star construction for four odd parts

The capped off-star pools are paired with opposite star-arm singleton
copies. Their quotas follow from the retained singleton-label cuts and
parity. The three equal remaining arm pools are assembled by two Hall
pairings, and every unused or capped copy is retained in a parallel
matching pair.
-/

noncomputable section
namespace Overfull.FourOdd
open Finset Classical Compression CircuitPatterns
open scoped BigOperators

private theorem starPair_mem (i : Fin 3) : starPair i ∈ labelStar 0 := by
  revert i
  decide

private theorem oppositePair_not_mem (i : Fin 3) : oppositePair i ∉ labelStar 0 := by
  revert i
  decide

private theorem star_leaf_sum (f : LabelPair → ℕ) (i : Fin 3) :
    (∑ p ∈ univ.filter (fun p : LabelPair => i.succ ∈ p.val), f p) +
        f (oppositePair i) = f (starPair i) + ∑ j : Fin 3, f (oppositePair j) := by
  have h0 : univ.filter (fun p : LabelPair => (1 : Fin 4) ∈ p.val) =
      {starPair 0, oppositePair 1, oppositePair 2} := by decide
  have h1 : univ.filter (fun p : LabelPair => (2 : Fin 4) ∈ p.val) =
      {starPair 1, oppositePair 0, oppositePair 2} := by decide
  have h2 : univ.filter (fun p : LabelPair => (3 : Fin 4) ∈ p.val) =
      {starPair 2, oppositePair 0, oppositePair 1} := by decide
  fin_cases i
  · change (∑ p ∈ univ.filter (fun p : LabelPair => (1 : Fin 4) ∈ p.val), f p) +
        f (oppositePair 0) = f (starPair 0) + ∑ j : Fin 3, f (oppositePair j)
    rw [h0, sum_insert (by decide), sum_insert (by decide), sum_singleton]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    dsimp [oppositePair]
    omega
  · change (∑ p ∈ univ.filter (fun p : LabelPair => (2 : Fin 4) ∈ p.val), f p) +
        f (oppositePair 1) = f (starPair 1) + ∑ j : Fin 3, f (oppositePair j)
    rw [h1, sum_insert (by decide), sum_insert (by decide), sum_singleton]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    dsimp [oppositePair]
    omega
  · change (∑ p ∈ univ.filter (fun p : LabelPair => (3 : Fin 4) ∈ p.val), f p) +
        f (oppositePair 2) = f (starPair 2) + ∑ j : Fin 3, f (oppositePair j)
    rw [h2, sum_insert (by decide), sum_insert (by decide), sum_singleton]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    dsimp [oppositePair]
    omega

private theorem biUnion_fin_three {E : Type*} (R : Fin 3 → Finset E) :
    univ.biUnion R = R 0 ∪ R 1 ∪ R 2 := by
  ext e
  simp only [mem_biUnion, mem_univ, true_and, mem_union]
  constructor
  · rintro ⟨i, hi⟩
    fin_cases i
    · exact Or.inl (Or.inl hi)
    · exact Or.inl (Or.inr hi)
    · exact Or.inr hi
  · rintro ((h | h) | h)
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩

variable {V E : Type*} [Fintype V] [Fintype E]

/-- Complete the retained star pools from their preserved leaf cuts.
All singleton quotas and both Hall inputs are constructed in the proof. -/
theorem exists_capped_star_decomposition
    (G : Multigraph V E) (vlabel : V → Fin 4)
    (hjoin : ∀ e, vlabel (G.firstEnd e) ≠ vlabel (G.secondEnd e))
    (h D B : ℕ)
    (P : CappedPools G (G.labelQuotient vlabel hjoin) (labelStar 0) B)
    (hdegree : ∀ v, G.degree v ≤ D)
    (hlower : ∀ i, h ≤ (G.labelQuotient vlabel hjoin).degreeOn P.retained i)
    (hparity : ∀ i, (G.labelQuotient vlabel hjoin).degreeOn P.retained i % 2 = h % 2)
    (hroom : 3 * (B + 1) + 12 * D < h) :
    Nonempty (Decomposition G (G.labelQuotient vlabel hjoin).edgeLabelPair
      P.retained h) := by
  let Q := G.labelQuotient vlabel hjoin
  let F : Fin 3 → Finset E := fun i => pairPool Q (starPair i)
  let O : Fin 3 → Finset E := fun i => P.kept (oppositePair i)
  let N := ∑ i : Fin 3, (O i).card
  let q := h - N
  have hN : N ≤ 3 * (B + 1) := by
    calc
      N ≤ ∑ _i : Fin 3, (B + 1) :=
        sum_le_sum (fun i _ => P.cap_bound _ (oppositePair_not_mem i))
      _ = 3 * (B + 1) := by simp [Nat.mul_comm]
  have hsum : N + q = h := by dsimp [q]; omega
  have hq : 12 * D < q := by omega
  have hF (i : Fin 3) : P.kept (starPair i) = F i := P.fixed _ (starPair_mem i)
  have hleaf (i : Fin 3) : Q.degreeOn P.retained i.succ + (O i).card =
      (F i).card + N := by
    rw [P.degree_eq_sum]
    have hi := star_leaf_sum (fun p => (P.kept p).card) i
    rw [hF i] at hi
    exact hi
  have hex (i : Fin 3) : ∃ S : Finset E, S ⊆ F i ∧ S.card = q + (O i).card ∧
      Nonempty (MatchingPairPartition G (F i \ S)) := by
    have hlo : h ≤ Q.degreeOn P.retained i.succ := hlower i.succ
    have hpa : Q.degreeOn P.retained i.succ % 2 = h % 2 := hparity i.succ
    have hid := hleaf i
    have hquota : q + (O i).card ≤ (F i).card := by omega
    have hmod : (F i).card % 2 = (q + (O i).card) % 2 := by omega
    apply exists_singletons_and_pairs_on G (F i)
      (pairPool_bipartite G vlabel hjoin (starPair i)) (q + (O i).card) hquota hmod
    intro v
    have hlocal := (restrictEdges_degree_le_original G (F i) v).trans (hdegree v)
    omega
  choose S hSF hScard hparts using hex
  have hT_exists (i : Fin 3) : ∃ T : Finset E, T ⊆ S i ∧ T.card = (O i).card :=
    exists_subset_card_eq (by rw [hScard]; omega)
  choose T hTS hTcard using hT_exists
  let R : Fin 3 → Finset E := fun i => S i \ T i
  have hRcard (i : Fin 3) : (R i).card = q := by
    dsimp [R]
    rw [card_sdiff_of_subset (hTS i), hScard i, hTcard i]
    omega
  have hRsub (i : Fin 3) : R i ⊆ F i :=
    sdiff_subset.trans (hSF i)
  have hFlab (i : Fin 3) (e : E) (he : e ∈ F i) : Q.edgeLabelPair e = starPair i :=
    (mem_pairPool Q _ e).mp he
  have hOlab (i : Fin 3) (e : E) (he : e ∈ O i) :
      Q.edgeLabelPair e = oppositePair i :=
    (mem_pairPool Q _ e).mp (P.subset _ he)
  have hFO (i : Fin 3) : Disjoint (F i) (O i) :=
    (pairPool_disjoint Q (starPair_ne_oppositePair i i)).mono subset_rfl (P.subset _)
  let H : Fin 3 → Finset E := fun i => F i ∪ O i
  have hHdisj : Pairwise (fun i j => Disjoint (H i) (H j)) := by
    intro i j hij
    dsimp [H]
    rw [disjoint_union_left, disjoint_union_right, disjoint_union_right]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact pairPool_disjoint Q (fun hp => hij (starPair_injective hp))
    · exact (pairPool_disjoint Q (starPair_ne_oppositePair i j)).mono
        subset_rfl (P.subset _)
    · exact (pairPool_disjoint Q (starPair_ne_oppositePair j i).symm).mono
        (P.subset _) subset_rfl
    · exact P.kept_disjoint (fun hp => hij (oppositePair_injective hp))
  let K : Fin 3 → Finset E := fun i => (F i \ S i) ∪ (O i ∪ T i)
  have hKsub (i : Fin 3) : K i ⊆ H i := by
    intro e he
    rcases mem_union.mp he with he | he
    · exact mem_union_left _ (mem_sdiff.mp he).1
    · rcases mem_union.mp he with he | he
      · exact mem_union_right _ he
      · exact mem_union_left _ (hSF i (hTS i he))
  have hKR (i : Fin 3) : Disjoint (K i) (R i) := by
    apply disjoint_left.mpr
    intro e heK heR
    obtain ⟨heS, heT⟩ := mem_sdiff.mp heR
    rcases mem_union.mp heK with he | he
    · exact (mem_sdiff.mp he).2 heS
    · rcases mem_union.mp he with he | he
      · exact disjoint_left.mp (hFO i) (hSF i heS) he
      · exact heT he
  have hKRcover (i : Fin 3) : K i ∪ R i = H i := by
    apply subset_antisymm
    · exact union_subset (hKsub i) ((hRsub i).trans subset_union_left)
    · intro e he
      rcases mem_union.mp he with heF | heO
      · by_cases heS : e ∈ S i
        · by_cases heT : e ∈ T i
          · exact mem_union_left _ (mem_union_right _ (mem_union_right _ heT))
          · exact mem_union_right _ (mem_sdiff.mpr ⟨heS, heT⟩)
        · exact mem_union_left _ (mem_union_left _ (mem_sdiff.mpr ⟨heF, heS⟩))
      · exact mem_union_left _ (mem_union_right _ (mem_union_left _ heO))
  have hKparts (i : Fin 3) : Nonempty (Decomposition G Q.edgeLabelPair (K i) (O i).card) := by
    let PP := Classical.choice (hparts i)
    let surplus := Decomposition.ofPairPartition PP (by
      intro M hM e he f hf
      exact (hFlab i e (mem_sdiff.mp (PP.part_subset hM he)).1).trans
        (hFlab i f (mem_sdiff.mp (PP.part_subset hM hf)).1).symm)
    obtain ⟨primary⟩ := exists_opposite_pool_decomposition G vlabel hjoin i (O i) (T i)
      (hOlab i) (fun e he => hFlab i e (hSF i (hTS i he))) (hTcard i).symm
    have hdis : Disjoint (F i \ S i) (O i ∪ T i) := by
      apply disjoint_union_right.mpr
      refine ⟨(hFO i).mono sdiff_subset subset_rfl, ?_⟩
      apply disjoint_left.mpr
      intro e he heT
      exact (mem_sdiff.mp he).2 (hTS i heT)
    exact ⟨(surplus.union primary hdis).cast rfl (by simp)⟩
  obtain ⟨PK⟩ := Decomposition.exists_biUnion univ K (fun i => (O i).card)
    (fun i => Classical.choice (hKparts i)) (by
      intro i _ j _ hij
      exact (hHdisj hij).mono (hKsub i) (hKsub j))
  obtain ⟨PR⟩ := exists_equal_star_pool_decomposition G Q.edgeLabelPair
    (R 0) (R 1) (R 2) D
    (fun e he => hFlab 0 e (hRsub 0 he))
    (fun e he => hFlab 1 e (hRsub 1 he))
    (fun e he => hFlab 2 e (hRsub 2 he))
    (by rw [hRcard, hRcard]) (by rw [hRcard, hRcard]) hdegree (by rw [hRcard]; exact hq)
  let PR' := PR.cast (biUnion_fin_three R).symm (hRcard 0)
  have hcross : Disjoint (univ.biUnion K) (univ.biUnion R) := by
    apply disjoint_left.mpr
    intro e heK heR
    obtain ⟨i, _, hei⟩ := mem_biUnion.mp heK
    obtain ⟨j, _, hej⟩ := mem_biUnion.mp heR
    by_cases hij : i = j
    · subst j
      exact disjoint_left.mp (hKR i) hei hej
    · exact disjoint_left.mp (hHdisj hij) (hKsub i hei)
        (mem_union_left _ (hRsub j hej))
  have hHcover : univ.biUnion H = P.retained := by
    ext e
    constructor
    · intro he
      obtain ⟨i, _, hi⟩ := mem_biUnion.mp he
      rcases mem_union.mp hi with hi | hi
      · exact mem_biUnion.mpr ⟨starPair i, mem_univ _, (hF i).symm ▸ hi⟩
      · exact mem_biUnion.mpr ⟨oppositePair i, mem_univ _, hi⟩
    · intro he
      obtain ⟨p, _, hp⟩ := mem_biUnion.mp he
      rcases starPair_oppositePair_cover p with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · exact mem_biUnion.mpr ⟨i, mem_univ _, mem_union_left _ ((hF i) ▸ hp)⟩
      · exact mem_biUnion.mpr ⟨i, mem_univ _, mem_union_right _ hp⟩
  have hcover : univ.biUnion K ∪ univ.biUnion R = P.retained := by
    rw [← paired_unions_cover K R (Equiv.refl (Fin 3))]
    have heq : (fun i => K i ∪ R ((Equiv.refl (Fin 3)) i)) = H := by
      funext i
      exact hKRcover i
    rw [heq, hHcover]
  exact ⟨(PK.union PR' hcross).cast hcover hsum⟩

/-- The complete canonical-star case, from original boundary degrees,
near-full star-pool supplies, and the original odd-part cut/parity bounds.
Every joining copy is covered, with exactly `h` primary pieces. -/
theorem exists_star_decomposition
    (G : Multigraph V E) (vlabel : V → Fin 4)
    (hjoin : ∀ e, vlabel (G.firstEnd e) ≠ vlabel (G.secondEnd e))
    (h D r0 : ℕ) (_hh : 0 < h) (hD : 0 < D)
    (hsmall : 1000 * D ≤ h) (hnearly : 999 * h ≤ 1000 * r0)
    (hdegree : ∀ v, G.degree v ≤ D)
    (hlower : ∀ i, h ≤ (G.labelQuotient vlabel hjoin).degree i)
    (hparity : ∀ i, (G.labelQuotient vlabel hjoin).degree i % 2 = h % 2)
    (hsupply : ∀ i : Fin 3,
      r0 ≤ (pairPool (G.labelQuotient vlabel hjoin) (starPair i)).card) :
    Nonempty (Decomposition G (G.labelQuotient vlabel hjoin).edgeLabelPair univ h) := by
  let B := 2 * D + (h - r0)
  have hDB : D ≤ B := by dsimp [B]; omega
  have hreserve : h ≤ r0 + B := by dsimp [B]; omega
  have hroom : 3 * (B + 1) + 12 * D < h := by dsimp [B]; omega
  obtain ⟨P⟩ := exists_cappedPools G vlabel hjoin (labelStar 0) B
    (fun v => (hdegree v).trans hDB)
  have hsupply' : ∀ p ∈ labelStar 0,
      r0 ≤ (pairPool (G.labelQuotient vlabel hjoin) p).card := by
    intro p hp
    rcases starPair_oppositePair_cover p with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact hsupply i
    · exact (oppositePair_not_mem i hp).elim
  have hlower' (i : Fin 4) :
      h ≤ (G.labelQuotient vlabel hjoin).degreeOn P.retained i :=
    P.degree_lower (Or.inr ⟨0, rfl⟩) hsupply' hlower hreserve i
  have hparity' (i : Fin 4) :
      (G.labelQuotient vlabel hjoin).degreeOn P.retained i % 2 = h % 2 :=
    (P.degree_parity i).trans (hparity i)
  obtain ⟨R⟩ := exists_capped_star_decomposition G vlabel hjoin h D B P
    hdegree hlower' hparity' hroom
  have hdis : Disjoint P.retained (univ \ P.retained) := by
    apply disjoint_left.mpr
    intro e he he'
    exact (mem_sdiff.mp he').2 he
  have hcover : P.retained ∪ (univ \ P.retained) = univ := by
    ext e
    simp only [mem_union, mem_sdiff, mem_univ, true_and]
    exact iff_true_intro (Classical.em _)
  exact ⟨(R.union P.discardedDecomposition hdis).cast hcover (Nat.add_zero h)⟩

end Overfull.FourOdd
