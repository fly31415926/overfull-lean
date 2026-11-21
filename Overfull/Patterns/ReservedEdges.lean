import Overfull.Patterns.Selection
import Overfull.Patterns.Multiplicity
import Overfull.Patterns.AbsorptionParity
import Overfull.Patterns.Cuts

/-!
# Actual edges retained for the frequent pattern

Numerical pair reserves are interpreted through exact subtraction from
the original host-edge pools. Internal completion edges never consume a
boundary pool. The surviving exceptional pairs give distinct neighbors,
and surviving joining pairs give actual edges and whole-cut supply after
the assigned exceptional vertices are absorbed.
-/

noncomputable section

namespace Overfull.Patterns

open Finset Classical SimpleGraph Compression FractionalMatching MatchingProbability
open ForeignPhase ForceMatching
open scoped BigOperators

variable {V I : Type*} [Fintype V] [DecidableEq V]

/-- The edges in an original host family that are present in an actual
graph on the same vertex set. -/
def survivingEdges (G R : SimpleGraph V) (A : Finset G.edgeSet) : Finset G.edgeSet :=
  A.filter (fun e => e.val ∈ R.edgeSet)

omit [Fintype V] [DecidableEq V] in
@[simp] theorem mem_survivingEdges (G R : SimpleGraph V) (A : Finset G.edgeSet)
    (e : G.edgeSet) :
    e ∈ survivingEdges G R A ↔ e ∈ A ∧ e.val ∈ R.edgeSet := by
  simp [survivingEdges]

omit [Fintype V] [DecidableEq V] in
@[simp] theorem survivingEdges_original (G : SimpleGraph V) (A : Finset G.edgeSet) :
    survivingEdges G G A = A := by
  ext e
  simp [e.property]

omit [Fintype V] [DecidableEq V] in
theorem survivingEdges_mono (G R H : SimpleGraph V) (hHR : H ≤ R)
    (A : Finset G.edgeSet) : survivingEdges G H A ⊆ survivingEdges G R A := by
  intro e he
  obtain ⟨heA, heH⟩ := (mem_survivingEdges G H A e).mp he
  exact (mem_survivingEdges G R A e).mpr ⟨heA, SimpleGraph.edgeSet_mono hHR heH⟩

omit [Fintype V] in
theorem survivingEdges_sdiff (G R H : SimpleGraph V) (A : Finset G.edgeSet) :
    survivingEdges G (R \ H) A = survivingEdges G R A \ survivingEdges G H A := by
  ext e
  simp only [mem_survivingEdges, mem_sdiff, edgeSet_sdiff, Set.mem_diff]
  tauto

omit [Fintype V] in
theorem survivingEdges_partition (G R H : SimpleGraph V) (hHR : H ≤ R)
    (A : Finset G.edgeSet) :
    (survivingEdges G (R \ H) A).card + (survivingEdges G H A).card =
      (survivingEdges G R A).card := by
  rw [survivingEdges_sdiff]
  exact card_sdiff_add_card_eq_card (survivingEdges_mono G R H hHR A)

omit [Fintype V] in
/-- Exact subtraction works for any original edge pool and every prefix
of actual present matching deletions. -/
theorem afterDeletions_pool_accounting (G : SimpleGraph V)
    (N : ℕ → G.Subgraph) (s : ℕ)
    (hpresent : ∀ j < s, (N j).spanningCoe ≤ afterDeletions G N j)
    (A : Finset G.edgeSet) :
    (survivingEdges G (afterDeletions G N s) A).card +
      (∑ j ∈ range s, (survivingEdges G (N j).spanningCoe A).card) = A.card := by
  induction s with
  | zero => simp
  | succ s ih =>
    have hh := ih (fun j hj => hpresent j (Nat.lt_succ_of_lt hj))
    have hstep := survivingEdges_partition G (afterDeletions G N s)
      (N s).spanningCoe (hpresent s (Nat.lt_succ_self s)) A
    rw [← afterDeletions_succ] at hstep
    rw [sum_range_succ]
    omega

/-- The original pool for one boundary pair, restricted to the actual
residual graph. -/
def survivingPool (G R : SimpleGraph V) (U : I → Finset V) (Z : Finset V)
    (code : I ↪ Fin 4) (b : BoundaryPair Z) : Finset G.edgeSet :=
  survivingEdges G R (boundaryPool G U Z code b)

@[simp] theorem mem_survivingPool (G R : SimpleGraph V) (U : I → Finset V)
    (Z : Finset V) (code : I ↪ Fin 4) (b : BoundaryPair Z) (e : G.edgeSet) :
    e ∈ survivingPool G R U Z code b ↔
      e ∈ boundaryPool G U Z code b ∧ e.val ∈ R.edgeSet := by
  simp [survivingPool]

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- An injective exact boundary quotient uses a pair once precisely when
that pair occurs in its pattern. -/
theorem boundaryPool_matching_card (U : I → Finset V) (Z : Finset V)
    (code : I ↪ Fin 4) (F : G.Subgraph) (P : Pattern Z)
    (hinj : Set.InjOn (labelledEdge G U Z code) (matchingEdges F))
    (himage : (matchingEdges F).image (labelledEdge G U Z code) = P.boundaryEdges)
    (b : BoundaryPair Z) :
    (survivingPool G F.spanningCoe U Z code b).card = pairIndicator b P := by
  have hfilter : survivingPool G F.spanningCoe U Z code b =
      (matchingEdges F).filter (fun e => labelledEdge G U Z code e = boundaryPairLabels b) := by
    ext e
    have heq : e.val ∈ F.spanningCoe.edgeSet ↔ e.val ∈ F.edgeSet := by
      rw [← edge_eq e]
      rfl
    simp [survivingPool, survivingEdges, boundaryPool, matchingEdges, heq, and_comm]
  rw [hfilter]
  unfold pairIndicator
  split_ifs with hb
  · rw [← himage] at hb
    obtain ⟨e, he, heq⟩ := mem_image.mp hb
    have hset : (matchingEdges F).filter
        (fun f => labelledEdge G U Z code f = boundaryPairLabels b) = {e} := by
      ext f
      simp only [mem_filter, mem_singleton]
      constructor
      · rintro ⟨hf, hfq⟩
        exact hinj hf he (hfq.trans heq.symm)
      · rintro rfl
        exact ⟨he, heq⟩
    rw [hset, card_singleton]
  · have hset : (matchingEdges F).filter
        (fun e => labelledEdge G U Z code e = boundaryPairLabels b) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro e he
      obtain ⟨heF, heq⟩ := mem_filter.mp he
      have hh : boundaryPairLabels b ∈ P.boundaryEdges := by
        rw [← himage]
        exact mem_image.mpr ⟨e, heF, heq⟩
      exact hb hh
    rw [hset, card_empty]

omit [DecidableRel G.Adj] in
/-- Completing only inside original cores consumes no additional edge
of any exceptional-to-core or core-to-core pool. -/
theorem boundaryPool_completion_eq (U : I → Finset V) (Z : Finset V)
    (code : I ↪ Fin 4)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hUZ : ∀ i, Disjoint (U i) Z)
    (F N : G.Subgraph) (hFN : F ≤ N)
    (hadded : ∀ u v, N.Adj u v → F.Adj u v ∨ ∃ i, u ∈ U i ∧ v ∈ U i)
    (b : BoundaryPair Z) :
    survivingPool G N.spanningCoe U Z code b =
      survivingPool G F.spanningCoe U Z code b := by
  ext e
  simp only [mem_survivingPool]
  apply and_congr_right
  intro he
  constructor
  · intro heN
    have hn : N.Adj (firstEnd e) (secondEnd e) := by
      rw [← edge_eq e] at heN
      exact heN
    rcases hadded _ _ hn with hf | ⟨i, hi, hj⟩
    · rw [← edge_eq e]
      exact hf
    · exact False.elim (boundaryPool_no_internal G U Z code hdisjoint hUZ b e he
        i (firstEnd e) (secondEnd e) hi hj (edge_eq e).symm)
  · intro heF
    rw [← edge_eq e] at heF ⊢
    exact hFN.2 heF

/-- Exact pool accounting for completed, exactly realized boundary
patterns. The completions and residual graph are the actual objects. -/
theorem completed_boundaryPool_accounting (U : I → Finset V) (Z : Finset V)
    (code : I ↪ Fin 4)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hUZ : ∀ i, Disjoint (U i) Z)
    (F N : ℕ → G.Subgraph) (P : ℕ → Pattern Z) (s : ℕ)
    (hpresent : ∀ j < s, (N j).spanningCoe ≤ afterDeletions G N j)
    (hcontains : ∀ j < s, F j ≤ N j)
    (hadded : ∀ j < s, ∀ u v, (N j).Adj u v →
      (F j).Adj u v ∨ ∃ i, u ∈ U i ∧ v ∈ U i)
    (hinj : ∀ j < s, Set.InjOn (labelledEdge G U Z code) (matchingEdges (F j)))
    (himage : ∀ j < s,
      (matchingEdges (F j)).image (labelledEdge G U Z code) = (P j).boundaryEdges)
    (b : BoundaryPair Z) :
    (survivingPool G (afterDeletions G N s) U Z code b).card +
      (∑ j ∈ range s, pairIndicator b (P j)) = (boundaryPool G U Z code b).card := by
  have h := afterDeletions_pool_accounting G N s hpresent (boundaryPool G U Z code b)
  change (survivingPool G (afterDeletions G N s) U Z code b).card +
    (∑ j ∈ range s, (survivingPool G (N j).spanningCoe U Z code b).card) = _ at h
  convert h using 2
  apply sum_congr rfl
  intro j hj
  rw [boundaryPool_completion_eq U Z code hdisjoint hUZ (F j) (N j)
    (hcontains j (mem_range.mp hj)) (hadded j (mem_range.mp hj)),
    boundaryPool_matching_card U Z code (F j) (P j)
      (hinj j (mem_range.mp hj)) (himage j (mem_range.mp hj))]

/-- The numerical reserved demand gives that many actual surviving
edges in every pair used by the frequent pattern. -/
theorem reserved_boundaryPool_card (U : I → Finset V) (Z : Finset V)
    (code : I ↪ Fin 4)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hUZ : ∀ i, Disjoint (U i) Z)
    (F N : ℕ → G.Subgraph) (m : Pattern Z → ℕ) (P₀ : Pattern Z) (r : ℕ)
    (hpresent : ∀ j < ∑ p, m p, (N j).spanningCoe ≤ afterDeletions G N j)
    (hcontains : ∀ j < ∑ p, m p, F j ≤ N j)
    (hadded : ∀ j < ∑ p, m p, ∀ u v, (N j).Adj u v →
      (F j).Adj u v ∨ ∃ i, u ∈ U i ∧ v ∈ U i)
    (hinj : ∀ j < ∑ p, m p, Set.InjOn (labelledEdge G U Z code) (matchingEdges (F j)))
    (himage : ∀ j < ∑ p, m p,
      (matchingEdges (F j)).image (labelledEdge G U Z code) =
        (enumeratedPattern m P₀ j).boundaryEdges)
    (hreserve : ∀ b : BoundaryPair Z, (r : ℝ)*pairIndicator b P₀ ≤
      (boundaryPool G U Z code b).card - ∑ p, (m p : ℝ)*pairIndicator b p)
    (b : BoundaryPair Z) (hb : boundaryPairLabels b ∈ P₀.boundaryEdges) :
    r ≤ (survivingPool G (afterDeletions G N (∑ p, m p)) U Z code b).card := by
  have hcount := completed_boundaryPool_accounting U Z code hdisjoint hUZ F N
    (enumeratedPattern m P₀) (∑ p, m p) hpresent hcontains hadded hinj himage b
  rw [enumeratedPattern_statistic] at hcount
  have hcountR : ((survivingPool G (afterDeletions G N (∑ p, m p)) U Z code b).card : ℝ) +
      (∑ p, (m p : ℝ)*pairIndicator b p) = (boundaryPool G U Z code b).card := by
    exact_mod_cast hcount
  have hr := hreserve b
  have hind : pairIndicator b P₀ = 1 := by simp [pairIndicator, hb]
  rw [hind, Nat.cast_one, mul_one] at hr
  have hreal : (r : ℝ) ≤
      (survivingPool G (afterDeletions G N (∑ p, m p)) U Z code b).card := by
    linarith only [hr, hcountR]
  exact_mod_cast hreal

theorem boundaryLabel_inr_core_iff (U : I → Finset V) (Z : Finset V)
    (code : I ↪ Fin 4)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hUZ : ∀ i, Disjoint (U i) Z)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i) (v : V) (i : I) :
    boundaryLabel U Z code v = Sum.inr (code i) ↔ v ∈ U i := by
  have h : v ∈ wholeUnion U Z code {Sum.inr (code i)} ↔ v ∈ U i := by
    rw [wholeUnion_single_core U Z code hdisjoint hUZ hcover i]
  simpa only [mem_wholeUnion, mem_singleton] using h

omit [DecidableRel G.Adj] in
/-- Every surviving exceptional-to-core pool edge identifies an actual
neighbor in the specified original core. -/
theorem survivingPool_exceptional_edge (R : SimpleGraph V)
    (U : I → Finset V) (Z : Finset V) (code : I ↪ Fin 4)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hUZ : ∀ i, Disjoint (U i) Z)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (z : Z) (i : I) (e : G.edgeSet)
    (he : e ∈ survivingPool G R U Z code (Sum.inl (z,code i))) :
    ∃ v ∈ U i, R.Adj z.val v ∧ e.val = s(z.val,v) := by
  obtain ⟨heP, heR⟩ := (mem_survivingPool G R U Z code _ e).mp he
  have hlabels := (mem_boundaryPool G U Z code _ e).mp heP
  have hz : z.val ∈ e.val := by
    apply (inl_mem_labelledEdge G U Z code e z).mp
    rw [hlabels]
    simp
  obtain ⟨v, heq⟩ := Sym2.mem_iff_exists.mp hz
  have hadj : R.Adj z.val v := by simpa only [heq] using heR
  have hmem : Sum.inr (code i) ∈ labelledEdge G U Z code e := by
    rw [hlabels]
    simp
  have hlab : Sum.inr (code i) = boundaryLabel U Z code v := by
    simpa only [labelledEdge, heq, Sym2.toFinset_mk_eq, image_insert, image_singleton,
      boundaryLabel_exceptional, mem_insert, mem_singleton, Sum.inr_ne_inl, false_or] using hmem
  exact ⟨v, (boundaryLabel_inr_core_iff U Z code hdisjoint hUZ hcover v i).mp hlab.symm,
    hadj, heq⟩

omit [DecidableRel G.Adj] in
/-- Simplicity makes the surviving exceptional pool inject into distinct
actual residual neighbors; multiplicities are not counted as neighbors. -/
theorem survivingPool_exceptional_card_le_neighbors (R : SimpleGraph V)
    (U : I → Finset V) (Z : Finset V) (code : I ↪ Fin 4)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hUZ : ∀ i, Disjoint (U i) Z)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i) (z : Z) (i : I) :
    (survivingPool G R U Z code (Sum.inl (z,code i))).card ≤
      (R.neighborFinset z.val ∩ U i).card := by
  let A := survivingPool G R U Z code (Sum.inl (z,code i))
  have hex (e : A) : ∃ v ∈ U i, R.Adj z.val v ∧ e.val.val = s(z.val,v) :=
    survivingPool_exceptional_edge R U Z code hdisjoint hUZ hcover z i e.val e.property
  choose next hnextU hnextAdj hnextEdge using hex
  let f : A → {v : V // v ∈ R.neighborFinset z.val ∩ U i} := fun e =>
    ⟨next e, mem_inter.mpr ⟨(R.mem_neighborFinset z.val (next e)).mpr (hnextAdj e), hnextU e⟩⟩
  have hinj : Function.Injective f := by
    intro e d heq
    have hn : next e = next d := congrArg Subtype.val heq
    apply Subtype.ext
    apply Subtype.ext
    rw [hnextEdge e, hnextEdge d, hn]
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hinj

/-- Actual joining edges between the two indicated labelled parts. -/
def partPairEdges (R : SimpleGraph V) (U : I → Finset V) (code : I ↪ Fin 4)
    (p : LabelPair) : Finset (Sym2 V) :=
  R.edgeFinset.filter (fun e => e.toFinset.image (coreLabel U code) = p.val)

@[simp] theorem mem_partPairEdges (R : SimpleGraph V) (U : I → Finset V)
    (code : I ↪ Fin 4) (p : LabelPair) (e : Sym2 V) :
    e ∈ partPairEdges R U code p ↔
      e ∈ R.edgeSet ∧ e.toFinset.image (coreLabel U code) = p.val := by
  simp [partPairEdges]

theorem partPairEdges_disjoint (R : SimpleGraph V) (U : I → Finset V)
    (code : I ↪ Fin 4) (p q : LabelPair) (hpq : p ≠ q) :
    Disjoint (partPairEdges R U code p) (partPairEdges R U code q) := by
  apply disjoint_left.mpr
  intro e he hf
  exact hpq (Subtype.ext (((mem_partPairEdges R U code p e).mp he).2.symm.trans
    ((mem_partPairEdges R U code q e).mp hf).2))

omit [Fintype V] [DecidableEq V] in
/-- Enlarging disjoint cores preserves the labels of their original
vertices. -/
theorem coreLabel_enlarged (U A : I → Finset V) (code : I ↪ Fin 4)
    (hU : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hA : ∀ i j, i ≠ j → Disjoint (A i) (A j))
    (hsub : ∀ i, U i ⊆ A i) (v : V) (hv : ∃ i, v ∈ U i) :
    coreLabel A code v = coreLabel U code v := by
  obtain ⟨i, hi⟩ := hv
  rw [coreLabel_of_mem A code hA (hsub i hi), coreLabel_of_mem U code hU hi]

omit [DecidableRel G.Adj] in
/-- Every surviving joining pool gives actual edges between the same
two labelled parts after enlargement. -/
theorem survivingPool_joining_subset (R : SimpleGraph V)
    (U A : I → Finset V) (Z : Finset V) (code : I ↪ Fin 4)
    (hU : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hA : ∀ i j, i ≠ j → Disjoint (A i) (A j))
    (hsub : ∀ i, U i ⊆ A i)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i) (p : LabelPair) :
    (survivingPool G R U Z code (Sum.inr p)).image Subtype.val ⊆
      partPairEdges R A code p := by
  intro ee hee
  obtain ⟨e, he, rfl⟩ := mem_image.mp hee
  obtain ⟨heP, heR⟩ := (mem_survivingPool G R U Z code _ e).mp he
  have hlabels := (mem_boundaryPool G U Z code _ e).mp heP
  have hout (v : V) (hv : v ∈ e.val) : v ∉ Z := by
    intro hz
    have hm := (inl_mem_labelledEdge G U Z code e ⟨v,hz⟩).mpr hv
    rw [hlabels] at hm
    simp at hm
  have hlabel (v : V) (hv : v ∈ e.val.toFinset) :
      boundaryLabel U Z code v = Sum.inr (coreLabel A code v) := by
    have hv' : v ∈ e.val := Sym2.mem_toFinset.mp hv
    rw [boundaryLabel_outside U Z code v (hout v hv')]
    rw [coreLabel_enlarged U A code hU hA hsub v ((hcover v).resolve_left (hout v hv'))]
  apply (mem_partPairEdges R A code p e.val).mpr
  refine ⟨heR, ?_⟩
  apply Finset.image_injective (f := (Sum.inr : Fin 4 → Z ⊕ Fin 4)) Sum.inr_injective
  rw [image_image]
  calc
    e.val.toFinset.image (fun v => Sum.inr (coreLabel A code v)) =
        labelledEdge G U Z code e := by
      apply image_congr
      intro v hv
      exact (hlabel v hv).symm
    _ = p.val.image Sum.inr := hlabels

omit [DecidableRel G.Adj] in
theorem survivingPool_joining_card_le (R : SimpleGraph V)
    (U A : I → Finset V) (Z : Finset V) (code : I ↪ Fin 4)
    (hU : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hA : ∀ i j, i ≠ j → Disjoint (A i) (A j))
    (hsub : ∀ i, U i ⊆ A i)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i) (p : LabelPair) :
    (survivingPool G R U Z code (Sum.inr p)).card ≤ (partPairEdges R A code p).card := by
  have h := card_le_card (survivingPool_joining_subset (G := G) R U A Z code hU hA hsub hcover p)
  rwa [card_image_of_injective _ Subtype.val_injective] at h

omit [Fintype V] in
theorem mem_part_union_iff_label (U : I → Finset V) (code : I ↪ Fin 4)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hcover : ∀ v, ∃ i, v ∈ U i) (J : Finset I) (v : V) :
    v ∈ J.biUnion U ↔ coreLabel U code v ∈ J.image code := by
  constructor
  · intro hv
    obtain ⟨i, hiJ, hi⟩ := mem_biUnion.mp hv
    exact mem_image.mpr ⟨i, hiJ, (coreLabel_of_mem U code hdisjoint hi).symm⟩
  · intro hv
    obtain ⟨i, hiJ, hi⟩ := mem_image.mp hv
    obtain ⟨j, hj⟩ := hcover v
    have hij : i = j := code.injective (hi.trans (coreLabel_of_mem U code hdisjoint hj))
    subst j
    exact mem_biUnion.mpr ⟨i, hiJ, hj⟩

/-- A joining pair crossing a label shore contributes actual edges to
the corresponding union-of-parts cut. -/
theorem partPairEdges_subset_cut (R : SimpleGraph V) (U : I → Finset V)
    (code : I ↪ Fin 4)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hcover : ∀ v, ∃ i, v ∈ U i) (J : Finset I) (p : LabelPair)
    (hcross : (p.val ∩ J.image code).card = 1) :
    partPairEdges R U code p ⊆ graphCutEdges R (J.biUnion U) := by
  intro e he
  obtain ⟨heR, heq⟩ := (mem_partPairEdges R U code p e).mp he
  apply mem_filter.mpr
  refine ⟨mem_edgeFinset.mpr heR, ?_⟩
  induction e using Sym2.inductionOn with
  | hf u v =>
    have hp : {coreLabel U code u, coreLabel U code v} = p.val := by
      simpa only [Sym2.toFinset_mk_eq, image_insert, image_singleton] using heq
    have hne : coreLabel U code u ≠ coreLabel U code v := by
      intro hh
      have hc := p.property
      rw [← hp, hh] at hc
      simp at hc
    have hcross' : (({coreLabel U code u, coreLabel U code v} : Finset (Fin 4)).filter
        (fun j => j ∈ J.image code)).card = 1 := by
      simpa only [filter_mem_eq_inter, hp] using hcross
    rw [crosses_pair, mem_part_union_iff_label U code hdisjoint hcover J u,
      mem_part_union_iff_label U code hdisjoint hcover J v]
    by_cases hu : coreLabel U code u ∈ J.image code
    · by_cases hv : coreLabel U code v ∈ J.image code
      · simp only [filter_insert, filter_singleton, hu, hv, if_true] at hcross'
        simp [hne] at hcross'
      · exact Or.inl ⟨hu, hv⟩
    · by_cases hv : coreLabel U code v ∈ J.image code
      · exact Or.inr ⟨hv, hu⟩
      · simp only [filter_insert, filter_singleton, hu, hv, if_false, card_empty] at hcross'
        norm_num at hcross'

/-- Disjoint actual joining-pair pools sum to the whole-cut supply in
the enlarged partition. The assertion applies to every union of parts. -/
theorem forest_cut_supply (R : SimpleGraph V) (U : I → Finset V)
    (code : I ↪ Fin 4)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hcover : ∀ v, ∃ i, v ∈ U i)
    (F₀ : Finset LabelPair) (r : ℕ)
    (hsupply : ∀ p ∈ F₀, r ≤ (partPairEdges R U code p).card) (J : Finset I) :
    r * forestCutCount F₀ (J.image code) ≤ graphCutCount R (J.biUnion U) := by
  let A := F₀.filter (fun p => (p.val ∩ J.image code).card = 1)
  have hsub : A.biUnion (partPairEdges R U code) ⊆ graphCutEdges R (J.biUnion U) := by
    intro e he
    obtain ⟨p, hp, he⟩ := mem_biUnion.mp he
    exact partPairEdges_subset_cut R U code hdisjoint hcover J p (mem_filter.mp hp).2 he
  have hdis : (A : Set LabelPair).PairwiseDisjoint (partPairEdges R U code) := by
    intro p _ q _ hpq
    exact partPairEdges_disjoint R U code p q hpq
  have hcard := Finset.card_biUnion hdis
  have hsum : ∑ p ∈ A, r ≤ ∑ p ∈ A, (partPairEdges R U code p).card :=
    sum_le_sum (fun p hp => hsupply p (mem_filter.mp hp).1)
  have hle := (hsum.trans_eq hcard.symm).trans (card_le_card hsub)
  simpa only [sum_const, smul_eq_mul, Nat.mul_comm, A, forestCutCount, graphCutCount] using hle

/-- Public whole-cut interface for the actual pair supply in the final
partition. -/
theorem forest_supply_of_pair_supply (R : SimpleGraph V) (U : I → Finset V)
    (code : I ↪ Fin 4) (F₀ : Finset LabelPair) (r : ℕ)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hcover : ∀ v, ∃ i, v ∈ U i)
    (hsupply : ∀ p ∈ F₀, r ≤ (partPairEdges R U code p).card) :
    ∀ J : Finset I,
      r * forestCutCount F₀ (J.image code) ≤ graphCutCount R (J.biUnion U) :=
  forest_cut_supply R U code hdisjoint hcover F₀ r hsupply

end Overfull.Patterns
