import Overfull.CircuitPatterns.BoundaryRealization
import Overfull.ForeignEdges.Assignment

/-!
# Actual host-edge pools for the boundary pairs

There are at most four pools per exceptional vertex and six joining
pools. Distinct pools are disjoint because every host edge has one fixed
pair of quotient labels.
-/

noncomputable section
namespace Overfull.CircuitPatterns

open Finset Classical SimpleGraph Compression FractionalMatching MatchingProbability
open CircuitPatternRealization
open scoped BigOperators

/-- A permissible boundary pair has an exceptional vertex and a core,
or two different cores. -/
abbrev BoundaryPair (E : Type*) := (E × Fin 4) ⊕ LabelPair

def boundaryPairLabels {E : Type*} [DecidableEq E] : BoundaryPair E → Finset (E ⊕ Fin 4)
  | Sum.inl (z,i) => {Sum.inl z, Sum.inr i}
  | Sum.inr p => p.val.image Sum.inr

@[simp] theorem boundaryPairLabels_exceptional {E : Type*} [DecidableEq E] (z : E) (i : Fin 4) :
    boundaryPairLabels (Sum.inl (z,i) : BoundaryPair E) = {Sum.inl z,Sum.inr i} := rfl

@[simp] theorem boundaryPairLabels_joining {E : Type*} [DecidableEq E] (p : LabelPair) :
    boundaryPairLabels (Sum.inr p : BoundaryPair E) = p.val.image Sum.inr := rfl

theorem boundaryPairLabels_injective {E : Type*} [DecidableEq E] :
    Function.Injective (boundaryPairLabels (E := E)) := by
  classical
  intro p q hpq
  cases p with
  | inl p =>
    cases q with
    | inl q =>
      obtain ⟨z,i⟩ := p
      obtain ⟨w,j⟩ := q
      have hz : Sum.inl z ∈ boundaryPairLabels (Sum.inl (w,j) : BoundaryPair E) := by
        rw [← hpq]; simp
      have hi : Sum.inr i ∈ boundaryPairLabels (Sum.inl (w,j) : BoundaryPair E) := by
        rw [← hpq]; simp
      have hzw : z = w := by simpa using hz
      have hij : i = j := by simpa using hi
      simp [hzw,hij]
    | inr q =>
      obtain ⟨z,i⟩ := p
      have hz : Sum.inl z ∈ boundaryPairLabels (Sum.inr q : BoundaryPair E) := by
        rw [← hpq]; simp
      simp at hz
  | inr p =>
    cases q with
    | inl q =>
      obtain ⟨z,i⟩ := q
      have hz : Sum.inl z ∈ boundaryPairLabels (Sum.inr p : BoundaryPair E) := by
        rw [hpq]; simp
      simp at hz
    | inr q =>
      apply congrArg Sum.inr
      apply Subtype.ext
      exact Finset.image_injective Sum.inr_injective hpq

@[simp] theorem boundaryPairLabels_card {E : Type*} [DecidableEq E] (b : BoundaryPair E) :
    (boundaryPairLabels b).card = 2 := by
  cases b with
  | inl b => obtain ⟨z,i⟩ := b; simp
  | inr p =>
    rw [boundaryPairLabels_joining,Finset.card_image_of_injective _ Sum.inr_injective]
    exact p.property

theorem card_boundaryPair (E : Type*) [Fintype E] :
    Fintype.card (BoundaryPair E) = 4*Fintype.card E+6 := by
  have hp : Fintype.card LabelPair = 6 := by decide
  simp [BoundaryPair,Fintype.card_sum,Fintype.card_prod,hp,Nat.mul_comm]

/-- Every edge of a pattern without internal exceptional pairs is one of
the permitted boundary pairs. -/
theorem boundaryEdge_has_pair {E : Type*} [Fintype E] [DecidableEq E]
    (P : Pattern E) (hP : P.internalPairs = ∅)
    (A : Finset (E ⊕ Fin 4)) (hA : A ∈ P.boundaryEdges) :
    ∃ b : BoundaryPair E, boundaryPairLabels b = A := by
  rw [boundaryEdges_of_no_internal P hP] at hA
  rcases mem_union.mp hA with hA | hA
  · obtain ⟨z,_hz,rfl⟩ := mem_image.mp hA
    exact ⟨Sum.inl (z,P.assignment z),rfl⟩
  · obtain ⟨p,_hp,rfl⟩ := mem_image.mp hA
    exact ⟨Sum.inr p,rfl⟩

variable {V I : Type*} [Fintype V] [DecidableEq V]

def boundaryPool (G : SimpleGraph V) (U : I → Finset V) (Z : Finset V)
    (code : I ↪ Fin 4) (b : BoundaryPair Z) : Finset G.edgeSet :=
  univ.filter (fun e => labelledEdge G U Z code e = boundaryPairLabels b)

@[simp] theorem mem_boundaryPool (G : SimpleGraph V) (U : I → Finset V)
    (Z : Finset V) (code : I ↪ Fin 4) (b : BoundaryPair Z) (e : G.edgeSet) :
    e ∈ boundaryPool G U Z code b ↔
      labelledEdge G U Z code e = boundaryPairLabels b := by
  simp [boundaryPool]

theorem boundaryPools_disjoint (G : SimpleGraph V) (U : I → Finset V)
    (Z : Finset V) (code : I ↪ Fin 4) (b c : BoundaryPair Z) (hne : b ≠ c) :
    Disjoint (boundaryPool G U Z code b) (boundaryPool G U Z code c) := by
  apply disjoint_left.mpr
  intro e he hf
  exact hne (boundaryPairLabels_injective
    ((mem_boundaryPool G U Z code b e).mp he |>.symm.trans
      ((mem_boundaryPool G U Z code c e).mp hf)))

def boundaryPairSpecial (Z : Finset V) : BoundaryPair Z → Finset V
  | Sum.inl (z,_) => {z.val}
  | Sum.inr _ => ∅

def boundaryPairArity {E : Type*} : BoundaryPair E → ℕ
  | Sum.inl _ => 1
  | Sum.inr _ => 2

omit [Fintype V] in
theorem boundaryPairSpecial_eq_image (Z : Finset V) (b : BoundaryPair Z) :
    boundaryPairSpecial Z b = (exceptionalLabels (boundaryPairLabels b)).image Subtype.val := by
  rcases b with ⟨z,i⟩ | p <;> simp [boundaryPairSpecial]

omit [Fintype V] [DecidableEq V] in
theorem boundaryPairArity_eq {E : Type*} [Fintype E] [DecidableEq E] (b : BoundaryPair E) :
    boundaryPairArity b = boundaryArity (boundaryPairLabels b) := by
  rcases b with ⟨z,i⟩ | p <;> simp [boundaryPairArity]

theorem boundaryPool_special (G : SimpleGraph V) (U : I → Finset V)
    (Z : Finset V) (code : I ↪ Fin 4) (b : BoundaryPair Z)
    (e : G.edgeSet) (he : e ∈ boundaryPool G U Z code b) :
    edgeEnds G e ∩ Z = boundaryPairSpecial Z b := by
  have hlabels := (mem_boundaryPool G U Z code b e).mp he
  ext v
  cases b with
  | inl b =>
    obtain ⟨z,i⟩ := b
    simp only [mem_inter,mem_edgeEnds,boundaryPairSpecial,mem_singleton]
    constructor
    · rintro ⟨hv,hvZ⟩
      have h := (inl_mem_labelledEdge G U Z code e ⟨v,hvZ⟩).mpr hv
      rw [hlabels] at h
      have hz : (⟨v,hvZ⟩ : Z) = z := by simpa using h
      exact congrArg Subtype.val hz
    · intro hv
      subst v
      refine ⟨?_,z.property⟩
      apply (inl_mem_labelledEdge G U Z code e z).mp
      rw [hlabels]
      simp
  | inr p =>
    simp only [mem_inter,mem_edgeEnds,boundaryPairSpecial,notMem_empty,iff_false,not_and]
    intro hv hvZ
    have h := (inl_mem_labelledEdge G U Z code e ⟨v,hvZ⟩).mpr hv
    rw [hlabels] at h
    simp at h

theorem boundaryPool_arity (G : SimpleGraph V) (U : I → Finset V)
    (Z : Finset V) (code : I ↪ Fin 4) (b : BoundaryPair Z)
    (e : G.edgeSet) (he : e ∈ boundaryPool G U Z code b) :
    (coreEnds G Z e).card ≤ boundaryPairArity b := by
  have h : (coreEnds G Z e).card + (edgeEnds G e ∩ Z).card = 2 := by
    convert coreEnds_card_add G Z e using 2
    congr 1
    ext v
    simp
  rw [boundaryPool_special G U Z code b e he] at h
  rcases b with ⟨z,i⟩ | p <;>
    simp only [boundaryPairSpecial,card_singleton,card_empty,boundaryPairArity] at * <;> omega

/-- Every pool edge has two different quotient labels, and therefore no
edge of any pool lies inside one of the original cores. -/
theorem boundaryPool_no_internal (G : SimpleGraph V) (U : I → Finset V)
    (Z : Finset V) (code : I ↪ Fin 4)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hUZ : ∀ i, Disjoint (U i) Z)
    (b : BoundaryPair Z) (e : G.edgeSet) (he : e ∈ boundaryPool G U Z code b)
    (i : I) (u v : V) (hu : u ∈ U i) (hv : v ∈ U i) :
    ¬ e.val = s(u,v) := by
  intro heq
  have huZ : u ∉ Z := fun h => disjoint_left.mp (hUZ i) hu h
  have hvZ : v ∉ Z := fun h => disjoint_left.mp (hUZ i) hv h
  have hlabels := (mem_boundaryPool G U Z code b e).mp he
  have heqLabels : labelledEdge G U Z code e = {Sum.inr (code i)} := by
    simp [labelledEdge,heq,Sym2.toFinset_mk_eq,boundaryLabel_outside U Z code u huZ,
      boundaryLabel_outside U Z code v hvZ,coreLabel_of_mem U code hdisjoint hu,
      coreLabel_of_mem U code hdisjoint hv]
  have hc := boundaryPairLabels_card b
  rw [← hlabels,heqLabels] at hc
  simp at hc

/-- The incidence available in a boundary pool at a core vertex is
bounded by the actual degree missing from its embedded core. -/
theorem boundaryPool_incidence_le_error (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : I → Finset V) (Z : Finset V) (code : I ↪ Fin 4)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hUZ : ∀ i, Disjoint (U i) Z)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (H : ∀ i, SimpleGraph (U i)) (hH : ∀ i, H i ≤ G.induce (U i : Set V))
    (k : ℕ) (a : ℝ) (ha : 0 ≤ a)
    (hregular : ∀ v, G.degree v = k)
    (hdegree : ∀ i v, (k : ℝ)-a ≤ (H i).degree v)
    (b : BoundaryPair Z) (v : V) :
    (((boundaryPool G U Z code b).filter (fun e => v ∈ coreEnds G Z e)).card : ℝ) ≤ a := by
  by_cases hvZ : v ∈ Z
  · simpa [coreEnds,hvZ] using ha
  obtain ⟨i,hi⟩ := (hcover v).resolve_left hvZ
  let A := boundaryPool G U Z code b
  let M := selectedMatching G A
  have hle : M.spanningCoe ≤ G \ Replacement.lift (U i) (H i) := by
    rintro u w ⟨huv,he⟩
    refine ⟨huv,?_⟩
    intro hcore
    obtain ⟨hu,hw⟩ := Replacement.lift_adj_mem (U i) (H i) hcore
    exact boundaryPool_no_internal G U Z code hdisjoint hUZ b
      ⟨s(u,w),huv⟩ he i u w hu hw rfl
  have hmdeg := SimpleGraph.degree_le_of_le hle (v := v)
  have hsplit := BipartitePackingAccounting.degree_sdiff_add_of_le G
    (Replacement.lift (U i) (H i)) (Replacement.lift_le (U i) (H i) G (hH i)) v
  rw [Replacement.lift_degree (U i) (H i) ⟨v,hi⟩] at hsplit
  have hsum : M.spanningCoe.degree v + (H i).degree ⟨v,hi⟩ ≤ k := by
    rw [← hregular v]
    simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hmdeg hsplit ⊢
    omega
  have heq : (A.filter (fun e => v ∈ coreEnds G Z e)).card = M.spanningCoe.degree v := by
    calc
      _ = incidentCount A v := by
        unfold incidentCount
        congr 1
        ext e
        simp only [mem_filter,mem_coreEnds,hvZ,not_false_eq_true,and_true]
        rw [incident_iff]
      _ = _ := by
        rw [← selectedMatching_edges G A]
        exact incidentCount_matchingEdges_degree G M v
  change ((A.filter (fun e => v ∈ coreEnds G Z e)).card : ℝ) ≤ a
  rw [heq]
  have hsumR : (M.spanningCoe.degree v : ℝ) + (H i).degree ⟨v,hi⟩ ≤ k := by
    exact_mod_cast hsum
  have hd := hdegree i ⟨v,hi⟩
  linarith

theorem boundaryPool_incidence_le_floor (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : I → Finset V) (Z : Finset V) (code : I ↪ Fin 4)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hUZ : ∀ i, Disjoint (U i) Z)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (H : ∀ i, SimpleGraph (U i)) (hH : ∀ i, H i ≤ G.induce (U i : Set V))
    (k : ℕ) (a : ℝ) (ha : 0 ≤ a)
    (hregular : ∀ v, G.degree v = k)
    (hdegree : ∀ i v, (k : ℝ)-a ≤ (H i).degree v)
    (b : BoundaryPair Z) (v : V) :
    ((boundaryPool G U Z code b).filter (fun e => v ∈ coreEnds G Z e)).card ≤ ⌊a⌋₊ := by
  exact Nat.le_floor (boundaryPool_incidence_le_error G U Z code hdisjoint hUZ hcover
    H hH k a ha hregular hdegree b v)

/-- A used boundary pool contains a core endpoint with positive exterior
incidence. Thus the real error is positive whenever a choice is needed. -/
theorem boundaryPool_nonempty_error_pos (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : I → Finset V) (Z : Finset V) (code : I ↪ Fin 4)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hUZ : ∀ i, Disjoint (U i) Z)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (H : ∀ i, SimpleGraph (U i)) (hH : ∀ i, H i ≤ G.induce (U i : Set V))
    (k : ℕ) (a : ℝ) (ha : 0 ≤ a)
    (hregular : ∀ v, G.degree v = k)
    (hdegree : ∀ i v, (k : ℝ)-a ≤ (H i).degree v)
    (b : BoundaryPair Z) (hb : (boundaryPool G U Z code b).Nonempty) : 0 < a := by
  obtain ⟨e,he⟩ := hb
  have h : (coreEnds G Z e).card + (edgeEnds G e ∩ Z).card = 2 := by
    convert coreEnds_card_add G Z e using 2
    congr 1
    ext v
    simp
  rw [boundaryPool_special G U Z code b e he] at h
  have hs : (boundaryPairSpecial Z b).card ≤ 1 := by
    rcases b with ⟨z,i⟩ | p <;> simp [boundaryPairSpecial]
  have hcore : 0 < (coreEnds G Z e).card := by omega
  obtain ⟨v,hv⟩ := card_pos.mp hcore
  have hcount : 0 < ((boundaryPool G U Z code b).filter (fun e => v ∈ coreEnds G Z e)).card :=
    card_pos.mpr ⟨e,mem_filter.mpr ⟨he,hv⟩⟩
  have hcountR : (0 : ℝ) <
      (((boundaryPool G U Z code b).filter (fun e => v ∈ coreEnds G Z e)).card : ℝ) := by
    exact_mod_cast hcount
  exact hcountR.trans_le (boundaryPool_incidence_le_error G U Z code hdisjoint hUZ hcover
    H hH k a ha hregular hdegree b v)

end Overfull.CircuitPatterns
