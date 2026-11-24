import Overfull.CircuitPatterns.Boundary
import Overfull.CircuitPatterns.Forest
import Overfull.Absorption.CoreFamily

/-!
# Part-order parity after absorbing a boundary pattern

When the frequent pattern has no internal exceptional edge, each
exceptional vertex contributes once to the cut of its assigned old core
and once to that core's enlargement. These two contributions cancel
modulo two, leaving exactly the degree of the joining forest.
-/

noncomputable section

namespace Overfull.CircuitPatterns

open Finset Classical SimpleGraph Compression FractionalMatching MatchingProbability

variable {E : Type*} [Fintype E]

/-- The number of exceptional vertices assigned to one fixed core label. -/
def Pattern.assignedCount (P : Pattern E) (i : Fin 4) : ℕ :=
  (univ.filter (fun z => P.assignment z = i)).card

variable [DecidableEq E]

/-- Without internal exceptional pairs, a singleton core cut consists of
its assigned exceptional edges and the incident joining-forest edges. -/
theorem Pattern.singleton_core_cutCount (P : Pattern E)
    (hno : P.internalPairs = ∅) (i : Fin 4) :
    P.cutCount {Sum.inr i} = P.assignedCount i + pairDegree P.forest i := by
  let edge : E → Finset (E ⊕ Fin 4) := fun z =>
    {Sum.inl z, Sum.inr (P.assignment z)}
  let pair : LabelPair → Finset (E ⊕ Fin 4) := fun p => p.val.image Sum.inr
  have hedge : Function.Injective edge := by
    intro z w heq
    have hz : Sum.inl z ∈ edge w := by rw [← heq]; simp [edge]
    simpa [edge] using hz
  have hpair : Function.Injective pair := by
    intro p q heq
    apply Subtype.ext
    exact Finset.image_injective Sum.inr_injective heq
  have hboundary : P.boundaryEdges = univ.image edge ∪ P.forest.image pair := by
    simp [Pattern.boundaryEdges, Pattern.Paired, hno, edge, pair]
  have htest (A : Finset (E ⊕ Fin 4)) :
      (A.filter (fun v => v ∈ ({Sum.inr i} : Finset (E ⊕ Fin 4)))).card = 1 ↔
        Sum.inr i ∈ A := by
    rw [filter_mem_eq_inter, inter_singleton]
    by_cases hi : Sum.inr i ∈ A <;> simp [hi]
  have hfiltered :
      P.boundaryEdges.filter (fun A =>
        (A.filter (fun v => v ∈ ({Sum.inr i} : Finset (E ⊕ Fin 4)))).card = 1) =
      P.boundaryEdges.filter (fun A => Sum.inr i ∈ A) := by
    ext A
    simp only [mem_filter, htest]
  have hleft : (univ.image edge).filter (fun A => Sum.inr i ∈ A) =
      (univ.filter (fun z => P.assignment z = i)).image edge := by
    rw [filter_image]
    congr 1
    ext z
    simp [edge, eq_comm]
  have hright : (P.forest.image pair).filter (fun A => Sum.inr i ∈ A) =
      (P.forest.filter (fun p => i ∈ p.val)).image pair := by
    rw [filter_image]
    congr 1
    ext p
    simp [pair]
  have hdisjoint : Disjoint
      ((univ.filter (fun z => P.assignment z = i)).image edge)
      ((P.forest.filter (fun p => i ∈ p.val)).image pair) := by
    apply disjoint_left.mpr
    intro A hA hB
    obtain ⟨z, _, rfl⟩ := mem_image.mp hA
    obtain ⟨p, _, hp⟩ := mem_image.mp hB
    have hz : Sum.inl z ∈ pair p := by rw [hp]; simp [edge]
    simp [pair] at hz
  unfold Pattern.cutCount
  rw [hfiltered, hboundary, filter_union, hleft, hright,
    card_union_of_disjoint hdisjoint, card_image_of_injective _ hedge,
    card_image_of_injective _ hpair]
  rfl

variable {V I : Type*} [Fintype V] [DecidableEq V] [DecidableEq I]

omit [Fintype V] in
/-- A graph-level assignment realizing the fixed label assignment has
exactly the corresponding finite pattern fiber sizes. -/
theorem assignedCount_eq_absorbedAt_card (Z : Finset V) (P : Pattern Z)
    (code : I ↪ Fin 4) (assignment : V → I)
    (hassignment : ∀ z : Z, P.assignment z = code (assignment z.val)) (i : I) :
    P.assignedCount (code i) = (Absorption.absorbedAt Z assignment i).card := by
  have hset : ((univ : Finset Z).filter (fun z => P.assignment z = code i)).image
      Subtype.val = Absorption.absorbedAt Z assignment i := by
    ext v
    constructor
    · intro hv
      obtain ⟨z, hz, rfl⟩ := mem_image.mp hv
      have hh := (mem_filter.mp hz).2
      rw [hassignment z] at hh
      exact (Absorption.mem_absorbedAt Z assignment i z.val).mpr
        ⟨z.property, code.injective hh⟩
    · intro hv
      obtain ⟨hvZ, hvi⟩ := (Absorption.mem_absorbedAt Z assignment i v).mp hv
      refine mem_image.mpr ⟨⟨v, hvZ⟩, mem_filter.mpr ⟨mem_univ _, ?_⟩, rfl⟩
      rw [hassignment, hvi]
  have hc := congrArg Finset.card hset
  rw [card_image_of_injective _ Subtype.val_injective] at hc
  exact hc

variable {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableEq I] in
/-- The absence of internal exceptional pairs constructs a genuine
assignment to the original core indices, compatible with the fixed code.
Values outside the exceptional set are irrelevant and may be arbitrary. -/
theorem Encodes.exists_core_assignment [Nonempty I]
    {U : I → Finset V} {Z : Finset V} {code : I ↪ Fin 4}
    {F : G.Subgraph} {P : Pattern Z} (hP : Encodes G U Z code F P)
    (hno : P.internalPairs = ∅)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i) :
    ∃ assignment : V → I,
      ∀ z : Z, P.assignment z = code (assignment z.val) := by
  have hex (z : Z) : ∃ i, P.assignment z = code i := by
    have hn : ¬ ∃ w : Z, F.Adj z.val w.val := by
      rw [← hP.paired_iff z]
      simp [Pattern.Paired, hno]
    obtain ⟨i, _, hi, _, _⟩ := hP.assignment_represented hdisjoint hcover z hn
    exact ⟨i, hi⟩
  choose assign hassigned using hex
  let assignment : V → I := fun v =>
    if hv : v ∈ Z then assign ⟨v, hv⟩ else Classical.choice inferInstance
  refine ⟨assignment, fun z => ?_⟩
  simpa [assignment, z.property] using hassigned z

/-- The cardinality of an actual enlarged part has the parity of the
joining-forest degree. Its parity is derived from an encoded matching's
uncovered-core parity; it is not an additional hypothesis. -/
theorem Encodes.enlarged_part_parity
    {U : I → Finset V} {Z : Finset V} {code : I ↪ Fin 4}
    {F : G.Subgraph} {P : Pattern Z} (hP : Encodes G U Z code F P)
    (hno : P.internalPairs = ∅)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hUZ : ∀ i, Disjoint (U i) Z)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (hparity : ∀ i, Even (((U i : Set V) \ F.verts).ncard))
    (assignment : V → I)
    (hassignment : ∀ z : Z, P.assignment z = code (assignment z.val)) (i : I) :
    (Absorption.enlargedSets U Z assignment i).card % 2 =
      pairDegree P.forest (code i) % 2 := by
  have hcut := hP.whole_cut_count {Sum.inr (code i)}
  rw [wholeUnion_single_core U Z code hdisjoint hUZ hcover i] at hcut
  have hp := (matching_uncovered_even_iff_cut_parity F hP.matching (U i)).mp (hparity i)
  rw [hcut, P.singleton_core_cutCount hno,
    assignedCount_eq_absorbedAt_card Z P code assignment hassignment i] at hp
  have hcard : (Absorption.enlargedSets U Z assignment i).card =
      (U i).card + (Absorption.absorbedAt Z assignment i).card := by
    apply card_union_of_disjoint
    exact Absorption.absorbedAt_disjoint_old U Z Z assignment hUZ (subset_refl _) i i
  omega

/-- When the four actual enlarged parts are odd, the encoded joining
forest is one of the explicitly listed perfect matchings or stars. -/
theorem Encodes.forestShape_of_odd_enlarged
    {U : I → Finset V} {Z : Finset V} {code : I ↪ Fin 4}
    {F : G.Subgraph} {P : Pattern Z} (hP : Encodes G U Z code F P)
    (hno : P.internalPairs = ∅)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hUZ : ∀ i, Disjoint (U i) Z)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (hparity : ∀ i, Even (((U i : Set V) \ F.verts).ncard))
    (assignment : V → I)
    (hassignment : ∀ z : Z, P.assignment z = code (assignment z.val))
    (hcode : Function.Surjective code)
    (hodd : ∀ i, (Absorption.enlargedSets U Z assignment i).card % 2 = 1) :
    LabelForestShape P.forest := by
  apply odd_leafForest_classification P.forest hP.forest
  intro j
  obtain ⟨i, rfl⟩ := hcode j
  rw [← hP.enlarged_part_parity hno hdisjoint hUZ hcover hparity assignment hassignment i]
  exact hodd i

/-- For four original cores, any embedding into the four fixed labels is
already surjective, so the all-odd conclusion needs no extra coding
assumption. -/
theorem Encodes.forestShape_of_four_odd_enlarged [Fintype I]
    {U : I → Finset V} {Z : Finset V} {code : I ↪ Fin 4}
    {F : G.Subgraph} {P : Pattern Z} (hP : Encodes G U Z code F P)
    (hno : P.internalPairs = ∅)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hUZ : ∀ i, Disjoint (U i) Z)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (hparity : ∀ i, Even (((U i : Set V) \ F.verts).ncard))
    (assignment : V → I)
    (hassignment : ∀ z : Z, P.assignment z = code (assignment z.val))
    (hfour : Fintype.card I = 4)
    (hodd : ∀ i, Odd (Absorption.enlargedSets U Z assignment i).card) :
    LabelForestShape P.forest := by
  have hcode : Function.Surjective code :=
    ((Fintype.bijective_iff_injective_and_card code).mpr
      ⟨code.injective, by simpa using hfour⟩).2
  exact hP.forestShape_of_odd_enlarged hno hdisjoint hUZ hcover hparity
    assignment hassignment hcode (fun i => Nat.odd_iff.mp (hodd i))

end Overfull.CircuitPatterns
