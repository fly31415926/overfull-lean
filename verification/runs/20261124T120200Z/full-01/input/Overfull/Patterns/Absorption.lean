import Overfull.Patterns.Assigned
import Overfull.Absorption.CoreFamily

/-!
# Absorbing every exceptional vertex into its reserved pattern core

The residual ambient graph is unchanged. Its actual reserved neighbors
supply the new minimum degree, and the original compressed representative
supplies the parity of each enlarged part.
-/

noncomputable section
namespace Overfull.Patterns
open Finset Classical SimpleGraph Compression MatchingProbability
open scoped BigOperators

variable {V I : Type*} [Fintype V]

/-- A pattern without an exceptional pair gives a represented assignment
of every exceptional vertex to an actual core, extended to all vertices
only to use the existing absorption constructors. -/
theorem Encodes.exists_total_assignment [Nonempty I]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {U : I → Finset V} {Z : Finset V} {code : I ↪ Fin 4}
    {F : G.Subgraph} {P : Pattern Z} (hP : Encodes G U Z code F P)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (hpairs : P.internalPairs = ∅) :
    ∃ assignment : V → I, ∀ z : Z, P.assignment z = code (assignment z.val) := by
  classical
  have hrep (z : Z) : ∃ i, P.assignment z = code i := by
    have hnpaired : ¬ P.Paired z := by simp [Pattern.Paired,hpairs]
    have hn : ¬ ∃ w : Z, F.Adj z.val w.val := by
      simpa only [← hP.paired_iff z] using hnpaired
    obtain ⟨i,_v,hi,_hvi,_hadj⟩ := hP.assignment_represented hdisjoint hcover z hn
    exact ⟨i,hi⟩
  choose chosen hchosen using hrep
  let assignment : V → I := fun v => if h : v ∈ Z then chosen ⟨v,h⟩ else Classical.choice inferInstance
  refine ⟨assignment,?_⟩
  intro z
  simpa [assignment,z.property] using hchosen z

/-- The actual enlarged core set is exactly its assigned quotient shore. -/
theorem enlargedSets_eq_assigned_shore
    (U : I → Finset V) (Z : Finset V) (code : I ↪ Fin 4)
    (P : Pattern Z) (assignment : V → I)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hUZ : ∀ i, Disjoint (U i) Z)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (hassignment : ∀ z : Z, P.assignment z = code (assignment z.val)) (i : I) :
    Absorption.enlargedSets U Z assignment i =
      wholeUnion U Z code (P.assignedShore (code i)) := by
  classical
  ext v
  simp only [Absorption.enlargedSets,mem_union,Absorption.mem_absorbedAt,mem_wholeUnion]
  by_cases hvZ : v ∈ Z
  · have hvU : v ∉ U i := fun hv => disjoint_left.mp (hUZ i) hv hvZ
    simp only [hvU,false_or,hvZ,true_and]
    have hvlabel := boundaryLabel_exceptional U Z code (⟨v,hvZ⟩ : Z)
    change boundaryLabel U Z code v = _ at hvlabel
    rw [hvlabel,Pattern.inl_mem_assignedShore,hassignment ⟨v,hvZ⟩]
    exact code.injective.eq_iff.symm
  · simp only [hvZ,false_and,or_false]
    rw [boundaryLabel_outside U Z code v hvZ,Pattern.inr_mem_assignedShore]
    exact (coreLabel_eq_iff U Z code hdisjoint hcover hvZ i).symm

/-- Reserved neighbors give an actual partition into enlarged robust
cores, with the stated common degree error. -/
theorem absorb_all_with_reserved_neighbors
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (U : I → Finset V) (H : ∀ i, SimpleGraph (U i))
    (Z : Finset V) (assignment : V → I) (h r : ℕ) (a a₁ ν τ : ℝ)
    (ha : 0 ≤ a) (ha₁ : 0 ≤ a₁) (hreserve : (h : ℝ)-r ≤ a₁)
    (hdisjoint : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hUZ : ∀ i, Disjoint (U i) Z)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (hembed : ∀ i, H i ≤ R.induce (U i : Set V))
    (hdegree : ∀ i v, (h : ℝ)-a ≤ ((H i).degree v : ℝ))
    (hneighbors : ∀ z ∈ Z, r ≤ (R.neighborFinset z ∩ U (assignment z)).card)
    (hν : 0 ≤ ν) (hντ : ν ≤ τ) (hτ : τ ≤ 1/4)
    (hsmall : ∀ i, (Z.card : ℝ) ≤ ν*(U i).card/4)
    (hrobust : ∀ i, IsRobustExpander (H i) ν τ) :
    let A := Absorption.enlargedSets U Z assignment
    let K := Absorption.enlargedGraphs R U H Z assignment
    Pairwise (fun i j => Disjoint (A i) (A j)) ∧
      (∀ v, ∃ i, v ∈ A i) ∧
      (∀ i, U i ⊆ A i) ∧
      (∀ i, K i ≤ R.induce (A i : Set V)) ∧
      (∀ i v, (h : ℝ)-(a+a₁) ≤ ((K i).degree v : ℝ)) ∧
      (∀ i, IsRobustExpander (K i) (ν/4) (2*τ)) := by
  classical
  dsimp only
  refine ⟨Absorption.enlargedSets_pairwise_disjoint U Z Z assignment hdisjoint hUZ
    subset_rfl,?_,Absorption.old_subset_enlarged U Z assignment,
    Absorption.enlargedGraphs_le_ambient R U H Z assignment hembed,?_,
    Absorption.enlargedGraphs_robust R U H Z Z assignment ν τ hν hντ hτ
      subset_rfl hsmall hrobust⟩
  · intro v
    have hh := Absorption.enlargedSets_cover U Z Z assignment hcover v
    simpa using hh
  · apply Absorption.enlargedGraphs_degree_error R U H Z assignment h a a₁ ha ha₁ hdegree
    intro z hz
    have hh : (r : ℝ) ≤ (R.neighborFinset z ∩ U (assignment z)).card := by
      exact_mod_cast hneighbors z hz
    linarith only [hreserve,hh]

variable [Fintype I]

/-- The graph-level enlarged parts inherit the joining-forest parity of
the distinguished compressed representative. -/
theorem Encodes.enlarged_part_parity
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {U : I → Finset V} {Z : Finset V} {code : I ↪ Fin 4}
    {F : G.Subgraph} {P : Pattern Z} (hP : Encodes G U Z code F P)
    (assignment : V → I)
    (hdisjoint : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hUZ : ∀ i, Disjoint (U i) Z)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (hparity : ∀ i, Even (((U i : Set V) \ F.verts).ncard))
    (hpairs : P.internalPairs = ∅)
    (hassignment : ∀ z : Z, P.assignment z = code (assignment z.val)) (i : I) :
    (Absorption.enlargedSets U Z assignment i).card % 2 =
      pairDegree P.forest (code i) % 2 := by
  rw [enlargedSets_eq_assigned_shore U Z code P assignment
    (fun i j h => hdisjoint h) hUZ hcover hassignment i]
  exact hP.assigned_shore_parity hdisjoint hUZ hcover hparity hpairs (code i)

/-- Four odd actual enlarged parts force the required matching or star. -/
theorem Encodes.enlarged_four_odd_forest
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {U : I → Finset V} {Z : Finset V} {code : I ↪ Fin 4}
    {F : G.Subgraph} {P : Pattern Z} (hP : Encodes G U Z code F P)
    (assignment : V → I) (hI : Fintype.card I = 4)
    (hdisjoint : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hUZ : ∀ i, Disjoint (U i) Z)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (hparity : ∀ i, Even (((U i : Set V) \ F.verts).ncard))
    (hpairs : P.internalPairs = ∅)
    (hassignment : ∀ z : Z, P.assignment z = code (assignment z.val))
    (hodd : ∀ i, (Absorption.enlargedSets U Z assignment i).card % 2 = 1) :
    (P.forest.card = 2 ∧ ∀ i : Fin 4, pairDegree P.forest i = 1) ∨
      ∃ center : Fin 4, P.forest.card = 3 ∧
        ∀ p : LabelPair, p ∈ P.forest ↔ center ∈ p.val := by
  have hcode : Function.Surjective code :=
    ((Fintype.bijective_iff_injective_and_card code).mpr
      ⟨code.injective,by simpa using hI⟩).2
  apply four_odd_label_forest P.forest hP.forest
  intro j
  obtain ⟨i,rfl⟩ := hcode j
  rw [← hP.enlarged_part_parity assignment hdisjoint hUZ hcover hparity hpairs hassignment i]
  exact hodd i

end Overfull.Patterns
