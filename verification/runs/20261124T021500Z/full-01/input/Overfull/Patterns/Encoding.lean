import Overfull.Patterns.Compression
import Mathlib.Data.Fintype.Powerset

/-!
# Finite boundary patterns with fixed core labels

A pattern records an exceptional matching, one core label at every
exceptional vertex, and a forest of joining pairs on the four core labels.
The unused assignment at a paired exceptional vertex is fixed to zero.
-/

noncomputable section

namespace Overfull.Patterns

open Finset Classical SimpleGraph Compression FractionalMatching MatchingProbability
open scoped BigOperators

/-- An unordered pair of distinct exceptional vertices. -/
abbrev ExceptionalPair (E : Type*) := {P : Finset E // P.card = 2}

/-- The finite ambient type of boundary patterns. The graph-level encoding
below supplies the matching, coverage, and forest restrictions. -/
structure Pattern (E : Type*) [Fintype E] where
  internalPairs : Finset (ExceptionalPair E)
  assignment : E → Fin 4
  forest : Finset LabelPair
  deriving Fintype

noncomputable def patternEquiv (E : Type*) [Fintype E] :
    Pattern E ≃ Finset (ExceptionalPair E) × (E → Fin 4) × Finset LabelPair where
  toFun P := ⟨P.internalPairs,P.assignment,P.forest⟩
  invFun P := ⟨P.1,P.2.1,P.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The exact finite bound used in the manuscript. -/
def patternBound (t : ℕ) : ℕ := 2^(t.choose 2)*4^t*2^6

@[simp] theorem card_labelPair : Fintype.card LabelPair = 6 := by
  norm_num [LabelPair, Fintype.card_finset_len, Nat.choose]

@[simp] theorem card_pattern (E : Type*) [Fintype E] :
    Fintype.card (Pattern E) = patternBound (Fintype.card E) := by
  rw [Fintype.card_congr (patternEquiv E)]
  simp [patternBound, Fintype.card_prod, ExceptionalPair, LabelPair, Nat.choose, Nat.mul_assoc]

theorem patternBound_mono : Monotone patternBound := by
  intro s t hst
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul
    (Nat.pow_le_pow_right (by omega : 0 < 2) (Nat.choose_le_choose 2 hst))
    (Nat.pow_le_pow_right (by omega : 0 < 4) hst))

theorem card_pattern_le (E : Type*) [Fintype E] (t : ℕ)
    (ht : Fintype.card E ≤ t) : Fintype.card (Pattern E) ≤ patternBound t := by
  rw [card_pattern]
  exact patternBound_mono ht

/-- A vertex is paired when it lies in an exceptional pair of the pattern. -/
def Pattern.Paired {E : Type*} [Fintype E] (P : Pattern E) (z : E) : Prop :=
  ∃ p ∈ P.internalPairs, z ∈ p.val

variable {V I : Type*} [Fintype V] [DecidableEq V]

/-- The exceptional pairs actually present in a subgraph. -/
noncomputable def actualInternalPairs (G : SimpleGraph V) (Z : Finset V)
    (F : G.Subgraph) : Finset (ExceptionalPair Z) :=
  univ.filter (fun p => ∃ z ∈ p.val, ∃ w ∈ p.val, F.Adj z.val w.val)

@[simp] theorem mem_actualInternalPairs (G : SimpleGraph V) (Z : Finset V)
    (F : G.Subgraph) (p : ExceptionalPair Z) :
    p ∈ actualInternalPairs G Z F ↔
      ∃ z ∈ p.val, ∃ w ∈ p.val, F.Adj z.val w.val := by
  simp [actualInternalPairs]

/-- The internal exceptional edge with its unordered endpoints. -/
def exceptionalPair {Z : Finset V} (z w : Z) (hne : z ≠ w) : ExceptionalPair Z :=
  ⟨{z,w}, by simp [hne]⟩

theorem exceptionalPair_mem_iff (G : SimpleGraph V) (Z : Finset V)
    (F : G.Subgraph) (z w : Z) (hne : z ≠ w) :
    exceptionalPair z w hne ∈ actualInternalPairs G Z F ↔ F.Adj z.val w.val := by
  rw [mem_actualInternalPairs]
  constructor
  · rintro ⟨u,hu,v,hv,huv⟩
    have hu' : u = z ∨ u = w := by simpa [exceptionalPair] using hu
    have hv' : v = z ∨ v = w := by simpa [exceptionalPair] using hv
    rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl
    · exact False.elim (G.loopless _ (F.adj_sub huv))
    · exact huv
    · exact F.symm huv
    · exact False.elim (G.loopless _ (F.adj_sub huv))
  · intro h
    exact ⟨z,by simp [exceptionalPair],w,by simp [exceptionalPair],h⟩

/-- Assign an unpaired exceptional vertex to the label of its matching
neighbor. Paired vertices, and uncovered vertices in an arbitrary input
subgraph, receive the fixed unused value zero. -/
noncomputable def actualAssignment (G : SimpleGraph V) (U : I → Finset V)
    (Z : Finset V) (code : I ↪ Fin 4) (F : G.Subgraph) (z : Z) : Fin 4 :=
  if _hpair : ∃ w : Z, F.Adj z.val w.val then 0
  else if h : ∃ v, F.Adj z.val v then coreLabel U code h.choose else 0

omit [DecidableEq V] in
theorem actualAssignment_paired (G : SimpleGraph V) (U : I → Finset V)
    (Z : Finset V) (code : I ↪ Fin 4) (F : G.Subgraph) (z : Z)
    (hp : ∃ w : Z, F.Adj z.val w.val) :
    actualAssignment G U Z code F z = 0 := by
  simp [actualAssignment, hp]

omit [DecidableEq V] in
theorem actualAssignment_of_adj (G : SimpleGraph V) (U : I → Finset V)
    (Z : Finset V) (code : I ↪ Fin 4) (F : G.Subgraph) (hF : F.IsMatching)
    (z : Z) (hp : ¬ ∃ w : Z, F.Adj z.val w.val)
    (v : V) (hv : F.Adj z.val v) :
    actualAssignment G U Z code F z = coreLabel U code v := by
  have hex : ∃ w, F.Adj z.val w := ⟨v,hv⟩
  have heq : hex.choose = v := (hF (F.edge_vert hv)).unique hex.choose_spec hv
  simp [actualAssignment, hp, hex, heq]

/-- This relation identifies every component of the finite pattern with
actual edges. It also records the covered exceptional set, absence of
core-internal edges, and the injective projection of joining edges. -/
structure Encodes (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : I → Finset V) (Z : Finset V) (code : I ↪ Fin 4)
    (F : G.Subgraph) (P : Pattern Z) : Prop where
  matching : F.IsMatching
  covered : (Z : Set V) ⊆ F.verts
  internal_pairs : P.internalPairs = actualInternalPairs G Z F
  assigned : P.assignment = actualAssignment G U Z code F
  no_core_internal : ∀ i u v, u ∈ U i → v ∈ U i → ¬ F.Adj u v
  projection : ∃ label : G.edgeSet → LabelPair,
    (∀ e ∈ nonexceptionalEdges G F Z,
      (label e).val = {coreLabel U code (firstEnd e), coreLabel U code (secondEnd e)}) ∧
    Set.InjOn label (nonexceptionalEdges G F Z) ∧
    P.forest = (nonexceptionalEdges G F Z).image label
  forest : LeafForest P.forest

/-- Fixed-code compressed matchings have finite boundary patterns. -/
theorem exists_encoding (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : I → Finset V) (Z : Finset V) (code : I ↪ Fin 4)
    (F : G.Subgraph) (hF : F.IsMatching) (hcovered : (Z : Set V) ⊆ F.verts)
    (hno : ∀ i u v, u ∈ U i → v ∈ U i → ¬ F.Adj u v)
    (hforest : JoiningForestWithCode G U Z code F) :
    ∃ P : Pattern Z, Encodes G U Z code F P := by
  obtain ⟨label,_hcard,hlabel,hinj,hforest⟩ := hforest
  exact ⟨⟨actualInternalPairs G Z F,actualAssignment G U Z code F,
      (nonexceptionalEdges G F Z).image label⟩,
    hF,hcovered,rfl,rfl,hno,⟨label,hlabel,hinj,rfl⟩,hforest⟩

theorem Encodes.assignment_of_adj {G : SimpleGraph V} [DecidableRel G.Adj]
    {U : I → Finset V} {Z : Finset V} {code : I ↪ Fin 4}
    {F : G.Subgraph} {P : Pattern Z} (hP : Encodes G U Z code F P)
    (z : Z) (hp : ¬ ∃ w : Z, F.Adj z.val w.val)
    (v : V) (hv : F.Adj z.val v) : P.assignment z = coreLabel U code v := by
  rw [hP.assigned]
  exact actualAssignment_of_adj G U Z code F hP.matching z hp v hv

/-- Every unpaired exceptional vertex is assigned to an actual core and
has an edge of the compressed matching into that core. -/
theorem Encodes.assignment_represented {G : SimpleGraph V} [DecidableRel G.Adj]
    {U : I → Finset V} {Z : Finset V} {code : I ↪ Fin 4}
    {F : G.Subgraph} {P : Pattern Z} (hP : Encodes G U Z code F P)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (z : Z) (hp : ¬ ∃ w : Z, F.Adj z.val w.val) :
    ∃ i v, P.assignment z = code i ∧ v ∈ U i ∧ F.Adj z.val v := by
  obtain ⟨v,hv,_huniq⟩ := hP.matching (hP.covered z.property)
  have hvZ : v ∉ Z := fun hh => hp ⟨⟨v,hh⟩,hv⟩
  obtain ⟨i,hi⟩ := (hcover v).resolve_left hvZ
  exact ⟨i,v,(hP.assignment_of_adj z hp v hv).trans
    (coreLabel_of_mem U code hdisjoint hi),hi,hv⟩

theorem Encodes.paired_iff {G : SimpleGraph V} [DecidableRel G.Adj]
    {U : I → Finset V} {Z : Finset V} {code : I ↪ Fin 4}
    {F : G.Subgraph} {P : Pattern Z} (hP : Encodes G U Z code F P) (z : Z) :
    P.Paired z ↔ ∃ w : Z, F.Adj z.val w.val := by
  constructor
  · rintro ⟨p,hp,hzp⟩
    rw [hP.internal_pairs,mem_actualInternalPairs] at hp
    obtain ⟨u,v,huv,hpval⟩ := Finset.card_eq_two.mp p.property
    have hadj : F.Adj u.val v.val := by
      have heq : p = exceptionalPair u v huv := Subtype.ext hpval
      rw [← mem_actualInternalPairs,heq] at hp
      exact (exceptionalPair_mem_iff G Z F u v huv).mp hp
    rw [hpval] at hzp
    have hz : z = u ∨ z = v := by simpa using hzp
    rcases hz with rfl | rfl
    · exact ⟨v,hadj⟩
    · exact ⟨u,F.symm hadj⟩
  · rintro ⟨w,hw⟩
    have hne : z ≠ w := by
      intro h
      subst w
      exact G.loopless _ (F.adj_sub hw)
    refine ⟨exceptionalPair z w hne,?_,by simp [exceptionalPair]⟩
    rw [hP.internal_pairs]
    exact (exceptionalPair_mem_iff G Z F z w hne).mpr hw

theorem Encodes.internal_pair_adj {G : SimpleGraph V} [DecidableRel G.Adj]
    {U : I → Finset V} {Z : Finset V} {code : I ↪ Fin 4}
    {F : G.Subgraph} {P : Pattern Z} (hP : Encodes G U Z code F P)
    (p : ExceptionalPair Z) (hp : p ∈ P.internalPairs)
    (z w : Z) (hends : p.val = {z,w}) : F.Adj z.val w.val := by
  have hne : z ≠ w := by
    intro hz
    have hc := p.property
    rw [hends,hz] at hc
    simp at hc
  have heq : p = exceptionalPair z w hne := Subtype.ext hends
  rw [hP.internal_pairs,heq] at hp
  exact (exceptionalPair_mem_iff G Z F z w hne).mp hp

/-- One fixed coding works simultaneously for compression and finite
pattern encoding. Every witness refers to actual host edges. -/
theorem exists_compressed_encoding (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : I → Finset V) (Z : Finset V) (code : I ↪ Fin 4)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hUZ : ∀ i, Disjoint (U i) Z)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (M : G.Subgraph) (hM : M.IsPerfectMatching) :
    ∃ F : G.Subgraph, ∃ P : Pattern Z,
      Encodes G U Z code F P ∧ F ≤ M ∧
      (∀ u v, M.Adj u v → u ∈ Z ∨ v ∈ Z → F.Adj u v) ∧
      F.edgeSet.ncard ≤ Z.card+3 ∧ F.verts.ncard ≤ 2*Z.card+6 ∧
      (∀ i, (F.verts.toFinset ∩ U i).card ≤ 2*Z.card+6) ∧
      (∀ i, Even (((U i : Set V) \ F.verts).ncard)) := by
  obtain ⟨F,hF,hFM,hretain,hcovered,hE,hV,hcore,heven,hno,hforest⟩ :=
    exists_compressed_matching_fixed_code G U Z code hdisjoint hUZ hcover M hM
  obtain ⟨P,hP⟩ := exists_encoding G U Z code F hF hcovered hno hforest
  exact ⟨F,P,hP,hFM,hretain,hE,hV,hcore,heven⟩

end Overfull.Patterns
