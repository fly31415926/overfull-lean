import Overfull.CompatibleCircuits.FourLabel
import Overfull.CompatibleCircuits.Lifting
import Overfull.CircuitPatterns.Forest
import Overfull.FourOdd.PairPools

/-!
# Decompositions of the actual joining copies of four odd parts

The primary pieces project injectively to one of the three perfect matchings
or four three-edge stars on the labels. Every other piece consists of two
distinct parallel projected copies and is an actual matching. Thus the
surplus pieces are genuine compatible circuits of length two.
-/

noncomputable section

namespace Overfull.FourOdd

open Finset Classical Compression CircuitPatterns

variable {V E : Type*}

/-- The exact primary shape in the four-odd-parts assertion. -/
def IsPrimary (label : E → LabelPair) (M : Finset E) : Prop :=
  Set.InjOn label M ∧ LabelForestShape (M.image label)

/-- Two distinct copies with the same unordered pair of part labels. -/
def IsParallelPair (label : E → LabelPair) (M : Finset E) : Prop :=
  M.card = 2 ∧ ∀ e ∈ M, ∀ f ∈ M, label e = label f

theorem IsPrimary.nonempty {label : E → LabelPair} {M : Finset E}
    (h : IsPrimary label M) : M.Nonempty := by
  by_contra hn
  have hz : M = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
  have hf := h.2
  rw [hz, Finset.image_empty] at hf
  exact (by decide : ¬ LabelForestShape ∅) hf

theorem IsParallelPair.nonempty {label : E → LabelPair} {M : Finset E}
    (h : IsParallelPair label M) : M.Nonempty := by
  apply Finset.card_pos.mp
  rw [h.1]
  decide

/-- A partition of all specified actual copies, with exactly `h` primary
pieces. The remaining pieces are actual matching parallel pairs. -/
structure Decomposition (G : Multigraph V E) (label : E → LabelPair)
    (C : Finset E) (h : ℕ) where
  parts : Finset (Finset E)
  primary : Finset (Finset E)
  primary_subset : primary ⊆ parts
  primary_card : primary.card = h
  nonempty : ∀ M ∈ parts, M.Nonempty
  matching : ∀ M ∈ parts, G.IsMatching M
  primary_shape : ∀ M ∈ primary, IsPrimary label M
  surplus_shape : ∀ M ∈ parts, M ∉ primary → IsParallelPair label M
  disjoint : ∀ M ∈ parts, ∀ N ∈ parts, M ≠ N → Disjoint M N
  cover : parts.biUnion id = C

namespace Decomposition

variable {G : Multigraph V E} {label : E → LabelPair}
variable {C D : Finset E} {h k : ℕ}

theorem part_subset (P : Decomposition G label C h)
    {M : Finset E} (hM : M ∈ P.parts) : M ⊆ C := by
  rw [← P.cover]
  exact Finset.subset_biUnion_of_mem id hM

theorem parts_disjoint_of_disjoint (P : Decomposition G label C h)
    (R : Decomposition G label D k) (hCD : Disjoint C D) :
    Disjoint P.parts R.parts := by
  apply Finset.disjoint_left.mpr
  intro M hM hMR
  obtain ⟨e, he⟩ := P.nonempty M hM
  exact Finset.disjoint_left.mp hCD (P.part_subset hM he) (R.part_subset hMR he)

theorem cross_disjoint (P : Decomposition G label C h)
    (R : Decomposition G label D k) (hCD : Disjoint C D)
    {M N : Finset E} (hM : M ∈ P.parts) (hN : N ∈ R.parts) :
    Disjoint M N :=
  hCD.mono (P.part_subset hM) (R.part_subset hN)

def empty (G : Multigraph V E) (label : E → LabelPair) :
    Decomposition G label ∅ 0 where
  parts := ∅
  primary := ∅
  primary_subset := by simp
  primary_card := by simp
  nonempty := by simp
  matching := by simp
  primary_shape := by simp
  surplus_shape := by simp
  disjoint := by simp
  cover := by simp

def singlePrimary (G : Multigraph V E) (label : E → LabelPair)
    (M : Finset E) (hM : G.IsMatching M) (hshape : IsPrimary label M) :
    Decomposition G label M 1 where
  parts := {M}
  primary := {M}
  primary_subset := by rfl
  primary_card := by simp
  nonempty := by intro N hN; simpa only [Finset.mem_singleton.mp hN] using hshape.nonempty
  matching := by intro N hN; simpa only [Finset.mem_singleton.mp hN] using hM
  primary_shape := by intro N hN; simpa only [Finset.mem_singleton.mp hN] using hshape
  surplus_shape := by simp
  disjoint := by simp
  cover := by simp

def singlePair (G : Multigraph V E) (label : E → LabelPair)
    (M : Finset E) (hM : G.IsMatching M) (hshape : IsParallelPair label M) :
    Decomposition G label M 0 where
  parts := {M}
  primary := ∅
  primary_subset := by simp
  primary_card := by simp
  nonempty := by intro N hN; simpa only [Finset.mem_singleton.mp hN] using hshape.nonempty
  matching := by intro N hN; simpa only [Finset.mem_singleton.mp hN] using hM
  primary_shape := by simp
  surplus_shape := by intro N hN _; simpa only [Finset.mem_singleton.mp hN] using hshape
  disjoint := by simp
  cover := by simp

/-- Join decompositions on disjoint original copy sets. -/
def union (P : Decomposition G label C h) (R : Decomposition G label D k)
    (hCD : Disjoint C D) : Decomposition G label (C ∪ D) (h + k) := by
  have hprimary : Disjoint P.primary R.primary :=
    (P.parts_disjoint_of_disjoint R hCD).mono P.primary_subset R.primary_subset
  refine {
    parts := P.parts ∪ R.parts
    primary := P.primary ∪ R.primary
    primary_subset := ?_
    primary_card := ?_
    nonempty := ?_
    matching := ?_
    primary_shape := ?_
    surplus_shape := ?_
    disjoint := ?_
    cover := ?_ }
  · exact Finset.union_subset_union P.primary_subset R.primary_subset
  · rw [Finset.card_union_of_disjoint hprimary, P.primary_card, R.primary_card]
  · intro M hM
    rcases Finset.mem_union.mp hM with hM | hM
    · exact P.nonempty M hM
    · exact R.nonempty M hM
  · intro M hM
    rcases Finset.mem_union.mp hM with hM | hM
    · exact P.matching M hM
    · exact R.matching M hM
  · intro M hM
    rcases Finset.mem_union.mp hM with hM | hM
    · exact P.primary_shape M hM
    · exact R.primary_shape M hM
  · intro M hM hn
    rcases Finset.mem_union.mp hM with hM | hM
    · exact P.surplus_shape M hM (fun h => hn (Finset.mem_union_left _ h))
    · exact R.surplus_shape M hM (fun h => hn (Finset.mem_union_right _ h))
  · intro M hM N hN hne
    rcases Finset.mem_union.mp hM with hM | hM <;>
      rcases Finset.mem_union.mp hN with hN | hN
    · exact P.disjoint M hM N hN hne
    · exact P.cross_disjoint R hCD hM hN
    · exact (P.cross_disjoint R hCD hN hM).symm
    · exact R.disjoint M hM N hN hne
  · calc
      _ = P.parts.biUnion id ∪ R.parts.biUnion id := by
        ext e
        simp only [Finset.mem_biUnion, Finset.mem_union, id_eq]
        aesop
      _ = C ∪ D := congrArg₂ (· ∪ ·) P.cover R.cover

/-- Change only the displayed covered set and primary count. -/
def cast (P : Decomposition G label C h) (hCD : C = D) (hhk : h = k) :
    Decomposition G label D k := hCD ▸ hhk ▸ P

/-- A disjoint indexed family of genuine primary pieces is a decomposition
with the exact cardinality of that index type. -/
def ofPrimaryFamily {I : Type*} [Fintype I]
    (G : Multigraph V E) (label : E → LabelPair) (M : I → Finset E)
    (hM : ∀ i, G.IsMatching (M i)) (hshape : ∀ i, IsPrimary label (M i))
    (hdisj : Pairwise (fun i j => Disjoint (M i) (M j))) :
    Decomposition G label (univ.biUnion M) (Fintype.card I) := by
  have hinj : Function.Injective M := by
    intro i j hij
    by_contra hne
    obtain ⟨e, he⟩ := (hshape i).nonempty
    exact Finset.disjoint_left.mp (hdisj hne) he (hij ▸ he)
  refine {
    parts := univ.image M
    primary := univ.image M
    primary_subset := by rfl
    primary_card := by rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
    nonempty := ?_
    matching := ?_
    primary_shape := ?_
    surplus_shape := by simp
    disjoint := ?_
    cover := ?_ }
  · intro N hN
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hN
    exact (hshape i).nonempty
  · intro N hN
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hN
    exact hM i
  · intro N hN
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hN
    exact hshape i
  · intro N hN N' hN' hne
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hN
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hN'
    exact hdisj (fun h => hne (congrArg M h))
  · ext e
    simp

/-- A disjoint indexed family of actual parallel matching pairs consists
entirely of surplus circuits and contributes no primary piece. -/
def ofParallelFamily {I : Type*} [Fintype I]
    (G : Multigraph V E) (label : E → LabelPair) (M : I → Finset E)
    (hM : ∀ i, G.IsMatching (M i)) (hshape : ∀ i, IsParallelPair label (M i))
    (hdisj : Pairwise (fun i j => Disjoint (M i) (M j))) :
    Decomposition G label (univ.biUnion M) 0 := by
  refine {
    parts := univ.image M
    primary := ∅
    primary_subset := by simp
    primary_card := by simp
    nonempty := ?_
    matching := ?_
    primary_shape := by simp
    surplus_shape := ?_
    disjoint := ?_
    cover := ?_ }
  · intro N hN
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hN
    exact (hshape i).nonempty
  · intro N hN
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hN
    exact hM i
  · intro N hN _
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hN
    exact hshape i
  · intro N hN N' hN' hne
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hN
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hN'
    exact hdisj (fun h => hne (congrArg M h))
  · ext e
    simp

/-- Finite assembly preserves exact coverage and adds only the actual
numbers of primary pieces. -/
theorem exists_biUnion {I : Type*} (S : Finset I) (C : I → Finset E) (h : I → ℕ)
    (P : ∀ i, Decomposition G label (C i) (h i))
    (hdisj : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (C i) (C j)) :
    Nonempty (Decomposition G label (S.biUnion C) (∑ i ∈ S, h i)) := by
  revert hdisj
  induction S using Finset.induction_on with
  | empty =>
    intro _
    simpa using (show Nonempty (Decomposition G label ∅ 0) from ⟨empty G label⟩)
  | @insert i S hi ih =>
    intro hdisj
    have hS : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (C i) (C j) := by
      intro j hj k hk hne
      exact hdisj j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hne
    obtain ⟨R⟩ := ih hS
    have hc : Disjoint (C i) (S.biUnion C) := by
      apply Finset.disjoint_left.mpr
      intro e he hiS
      obtain ⟨j, hj, hej⟩ := Finset.mem_biUnion.mp hiS
      have hij : i ≠ j := fun h => hi (h.symm ▸ hj)
      exact Finset.disjoint_left.mp
        (hdisj i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj) hij) he hej
    simpa only [Finset.biUnion_insert, Finset.sum_insert hi] using
      (show Nonempty (Decomposition G label (C i ∪ S.biUnion C) (h i + ∑ j ∈ S, h j))
        from ⟨(P i).union R hc⟩)

/-- Reuse an actual matching-pair partition when every pair has a constant
projected label. All its pieces are surplus circuits. -/
def ofPairPartition (P : MatchingPairPartition G C)
    (hlabel : ∀ M ∈ P.parts, ∀ e ∈ M, ∀ f ∈ M, label e = label f) :
    Decomposition G label C 0 where
  parts := P.parts
  primary := ∅
  primary_subset := by simp
  primary_card := by simp
  nonempty := by
    intro M hM
    apply Finset.card_pos.mp
    rw [P.card_two M hM]
    decide
  matching := P.matching
  primary_shape := by simp
  surplus_shape := by
    intro M hM _
    exact ⟨P.card_two M hM, hlabel M hM⟩
  disjoint := P.disjoint
  cover := P.cover

end Decomposition

/-- The surplus-pair formulation gives the manuscript's actual circuit
conclusion in the quotient, with the stronger length bound two. -/
theorem IsParallelPair.isCircuit (Q : Multigraph (Fin 4) E)
    {M : Finset E} (hM : IsParallelPair Q.edgeLabelPair M) : Q.IsCircuit M := by
  obtain ⟨e, f, hne, rfl⟩ := Finset.card_eq_two.mp hM.1
  exact Q.isCircuit_parallel_pair hne
    ((Q.edgeLabelPair_eq_iff e f).mp (hM.2 e (by simp) f (by simp)))

end Overfull.FourOdd
