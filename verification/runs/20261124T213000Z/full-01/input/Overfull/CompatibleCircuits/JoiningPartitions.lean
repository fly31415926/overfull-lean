import Overfull.CompatibleCircuits.AtMostThree
import Overfull.CompatibleCircuits.QuotientCuts

/-!
# Exact lifting of joining-copy circuit partitions

Every quotient part is mapped through the injective subtype projection, so
the original multigraph copies, disjointness, and complete coverage survive.
The host wrappers derive quotient admissibility and parity from the checked
regular-host cut bounds. These are supporting joining decompositions, not
the complete two-core factorization or a palette/completion construction.
-/

noncomputable section

namespace Overfull.FourOdd

open Finset Classical

variable {V E I : Type*} [Fintype E] [DecidableEq I]
    (G : Multigraph V E) (label : V → I)

/-- Subtype projection takes an actual joining-copy matching to a host matching. -/
theorem joiningGraph_isMatching_image {D : Finset (joiningCopies G label)}
    (hD : (joiningGraph G label).IsMatching D) :
    G.IsMatching (D.image Subtype.val) := by
  intro e he f hf v hve hvf
  obtain ⟨e', he', rfl⟩ := mem_image.mp he
  obtain ⟨f', hf', rfl⟩ := mem_image.mp hf
  exact congrArg Subtype.val (hD e' he' f' hf' v hve hvf)

/-- The lifted family consists of finite sets of the original host copies. -/
def liftJoiningParts {C : Finset (joiningCopies G label)}
    (P : (joiningQuotient G label).CompatibleCircuitPartition
      ((joiningGraph G label).endpointClass label) C) : Finset (Finset E) :=
  P.parts.image (fun D => D.image Subtype.val)

variable {C : Finset (joiningCopies G label)}
    (P : (joiningQuotient G label).CompatibleCircuitPartition
      ((joiningGraph G label).endpointClass label) C)

/-- No circuit part disappears under the original-copy injection. -/
theorem liftJoiningParts_nonempty {M : Finset E}
    (hM : M ∈ liftJoiningParts G label P) : M.Nonempty := by
  obtain ⟨D, hD, rfl⟩ := mem_image.mp hM
  exact (P.circuit D hD).1.image _

/-- Every lifted circuit part is a matching in the original multigraph. -/
theorem liftJoiningParts_isMatching {M : Finset E}
    (hM : M ∈ liftJoiningParts G label P) : G.IsMatching M := by
  obtain ⟨D, hD, rfl⟩ := mem_image.mp hM
  apply joiningGraph_isMatching_image G label
  exact ((joiningGraph G label).compatible_endpointClass_iff label
    (joiningGraph_join G label) D).mp (P.compatible D hD)

/-- The size bound counts original copies, including parallel multiplicity. -/
theorem liftJoiningParts_card_le [Fintype I] {M : Finset E}
    (hM : M ∈ liftJoiningParts G label P) : M.card ≤ Fintype.card I := by
  obtain ⟨D, hD, rfl⟩ := mem_image.mp hM
  rw [card_image_of_injective _ Subtype.val_injective]
  exact (P.circuit D hD).card_le

/-- Distinct lifted parts have no common original copy. -/
theorem liftJoiningParts_disjoint {M N : Finset E}
    (hM : M ∈ liftJoiningParts G label P)
    (hN : N ∈ liftJoiningParts G label P) (hne : M ≠ N) : Disjoint M N := by
  obtain ⟨D, hD, rfl⟩ := mem_image.mp hM
  obtain ⟨D', hD', rfl⟩ := mem_image.mp hN
  apply (Finset.disjoint_image Subtype.val_injective).mpr
  apply P.disjoint D hD D' hD'
  intro h
  apply hne
  exact congrArg (fun S : Finset (joiningCopies G label) => S.image Subtype.val) h

/-- Exact coverage commutes with the injective original-copy projection. -/
theorem liftJoiningParts_cover :
    (liftJoiningParts G label P).biUnion id = C.image Subtype.val := by
  have hcover : P.parts.biUnion id = C := by
    convert P.cover using 1
    congr
    exact Subsingleton.elim _ _
  unfold liftJoiningParts
  rw [Finset.image_biUnion]
  change P.parts.biUnion (fun D => D.image Subtype.val) = C.image Subtype.val
  rw [← Finset.biUnion_image]
  change (P.parts.biUnion id).image Subtype.val = C.image Subtype.val
  exact congrArg (fun S : Finset (joiningCopies G label) => S.image Subtype.val) hcover

/-- Distinct actual circuit parts are never merged by subtype projection. -/
theorem liftJoiningParts_card : (liftJoiningParts G label P).card = P.parts.card := by
  exact card_image_of_injective _ (Finset.image_injective Subtype.val_injective)

/-- A complete quotient partition covers precisely all original joining copies. -/
theorem liftJoiningParts_cover_univ
    (P : (joiningQuotient G label).CompatibleCircuitPartition
      ((joiningGraph G label).endpointClass label) univ) :
    (liftJoiningParts G label P).biUnion id = joiningCopies G label := by
  rw [liftJoiningParts_cover]
  ext e
  constructor
  · intro he
    obtain ⟨f, _, rfl⟩ := mem_image.mp he
    exact f.property
  · intro he
    exact mem_image.mpr ⟨⟨e, he⟩, mem_univ _, rfl⟩

/-- The completed small-quotient theorem yields an exact partition of the
host's actual joining copies into nonempty matchings of at most three copies. -/
theorem exists_joining_matching_partition_of_card_le_three [Fintype I]
    (hI : Fintype.card I ≤ 3)
    (hadmissible : (joiningQuotient G label).AdmissibleOn
      ((joiningGraph G label).endpointClass label) univ)
    (heven : ∀ i, Even ((joiningQuotient G label).degree i)) :
    ∃ parts : Finset (Finset E),
      (∀ M ∈ parts, M.Nonempty ∧ G.IsMatching M ∧ M.card ≤ 3) ∧
      (∀ M ∈ parts, ∀ N ∈ parts, M ≠ N → Disjoint M N) ∧
      parts.biUnion id = joiningCopies G label := by
  obtain ⟨P⟩ := (joiningQuotient G label).exists_compatibleCircuitPartition_of_card_le_three
    hI ((joiningGraph G label).endpointClass label) univ hadmissible heven
  refine ⟨liftJoiningParts G label P, ?_, ?_, liftJoiningParts_cover_univ G label P⟩
  · intro M hM
    exact ⟨liftJoiningParts_nonempty G label P hM,
      liftJoiningParts_isMatching G label P hM,
      (liftJoiningParts_card_le G label P hM).trans hI⟩
  · intro M hM N hN hne
    exact liftJoiningParts_disjoint G label P hM hN hne

variable [Fintype V] [Fintype I]

/-- All-even label fibers give the exact joining matching partition directly
from regularity and no overfull set, with no separate class or joining bound. -/
theorem exists_joining_matching_partition_of_even_fibers
    (hI : Fintype.card I ≤ 3) {h : ℕ}
    (hregular : ∀ v, G.degree v = h)
    (hno : ∀ X : Finset V, ¬ G.IsOverfull h X)
    (hfibers : ∀ i, (univ.filter (fun v => label v = i)).card % 2 = 0) :
    ∃ parts : Finset (Finset E),
      (∀ M ∈ parts, M.Nonempty ∧ G.IsMatching M ∧ M.card ≤ 3) ∧
      (∀ M ∈ parts, ∀ N ∈ parts, M ≠ N → Disjoint M N) ∧
      parts.biUnion id = joiningCopies G label := by
  apply exists_joining_matching_partition_of_card_le_three G label hI
  · exact joiningQuotient_admissible_of_even_fibers G label hregular hno hfibers
  · exact joiningQuotient_degree_even_of_even_fibers G label hregular hfibers

/-- An even regular degree and an explicit half-degree joining bound provide
a second sufficient host interface. This is not a full factorization theorem. -/
theorem exists_joining_matching_partition_of_even_degree_bound
    (hI : Fintype.card I ≤ 3) {h D : ℕ}
    (hregular : ∀ v, G.degree v = h)
    (hno : ∀ X : Finset V, ¬ G.IsOverfull h X) (heven : Even h)
    (hD : ∀ v, G.degreeOn (joiningCopies G label) v ≤ D) (hhalf : 2 * D ≤ h) :
    ∃ parts : Finset (Finset E),
      (∀ M ∈ parts, M.Nonempty ∧ G.IsMatching M ∧ M.card ≤ 3) ∧
      (∀ M ∈ parts, ∀ N ∈ parts, M ≠ N → Disjoint M N) ∧
      parts.biUnion id = joiningCopies G label := by
  apply exists_joining_matching_partition_of_card_le_three G label hI
  · exact joiningQuotient_admissible_of_degree_bound G label hregular hno hD hhalf
  · exact joiningQuotient_degree_even_of_even_regular G label hregular heven

end Overfull.FourOdd
