import Overfull.Patterns.PairedForests
import Overfull.CompatibleCircuits.FourLabel
import Overfull.CompatibleCircuits.Lifting

/-!
# Actual circuit partitions of the discarded matching copies

An all-odd matching projection on four labels has an actual retained
matching or star. The discarded copies have even projected degrees and
are still an original-graph matching, so endpoint compatibility follows
directly. Ordinary Eulerian decomposition on four labels therefore
partitions them into compatible circuits, each lifting to a matching of
at most four original copies.

The host in this interface consists of joining copies: its endpoint labels
are distinct on every edge. The theorem requires neither a supplied
circuit partition nor the general Fan--Zhang existence theorem.
-/

noncomputable section

namespace Overfull.Patterns

open Finset Classical Compression

variable {V E I : Type*}

/-- The pair label of an actual quotient edge counts the same incidences
as the quotient multigraph, including parallel edge copies. -/
theorem copyDegree_edgeLabelPair (Q : Multigraph (Fin 4) E)
    (C : Finset E) (i : Fin 4) :
    copyDegree C Q.edgeLabelPair i = Q.degreeOn C i := by
  unfold copyDegree Multigraph.degreeOn
  congr 1
  ext e
  simp only [mem_filter, Q.mem_edgeLabelPair]

/-- A retained actual matching forest and a genuine circuit partition of
all discarded copies. The quotient and every partition retain the original
edge-copy type. -/
structure ForestCircuitSplit (G : Multigraph V E) (label : V → Fin 4)
    (hjoin : ∀ e, label (G.firstEnd e) ≠ label (G.secondEnd e)) (M : Finset E) where
  forest : Finset E
  forest_subset : forest ⊆ M
  forest_matching : G.IsMatching forest
  forest_injective : Set.InjOn (G.labelQuotient label hjoin).edgeLabelPair forest
  forest_shape : LabelForestShape (forest.image (G.labelQuotient label hjoin).edgeLabelPair)
  forest_card_le : forest.card ≤ 3
  remainder_even : ∀ i : Fin 4, Even ((G.labelQuotient label hjoin).degreeOn (M \ forest) i)
  circuits : (G.labelQuotient label hjoin).CompatibleCircuitPartition
    (G.endpointClass label) (M \ forest)

namespace ForestCircuitSplit

variable {G : Multigraph V E} {label : V → Fin 4}
variable {hjoin : ∀ e, label (G.firstEnd e) ≠ label (G.secondEnd e)} {M : Finset E}
variable (S : ForestCircuitSplit G label hjoin M)

/-- Each circuit consists of actual discarded original copies. -/
theorem circuit_subset {D : Finset E} (hD : D ∈ S.circuits.parts) :
    D ⊆ M \ S.forest :=
  Multigraph.CompatibleCircuitPartition.part_subset
    (G.labelQuotient label hjoin) S.circuits hD

/-- Endpoint compatibility lifts every circuit to an actual original matching. -/
theorem circuit_matching {D : Finset E} (hD : D ∈ S.circuits.parts) :
    G.IsMatching D :=
  (G.compatible_endpointClass_iff label hjoin D).mp (S.circuits.compatible D hD)

/-- A connected 2-regular quotient circuit has at most four original copies. -/
theorem circuit_card_le {D : Finset E} (hD : D ∈ S.circuits.parts) : D.card ≤ 4 := by
  simpa only [Fintype.card_fin] using (S.circuits.circuit D hD).card_le

/-- The primary forest and all surplus circuits use disjoint actual copies. -/
theorem forest_disjoint_circuits : Disjoint S.forest (S.circuits.parts.biUnion id) := by
  rw [S.circuits.cover]
  exact disjoint_sdiff_self_right

/-- The primary forest and surplus circuits cover the original matching exactly. -/
theorem cover : S.forest ∪ S.circuits.parts.biUnion id = M := by
  rw [S.circuits.cover]
  exact union_sdiff_of_subset S.forest_subset

end ForestCircuitSplit

/-- Construct the retained matching/star and the actual surplus-circuit
partition from an original matching with all four quotient degrees odd. -/
theorem exists_odd_matching_forest_circuit_split (G : Multigraph V E)
    (label : V → Fin 4)
    (hjoin : ∀ e, label (G.firstEnd e) ≠ label (G.secondEnd e))
    (M : Finset E) (hM : G.IsMatching M)
    (hodd : ∀ i : Fin 4, Odd ((G.labelQuotient label hjoin).degreeOn M i)) :
    Nonempty (ForestCircuitSplit G label hjoin M) := by
  let Q := G.labelQuotient label hjoin
  have hoddCopies (i : Fin 4) : Odd (copyDegree M Q.edgeLabelPair i) := by
    rw [copyDegree_edgeLabelPair]
    exact hodd i
  obtain ⟨T, hTM, hTmatching, hinj, hshape, hTcard, hevenCopies⟩ :=
    exists_odd_matching_forest G M Q.edgeLabelPair hM hoddCopies
  have heven (i : Fin 4) : Even (Q.degreeOn (M \ T) i) := by
    rw [← copyDegree_edgeLabelPair]
    exact hevenCopies i
  have hcomp : Q.Compatible (G.endpointClass label) (M \ T) :=
    Multigraph.Compatible.mono Q ((G.compatible_endpointClass_iff label hjoin M).mpr hM)
      sdiff_subset
  obtain ⟨P⟩ := Q.exists_compatibleCircuitPartition_of_compatible
    (G.endpointClass label) (M \ T) hcomp heven
  exact ⟨{
    forest := T
    forest_subset := hTM
    forest_matching := hTmatching
    forest_injective := hinj
    forest_shape := hshape
    forest_card_le := hTcard
    remainder_even := heven
    circuits := P
  }⟩

/-- The same actual construction for an arbitrarily indexed family. -/
theorem exists_matching_family_forest_circuit_splits (G : Multigraph V E)
    (label : V → Fin 4)
    (hjoin : ∀ e, label (G.firstEnd e) ≠ label (G.secondEnd e))
    (M : I → Finset E) (hM : ∀ j, G.IsMatching (M j))
    (hodd : ∀ j (i : Fin 4), Odd ((G.labelQuotient label hjoin).degreeOn (M j) i)) :
    Nonempty (∀ j, ForestCircuitSplit G label hjoin (M j)) :=
  ⟨fun j => Classical.choice
    (exists_odd_matching_forest_circuit_split G label hjoin (M j) (hM j) (hodd j))⟩

/-- Pair the two six-endpoint matching families and partition every paired
union into one retained forest and actual surplus circuits. The odd-sum
hypothesis is supplied for every potential pair, not for a preselected
pairing or a hypothesized circuit decomposition. -/
theorem exists_paired_forest_circuit_splits (G : Multigraph V E)
    (label : V → Fin 4)
    (hjoin : ∀ e, label (G.firstEnd e) ≠ label (G.secondEnd e))
    (u a : ℕ) (M N : Fin u → Finset E)
    (hM : ∀ i, G.IsMatching (M i)) (hN : ∀ i, G.IsMatching (N i))
    (hsizeM : ∀ i, (G.edgeSupport (M i)).card ≤ 6)
    (hsizeN : ∀ i, (G.edgeSupport (N i)).card ≤ 6)
    (hloadM : ∀ v, (univ.filter (fun i => v ∈ G.edgeSupport (M i))).card ≤ a)
    (hloadN : ∀ v, (univ.filter (fun i => v ∈ G.edgeSupport (N i))).card ≤ a)
    (hsize : 12 * a < u)
    (hodd : ∀ i j (k : Fin 4), Odd
      ((G.labelQuotient label hjoin).degreeOn (M i) k +
        (G.labelQuotient label hjoin).degreeOn (N j) k)) :
    ∃ f : Equiv.Perm (Fin u),
      Nonempty (∀ i, ForestCircuitSplit G label hjoin (M i ∪ N (f i))) ∧
      ∀ i, Disjoint (G.edgeSupport (M i)) (G.edgeSupport (N (f i))) := by
  obtain ⟨f, hsupports, hmatching⟩ := exists_six_endpoint_pairing G u a M N
    hM hN hsizeM hsizeN hloadM hloadN hsize
  refine ⟨f, ?_, hsupports⟩
  apply exists_matching_family_forest_circuit_splits G label hjoin
    (fun i => M i ∪ N (f i)) hmatching
  intro i k
  rw [← copyDegree_edgeLabelPair, copyDegree_union_of_disjoint _ _ _
    (disjoint_copies_of_disjoint_support G _ _ (hsupports i)),
    copyDegree_edgeLabelPair, copyDegree_edgeLabelPair]
  exact hodd i (f i) k

/-- Across a finite family, all original copies remain covered by the
retained forests and the actual circuit partitions. -/
theorem forest_circuit_splits_cover [Fintype I] (G : Multigraph V E)
    (label : V → Fin 4)
    (hjoin : ∀ e, label (G.firstEnd e) ≠ label (G.secondEnd e))
    (M : I → Finset E) (S : ∀ i, ForestCircuitSplit G label hjoin (M i)) :
    univ.biUnion (fun i => (S i).forest) ∪
        univ.biUnion (fun i => (S i).circuits.parts.biUnion id) = univ.biUnion M := by
  have hremainders : (fun i => (S i).circuits.parts.biUnion id) =
      (fun i => M i \ (S i).forest) := funext (fun i => (S i).circuits.cover)
  rw [hremainders]
  exact selected_family_remainders_cover M (fun i => (S i).forest)
    (fun i => (S i).forest_subset)

/-- Distinct original family members give disjoint circuit remainders;
the forest union is disjoint from the union of all surplus circuits. -/
theorem forest_circuit_splits_disjoint [Fintype I] (G : Multigraph V E)
    (label : V → Fin 4)
    (hjoin : ∀ e, label (G.firstEnd e) ≠ label (G.secondEnd e))
    (M : I → Finset E) (S : ∀ i, ForestCircuitSplit G label hjoin (M i))
    (hM : Pairwise (fun i j => Disjoint (M i) (M j))) :
    Pairwise (fun i j => Disjoint (S i).forest (S j).forest) ∧
    Pairwise (fun i j => Disjoint ((S i).circuits.parts.biUnion id)
      ((S j).circuits.parts.biUnion id)) ∧
    Disjoint (univ.biUnion (fun i => (S i).forest))
      (univ.biUnion (fun i => (S i).circuits.parts.biUnion id)) := by
  have hremainders : (fun i => (S i).circuits.parts.biUnion id) =
      (fun i => M i \ (S i).forest) := funext (fun i => (S i).circuits.cover)
  refine ⟨selected_family_pairwise_disjoint M (fun i => (S i).forest)
    hM (fun i => (S i).forest_subset), ?_, ?_⟩
  · intro i j hij
    rw [(S i).circuits.cover, (S j).circuits.cover]
    exact (hM hij).mono sdiff_subset sdiff_subset
  · rw [hremainders]
    exact selected_family_remainders_disjoint M (fun i => (S i).forest)
      hM (fun i => (S i).forest_subset)

end Overfull.Patterns
