import Overfull.NativeReserve.CutSafety
import Overfull.NativeReserve.NativeCutWeights

/-!
# Cut certificates from the retained joining matchings

Whole shores have the parity of each actual matching cut. On even shores,
every matching that contributes an incident crossing contributes at least
two crossing copies. These facts certify both whole cuts and all toggles.
-/

noncomputable section

namespace Overfull.TerminalFourTwoOdd

open Finset Classical Multigraph NativeReserve ForceMatching
open scoped BigOperators

variable {V E I : Type*} [Fintype E] [Fintype I]

private theorem card_matching_partition (M : I → Finset E)
    (hdisj : Pairwise (fun i j => Disjoint (M i) (M j)))
    (T : Finset E) (hcover : T ⊆ univ.biUnion M) :
    T.card = ∑ i, (T ∩ M i).card := by
  have heq : T = univ.biUnion (fun i => T ∩ M i) := by
    ext e
    simp only [mem_biUnion, mem_univ, true_and, mem_inter]
    constructor
    · intro he
      obtain ⟨i, _, hi⟩ := mem_biUnion.mp (hcover he)
      exact ⟨i, he, hi⟩
    · rintro ⟨i, he, _⟩
      exact he
  rw [heq, card_biUnion]
  intro i _ j _ hij
  exact (hdisj hij).mono inter_subset_right inter_subset_right

private theorem cutOn_inter (G : Multigraph V E) (M : Finset E) (X : Finset V) :
    G.cutOn M X = G.cutEdges X ∩ M := by
  ext e
  simp only [mem_cutOn, mem_inter, mem_cutEdges]
  tauto

omit [Fintype I] in
theorem matching_partition_odd_cut (G : Multigraph V E) (k : ℕ)
    (M : Fin k → Finset E) (hdisj : Pairwise (fun i j => Disjoint (M i) (M j)))
    (X : Finset V) (hcover : G.cutEdges X ⊆ univ.biUnion M)
    (hparity : ∀ i, (G.cutOn (M i) X).card % 2 = 1) :
    k ≤ G.cutSize X := by
  have hcard := card_matching_partition M hdisj (G.cutEdges X) hcover
  calc
    k = ∑ _i : Fin k, 1 := by simp
    _ ≤ ∑ i : Fin k, (G.cutEdges X ∩ M i).card := by
      apply sum_le_sum
      intro i _
      have hi := hparity i
      rw [cutOn_inter] at hi
      omega
    _ = G.cutSize X := hcard.symm

omit [Fintype I] in
theorem matching_partition_even_incidence (G : Multigraph V E) (k : ℕ)
    (M : Fin k → Finset E) (hM : ∀ i, G.IsMatching (M i))
    (hdisj : Pairwise (fun i j => Disjoint (M i) (M j)))
    (X : Finset V) (hcover : G.cutEdges X ⊆ univ.biUnion M)
    (hparity : ∀ i, (G.cutOn (M i) X).card % 2 = 0) (v : V) :
    2 * cutIncidence G X v ≤ G.cutSize X := by
  have hcut := card_matching_partition M hdisj (G.cutEdges X) hcover
  have hinc := card_matching_partition M hdisj (G.cutEdges X ∩ G.incidenceEdges v)
    (fun _ he => hcover (mem_inter.mp he).1)
  unfold cutIncidence
  rw [hinc, mul_sum]
  change _ ≤ (G.cutEdges X).card
  rw [hcut]
  apply sum_le_sum
  intro i _
  have hsmall : ((G.cutEdges X ∩ G.incidenceEdges v) ∩ M i).card ≤ 1 := by
    apply card_le_one.mpr
    intro e he f hf
    exact hM i e (mem_inter.mp he).2 f (mem_inter.mp hf).2 v
      ((G.mem_incidenceEdges v e).mp (mem_inter.mp (mem_inter.mp he).1).2)
      ((G.mem_incidenceEdges v f).mp (mem_inter.mp (mem_inter.mp hf).1).2)
  have hsub : (G.cutEdges X ∩ G.incidenceEdges v) ∩ M i ⊆ G.cutEdges X ∩ M i := by
    intro e he
    exact mem_inter.mpr ⟨(mem_inter.mp (mem_inter.mp he).1).1, (mem_inter.mp he).2⟩
  have hle := card_le_card hsub
  have hp := hparity i
  rw [cutOn_inter] at hp
  omega

/-- Covering all copies outside the cores covers every whole-core cut. -/
theorem whole_cut_covered (G : Multigraph V E) (U : I → Finset V) (Z : Finset V)
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hZ : ∀ i, Disjoint (U i) Z) (M : Finset E)
    (hcover : ∀ e, (∀ i, e ∉ G.internalEdges (U i)) → e ∈ M)
    (X : Finset V) (hX : X ∈ wholeUnions U Z) : G.cutEdges X ⊆ M := by
  intro e he
  apply hcover e
  intro i hi
  have hends := (G.mem_internalEdges (U i) e).mp hi
  exact (G.mem_cutEdges X e).mp he
    (propext (whole_core_membership_iff (U i) X
      (wholeUnions_whole U Z X hdisj hZ hX i) hends.1 hends.2))

theorem whole_matching_cut_parity (G : Multigraph V E) (U : I → Finset V) (Z : Finset V)
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (M : Finset E) (hM : G.IsMatching M)
    (hZ : Z ⊆ G.edgeSupport M) (hparity : ∀ i, Even (U i \ G.edgeSupport M).card)
    (X : Finset V) (hX : X ∈ wholeUnions U Z) :
    (G.cutOn M X).card % 2 = X.card % 2 := by
  exact ((hM.uncovered_even_iff_cut_parity G X).mp
    (even_uncovered_whole_union U Z (G.edgeSupport M) hdisj hZ hparity X hX)).symm

end Overfull.TerminalFourTwoOdd
