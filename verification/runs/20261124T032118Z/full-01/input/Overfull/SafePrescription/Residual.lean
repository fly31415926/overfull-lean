import Overfull.SafePrescription.Classification

namespace Overfull.SafePrescription

open Finset Classical MatchingProbability FractionalMatching ForceMatching
open scoped BigOperators

variable {V I : Type*} [Fintype V] [Fintype I]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The actual matching edges that are not internal to a specified core. -/
noncomputable def exteriorEdges (U : I → Finset V) (N : G.Subgraph) : Finset G.edgeSet :=
  (matchingEdges N).filter (fun e => ¬ ∃ i, firstEnd e ∈ U i ∧ secondEnd e ∈ U i)

theorem matchingEdges_card_ncard (N : G.Subgraph) :
    (matchingEdges N).card = N.edgeSet.ncard := by
  have himage : (matchingEdges N).image Subtype.val = N.edgeSet.toFinset := by
    ext e
    simp only [mem_image, matchingEdges, mem_filter, mem_univ, true_and, Set.mem_toFinset]
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact hf
    · intro he
      exact ⟨⟨e, N.edgeSet_subset he⟩, he, rfl⟩
  have hcard := congrArg Finset.card himage
  rw [card_image_of_injective _ Subtype.val_injective] at hcard
  exact hcard.trans (Set.ncard_eq_toFinset_card' _).symm

/-- Completing a prescribed matching only inside cores adds no exterior edge. -/
theorem exteriorEdges_subset_prescribed (U : I → Finset V) (F N : G.Subgraph)
    (hedges : ∀ v w, N.Adj v w → F.Adj v w ∨ ∃ i, v ∈ U i ∧ w ∈ U i) :
    exteriorEdges G U N ⊆ matchingEdges F := by
  intro e he
  obtain ⟨heN, hext⟩ := mem_filter.mp he
  have hadj : N.Adj (firstEnd e) (secondEnd e) := by
    change s(firstEnd e, secondEnd e) ∈ N.edgeSet
    rw [edge_eq e]
    exact (mem_filter.mp heN).2
  rcases hedges _ _ hadj with heF | hi
  · apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    rw [← edge_eq e]
    exact heF
  · exact False.elim (hext hi)

theorem exteriorEdges_card_le (U : I → Finset V) (F N : G.Subgraph) (L : ℕ)
    (hedges : ∀ v w, N.Adj v w → F.Adj v w ∨ ∃ i, v ∈ U i ∧ w ∈ U i)
    (hF : F.edgeSet.ncard ≤ L) : (exteriorEdges G U N).card ≤ L := by
  calc
    _ ≤ (matchingEdges F).card := card_le_card (exteriorEdges_subset_prescribed G U F N hedges)
    _ = F.edgeSet.ncard := matchingEdges_card_ncard G F
    _ ≤ L := hF

/-- A whole-core union is crossed only by actual exterior matching edges. -/
theorem matching_cut_le_exterior_of_whole (U : I → Finset V) (N : G.Subgraph)
    (X : Finset V) (hwhole : ∀ i, U i ⊆ X ∨ Disjoint (U i) X) :
    cutCount (matchingEdges N) X ≤ (exteriorEdges G U N).card := by
  apply card_le_card
  intro e he
  obtain ⟨heN, hcross⟩ := mem_filter.mp he
  apply mem_filter.mpr
  refine ⟨heN, ?_⟩
  rintro ⟨i, hi, hj⟩
  exact hcross (propext (same_core_membership U X hwhole hi hj))

/-- Total core minority at most one bounds the cut of any actual perfect
matching by its exterior edge count plus one. -/
theorem matching_cut_le_exterior_add_one (U : I → Finset V) (Z : Finset V)
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hUZ : ∀ i, Disjoint (U i) Z)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (N : G.Subgraph) (hN : N.IsPerfectMatching) (X : Finset V)
    (hminority : (∑ i, min (X ∩ U i).card (U i \ X).card) ≤ 1) :
    cutCount (matchingEdges N) X ≤ (exteriorEdges G U N).card + 1 := by
  rcases classified_of_minority U Z X hUZ hcover hminority with hX | ⟨Y, hY, v, rfl⟩
  · have hwhole := wholeUnions_whole U Z X hdisj hUZ hX
    exact (matching_cut_le_exterior_of_whole G U N X hwhole).trans (Nat.le_add_right _ _)
  · have hwhole := wholeUnions_whole U Z Y hdisj hUZ hY
    have hcut := matching_cut_le_exterior_of_whole G U N Y hwhole
    have htoggle := cut_toggle (matchingEdges N) Y v
    rw [incidentCount_matching N hN v] at htoggle
    omega

/-- A violating residual shore with small total core minority already had
a small cut in the original graph. All counts refer to actual matching edges. -/
theorem original_cut_lt_of_overfull (U : I → Finset V) (Z : Finset V)
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hUZ : ∀ i, Disjoint (U i) Z)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (h : ℕ) (hregular : ∀ v, G.degree v = h)
    (N : G.Subgraph) (hN : N.IsPerfectMatching) (L : ℕ)
    (hexterior : (exteriorEdges G U N).card ≤ L) (X : Finset V)
    (hminority : (∑ i, min (X ∩ U i).card (U i \ X).card) ≤ 1)
    (hover : IsOverfull (G \ N.spanningCoe) (h-1) X) :
    X.card % 2 = 1 ∧ cutCount (univ : Finset G.edgeSet) X < h+L := by
  have hregularR : ∀ v, (G \ N.spanningCoe).degree v = h-1 := remaining_regular hregular N hN
  have hodd : X.card % 2 = 1 := by
    by_contra hn
    exact not_overfull_of_even_card (G \ N.spanningCoe) X (h-1)
      (fun v => (hregularR v).le) (by omega) hover
  have hcutR := regular_overfull_cut (G \ N.spanningCoe) (h-1) hregularR X hodd hover
  have hbad : CutFailure N h X := by
    rw [cutFailure_iff_actual_cut, graphCutCount_eq_cutSize]
    convert hcutR using 1
    congr 1
    exact Subsingleton.elim _ _
  have hmatching := matching_cut_le_exterior_add_one G U Z hdisj hUZ hcover N hN X hminority
  have hpartition := cut_partition N X
  unfold CutFailure at hbad
  exact ⟨hodd, by omega⟩

/-- Actual robust residual cores reduce a possible overfull shore to an
original small cut. Classification and the tested matching inequalities
then rule it out, independently of how the internal completion was chosen. -/
theorem residual_no_overfull_of_small_cut_classification
    (U : I → Finset V) (Z : Finset V)
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hUZ : ∀ i, Disjoint (U i) Z)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (h : ℕ) (hregular : ∀ v, G.degree v = h)
    (N : G.Subgraph) (hN : N.IsPerfectMatching) (L : ℕ) (b : ℝ)
    (hexterior : (exteriorEdges G U N).card ≤ L) (hLb : (L : ℝ) ≤ b)
    (𝓧 : Finset (Finset V)) (hsafe : ¬ FamilyFailure N h 𝓧)
    (hclass : ∀ X : Finset V, X.card % 2 = 1 →
      (cutCount (univ : Finset G.edgeSet) X : ℝ) ≤ h+b →
      X ∈ 𝓧 ∨ ∃ Y ∈ 𝓧, ∃ v, X = toggle Y v)
    (H : ∀ i, SimpleGraph (U i))
    (hH : ∀ i, H i ≤ (G \ N.spanningCoe).induce (U i : Set V))
    (α κ ν τ a : ℝ)
    (hα : 0 < α) (hκ : 0 < κ) (hν : 0 < ν) (hτ : 0 ≤ τ)
    (hτα : τ ≤ α/10)
    (hhlo : α*Fintype.card V ≤ (h-1 : ℕ))
    (hhhi : ((h-1 : ℕ) : ℝ) ≤ 2*Fintype.card V)
    (ha : a ≤ α*Fintype.card V/10)
    (hlarge : 3 < ν^2*κ^2*(Fintype.card V : ℝ))
    (hsize : ∀ i, κ*Fintype.card V ≤ ((U i).card : ℝ))
    (hrobust : ∀ i, IsRobustExpander (H i) ν τ)
    (hdegree : ∀ i v, ((h-1 : ℕ) : ℝ)-a ≤ ((H i).degree v : ℝ)) :
    ∀ X : Finset V, ¬ IsOverfull (G \ N.spanningCoe) (h-1) X := by
  let R := G \ N.spanningCoe
  let C : ∀ i, SmallCuts.Core (Multigraph.ofSimpleGraph R) (U i) :=
    fun i => embeddedCore R (U i) (H i) (hH i)
  have hregularR : ∀ v, R.degree v = h-1 := remaining_regular hregular N hN
  intro X hover
  have hodd : X.card % 2 = 1 := by
    by_contra hn
    exact not_overfull_of_even_card R X (h-1) (fun v => (hregularR v).le) (by omega) hover
  have hcutR := regular_overfull_cut R (h-1) hregularR X hodd hover
  have hcutR' : ((Multigraph.ofSimpleGraph R).cutSize X : ℝ) ≤ ((h-1 : ℕ) : ℝ)+0 := by
    have hinst : G.fintypeEdgeSetSdiff N.spanningCoe = R.fintypeEdgeSet := Subsingleton.elim _ _
    simp only [hinst, add_zero]
    exact_mod_cast hcutR.le
  have hbzero : (0 : ℝ) ≤ α*Fintype.card V/10 := by positivity
  have hminority := SmallCuts.minority_sum_le_one (Multigraph.ofSimpleGraph R) U C hdisj
    α κ ν τ a 0 ((h-1 : ℕ) : ℝ) hα hκ hν hτ hτα hhlo hhhi ha hbzero hlarge
    hsize hrobust hdegree X hcutR'
  have horiginal := (original_cut_lt_of_overfull G U Z hdisj hUZ hcover h hregular
    N hN L hexterior X hminority hover).2
  have horiginalR : (cutCount (univ : Finset G.edgeSet) X : ℝ) < h+L := by
    exact_mod_cast horiginal
  have horiginalB : (cutCount (univ : Finset G.edgeSet) X : ℝ) ≤ h+b := by linarith
  have hnot := safe_cut_of_classified N h 𝓧 hsafe X hodd (hclass X hodd horiginalB)
  apply hnot
  rw [cutFailure_iff_actual_cut, graphCutCount_eq_cutSize]
  convert hcutR using 1
  congr 1
  exact Subsingleton.elim _ _

end Overfull.SafePrescription
