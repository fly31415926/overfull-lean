import Overfull.SafePrescription.Boundary
import Overfull.ForceMatching.Probability

namespace Overfull.SafePrescription

open Finset Classical SimpleGraph FractionalMatching MatchingProbability
open scoped BigOperators

variable {V I : Type*} [Fintype V]

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A finite Markov estimate and the cut-failure bound select one actual
perfect matching with both properties. -/
theorem exists_bounded_matching_for_family (h : ℕ) (hh : 0 < h)
    (hregular : ∀ v, G.degree v = h) (hno : ∀ X : Finset V, ¬ IsOverfull G h X)
    (𝓧 : Finset (Finset V)) (E : Finset G.edgeSet) (q : ℕ) (hq : 0 < q)
    (hbudget : 11*(𝓧.card : ℝ)/h + (E.card : ℝ)/h/q < 1) :
    ∃ K : G.Subgraph, K.IsPerfectMatching ∧ ¬ FamilyFailure K h 𝓧 ∧
      (E.filter (fun e => e.val ∈ K.edgeSet)).card ≤ q := by
  classical
  obtain ⟨ι,hι,⟨D⟩⟩ := MatchingProbability.exists_distribution hh hregular hno
  letI := hι
  let count : ι → ℕ := fun i => (E.filter (fun e => e.val ∈ (D.matching i).edgeSet)).card
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hmarkov := probability_markov D.weight D.nonneg (fun i => (count i : ℝ))
    (fun _ => Nat.cast_nonneg _) (q : ℝ) (fun i => q < count i)
    (fun i hi => by
      change (q : ℝ) ≤ (count i : ℝ)
      exact_mod_cast hi.le)
  rw [ForceMatching.Distribution.expected_selected_edges D E] at hmarkov
  have hboundary : probability D.weight (fun i => q < count i) ≤ (E.card : ℝ)/h/q := by
    apply (le_div_iff₀ hqR).mpr
    simpa only [mul_comm] using hmarkov
  have hfailure := D.family_failure_probability hh hregular hno 𝓧
  have hgood : ∃ i, ¬ FamilyFailure (D.matching i) h 𝓧 ∧ count i ≤ q := by
    by_contra hnone
    have hall : ∀ i, FamilyFailure (D.matching i) h 𝓧 ∨ q < count i := by
      intro i
      by_cases hi : FamilyFailure (D.matching i) h 𝓧
      · exact Or.inl hi
      · exact Or.inr (lt_of_not_ge (fun hle => hnone ⟨i,hi,hle⟩))
    have htotal : probability D.weight (fun _ : ι => True) = 1 := by
      simpa only [probability,filter_true] using D.sum_one
    have hone := probability_mono D.weight D.nonneg (fun i (_ : True) => hall i)
    rw [htotal] at hone
    have hunion := probability_union_le D.weight D.nonneg
      (fun i => FamilyFailure (D.matching i) h 𝓧) (fun i => q < count i)
    linarith
  obtain ⟨i,hsafe,hcount⟩ := hgood
  exact ⟨D.matching i,D.perfect i,hsafe,hcount⟩

/-- The sampling constants in Lemma 4.9. The degree comparison uses real
division, so the bound is not weakened by natural-number truncation. -/
theorem exists_bounded_matching (h k₀ t₀ : ℕ)
    (hregular : ∀ v, G.degree v = h) (hno : ∀ X : Finset V, ¬ IsOverfull G h X)
    (𝓧 : Finset (Finset V)) (E : Finset G.edgeSet)
    (hfamily : 44*𝓧.card < h) (hscale : (k₀ : ℝ)/1024 < h)
    (hedges : E.card ≤ (t₀+6)*k₀) :
    ∃ K : G.Subgraph, K.IsPerfectMatching ∧ ¬ FamilyFailure K h 𝓧 ∧
      (E.filter (fun e => e.val ∈ K.edgeSet)).card ≤ 4096*(t₀+6) := by
  have hh : 0 < h := by omega
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hq : 0 < 4096*(t₀+6) := by omega
  apply exists_bounded_matching_for_family h hh hregular hno 𝓧 E (4096*(t₀+6)) hq
  have hfamilyR : 44*(𝓧.card : ℝ) < h := by exact_mod_cast hfamily
  have hfailure : 11*(𝓧.card : ℝ)/h < 1/4 := by
    apply (div_lt_iff₀ hhR).mpr
    linarith
  have hqR : (0 : ℝ) < (4096*(t₀+6) : ℕ) := by exact_mod_cast hq
  have hedgesR : (E.card : ℝ) ≤ ((t₀ : ℝ)+6)*k₀ := by exact_mod_cast hedges
  have hscale' : (k₀ : ℝ) < 1024*(h : ℝ) := by linarith
  have hproduct := mul_lt_mul_of_pos_left hscale' (by positivity : (0 : ℝ) < (t₀ : ℝ)+6)
  have hboundary : (E.card : ℝ)/h/(4096*(t₀+6) : ℕ) < 1/4 := by
    apply (div_lt_iff₀ hqR).mpr
    apply (div_lt_iff₀ hhR).mpr
    push_cast
    nlinarith
  linarith

/-- The sampled matching and its actual fixed boundary submatching. -/
theorem exists_sampled_boundary (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → I) (Z₀ : Finset V) (h k₀ t₀ : ℕ)
    (hregular : ∀ v, G.degree v = h) (hno : ∀ X : Finset V, ¬ IsOverfull G h X)
    (𝓧 : Finset (Finset V)) (hfamily : 44*𝓧.card < h)
    (hscale : (k₀ : ℝ)/1024 < h)
    (hedges : (boundaryEdges G c Z₀).card ≤ (t₀+6)*k₀) :
    ∃ K B : G.Subgraph, K.IsPerfectMatching ∧ ¬ FamilyFailure K h 𝓧 ∧
      B.IsMatching ∧ B ≤ K ∧ B.edgeSet.ncard ≤ 4096*(t₀+6) ∧
      B.verts.ncard ≤ 2*(4096*(t₀+6)) ∧ B.verts.ncard = 2*B.edgeSet.ncard ∧
      matchingEdges B = (boundaryEdges G c Z₀).filter (fun e => e.val ∈ K.edgeSet) ∧
      (∀ u v, B.Adj u v ↔ K.Adj u v ∧ (u ∈ Z₀ ∨ v ∈ Z₀ ∨ c u ≠ c v)) := by
  obtain ⟨K,hK,hsafe,hcount⟩ :=
    exists_bounded_matching h k₀ t₀ hregular hno 𝓧 (boundaryEdges G c Z₀)
      hfamily hscale hedges
  obtain ⟨B,hB,hBK,hBE,hBcard,hBverts,hBadj⟩ := exists_boundary_submatching G c Z₀ K hK.1
  refine ⟨K,B,hK,hsafe,hB,hBK,?_,?_,hBverts,hBE,hBadj⟩
  · rw [hBcard]
    exact hcount
  · omega

end Overfull.SafePrescription
