import Overfull.MatchingProbability
import Overfull.MatchingExtension
import Mathlib.Tactic

namespace Overfull.ForceMatching

open Finset Classical MatchingProbability
open scoped BigOperators

variable {V I : Type*} [Fintype I]

/-- All unions of whole cores and exceptional singletons. -/
noncomputable def wholeUnions (U : I → Finset V) (Z : Finset V) : Finset (Finset V) :=
  (((univ : Finset I).powerset) ×ˢ Z.powerset).image (fun p => p.1.biUnion U ∪ p.2)

theorem mem_wholeUnions (U : I → Finset V) (Z X : Finset V) :
    X ∈ wholeUnions U Z ↔ ∃ A : Finset I, ∃ B : Finset V, B ⊆ Z ∧ X = A.biUnion U ∪ B := by
  classical
  simp only [wholeUnions,mem_image,mem_product,mem_powerset,subset_univ,true_and]
  constructor
  · rintro ⟨⟨A,B⟩,hB,rfl⟩
    exact ⟨A,B,hB,rfl⟩
  · rintro ⟨A,B,hB,rfl⟩
    exact ⟨(A,B),hB,rfl⟩

theorem wholeUnions_card (U : I → Finset V) (Z : Finset V) :
    (wholeUnions U Z).card ≤ 2^(Fintype.card I + Z.card) := by
  classical
  calc
    _ ≤ (((univ : Finset I).powerset) ×ˢ Z.powerset).card := card_image_le
    _ = _ := by rw [card_product,card_powerset,card_powerset,card_univ,pow_add]

theorem wholeUnions_card_le (U : I → Finset V) (Z : Finset V) (t : ℕ)
    (hI : Fintype.card I ≤ 4) (hZ : Z.card ≤ t) :
    (wholeUnions U Z).card ≤ 2^(t+4) := by
  apply (wholeUnions_card U Z).trans
  exact Nat.pow_le_pow_right (by omega) (by omega)

variable {G : SimpleGraph V}

/-- An actual matching uses an edge of the specified star. -/
def StarHit (M : G.Subgraph) (S : Finset G.edgeSet) : Prop :=
  ∃ e ∈ S, e.val ∈ M.edgeSet

theorem star_matching_card_le_one (M : G.Subgraph) (hM : M.IsMatching)
    (S : Finset G.edgeSet) (v : V) (hstar : ∀ e ∈ S, v ∈ e.val) :
    (S.filter (fun e => e.val ∈ M.edgeSet)).card ≤ 1 := by
  classical
  apply card_le_one.mpr
  intro e he f hf
  obtain ⟨heS,heM⟩ := mem_filter.mp he
  obtain ⟨hfS,hfM⟩ := mem_filter.mp hf
  have heq := MatchingExtension.matching_edge_eq G hM
    ⟨e.val,heM⟩ ⟨f.val,hfM⟩ (hstar e heS) (hstar f hfS)
  exact Subtype.ext (congrArg (fun x : M.edgeSet => x.val) heq)

theorem star_matching_card (M : G.Subgraph) (hM : M.IsMatching)
    (S : Finset G.edgeSet) (v : V) (hstar : ∀ e ∈ S, v ∈ e.val) :
    (S.filter (fun e => e.val ∈ M.edgeSet)).card = if StarHit M S then 1 else 0 := by
  classical
  have hle := star_matching_card_le_one M hM S v hstar
  by_cases hhit : StarHit M S
  · have hpos : 0 < (S.filter (fun e => e.val ∈ M.edgeSet)).card := by
      obtain ⟨e,heS,heM⟩ := hhit
      exact card_pos.mpr ⟨e,mem_filter.mpr ⟨heS,heM⟩⟩
    simp only [if_pos hhit]
    omega
  · have hz : S.filter (fun e => e.val ∈ M.edgeSet) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro e he
      exact hhit ⟨e,(mem_filter.mp he).1,(mem_filter.mp he).2⟩
    simp [hz,hhit]

namespace Distribution

variable {ι : Type*} [Fintype ι] {k : ℕ} (D : MatchingProbability.Distribution G k ι)

theorem expected_selected_edges (S : Finset G.edgeSet) :
    (∑ i, D.weight i * ((S.filter (fun e => e.val ∈ (D.matching i).edgeSet)).card : ℝ)) =
      (S.card : ℝ) / k := by
  classical
  have hcount (M : G.Subgraph) :
      ((S.filter (fun e => e.val ∈ M.edgeSet)).card : ℝ) =
        ∑ e ∈ S, if e.val ∈ M.edgeSet then (1 : ℝ) else 0 := by
    simp only [Finset.sum_boole]
  calc
    _ = ∑ e ∈ S, ∑ i ∈ univ.filter (fun i => e.val ∈ (D.matching i).edgeSet), D.weight i := by
      simp only [hcount,Finset.mul_sum,mul_ite,mul_one,mul_zero]
      rw [Finset.sum_comm]
      simp only [Finset.sum_filter]
    _ = ∑ _e ∈ S, (1 : ℝ) / k := by
      apply Finset.sum_congr rfl
      intro e _
      exact D.marginal e
    _ = _ := by simp [div_eq_mul_inv]

/-- Uniform edge marginals give the exact probability of meeting an
actual star, because a perfect matching uses at most one star edge. -/
theorem star_hit_probability (S : Finset G.edgeSet) (v : V)
    (hstar : ∀ e ∈ S, v ∈ e.val) :
    probability D.weight (fun i => StarHit (D.matching i) S) = (S.card : ℝ) / k := by
  classical
  rw [← expected_selected_edges D S]
  simp only [probability,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  rw [star_matching_card (D.matching i) (D.perfect i).1 S v hstar]
  split_ifs <;> simp

end Distribution

variable [Fintype V] [DecidableRel G.Adj]

/-- A sufficiently large star has a positive probability of being met
while all tested odd-cut inequalities are preserved. -/
theorem exists_star_matching_for_family (k : ℕ) (hk : 0 < k)
    (hregular : ∀ v, G.degree v = k) (hno : ∀ X : Finset V, ¬ IsOverfull G k X)
    (𝓧 : Finset (Finset V)) (S : Finset G.edgeSet) (v : V)
    (hstar : ∀ e ∈ S, v ∈ e.val) (hsize : 11*𝓧.card < S.card) :
    ∃ M : G.Subgraph, M.IsPerfectMatching ∧ StarHit M S ∧ ¬ FamilyFailure M k 𝓧 := by
  classical
  obtain ⟨ι,hι,⟨D⟩⟩ := MatchingProbability.exists_distribution hk hregular hno
  letI := hι
  have hgood : ∃ i, StarHit (D.matching i) S ∧ ¬ FamilyFailure (D.matching i) k 𝓧 := by
    by_contra h
    have himp : ∀ i, StarHit (D.matching i) S → FamilyFailure (D.matching i) k 𝓧 := by
      simpa only [not_exists,not_and,not_not] using h
    have hle := probability_mono D.weight D.nonneg himp
    rw [Distribution.star_hit_probability D S v hstar] at hle
    have hfail := D.family_failure_probability hk hregular hno 𝓧
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    have hsizeR : 11*(𝓧.card : ℝ) < S.card := by exact_mod_cast hsize
    have hlt := (div_lt_div_iff_of_pos_right hkR).mpr hsizeR
    linarith
  obtain ⟨i,hi,hgood⟩ := hgood
  exact ⟨D.matching i,D.perfect i,hi,hgood⟩

/-- The probability step of Lemma 4.11 with the manuscript's exact
constant `11 * 2^(t+4)`. The distribution is constructed from the graph. -/
theorem exists_star_matching (U : I → Finset V) (Z : Finset V) (t k : ℕ)
    (hI : Fintype.card I ≤ 4) (hZ : Z.card ≤ t) (hk : 0 < k)
    (hregular : ∀ v, G.degree v = k) (hno : ∀ X : Finset V, ¬ IsOverfull G k X)
    (S : Finset G.edgeSet) (v : V) (hstar : ∀ e ∈ S, v ∈ e.val)
    (hsize : 11*2^(t+4) < S.card) :
    ∃ M : G.Subgraph, M.IsPerfectMatching ∧ StarHit M S ∧
      ¬ FamilyFailure M k (wholeUnions U Z) := by
  apply exists_star_matching_for_family k hk hregular hno (wholeUnions U Z) S v hstar
  exact (Nat.mul_le_mul_left 11 (wholeUnions_card_le U Z t hI hZ)).trans_lt hsize

end Overfull.ForceMatching
