import Overfull.CircuitPatterns.Cuts
import Overfull.CircuitPatterns.Rounding
import Overfull.SafePrescription.Counting

/-!
# Safety of the actual frequent-pattern deletion sequence

Original weighted cut inequalities are combined with exact cut subtraction.
The numerical weights remaining after a prefix are not asserted to be a
fractional matching decomposition of the residual graph.
-/

namespace Overfull.CircuitPatterns

open Finset Classical SimpleGraph MatchingProbability FractionalMatching
open ForeignPhase ForceMatching
open scoped BigOperators

section Counting

variable {P : Type*} [Fintype P]

/-- The number of occurrences of a pattern in a processed prefix. -/
noncomputable def prefixMultiplicity (kind : ℕ → P) (s : ℕ) (p : P) : ℕ :=
  ((range s).filter (fun j => kind j = p)).card

theorem prefixMultiplicity_sum (kind : ℕ → P) (s : ℕ) :
    ∑ p, prefixMultiplicity kind s p = s := by
  classical
  simp only [prefixMultiplicity, card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  simp

theorem prefixMultiplicity_statistic (kind : ℕ → P) (s : ℕ) (c : P → ℕ) :
    (∑ p, prefixMultiplicity kind s p * c p) = ∑ j ∈ range s, c (kind j) := by
  classical
  simp only [prefixMultiplicity, card_eq_sum_ones, sum_filter, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  simp [ite_mul, eq_comm]

omit [Fintype P] in
theorem prefixMultiplicity_mono (kind : ℕ → P) {s q : ℕ} (hs : s ≤ q) (p : P) :
    prefixMultiplicity kind s p ≤ prefixMultiplicity kind q p := by
  exact card_le_card (filter_subset_filter _ (range_mono hs))

omit [Fintype P] in
theorem prefixMultiplicity_pos (kind : ℕ → P) (s j : ℕ) (hj : j < s) :
    0 < prefixMultiplicity kind s (kind j) := by
  classical
  exact card_pos.mpr ⟨j, mem_filter.mpr ⟨mem_range.mpr hj, rfl⟩⟩

end Counting

variable {V I : Type*} [Fintype V] [Fintype I]

omit [Fintype V] in
/-- Toggling one exceptional vertex stays inside the finite whole-union
family. No core is split by this operation. -/
theorem wholeUnions_toggle_exceptional (U : I → Finset V) (Z X : Finset V)
    (hZ : ∀ i, Disjoint (U i) Z) (hX : X ∈ wholeUnions U Z)
    (v : V) (hv : v ∈ Z) : toggle X v ∈ wholeUnions U Z := by
  classical
  obtain ⟨A, B, hB, rfl⟩ := (mem_wholeUnions U Z X).mp hX
  have hvA : v ∉ A.biUnion U := by
    intro h
    obtain ⟨i, _, hi⟩ := mem_biUnion.mp h
    exact disjoint_left.mp (hZ i) hi hv
  refine (mem_wholeUnions U Z _).mpr ⟨A, toggle B v, ?_, ?_⟩
  · intro w hw
    by_cases hvB : v ∈ B
    · exact hB (mem_of_mem_erase (by simpa [toggle, hvB] using hw))
    · have hw' : w = v ∨ w ∈ B := by simpa [toggle, hvB] using hw
      exact hw'.elim (fun h => h ▸ hv) (fun h => hB h)
  · ext w
    by_cases hwv : w = v
    · subst w
      by_cases hvB : v ∈ B <;> simp [toggle, hvA, hvB]
    · by_cases hvB : v ∈ B <;> simp [toggle, hvA, hvB, hwv]

/-- Completing boundary matchings by internal core edges leaves all whole
cut counts unchanged. -/
theorem completion_whole_cut_count (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : I → Finset V) (Z : Finset V)
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hZ : ∀ i, Disjoint (U i) Z)
    (F N : G.Subgraph) (hFN : F ≤ N)
    (hadded : ∀ u v, N.Adj u v → F.Adj u v ∨ ∃ i, u ∈ U i ∧ v ∈ U i)
    (X : Finset V) (hX : X ∈ wholeUnions U Z) :
    cutCount (matchingEdges N) X = cutCount (matchingEdges F) X := by
  unfold cutCount
  rw [completed_cutEdges_eq U F N hFN hadded X
    (wholeUnions_whole U Z X hdisj hZ hX)]

/-- An actual cut incidence at a core vertex is at most the core degree
error, for every whole union. -/
theorem whole_cut_core_incidence (G : SimpleGraph V)
    (U : I → Finset V) (Z X : Finset V)
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hZ : ∀ i, Disjoint (U i) Z) (hX : X ∈ wholeUnions U Z)
    (H : ∀ i, SimpleGraph (U i)) (hH : ∀ i, H i ≤ G.induce (U i : Set V))
    (k : ℕ) (a : ℝ) (hregular : ∀ v, G.degree v = k)
    (hdegree : ∀ i v, (k : ℝ)-a ≤ ((H i).degree v : ℝ))
    (i : I) (v : U i) : (graphCutIncidence G X v.val : ℝ) ≤ a := by
  classical
  rw [← univ_cut_incidence_eq_graph]
  exact SafePrescription.cut_incident_core_bound G (U i) X (H i) (hH i)
    (wholeUnions_whole U Z X hdisj hZ hX i) k a hregular (hdegree i) v


/-- Whole odd cuts and the large-or-preserved dichotomy imply all safe
one-vertex toggles. Exceptional toggles are again whole unions. -/
theorem whole_toggles_safe (G R : SimpleGraph V)
    (U : I → Finset V) (Z : Finset V)
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hZ : ∀ i, Disjoint (U i) Z) (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (k h : ℕ) (hregularG : ∀ v, G.degree v = k)
    (hregularR : ∀ v, R.degree v = h)
    (hnoG : ∀ X : Finset V, ¬ IsOverfull G k X)
    (H : ∀ i, SimpleGraph (U i)) (hH : ∀ i, H i ≤ R.induce (U i : Set V))
    (a : ℝ) (hdegree : ∀ i v, (h : ℝ)-a ≤ ((H i).degree v : ℝ))
    (hwhole : ∀ X ∈ wholeUnions U Z, X.card % 2 = 1 → h ≤ graphCutCount R X)
    (hcases : ∀ X ∈ wholeUnions U Z, X.card % 2 = 0 →
      2*a ≤ (graphCutCount R X : ℝ) ∨ graphCutEdges R X = graphCutEdges G X) :
    ∀ X ∈ wholeUnions U Z, X.card % 2 = 0 → ∀ v, h ≤ graphCutCount R (toggle X v) := by
  intro X hX heven v
  by_cases hvZ : v ∈ Z
  · exact hwhole (toggle X v) (wholeUnions_toggle_exceptional U Z X hZ hX v hvZ)
      (toggle_odd heven v)
  · obtain ⟨i, hvi⟩ := (hcover v).resolve_left hvZ
    rcases hcases X hX heven with hlargeCut | hpreserved
    · have hinc := whole_cut_core_incidence R U Z X hdisj hZ hX H hH h a
        hregularR hdegree i ⟨v,hvi⟩
      apply toggle_safe_of_incidence R h hregularR X v
      have hincR : 2 * (graphCutIncidence R X v : ℝ) ≤ graphCutCount R X := by
        linarith only [hinc, hlargeCut]
      exact_mod_cast hincR
    · exact toggle_safe_of_preserved_cut G R k h hregularG hregularR hnoG X heven hpreserved v

section Weighted

variable {P : Type*} [Fintype P]

/-- Exact subtraction expressed in the common finite pattern coordinates. -/
theorem pattern_cut_accounting (G : SimpleGraph V) [DecidableRel G.Adj]
    (N : ℕ → G.Subgraph) (kind : ℕ → P) (s : ℕ)
    (hpresent : ∀ j < s, (N j).spanningCoe ≤ afterDeletions G N j)
    (X : Finset V) (c : P → ℕ)
    (hcount : ∀ j < s, cutCount (matchingEdges (N j)) X = c (kind j)) :
    graphCutCount (afterDeletions G N s) X +
      (∑ p, prefixMultiplicity kind s p * c p) = graphCutCount G X := by
  rw [prefixMultiplicity_statistic]
  have heq : (∑ j ∈ range s, c (kind j)) =
      ∑ j ∈ range s, cutCount (matchingEdges (N j)) X := by
    apply sum_congr rfl
    intro j hj
    exact (hcount j (mem_range.mp hj)).symm
  rw [heq]
  exact afterDeletions_cut_accounting G N s hpresent X

/-- Original weighted inequalities prove the odd-cut bound of the actual
residual after any prefix. -/
theorem weighted_odd_cut_afterDeletions (G : SimpleGraph V) [DecidableRel G.Adj]
    (N : ℕ → G.Subgraph) (kind : ℕ → P) (s k : ℕ) (hs : s ≤ k)
    (hpresent : ∀ j < s, (N j).spanningCoe ≤ afterDeletions G N j)
    (w : P → ℝ) (hsum : ∑ p, w p = k)
    (hn : ∀ p, (prefixMultiplicity kind s p : ℝ) ≤ w p)
    (X : Finset V) (c : P → ℕ)
    (hcount : ∀ j < s, cutCount (matchingEdges (N j)) X = c (kind j))
    (hodd : ∀ p, 0 < w p → 1 ≤ c p)
    (hcap : (∑ p, w p*c p) ≤ graphCutCount G X) :
    k-s ≤ graphCutCount (afterDeletions G N s) X := by
  have hbound := prefix_odd_cut_bound_on_support w (prefixMultiplicity kind s) c
    k (graphCutCount G X) hsum hn hodd hcap
  have hsumN := prefixMultiplicity_sum kind s
  have hsumR : (∑ p, (prefixMultiplicity kind s p : ℝ)) = s := by
    exact_mod_cast hsumN
  rw [hsumR] at hbound
  have hacct := pattern_cut_accounting G N kind s hpresent X c hcount
  have hacctR : (graphCutCount (afterDeletions G N s) X : ℝ) +
      (∑ p, (prefixMultiplicity kind s p : ℝ) * c p) = graphCutCount G X := by
    exact_mod_cast hacct
  have hresult : ((k-s : ℕ) : ℝ) ≤ graphCutCount (afterDeletions G N s) X := by
    rw [Nat.cast_sub hs]
    linarith
  exact_mod_cast hresult

/-- Every even whole cut is either large enough for the error bound or
retains precisely its original edges. Tests use one common proposal. -/
theorem proposed_cut_dichotomy (G : SimpleGraph V) [DecidableRel G.Adj]
    (N : ℕ → G.Subgraph) (kind : ℕ → P) (s : ℕ)
    (hpresent : ∀ j < s, (N j).spanningCoe ≤ afterDeletions G N j)
    (proposal accepted : P → ℕ)
    (hn : ∀ p, prefixMultiplicity kind s p ≤ accepted p)
    (hm : ∀ p, accepted p ≤ proposal p)
    (X : Finset V) (c : P → ℕ) (a : ℝ)
    (hcount : ∀ j < s, cutCount (matchingEdges (N j)) X = c (kind j))
    (hprotected : (graphCutCount G X : ℝ)-(∑ p, (proposal p : ℝ)*c p) < 2*a →
      ∀ p, accepted p*c p = 0) :
    2*a ≤ (graphCutCount (afterDeletions G N s) X : ℝ) ∨
      graphCutEdges (afterDeletions G N s) X = graphCutEdges G X := by
  by_cases hsmall : (graphCutCount G X : ℝ)-(∑ p, (proposal p : ℝ)*c p) < 2*a
  · apply Or.inr
    apply afterDeletions_cut_unchanged G N s hpresent X
    intro j hj
    rw [hcount j hj]
    have hpos : 0 < accepted (kind j) := (prefixMultiplicity_pos kind s j hj).trans_le (hn _)
    have hzero := hprotected hsmall (kind j)
    rcases Nat.mul_eq_zero.mp hzero with hz | hz
    · omega
    · exact hz
  · apply Or.inl
    have hacct := pattern_cut_accounting G N kind s hpresent X c hcount
    have hacctR : (graphCutCount (afterDeletions G N s) X : ℝ) +
        (∑ p, (prefixMultiplicity kind s p : ℝ) * c p) = graphCutCount G X := by
      exact_mod_cast hacct
    have hmon := prefix_cut_mono proposal (prefixMultiplicity kind s) c
      (graphCutCount G X) (fun p => (hn p).trans (hm p))
    linarith


set_option maxHeartbeats 1000000 in
/-- A concrete completed deletion prefix is safe. The hypotheses concern
original weights, exact boundary counts, a fixed numerical proposal and
actual robust cores; no no-overfull property of the residual is assumed. -/
theorem no_overfull_after_pattern_deletions (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : I → Finset V) (Z : Finset V)
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hZ : ∀ i, Disjoint (U i) Z) (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (N : ℕ → G.Subgraph) (kind : ℕ → P) (s k : ℕ) (hs : s ≤ k)
    (hregularG : ∀ v, G.degree v = k)
    (hnoG : ∀ X : Finset V, ¬ IsOverfull G k X)
    (hpresent : ∀ j < s, (N j).spanningCoe ≤ afterDeletions G N j)
    (hregular : ∀ v, (afterDeletions G N s).degree v = k-s)
    (H : ∀ i, SimpleGraph (U i))
    (hH : ∀ i, H i ≤ (afterDeletions G N s).induce (U i : Set V))
    (α c ν τ a : ℝ) (hα : 0 < α) (hc : 0 < c) (hν : 0 < ν) (hτ : 0 ≤ τ)
    (hτα : τ ≤ α / 10)
    (hklo : α * Fintype.card V ≤ ((k-s : ℕ) : ℝ))
    (hkhi : ((k-s : ℕ) : ℝ) ≤ 2 * Fintype.card V)
    (ha : a ≤ α * Fintype.card V / 10)
    (hlarge : 3 < ν ^ 2 * c ^ 2 * (Fintype.card V : ℝ))
    (hsize : ∀ i, c * Fintype.card V ≤ ((U i).card : ℝ))
    (hrobust : ∀ i, IsRobustExpander (H i) ν τ)
    (hdegree : ∀ i v, ((k-s : ℕ) : ℝ)-a ≤ ((H i).degree v : ℝ))
    (w : P → ℝ) (hsum : ∑ p, w p = k)
    (proposal accepted : P → ℕ)
    (hn : ∀ p, prefixMultiplicity kind s p ≤ accepted p)
    (hm : ∀ p, accepted p ≤ proposal p)
    (hweight : ∀ p, (proposal p : ℝ) ≤ w p)
    (crossing : Finset V → P → ℕ)
    (hcounts : ∀ X ∈ wholeUnions U Z, ∀ j < s,
      cutCount (matchingEdges (N j)) X = crossing X (kind j))
    (hodd : ∀ X ∈ wholeUnions U Z, X.card % 2 = 1 →
      ∀ p, 0 < w p → 1 ≤ crossing X p)
    (hcap : ∀ X ∈ wholeUnions U Z,
      (∑ p, w p*crossing X p) ≤ graphCutCount G X)
    (hprotected : ∀ X ∈ wholeUnions U Z, X.card % 2 = 0 →
      (graphCutCount G X : ℝ)-(∑ p, (proposal p : ℝ)*crossing X p) < 2*a →
        ∀ p, accepted p*crossing X p = 0) :
    ∀ X : Finset V, ¬ IsOverfull (afterDeletions G N s) (k-s) X := by
  classical
  have hnweight (p : P) : (prefixMultiplicity kind s p : ℝ) ≤ w p := by
    exact (show (prefixMultiplicity kind s p : ℝ) ≤ proposal p from
      by exact_mod_cast (hn p).trans (hm p)).trans (hweight p)
  have hwhole (X : Finset V) (hX : X ∈ wholeUnions U Z) (hXodd : X.card % 2 = 1) :
      k-s ≤ graphCutCount (afterDeletions G N s) X :=
    weighted_odd_cut_afterDeletions G N kind s k hs hpresent w hsum hnweight X
      (crossing X) (hcounts X hX) (hodd X hX hXodd) (hcap X hX)
  have hcases (X : Finset V) (hX : X ∈ wholeUnions U Z) (heven : X.card % 2 = 0) :
      2*a ≤ (graphCutCount (afterDeletions G N s) X : ℝ) ∨
        graphCutEdges (afterDeletions G N s) X = graphCutEdges G X :=
    proposed_cut_dichotomy G N kind s hpresent proposal accepted hn hm
      X (crossing X) a (hcounts X hX) (hprotected X hX heven)
  exact no_overfull_of_whole_cut_bounds (afterDeletions G N s) U Z hdisj hZ hcover
    (k-s) hregular H hH α c ν τ a hα hc hν hτ hτα hklo hkhi ha hlarge
    hsize hrobust hdegree hwhole
    (whole_toggles_safe G (afterDeletions G N s) U Z hdisj hZ hcover k (k-s)
      (fun v => by simpa only [← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hregularG v)
      hregular hnoG H hH a hdegree hwhole hcases)

end Weighted
end Overfull.CircuitPatterns
