import Mathlib.Tactic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Archimedean

/-!
# Arithmetic of the proposed sharpness family

This file proves numerical statements used in Proposition 7.1 and Corollary 7.2
of `Four_Robust_Component_Cases_2026-11-20.tex`. It does not prove that the graph
construction has the claimed degree, edge chromatic index, or odd-set bounds.
-/

namespace Overfull.SharpnessArithmetic

/-- The exact number of edges in an odd clique. -/
theorem odd_clique_edge_count (a : Nat) :
    (2 * a + 1).choose 2 = a * (2 * a + 1) := by
  rw [Nat.choose_two_right]
  have hsub : 2 * a + 1 - 1 = 2 * a := by omega
  rw [hsub]
  have hmul : (2 * a + 1) * (2 * a) = (a * (2 * a + 1)) * 2 := by ring
  rw [hmul]
  omega

/-- The edge-count expression in Proposition 7.1 simplifies as claimed.
The combinatorial assertion that this expression counts the construction's
edges is a separate obligation. -/
theorem sharpness_edge_count (delta : Nat)
    (hodd : delta % 2 = 1) (hdelta : 3 ≤ delta) :
    4 * delta.choose 2 + 4 * (delta - 2) + 5 + 3 =
      2 * delta * (delta + 1) := by
  obtain ⟨a, rfl⟩ : ∃ a : Nat, delta = 2 * a + 1 :=
    ⟨delta / 2, by omega⟩
  rw [odd_clique_edge_count]
  have hsub : (2 * a + 1 - 2) + 2 = 2 * a + 1 :=
    Nat.sub_add_cancel (by omega)
  nlinarith

/-- A nontrivial cut in a clique has at least `delta - 1` edges. This is
only the arithmetic inequality after the intersection size is known. -/
theorem clique_cut_lower_bound (delta t : Nat)
    (ht : 1 ≤ t) (htop : t < delta) :
    delta - 1 ≤ t * (delta - t) := by
  have hsum : t + (delta - t) = delta := by omega
  simpa [hsum] using Nat.add_sub_one_le_mul
    (a := t) (b := delta - t) (by omega) (by omega)

/-- The lower bounds on the original odd cut and its spoke contribution
imply the required weighted odd-cut bound. -/
theorem weighted_petersen_cut_bound (delta base spokes : Nat)
    (hdelta : 3 ≤ delta) (hbase : 3 ≤ base) (hspokes : 1 ≤ spokes) :
    delta ≤ base + (delta - 3) * spokes := by
  have hmul : delta - 3 ≤ (delta - 3) * spokes := by
    simpa using Nat.mul_le_mul_left (delta - 3) hspokes
  omega

/-- The family reaches equality in the whole-graph overfull threshold. -/
theorem sharpness_whole_graph_threshold (delta : Nat) :
    delta * ((4 * delta + 5 - 1) / 2) = 2 * delta * (delta + 1) := by
  have hdiv : (4 * delta + 5 - 1) / 2 = 2 * (delta + 1) := by omega
  rw [hdiv]
  ring

/-- The corresponding signed deficiency of the whole graph is `delta`. -/
theorem sharpness_whole_graph_deficiency (delta : Int) :
    delta * (4 * delta + 5) - 2 * (2 * delta * (delta + 1)) = delta := by
  ring

/-- The degree ratio approaches the quarter boundary from below. -/
theorem sharpness_ratio_below_quarter (delta : Nat) :
    (delta : ℝ) / (4 * delta + 5) < 1 / 4 := by
  have hpos : (0 : ℝ) < 4 * delta + 5 := by positivity
  apply (div_lt_iff₀ hpos).2
  linarith

/-- The exact gap between the family degree ratio and one quarter. -/
theorem sharpness_ratio_gap (delta : Nat) :
    (1 / 4 : ℝ) - (delta : ℝ) / (4 * delta + 5) =
      5 / (4 * (4 * delta + 5)) := by
  have hne : (4 * (delta : ℝ) + 5) ≠ 0 := by positivity
  field_simp [hne]
  ring

/-- For every real coefficient below one quarter, all sufficiently large
family parameters meet the coefficient. No graph-existence claim is made. -/
theorem eventually_above_coefficient (c : ℝ) (hc : c < 1 / 4) :
    ∃ n : Nat, ∀ delta : Nat, n ≤ delta →
      c ≤ (delta : ℝ) / (4 * delta + 5) := by
  have hden : (0 : ℝ) < 1 - 4 * c := by linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (5 * c / (1 - 4 * c))
  refine ⟨n, ?_⟩
  intro delta hdelta
  have hcast : (n : ℝ) ≤ delta := by exact_mod_cast hdelta
  have hquot : 5 * c / (1 - 4 * c) < (delta : ℝ) := lt_of_lt_of_le hn hcast
  have hprod : 5 * c < (delta : ℝ) * (1 - 4 * c) :=
    (div_lt_iff₀ hden).1 hquot
  have hpos : (0 : ℝ) < 4 * delta + 5 := by positivity
  apply (le_div_iff₀ hpos).2
  nlinarith

/-- Arbitrarily large odd family parameters satisfy any fixed coefficient
below one quarter. This supplies the numerical quantifiers in Corollary 7.2. -/
theorem arbitrarily_large_odd_parameters (c : ℝ) (hc : c < 1 / 4) (n : Nat) :
    ∃ delta : Nat, 3 ≤ delta ∧ delta % 2 = 1 ∧ n ≤ 4 * delta + 5 ∧
      c ≤ (delta : ℝ) / (4 * delta + 5) := by
  obtain ⟨m, hm⟩ := eventually_above_coefficient c hc
  refine ⟨2 * (m + n) + 3, ?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega
  · exact hm _ (by omega)

end Overfull.SharpnessArithmetic
