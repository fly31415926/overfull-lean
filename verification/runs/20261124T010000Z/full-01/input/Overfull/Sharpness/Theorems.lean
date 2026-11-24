import Overfull.Specifications
import Overfull.Relabeling
import Overfull.Sharpness.ColoringObstruction
import Overfull.Sharpness.UpperColoring
import Overfull.Sharpness.OddSets
import Overfull.SharpnessArithmetic

/-!
The complete sharpness proposition and its asymptotic density corollary.
The main asymptotic edge-coloring theorem of the manuscript is a separate
statement and is not proved in this project.
-/

namespace Overfull

open Sharpness

attribute [local instance] Classical.propDecidable

/-- Proposition 7.1, including connectedness, exact maximum degree, both
coloring assertions, every odd-set inequality, and the exact edge count. -/
theorem sharpness_family : SharpnessFamily := by
  classical
  intro Δ hΔ hodd
  let G := (Family.graph Δ).overFin (Family.vertex_count Δ)
  let f : Family.graph Δ ≃g G :=
    (Family.graph Δ).overFinIso (Family.vertex_count Δ)
  refine ⟨G, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact f.connected_iff.mp (Family.connected hΔ)
  · exact (iso_maxDegree_eq f).symm.trans (Family.maximum_degree hΔ)
  · intro hcolor
    exact Family.not_edge_colorable hΔ hodd ((iso_edgeColorable_iff f Δ).mpr hcolor)
  · exact (iso_edgeColorable_iff f (Δ + 1)).mp (Family.has_upper_coloring hΔ hodd)
  · exact (iso_no_overfull_iff f Δ).mp (Family.no_overfull hΔ hodd)
  · exact f.card_edgeFinset_eq.symm.trans (Family.edge_count hΔ)

/-- Corollary 7.2: every coefficient strictly below one quarter admits
arbitrarily large connected simple class-2 counterexamples with no overfull
set at their maximum degree. -/
theorem arbitrarily_large_class_two_graphs (c : ℝ) (hc : c < 1 / 4) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ ∃ G : SimpleGraph (Fin n),
      G.Connected ∧ c * (n : ℝ) ≤ (G.maxDegree : ℝ) ∧
      ¬ Nonempty (EdgeColoring G G.maxDegree) ∧
      Nonempty (EdgeColoring G (G.maxDegree + 1)) ∧
      ∀ X : Finset (Fin n), ¬ IsOverfull G G.maxDegree X := by
  classical
  obtain ⟨Δ, hΔ, hodd, hN, hratio⟩ :=
    SharpnessArithmetic.arbitrarily_large_odd_parameters c hc N
  obtain ⟨G, hconnected, hmax, hnot, hcolor, hover, _⟩ := sharpness_family Δ hΔ hodd
  refine ⟨4 * Δ + 5, hN, G, hconnected, ?_, ?_, ?_, ?_⟩
  · rw [hmax]
    have hpos : (0 : ℝ) < 4 * Δ + 5 := by positivity
    have hmul := (le_div_iff₀ hpos).mp hratio
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hmul
  · simpa only [hmax] using hnot
  · simpa only [hmax] using hcolor
  · simpa only [hmax] using hover

end Overfull
