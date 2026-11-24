import Overfull.Terminal.ClosedCores
import Overfull.Terminal.OddFactorization
import Overfull.Terminal.CoreBridge
import Overfull.Terminal.RemainingProfile
import Overfull.Terminal.ParityCases
import Overfull.Terminal.Reassembly

/-!
# Factor the constructed residual and restore every completed matching

Both residual parity cases use the actual profile produced by the boundary
prefix. All local colorings and the original host coloring are conclusions.
-/

noncomputable section

namespace Overfull.Terminal

open Finset Classical SimpleGraph Multigraph SmallCuts ForeignPhase

/-- One uniform residual tolerance works for both parity outcomes of the
constructed three-core prefix, and restores a coloring of the original host. -/
theorem exists_uniform_completed_prefix_factorization (α ν τ : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτ : τ ≤ α / 64) :
    ∃ η : ℝ, 0 < η ∧ ∃ m₀ : ℕ,
      ∀ (V : Type*) [Fintype V] (G : SimpleGraph V)
        (U : Fin 3 → Finset V) (H : ∀ i, SimpleGraph (U i))
        (h : ℕ) (a : ℝ) (P : ThreeCorePrefix G U H h a ν τ),
        (∀ i j, i ≠ j → Disjoint (U i) (U j)) →
        (∀ v, ∃ i, v ∈ U i) →
        (∀ i, m₀ ≤ (U i).card) →
        (∀ i, α * (U i).card ≤ ((h - P.rounds : ℕ) : ℝ)) →
        (∀ i, a ≤ η * (U i).card) →
        Nonempty ((Multigraph.ofSimpleGraph G).EdgeColoring h) := by
  have hτeven : τ ≤ min α 1 / 16 := by rw [min_eq_left hα1]; linarith
  obtain ⟨ηE, hηE, mE, hEven⟩ :=
    exists_uniform_closed_core_factorization α ν τ hα hν hντ hτeven
  obtain ⟨ηO, hηO, mO, hOdd⟩ :=
    exists_uniform_two_odd_coloring α ν τ hα hα1 hν hντ hτ
  refine ⟨min ηE ηO, lt_min hηE hηO, max mE mO, ?_⟩
  intro V _ G U H h a P hdisjoint hcover hm hk ha
  let R := afterDeletions G P.completion.full P.rounds
  let C : ∀ i, Core (Multigraph.ofSimpleGraph R) (U i) :=
    completionCore P.completion P.rounds le_rfl
  have hregular : ∀ v, (Multigraph.ofSimpleGraph R).degree v = h - P.rounds :=
    completionResidual_regular P.completion P.rounds le_rfl
  have hrobust (i : Fin 3) : IsRobustExpander (C i).graph ν τ :=
    completionCore_robust P.completion P.rounds le_rfl i
  have hdegree (i : Fin 3) (v : U i) :
      ((h - P.rounds : ℕ) : ℝ) - a ≤ ((C i).graph.degree v : ℝ) :=
    (completionCore_degree P.completion P.rounds le_rfl P.rounds_le i v).1
  apply completion_restores_coloring P.completion P.rounds_le
  rcases P.parity with ⟨heven, hempty⟩ | ⟨x, y, hxy, hparity, hcard, hcuts⟩
  · obtain ⟨c⟩ := hEven V R.edgeSet (Fin 3) (Multigraph.ofSimpleGraph R) U C
      (h - P.rounds) a hdisjoint hcover
      (fun i => (le_max_left mE mO).trans (hm i)) heven
      (P.residual_cuts_empty hdisjoint hcover hempty) hregular hk hrobust
      (fun i => (ha i).trans (mul_le_mul_of_nonneg_right
        (min_le_left ηE ηO) (Nat.cast_nonneg (U i).card))) hdegree
    exact c
  · obtain ⟨z, hzx, hzy, hindices⟩ := exists_third_core_index x y hxy
    have hz : Even (U z).card := Nat.even_iff.mpr (by simpa [hzx, hzy] using hparity z)
    have hx : Odd (U x).card := Nat.odd_iff.mpr (by simpa using hparity x)
    have hy : Odd (U y).card := Nat.odd_iff.mpr (by simpa using hparity y)
    obtain ⟨M, hM, hdM, hparts, hcX, hcY⟩ :=
      P.exists_residual_primary_family hdisjoint hcover x y hxy hcard hcuts
    have hcutOn (A : Finset V) (S : Finset R.edgeSet) :
        (Multigraph.ofSimpleGraph R).cutOn S A =
          S ∩ (Multigraph.ofSimpleGraph R).cutEdges A := by
      ext e
      simp only [Multigraph.mem_cutOn, mem_inter, Multigraph.mem_cutEdges]
    obtain ⟨c⟩ := hOdd V R.edgeSet (Multigraph.ofSimpleGraph R)
      (U z) (U x) (U y) (C z) (C x) (C y) (h - P.rounds) a
      (hdisjoint z x hzx) (hdisjoint z y hzy) (hdisjoint x y hxy)
      (reordered_three_core_cover U hcover z x y hindices) hz hx hy
      ((le_max_right mE mO).trans (hm z))
      ((le_max_right mE mO).trans (hm x))
      ((le_max_right mE mO).trans (hm y))
      hregular (hk z) (hk x) (hk y) (hrobust z) (hrobust x) (hrobust y)
      ((ha z).trans (mul_le_mul_of_nonneg_right
        (min_le_right ηE ηO) (Nat.cast_nonneg (U z).card)))
      ((ha x).trans (mul_le_mul_of_nonneg_right
        (min_le_right ηE ηO) (Nat.cast_nonneg (U x).card)))
      ((ha y).trans (mul_le_mul_of_nonneg_right
        (min_le_right ηE ηO) (Nat.cast_nonneg (U y).card)))
      (hdegree z) (hdegree x) (hdegree y) M hM hdM hparts
      (fun j => by simpa only [← hcutOn] using hcX j)
      (fun j => by simpa only [← hcutOn] using hcY j)
    exact c

end Overfull.Terminal
