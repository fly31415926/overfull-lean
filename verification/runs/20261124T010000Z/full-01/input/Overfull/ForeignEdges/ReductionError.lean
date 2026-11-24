import Overfull.ForeignEdges.Reduction

/-!
# Arbitrarily small final error with fixed output robustness

The reduction's robust output parameter is chosen before the requested
final error.  Shrinking only the original error tolerance absorbs all
three possible core losses and exceptional-set increases.  The same
choice retains a fixed linear lower bound on every actual final core.
-/

namespace Overfull.ForeignProcess

open Finset Classical

/-- At most three core-error increases and three exceptional-vertex
additions multiply the original combined error budget by at most seven.
The retained degree then converts that budget to the requested tolerance. -/
theorem final_error_of_initial_budget (α η ε a : ℝ) (n k h t₀ t : ℕ)
    (hη : 0 < η) (ha : 0 ≤ a)
    (hdensity : α*n ≤ k) (hreserve : k ≤ 256*h)
    (ht : t ≤ t₀+3) (hbudget : a+(t₀ : ℝ)+1 ≤ ε*n)
    (hε : ε ≤ η*α/1792) : (a+3)+(t : ℝ)+1 ≤ η*h := by
  have htR : (t : ℝ) ≤ t₀+3 := by exact_mod_cast ht
  have ht₀ : (0 : ℝ) ≤ t₀ := Nat.cast_nonneg _
  have hseven : (a+3)+(t : ℝ)+1 ≤ 7*(a+(t₀ : ℝ)+1) := by
    linarith only [htR,ha,ht₀]
  have hbound := hseven.trans
    (mul_le_mul_of_nonneg_left hbudget (show (0 : ℝ) ≤ 7 by norm_num))
  have heps := mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg n)
  have hreserveR : (k : ℝ) ≤ 256*h := by exact_mod_cast hreserve
  have hscale := mul_le_mul_of_nonneg_left (hdensity.trans hreserveR) hη.le
  nlinarith only [hbound,heps,hscale]

/-- A small original combined error budget already forces enough initial
order to absorb the three possible vertex moves.  No extra order threshold
is needed for the final core-size bound. -/
theorem final_core_size_of_initial_budget (α ε a : ℝ) (n m₀ m t : ℕ)
    (ha : 0 ≤ a) (hbudget : a+(t : ℝ)+1 ≤ ε*n)
    (hε : ε ≤ α/6) (hsize : α*n ≤ m₀) (hloss : m₀ ≤ m+3) :
    (α/2)*n ≤ (m : ℝ) ∧ 3 ≤ m := by
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg _
  have heps := mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg n)
  have hlossR : (m₀ : ℝ) ≤ m+3 := by exact_mod_cast hloss
  have hlarge : 6 ≤ α*n := by nlinarith only [ha,ht,hbudget,heps]
  have hlower : (α/2)*n ≤ (m : ℝ) := by nlinarith only [hsize,hlossR,hlarge]
  refine ⟨hlower,?_⟩
  have hh : (3 : ℝ) ≤ m := by nlinarith only [hlarge,hlower]
  exact_mod_cast hh

end Overfull.ForeignProcess

namespace Overfull

open Finset Classical SimpleGraph ForeignProcess

universe u v

/-- Proposition 4.10 with an explicit arbitrary final error request.
The positive robust output parameter precedes that request.  All error
and order choices precede the graph, its types, its exceptional order,
and its core error.  The witness includes the actual original-host
matching sequence, final incidence bound, and surviving robust cores. -/
theorem foreign_edge_reduction_with_small_error (α τ ν₀ : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hν₀ : 0 < ν₀)
    (hν₀τ : ν₀ ≤ τ) (hτ : τ ≤ (α/256)/1000) :
    ∃ νout : ℝ, 0 < νout ∧ νout ≤ τ/2 ∧
      ∀ η : ℝ, 0 < η → ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ,
        ∀ (V : Type u) (I : Type v) [Fintype V] [Fintype I] [Nonempty I]
          (G : SimpleGraph V) (U : I → Finset V) (H : ∀ i, SimpleGraph (U i))
          (Z : Finset V) (k : ℕ) (a : ℝ),
          n₀ ≤ Fintype.card V → Fintype.card I ≤ 4 →
          (∀ v, G.degree v = k) → α*Fintype.card V ≤ k →
          (∀ X : Finset V, ¬ IsOverfull G k X) →
          Pairwise (fun i l => Disjoint (U i) (U l)) →
          (∀ i, Disjoint (U i) Z) → (∀ v, v ∈ Z ∨ ∃ i, v ∈ U i) →
          (∀ i, α*Fintype.card V ≤ ((U i).card : ℝ)) →
          (∀ i, H i ≤ G.induce (U i : Set V)) →
          (∀ i x, (k : ℝ)-a ≤ ((H i).degree x : ℝ)) →
          (∀ i, IsRobustExpander (H i) ν₀ τ) →
          0 ≤ a → a+(Z.card : ℝ)+1 ≤ ε*Fintype.card V →
          ∃ R : ReductionResult G U Z k a νout (τ/2),
            (a+3)+(R.Z.card : ℝ)+1 ≤ η*R.h ∧
            ∀ i, (α/2)*Fintype.card V ≤ ((R.U i).card : ℝ) := by
  obtain ⟨ε₀,hε₀,νout,hνout,hνoutRange,n₀,hreduce⟩ :=
    foreign_edge_reduction.{u,v} α τ ν₀ hα hα1 hν₀ hν₀τ hτ
  refine ⟨νout,hνout,hνoutRange,?_⟩
  intro η hη
  let ε := min ε₀ (min (α/6) (η*α/1792))
  have hε : 0 < ε := lt_min hε₀ (lt_min (by positivity) (by positivity))
  have hεbase : ε ≤ ε₀ := min_le_left _ _
  have hεsize : ε ≤ α/6 := (min_le_right _ _).trans (min_le_left _ _)
  have hεerror : ε ≤ η*α/1792 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ε,hε,n₀,?_⟩
  intro V I _ _ _ G U H Z k a hn hI hregular hdensity hsafe
    hdisjoint hUZ hcover hsize hembed hdegree hrobust ha hbudget
  have hbudget₀ : a+(Z.card : ℝ)+1 ≤ ε₀*Fintype.card V :=
    hbudget.trans (mul_le_mul_of_nonneg_right hεbase (Nat.cast_nonneg _))
  obtain ⟨R⟩ := hreduce V I G U H Z k a hn hI hregular hdensity hsafe
    hdisjoint hUZ hcover hsize hembed hdegree hrobust ha hbudget₀
  refine ⟨R,?_,?_⟩
  · exact final_error_of_initial_budget α η ε a (Fintype.card V) k R.h Z.card R.Z.card
      hη ha hdensity R.retained_degree R.exceptional_card hbudget hεerror
  · intro i
    exact (final_core_size_of_initial_budget α ε a (Fintype.card V)
      (U i).card (R.U i).card Z.card ha hbudget hεsize (hsize i) (R.core_order_loss i)).1

end Overfull
