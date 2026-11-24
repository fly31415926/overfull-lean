import Overfull.Absorption.CoreFamily
import Overfull.Absorption.Potential

/-!
# Absorbing the selected band after the forcing phase

The outside degree already counts every edge outside the assigned enlarged
core.  Consequently the second absorption loses only the forced-star
constant, with no second exceptional-order term.
-/

namespace Overfull.Absorption

open Finset Classical SimpleGraph

variable {V I : Type*} [Fintype V]

/-- The exact terminal outside-degree bound gives one common error for
the second enlargement. -/
theorem enlargedGraphs_degree_lower_of_outside (G : SimpleGraph V)
    (U : I → Finset V) (H : ∀ i, SimpleGraph (U i))
    (B : Finset V) (assignment : V → I) (h d : ℕ) (a : ℝ)
    (ha : 0 ≤ a) (hregular : ∀ v, G.degree v = h)
    (hdegree : ∀ i v, (h : ℝ)-a ≤ ((H i).degree v : ℝ))
    (hout : ∀ v ∈ B, outsideDegree G (U (assignment v)) v ≤ d) :
    ∀ i v, (h : ℝ)-(a+d) ≤
      ((enlargedGraphs G U H B assignment i).degree v : ℝ) := by
  classical
  intro i
  apply enlargedCore_degree_lower G (U i) (absorbedAt B assignment i) (H i)
  · intro v
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    linarith [hdegree i v]
  · intro v hv
    obtain ⟨hvB,hvi⟩ := (mem_absorbedAt B assignment i v).mp hv
    have hl := assigned_neighbors_lower G (U (assignment v)) v h d (hregular v) (hout v hvB)
    rw [hvi] at hl
    have hr : (h : ℝ) ≤ (G.neighborFinset v ∩ U i).card+d := by exact_mod_cast hl
    linarith

/-- A natural deletion count below one quarter of the entry degree
retains at least three quarters of that degree, including all rounding. -/
theorem retained_degree_three_quarters (h p s : ℕ)
    (hp : 4*p < h) (hs : s ≤ p) :
    0 < h-s ∧ 3*(h : ℝ)/4 ≤ ((h-s : ℕ) : ℝ) := by
  have hsh : s ≤ h := by omega
  constructor
  · omega
  · rw [Nat.cast_sub hsh]
    have hr : (4 : ℝ)*p < h := by exact_mod_cast hp
    have hsr : (s : ℝ) ≤ p := by exact_mod_cast hs
    linarith

end Overfull.Absorption
