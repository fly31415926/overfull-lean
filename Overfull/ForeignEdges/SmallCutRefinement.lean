import Overfull.ForeignEdges.RefinementCore

/-!
# Refinement from an actual small cut

This wrapper derives the minority deletion input from the proved robust
small-cut theorem.  The ambient cut size, core degrees, and core sizes are
actual graph data.  It also derives the core order and the one-vertex
robust-deletion allowance from the same quantitative order hypothesis.
-/

namespace Overfull.ForeignRefinement

open Finset Classical SimpleGraph SafePrescription MatchingProbability
open scoped BigOperators

variable {V I : Type*} [Fintype V] [Fintype I]

/-- An actual small cut separating two core majorities in one group gives
a complete refinement step.  The total minority bound, the minimum order
of the surviving cores, and the robust deletion allowance are conclusions
of the supplied quantitative hypotheses. -/
theorem exists_small_cut_refinement (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : I → Finset V) (H : ∀ i, SimpleGraph (U i))
    (Z Z₀ : Finset V) (c : V → Fin 4) (p : I → Fin 4) (X : Finset V)
    (h : ℕ) (α κ a b ν τ T : ℝ)
    (hI : Fintype.card I ≤ 4)
    (hdisjoint : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hUZ : ∀ i, Disjoint (U i) Z) (hZ₀ : Z₀ ⊆ Z)
    (hcover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i)
    (hlabel : ∀ i v, v ∈ U i → c v = p i)
    (htrigger : ∃ i j, p i = p j ∧ ¬ (coreMajority U X i ↔ coreMajority U X j))
    (hregular : ∀ v, G.degree v = h)
    (hreserve : (Z.card : ℝ)+1+T < h)
    (hembed : ∀ i, H i ≤ G.induce (U i : Set V))
    (hdegree : ∀ i v, (h : ℝ)-a ≤ ((H i).degree v : ℝ))
    (hrobust : ∀ i, IsRobustExpander (H i) ν τ)
    (hα : 0 < α) (hκ : 0 < κ) (hν : 0 < ν) (hνone : ν ≤ 1)
    (hτ : 0 ≤ τ) (hτα : τ ≤ α/10)
    (hhlo : α*Fintype.card V ≤ h) (hhhi : (h : ℝ) ≤ 2*Fintype.card V)
    (ha : a ≤ α*Fintype.card V/10) (hb : b ≤ α*Fintype.card V/10)
    (hlarge : 3 < ν^2*κ^2*(Fintype.card V : ℝ))
    (hsize : ∀ i, κ*Fintype.card V ≤ ((U i).card : ℝ))
    (hcut : (cutCount (univ : Finset G.edgeSet) X : ℝ) ≤ h+b) :
    Nonempty (RefinementStep G U H Z Z₀ c p X h a ν τ T) := by
  classical
  let C : ∀ i, SmallCuts.Core (Multigraph.ofSimpleGraph G) (U i) :=
    fun i => ForceMatching.embeddedCore G (U i) (H i) (hembed i)
  have hcut' : ((Multigraph.ofSimpleGraph G).cutSize X : ℝ) ≤ (h : ℝ)+b := by
    simpa only [SafePrescription.cutCount_univ_eq_cutSize] using hcut
  have hminority := SmallCuts.minority_sum_le_one (Multigraph.ofSimpleGraph G) U C hdisjoint
    α κ ν τ a b h hα hκ hν hτ hτα hhlo hhhi ha hb hlarge hsize hrobust hdegree X hcut'
  have hn : (0 : ℝ) < Fintype.card V := by
    have hn₀ : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
    by_contra hh
    have heq : (Fintype.card V : ℝ) = 0 := by linarith only [hn₀,hh]
    rw [heq] at hlarge
    norm_num at hlarge
  obtain ⟨i₀,j₀,hp,hmajority⟩ := htrigger
  have hκone : κ ≤ 1 := by
    have hcard : ((U i₀).card : ℝ) ≤ Fintype.card V := by exact_mod_cast card_le_univ (U i₀)
    have hb := (hsize i₀).trans hcard
    nlinarith only [hb,hn]
  have hαtwo : α ≤ 2 := by nlinarith only [hhlo,hhhi,hn]
  have hτquarter : τ < 1/4 := by linarith only [hτα,hαtwo]
  let q := ν*κ
  have hqpos : 0 < q := mul_pos hν hκ
  have hqone : q ≤ 1 := by
    calc
      ν*κ ≤ 1*κ := mul_le_mul_of_nonneg_right hνone hκ.le
      _ ≤ 1 := by simpa using hκone
  have hquad : 3 < q^2*(Fintype.card V : ℝ) := by
    simpa only [q,mul_pow,mul_assoc] using hlarge
  have hscale := mul_le_mul_of_nonneg_right hqone (mul_nonneg hqpos.le hn.le)
  have hqbig : 3 < q*Fintype.card V := by nlinarith only [hscale,hquad]
  have hκbig : 3 < κ*Fintype.card V := by
    have hmul := mul_le_mul_of_nonneg_right hνone (mul_nonneg hκ.le hn.le)
    dsimp only [q] at hqbig
    nlinarith only [hqbig,hmul]
  have horder (i : I) : 3 ≤ (U i).card := by
    have hi := hsize i
    have hh : (3 : ℝ) < (U i).card := hκbig.trans_le hi
    have hnat : 3 < (U i).card := by exact_mod_cast hh
    omega
  have hdelete (i : I) : 2 ≤ ν*(U i).card := by
    have hi := mul_le_mul_of_nonneg_left (hsize i) hν.le
    dsimp only [q] at hqbig
    nlinarith only [hqbig,hi]
  have hdegree' (i : I) (v : U i) :
      (h : ℝ)-a ≤ ((H i).degree v : ℝ) ∧ ((H i).degree v : ℝ) ≤ h := by
    refine ⟨hdegree i v,?_⟩
    have hle := (Replacement.lift (U i) (H i)).degree_le_of_le (v := v.val)
      (Replacement.lift_le (U i) (H i) G (hembed i))
    rw [Replacement.lift_degree,hregular] at hle
    exact_mod_cast hle
  exact exists_refinement_step G U H Z Z₀ c p X h a ν τ T hI hdisjoint hUZ hZ₀
    hcover hlabel horder hminority ⟨i₀,j₀,hp,hmajority⟩ hregular hreserve hembed hdegree'
    hrobust hν.le hνone hτ hτquarter hdelete

end Overfull.ForeignRefinement
