import Overfull.TerminalFourOdd.CommonCenter
import Overfull.TerminalFourOdd.CompletedNondominant

/-!
# Both residual alternatives of the constructed four-odd prefix

The selection precedes completion. Its surviving common-center or positive
singleton-reserve certificate determines which proved residual factorization
to apply, after which all completed original matchings are restored.
-/

noncomputable section

namespace Overfull.TerminalFourOdd

open Finset Classical SimpleGraph FourOdd ForeignPhase SmallCuts Terminal

theorem exists_uniform_completed_four_odd_factorization (α γ ν τ : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hγ : 0 < γ)
    (hν : 0 < ν) (hντ : ν ≤ τ) (hτ : τ ≤ min α 1/16) :
    ∃ η : ℝ, 0 < η ∧ ∃ m₀ : ℕ,
      ∀ (V : Type*) [Fintype V] (G : SimpleGraph V)
        (U : Fin 4 → Finset V) (H : ∀ i, SimpleGraph (U i))
        (label : V → Fin 4) (h : ℕ) (a : ℝ)
        (P : FourOddPrefix G U H label h a ν τ),
        (∀ i, labelShore label {i} = U i) → (∀ i, (U i).card % 2 = 1) →
        (∀ i, m₀ ≤ (U i).card) →
        (∀ i, α*(U i).card ≤ ((h-P.rounds : ℕ) : ℝ)) → 0 ≤ a →
        (∀ i, a ≤ η*(U i).card) → (∀ i, γ*(U i).card ≤ (P.rounds : ℝ)) →
        ∃ M : Fin h → Finset G.edgeSet,
          (∀ i, (Multigraph.ofSimpleGraph G).IsPerfectMatching (M i)) ∧
          Pairwise (fun i j => Disjoint (M i) (M j)) ∧ univ.biUnion M = univ := by
  have hτN : τ ≤ α/8 := by have hh := min_le_left α (1:ℝ); linarith
  obtain ⟨ηN,hηN,mN,hN⟩ := exists_uniform_nondominant_coloring α γ ν τ
    hα hα1 hγ hν hντ hτN
  obtain ⟨ηC,hηC,mC,hC⟩ := exists_uniform_common_center_coloring α ν τ
    hα hν hντ hτ
  refine ⟨min ηN ηC,lt_min hηN hηC,max mN mC,?_⟩
  intro V _ G U H label h a P hparts hodd hm hk ha herror hreserve
  have hU : U = fun i => labelShore label {i} := funext (fun i => (hparts i).symm)
  subst U
  let R := afterDeletions G P.completion.full P.rounds
  let C : ∀ i, Core (Multigraph.ofSimpleGraph R) (labelShore label {i}) :=
    completionCore P.completion P.rounds le_rfl
  have hregular : ∀ v, (Multigraph.ofSimpleGraph R).degree v = h-P.rounds :=
    completionResidual_regular P.completion P.rounds le_rfl
  have hrobust (i : Fin 4) : IsRobustExpander (C i).graph ν τ :=
    completionCore_robust P.completion P.rounds le_rfl i
  have hdegree (i : Fin 4) (v : labelShore label {i}) :
      ((h-P.rounds : ℕ) : ℝ)-a ≤ ((C i).graph.degree v : ℝ) :=
    (completionCore_degree P.completion P.rounds le_rfl P.rounds_le i v).1
  obtain ⟨M,hM,hdisj,hcover,hprofile,hsize,hcounts,hcenters⟩ := P.exists_residual_primary_family
  have hinst : (fun e f : R.edgeSet => propDecidable (e = f)) =
      (inferInstance : DecidableEq R.edgeSet) := Subsingleton.elim _ _
  have hcolored : Nonempty ((Multigraph.ofSimpleGraph R).EdgeColoring (h-P.rounds)) := by
    rcases P.geometry with ⟨c,hc⟩ | hsingle
    · exact hC V R.edgeSet (Multigraph.ofSimpleGraph R) label C (h-P.rounds) a
        (fun i => (le_max_right mN mC).trans (hm i)) hodd hregular hk hrobust
        (fun i => (herror i).trans (mul_le_mul_of_nonneg_right (min_le_right ηN ηC)
          (Nat.cast_nonneg (labelShore label {i}).card))) hdegree
        M hdisj (by simpa only [hinst] using hcover) hprofile hsize c (hcenters c hc)
    · exact hN V R.edgeSet (Multigraph.ofSimpleGraph R) label C (h-P.rounds) a
        (fun i => (le_max_left mN mC).trans (hm i)) hodd hregular hk hrobust ha
        (fun i => (herror i).trans (mul_le_mul_of_nonneg_right (min_le_left ηN ηC)
          (Nat.cast_nonneg (labelShore label {i}).card))) hdegree
        M hM hdisj (by simpa only [hinst] using hcover)
        (fun j i => (hprofile j).cut_one_or_three i) (fun i => by
          have hs : (P.rounds : ℝ) ≤ (singletonParts (Multigraph.ofSimpleGraph G)
              label P.remaining i).card := by exact_mod_cast hsingle i
          exact ((hreserve i).trans hs).trans_eq (by exact_mod_cast (hcounts i).symm))
  obtain ⟨color⟩ := hcolored
  exact completion_restores_one_factorization P.completion P.rounds_le color

end Overfull.TerminalFourOdd
