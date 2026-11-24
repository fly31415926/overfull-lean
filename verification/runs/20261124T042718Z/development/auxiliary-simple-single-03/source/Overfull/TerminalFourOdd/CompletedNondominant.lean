import Overfull.TerminalFourOdd.Nondominant
import Overfull.TerminalFourOdd.Residual
import Overfull.Terminal.CoreBridge
import Overfull.Terminal.Reassembly

/-!
# Factor the four-odd residual and restore its completed prefix

The surviving primary forests and singleton counts are transported from
the constructed original-copy transcript. The residual coloring and the
full original-host factorization are conclusions of the proof.
-/

noncomputable section

namespace Overfull.TerminalFourOdd

open Finset Classical SimpleGraph FourOdd ForeignPhase SmallCuts Terminal

theorem exists_uniform_completed_nondominant_factorization (α γ ν τ : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hγ : 0 < γ)
    (hν : 0 < ν) (hντ : ν ≤ τ) (hτ : τ ≤ α/8) :
    ∃ η : ℝ, 0 < η ∧ ∃ m₀ : ℕ,
      ∀ (V : Type*) [Fintype V] (G : SimpleGraph V)
        (U : Fin 4 → Finset V) (H : ∀ i, SimpleGraph (U i))
        (label : V → Fin 4) (h : ℕ) (a : ℝ)
        (P : FourOddPrefix G U H label h a ν τ),
        (∀ i, labelShore label {i} = U i) → (∀ i, (U i).card % 2 = 1) →
        (∀ i, m₀ ≤ (U i).card) →
        (∀ i, α*(U i).card ≤ ((h-P.rounds : ℕ) : ℝ)) → 0 ≤ a →
        (∀ i, a ≤ η*(U i).card) →
        (∀ i, γ*(U i).card ≤
          ((singletonParts (Multigraph.ofSimpleGraph G) label P.remaining i).card : ℝ)) →
        ∃ M : Fin h → Finset G.edgeSet,
          (∀ i, (Multigraph.ofSimpleGraph G).IsPerfectMatching (M i)) ∧
          Pairwise (fun i j => Disjoint (M i) (M j)) ∧ univ.biUnion M = univ := by
  obtain ⟨η,hη,m₀,hfactor⟩ := exists_uniform_nondominant_coloring α γ ν τ
    hα hα1 hγ hν hντ hτ
  refine ⟨η,hη,m₀,?_⟩
  intro V _ G U H label h a P hparts hodd hm hk ha herror hsingle
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
  obtain ⟨M,hM,hdisj,hcover,hprofile,_hsize,hcounts,_hcenters⟩ := P.exists_residual_primary_family
  have hinst : (fun e f : R.edgeSet => propDecidable (e = f)) =
      (inferInstance : DecidableEq R.edgeSet) := Subsingleton.elim _ _
  obtain ⟨c⟩ := hfactor V R.edgeSet (Multigraph.ofSimpleGraph R) label C
    (h-P.rounds) a hm hodd hregular hk hrobust ha herror hdegree
    M hM hdisj (by simpa only [hinst] using hcover)
    (fun j i => (hprofile j).cut_one_or_three i) (fun i => by
      exact (hsingle i).trans_eq (by exact_mod_cast (hcounts i).symm))
  exact completion_restores_one_factorization P.completion P.rounds_le c

end Overfull.TerminalFourOdd
