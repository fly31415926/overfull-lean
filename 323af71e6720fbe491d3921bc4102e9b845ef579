import Overfull.TerminalFourTwoOdd.RemainingProfile
import Overfull.TerminalFourTwoOdd.ResidualColoring
import Overfull.Terminal.CoreBridge
import Overfull.Terminal.Reassembly

/-! Factor the actual residual profile and restore every completed prefix matching. -/

noncomputable section

namespace Overfull.TerminalFourTwoOdd

open Finset Classical SimpleGraph Multigraph SmallCuts ForeignPhase FourOdd Terminal

private theorem other_two_indices (x y : Fin 4) (hxy : x ≠ y) :
    ∃ z w : Fin 4, z ≠ w ∧ z ≠ x ∧ z ≠ y ∧ w ≠ x ∧ w ≠ y ∧
      ∀ i : Fin 4, i=z ∨ i=w ∨ i=x ∨ i=y := by
  have hh : ∀ x y : Fin 4, x ≠ y →
      ∃ z w : Fin 4, z ≠ w ∧ z ≠ x ∧ z ≠ y ∧ w ≠ x ∧ w ≠ y ∧
        ∀ i : Fin 4, i=z ∨ i=w ∨ i=x ∨ i=y := by decide
  exact hh x y hxy

set_option maxHeartbeats 1600000 in
theorem exists_uniform_completed_four_two_odd_factorization (α ν τ : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτ : τ ≤ α/64) :
    ∃ η : ℝ, 0 < η ∧ ∃ m₀ : ℕ,
      ∀ (V : Type*) [Fintype V] (G : SimpleGraph V)
        (U : Fin 4 → Finset V) (H : ∀ i, SimpleGraph (U i))
        (label : V → Fin 4) (x y : Fin 4) (h : ℕ) (a : ℝ)
        (P : FourTwoOddPrefix G U H label x y h a ν τ),
        (∀ i, labelShore label {i} = U i) → x ≠ y →
        (∀ i, (U i).card % 2 = if i=x ∨ i=y then 1 else 0) →
        Pairwise (fun i j => Disjoint (U i) (U j)) →
        (∀ v, ∃ i, v ∈ U i) →
        (∀ i, m₀ ≤ (U i).card) →
        α*Fintype.card V ≤ ((h-P.rounds : ℕ) : ℝ) →
        (∀ i, α*Fintype.card V ≤ ((U i).card : ℝ)) →
        (∀ i, a ≤ η*(U i).card) →
        Nonempty ((Multigraph.ofSimpleGraph G).EdgeColoring h) := by
  obtain ⟨η,hη,m₀,hfactor⟩ := exists_uniform_four_two_odd_coloring α ν τ
    hα hα1 hν hντ hτ
  refine ⟨η,hη,m₀,?_⟩
  intro V _ G U H label x y h a P hparts hxy hparity hdisjoint hcover hm hk hsize ha
  obtain ⟨z,w,hzw,hzx,hzy,hwx,hwy,hindices⟩ := other_two_indices x y hxy
  let R := afterDeletions G P.completion.full P.rounds
  let C : ∀ i, Core (Multigraph.ofSimpleGraph R) (U i) :=
    completionCore P.completion P.rounds le_rfl
  have hregular : ∀ v, (Multigraph.ofSimpleGraph R).degree v = h-P.rounds :=
    completionResidual_regular P.completion P.rounds le_rfl
  have hrobust (i : Fin 4) : IsRobustExpander (C i).graph ν τ :=
    completionCore_robust P.completion P.rounds le_rfl i
  have hdegree (i : Fin 4) (v : U i) :
      ((h-P.rounds : ℕ) : ℝ)-a ≤ ((C i).graph.degree v : ℝ) :=
    (completionCore_degree P.completion P.rounds le_rfl P.rounds_le i v).1
  obtain ⟨M,hM,hdM,hpartsM,hcut,hpar⟩ := P.exists_residual_primary_family hparts
  have hinst : (fun e f : R.edgeSet => propDecidable (e = f)) =
      (inferInstance : DecidableEq R.edgeSet) := Subsingleton.elim _ _
  have hcoverM : ∀ e : R.edgeSet,
      e ∉ (Multigraph.ofSimpleGraph R).internalEdges (U z) →
      e ∉ (Multigraph.ofSimpleGraph R).internalEdges (U w) →
      e ∉ (Multigraph.ofSimpleGraph R).internalEdges (U x) →
      e ∉ (Multigraph.ofSimpleGraph R).internalEdges (U y) → ∃ j, e ∈ M j := by
    intro e hez hew hex hey
    have hjoin : e ∈ joiningCopies (Multigraph.ofSimpleGraph R) label := by
      apply (mem_joiningCopies _ _ e).mpr
      intro heq
      let i := label ((Multigraph.ofSimpleGraph R).firstEnd e)
      have hf : (Multigraph.ofSimpleGraph R).firstEnd e ∈ U i := by
        rw [← hparts]
        simp [mem_labelShore,i]
      have hs : (Multigraph.ofSimpleGraph R).secondEnd e ∈ U i := by
        rw [← hparts]
        simp only [mem_labelShore,mem_singleton]
        exact heq.symm
      have hinner := ((Multigraph.ofSimpleGraph R).mem_internalEdges (U i) e).mpr ⟨hf,hs⟩
      rcases hindices i with hi | hi | hi | hi
      · exact hez (by simpa only [hi] using hinner)
      · exact hew (by simpa only [hi] using hinner)
      · exact hex (by simpa only [hi] using hinner)
      · exact hey (by simpa only [hi] using hinner)
    have hp : e ∈ univ.biUnion M := by
      have hh : univ.biUnion M = joiningCopies (Multigraph.ofSimpleGraph R) label := by
        simpa only [hinst] using hpartsM
      rwa [hh]
    obtain ⟨j,_,hj⟩ := mem_biUnion.mp hp
    exact ⟨j,hj⟩
  have hcutOn (A : Finset V) (N : Finset R.edgeSet) :
      (Multigraph.ofSimpleGraph R).cutOn N A = N ∩ (Multigraph.ofSimpleGraph R).cutEdges A := by
    ext e
    simp only [Multigraph.mem_cutOn,mem_inter,Multigraph.mem_cutEdges]
  obtain ⟨c⟩ := hfactor V R.edgeSet (Multigraph.ofSimpleGraph R)
    (U z) (U w) (U x) (U y) (C z) (C w) (C x) (C y) (h-P.rounds) a
    (hdisjoint hzw) (hdisjoint hzx) (hdisjoint hzy)
    (hdisjoint hwx) (hdisjoint hwy) (hdisjoint hxy)
    (by intro v
        obtain ⟨i,hi⟩ := hcover v
        rcases hindices i with rfl | rfl | rfl | rfl
        · exact Or.inl hi
        · exact Or.inr (Or.inl hi)
        · exact Or.inr (Or.inr (Or.inl hi))
        · exact Or.inr (Or.inr (Or.inr hi)))
    (Nat.even_iff.mpr (by simpa [hzx,hzy] using hparity z))
    (Nat.even_iff.mpr (by simpa [hwx,hwy] using hparity w))
    (Nat.odd_iff.mpr (by simpa using hparity x))
    (Nat.odd_iff.mpr (by simpa using hparity y))
    (hm z) (hm w) (hm x) (hm y) hregular hk (hsize z) (hsize w)
    (hrobust z) (hrobust w) (hrobust x) (hrobust y)
    (ha z) (ha w) (ha x) (ha y) (hdegree z) (hdegree w) (hdegree x) (hdegree y)
    M hM hdM hcoverM
    (by intro j; simpa only [hinst,← hcutOn] using hcut j x (Or.inl rfl))
    (by intro j; simpa only [hinst,← hcutOn] using hcut j y (Or.inr rfl))
    (by intro j
        apply ((hM j).uncovered_even_iff_cut_parity (Multigraph.ofSimpleGraph R) (U z)).mpr
        simpa only [hinst] using (hpar j z).symm)
    (by intro j
        apply ((hM j).uncovered_even_iff_cut_parity (Multigraph.ofSimpleGraph R) (U w)).mpr
        simpa only [hinst] using (hpar j w).symm)
  exact completion_restores_coloring P.completion P.rounds_le c

end Overfull.TerminalFourTwoOdd
