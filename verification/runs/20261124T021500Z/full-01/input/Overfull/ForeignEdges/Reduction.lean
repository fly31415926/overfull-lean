import Overfull.ForeignEdges.ConfiguredEpoch
import Overfull.ForeignEdges.ProcessRefinement
import Overfull.ForeignEdges.ReductionResult

/-!
# The actual foreign-edge reduction

The inner induction constructs an interrupted or completed epoch from its
actual graph data. A triggered cut constructs the next actual entry. The
outer induction has at most three refinements, and at its final index the
core labels are injective, so no trigger is possible. The resulting object
contains the original-host perfect-matching sequence and its exact residual.
-/

namespace Overfull.ForeignProcess

open Finset Classical SimpleGraph ForceMatching SafePrescription MatchingProbability
open ForeignEpochParameters ForeignEpoch ForeignPhase ForeignRuleCompletion

universe u v
variable {V : Type u} {I : Type v} [Fintype V] [Fintype I] [Nonempty I]
variable {α τ ν₀ : ℝ} {G₀ : SimpleGraph V} {U₀ : I → Finset V}
variable {Zinit : Finset V} {k₀ : ℕ} {a₀ : ℝ}
variable {P : RestartParameters.{u,u,v} α τ ν₀}

set_option maxHeartbeats 1200000 in
/-- The outer finite induction uses only the actual epoch and refinement
constructions. Its uniform numerical packet is supplied by the original
parameter theorem; it is not a per-round existence hypothesis. -/
theorem reduce_from_entry
    (hα : 0 < α) (hα1 : α ≤ 1) (hτ : τ ≤ (α/256)/1000)
    (hdensity : α*Fintype.card V ≤ k₀) (hk₀n : k₀ ≤ Fintype.card V)
    (hI : Fintype.card I ≤ 4)
    (hbound : ∀ (j : Fin 4) (E : Entry G₀ U₀ Zinit k₀ a₀ P j), EntryBounds E)
    (j : Fin 4) (E : Entry G₀ U₀ Zinit k₀ a₀ P j) :
    Nonempty (ReductionResult G₀ U₀ Zinit k₀ a₀ P.finalOutput (τ/2)) := by
  classical
  have finish : ∀ fuel : ℕ, ∀ j : Fin 4, j.val+fuel = 3 →
      ∀ E : Entry G₀ U₀ Zinit k₀ a₀ P j,
        Nonempty (ReductionResult G₀ U₀ Zinit k₀ a₀ P.finalOutput (τ/2)) := by
    intro fuel
    induction fuel using Nat.strong_induction_on with
    | h fuel ih =>
      intro j hjfuel E
      let B := hbound j E
      obtain ⟨D⟩ := E.exists_fresh_epoch hI B
      let Q := D.setup
      obtain ⟨s,T,hs,hT,hstop⟩ := Q.exists_stopping_transcript
      have hs' : s ≤ 3*E.h/4 := hs
      have hT' : Valid D.rule E.h classLoss (P.packingError j) D.classes s T := hT
      rcases hstop with hcomplete | htrigger
      · have hsd : s = 3*E.h/4 := hcomplete
        subst s
        exact ⟨E.result_of_completed_epoch B D.rule Q.horizon D.certificate
          Q.horizon_le D.assignment D.classes D.class_union T hT' hI⟩
      · obtain ⟨X,_hodd,hcut,i,l,hil,hmajority⟩ := htrigger
        have hj : j.val < 3 := by
          by_contra hn
          have hj3 : j.val = 3 := by omega
          exact hmajority (E.no_trigger_at_three hI hj3 X i l hil)
        let r : Fin 3 := ⟨j.val,hj⟩
        have hsq (i : I) : s ≤ Q.horizon i := hs.trans (Q.horizon_le i)
        have hsh : s ≤ E.h := (phase_degree_reserve E.h s hs').1
        have hKembed : ∀ i, T.currentCore s i ≤ (T.graph s).induce (E.U i : Set V) :=
          hT'.core_embed E.core_embed
        have hKdegree : ∀ i x,
            ((E.h-s : ℕ) : ℝ)-(a₀+(j.val : ℝ)) ≤ (T.currentCore s i).degree x := by
          intro i x
          exact (hT'.core_degree E.core_embed E.regular (a₀+(j.val : ℝ))
            E.core_degree Q.packing_budget Q.horizon (P.output j) (τ/2)
            D.certificate hsq hsh i x).1
        have hKrobust : ∀ i, IsRobustExpander (T.currentCore s i) (P.output j) (τ/2) := by
          intro i
          exact (hT'.core_packing E.core_embed E.regular Q.initial_packing_degrees
            Q.horizon (P.output j) (τ/2) D.certificate hsq i).2
        have hcut' : (cutCount (univ : Finset (T.graph s).edgeSet) X : ℝ) ≤
            (E.h-s : ℕ)+((2*(E.Z.card+markedLimit+boundaryLimit+30) : ℕ) : ℝ) := hcut
        obtain ⟨E'⟩ := Entry.refine_from_prefix r E B hα hα1 hτ hdensity hk₀n hI
          T.full s hT'.perfect hT'.present hs' hT'.safe (T.currentCore s)
          hKembed hKdegree hKrobust X hcut' ⟨i,l,hil,hmajority⟩
        exact ih (3-(j.val+1)) (by omega) ⟨j.val+1,by omega⟩
          (by change j.val+1+(3-(j.val+1)) = 3; omega) E'
  exact finish (3-j.val) j (by omega) E

end Overfull.ForeignProcess

namespace Overfull

open Finset Classical SimpleGraph ForeignEpochParameters ForeignProcess

universe u v

set_option maxHeartbeats 800000 in
/-- Foreign-edge reduction with all constants chosen before the graph.
The output contains the actual perfect-matching sequence, the final
regular non-overfull graph, actual surviving robust cores, and the total
exceptional incidence bound. No global-process or local-completion
existence premise remains. -/
theorem foreign_edge_reduction (α τ ν₀ : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hν₀ : 0 < ν₀)
    (hν₀τ : ν₀ ≤ τ) (hτ : τ ≤ (α/256)/1000) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ νout : ℝ, 0 < νout ∧ νout ≤ τ/2 ∧ ∃ n₀ : ℕ,
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
        Nonempty (ReductionResult G U Z k a νout (τ/2)) := by
  obtain ⟨P⟩ : Nonempty (RestartParameters.{u,u,v} α τ ν₀) :=
    exists_restart_parameters α τ ν₀ hα hα1 hν₀ hν₀τ hτ
  obtain ⟨ε,hε,n₀,hparameters⟩ := P.exists_process_parameters hα hα1
  refine ⟨ε,hε,P.finalOutput,P.finalOutput_pos,P.finalOutput_le_range,n₀,?_⟩
  intro V I _ _ _ G U H Z k a hn hI hregular hdensity hsafe
    hdisjoint hUZ hcover hsize hembed hdegree hrobust ha hbudget
  have hnpos : 0 < Fintype.card V := by
    by_contra hh
    have hzero : Fintype.card V = 0 := by omega
    rw [hzero,Nat.cast_zero,mul_zero] at hbudget
    have hz : (0 : ℝ) ≤ Z.card := Nat.cast_nonneg _
    linarith only [ha,hz,hbudget]
  obtain ⟨v₀⟩ := Fintype.card_pos_iff.mp hnpos
  have hkn : k ≤ Fintype.card V := by
    have hh := G.degree_lt_card_verts v₀
    rw [hregular v₀] at hh
    exact hh.le
  let E := Entry.initial G U H Z k a P hregular hsafe hdisjoint hUZ hcover
    hembed hdegree hrobust
  have hbound (j : Fin 4) (E' : Entry G U Z k a P j) : EntryBounds E' :=
    hparameters G U Z k a j E' hn hdensity hkn hsize ha hbudget
  exact reduce_from_entry hα hα1 hτ hdensity hkn hI hbound 0 E

end Overfull
