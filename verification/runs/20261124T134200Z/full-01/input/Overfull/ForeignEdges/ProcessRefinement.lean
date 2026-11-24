import Overfull.ForeignEdges.ProcessParameters

/-!
# Restarting the actual process at a triggered prefix

The scalar packet comes from the single original parameter choice.  The
current core graphs and matching prefix are actual supplied objects.
The actual small-cut theorem constructs the refinement, and the state
update appends its matching prefix to the original-host transcript.
-/

namespace Overfull.ForeignProcess.Entry

open Finset Classical SimpleGraph ForceMatching SafePrescription MatchingProbability
open ForeignEpochParameters ForeignRefinement ForeignPhase ForeignConcatenation

variable {V I : Type*} [Fintype V] [Fintype I]
variable {α τ ν₀ : ℝ} {G₀ : SimpleGraph V} {U₀ : I → Finset V}
variable {Zinit : Finset V} {k₀ : ℕ} {a₀ : ℝ} {P : RestartParameters α τ ν₀}

/-- An actual triggering cut at an actual interrupted epoch prefix
constructs the next entry.  No next-state or refinement-existence premise
is used: the refinement is obtained from the proved small-cut theorem. -/
theorem refine_from_prefix (r : Fin 3)
    (E : Entry G₀ U₀ Zinit k₀ a₀ P ⟨r.val,by omega⟩) (B : EntryBounds E)
    (hα : 0 < α) (hα1 : α ≤ 1) (hτ : τ ≤ (α/256)/1000)
    (hdensity : α*Fintype.card V ≤ k₀) (hk₀n : k₀ ≤ Fintype.card V)
    (hI : Fintype.card I ≤ 4)
    (N : ℕ → E.G.Subgraph) (s : ℕ)
    (hperfect : ∀ m < s, (N m).IsPerfectMatching)
    (hpresent : ∀ m < s, (N m).spanningCoe ≤ afterDeletions E.G N m)
    (hs : s ≤ 3*E.h/4)
    (hsafe : ∀ X : Finset V, ¬ IsOverfull (afterDeletions E.G N s) (E.h-s) X)
    (K : ∀ i, SimpleGraph (E.U i))
    (hembed : ∀ i, K i ≤ (afterDeletions E.G N s).induce (E.U i : Set V))
    (hdegree : ∀ i v, ((E.h-s : ℕ) : ℝ)-(a₀+(r.val : ℝ)) ≤ ((K i).degree v : ℝ))
    (hrobust : ∀ i, IsRobustExpander (K i) (P.output ⟨r.val,by omega⟩) (τ/2))
    (X : Finset V)
    (hcut : (cutCount (univ : Finset (afterDeletions E.G N s).edgeSet) X : ℝ) ≤
      (E.h-s : ℕ)+((2*(E.Z.card+markedLimit+boundaryLimit+30) : ℕ) : ℝ))
    (htrigger : ∃ i l, E.p i = E.p l ∧
      ¬ (coreMajority E.U X i ↔ coreMajority E.U X l)) :
    Nonempty (Entry G₀ U₀ Zinit k₀ a₀ P ⟨r.val+1,by omega⟩) := by
  classical
  have scalar := B.ambient_prefix s hs
  have hregular (v : V) : (afterDeletions E.G N s).degree v = E.h-s :=
    (actual_prefix_degree_reserve E.G N k₀ E.h r.val s E.regular
      hperfect hpresent E.retained_degree hs v).1
  have hdegree_le : E.h-s ≤ k₀ := (Nat.sub_le _ _).trans E.degree_le
  obtain ⟨S,_hnext⟩ := P.refine_at_prefix r hα hα1 hτ
    (afterDeletions E.G N s) E.U K E.Z E.marked E.c E.p X (E.h-s) k₀
    (a₀+(r.val : ℝ)) B.order_pos hdensity hk₀n (B.degree_reserve s hs) hdegree_le
    B.error_nonneg B.small_error B.small_cut hI E.core_disjoint
    E.core_exceptional_disjoint E.marked_subset E.cover E.homogeneous htrigger
    hregular hembed hdegree hrobust B.core_size B.robust_large hcut
  have hrecorded : cutCount (univ : Finset (afterDeletions E.G N s).edgeSet) X ≤ 2*k₀ := by
    have hh := hcut.trans scalar.recorded_cut
    exact_mod_cast hh
  exact ⟨Entry.advance r E N s hperfect hpresent hs hsafe K X S hI
    scalar.initial_pos hrecorded⟩

end Overfull.ForeignProcess.Entry
