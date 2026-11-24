import Overfull.ForeignEdges.ProcessParameters
import Overfull.ForeignEdges.EpochConclusion

/-!
# The actual foreign-edge reduction result

The result records one perfect-matching prefix in the original graph and
its exact residual.  It is independent of the restart schedule and the
epoch which completes.  Its cores, exceptional set, assignment, and final
incidence bound are the actual data of that completed epoch.
-/

namespace Overfull.ForeignProcess

open Finset Classical SimpleGraph ForceMatching SafePrescription MatchingProbability
open ForeignEpochParameters ForeignEpoch ForeignConcatenation ForeignPhase
open ForeignAssignment ForeignRuleCompletion ForeignTranscript
open scoped BigOperators

variable {V I : Type*} [Fintype V] [Fintype I]

/-- The graph-level conclusion, with no restart parameters or epoch
indices in its type.  Every used matching lives in the original host. -/
structure ReductionResult (G₀ : SimpleGraph V) (U₀ : I → Finset V)
    (Zinit : Finset V) (k₀ : ℕ) (a₀ νout rangeOut : ℝ) where
  G : SimpleGraph V
  h : ℕ
  N : ℕ → G₀.Subgraph
  rounds : ℕ
  graph_eq : G = afterDeletions G₀ N rounds
  perfect : ∀ s < rounds, (N s).IsPerfectMatching
  present : ∀ s < rounds, (N s).spanningCoe ≤ afterDeletions G₀ N s
  regular : ∀ v, G.degree v = h
  no_overfull : ∀ X : Finset V, ¬ IsOverfull G h X
  degree_le : h ≤ k₀
  retained_degree : k₀ ≤ 256*h
  U : I → Finset V
  H : ∀ i, SimpleGraph (U i)
  Z : Finset V
  assign : V → I
  core_subset : ∀ i, U i ⊆ U₀ i
  core_order_loss : ∀ i, (U₀ i).card ≤ (U i).card+3
  exceptional_subset : Zinit ⊆ Z
  exceptional_card : Z.card ≤ Zinit.card+3
  core_disjoint : Pairwise (fun i l => Disjoint (U i) (U l))
  core_exceptional_disjoint : ∀ i, Disjoint (U i) Z
  cover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i
  core_embed : ∀ i, H i ≤ G.induce (U i : Set V)
  core_degree : ∀ i v, (h : ℝ)-(a₀+3) ≤ ((H i).degree v : ℝ)
  core_robust : ∀ i, IsRobustExpander (H i) νout rangeOut
  foreign_bound :
    (∑ v ∈ Z, ((G.neighborFinset v).filter
      (fun w => ∃ i, w ∈ U i ∧ i ≠ assign v)).card) ≤
        256*(classLoss+6+markedLimit)*h

namespace ReductionResult

variable {G₀ : SimpleGraph V} {U₀ : I → Finset V} {Zinit : Finset V}
variable {k₀ : ℕ} {a₀ νout rangeOut : ℝ}

/-- The final graph is an actual subgraph of the original host. -/
theorem graph_le_original (R : ReductionResult G₀ U₀ Zinit k₀ a₀ νout rangeOut) :
    R.G ≤ G₀ := by
  rw [R.graph_eq]
  exact sdiff_le

/-- The current-host condition makes all used original-host matchings
pairwise edge-disjoint. -/
theorem pairwise_disjoint (R : ReductionResult G₀ U₀ Zinit k₀ a₀ νout rangeOut) :
    ∀ s ∈ range R.rounds, ∀ t ∈ range R.rounds, s ≠ t →
      Disjoint (R.N s).spanningCoe (R.N t).spanningCoe :=
  ForeignIncidence.deletion_sequence_pairwise G₀ R.N R.rounds R.present

end ReductionResult

namespace Entry

variable {α τ ν₀ : ℝ} {G₀ : SimpleGraph V} {U₀ : I → Finset V}
variable {Zinit : Finset V} {k₀ : ℕ} {a₀ : ℝ}
variable {P : RestartParameters α τ ν₀} {j : Fin 4}

/-- Complete the reduction from a constructed valid full epoch.  The
actual local matchings are appended to the prior original-host prefix;
the final cores are exactly the unused cores of the actual transcript. -/
noncomputable def result_of_completed_epoch
    (E : Entry G₀ U₀ Zinit k₀ a₀ P j) (B : EntryBounds E)
    (rule : ∀ i, (s : ℕ) → (Fin s → Finset (E.U i) × (E.H i).Subgraph) →
      Finset (E.U i) → (E.H i).Subgraph)
    (q : I → ℕ)
    (hcertificate : ∀ i, RuleCertificate (E.H i) (q i) (P.packingError j)
      (P.output j) (τ/2) (rule i))
    (horizon : ∀ i, 3*E.h/4 ≤ q i)
    (assign : V → I) (A : ℕ → Finset E.G.edgeSet)
    (hclasses : (range (3*E.h/4)).biUnion A =
      foreignEdges E.G E.U (E.Z \ E.marked) E.c E.p assign)
    (T : Transcript E.G E.U E.H)
    (hT : Valid rule E.h classLoss (P.packingError j) A (3*E.h/4) T)
    (hI : Fintype.card I ≤ 4) :
    ReductionResult G₀ U₀ Zinit k₀ a₀ P.finalOutput (τ/2) := by
  classical
  let d := 3*E.h/4
  have hd : d ≤ E.h := (phase_degree_reserve E.h d le_rfl).1
  have hj : j.val ≤ 3 := by omega
  have ha (i : I) : a₀+(j.val : ℝ) ≤ P.packingError j*(E.U i).card := by
    have hb := B.packing_error i
    have hz : (0 : ℝ) ≤ E.Z.card := Nat.cast_nonneg _
    linarith only [hb,hz]
  have hcores := hT.common_core_guarantees P j d E.core_embed E.regular
    (a₀+(j.val : ℝ)) E.core_degree ha q hcertificate horizon hd
  let Q := appendEpoch G₀ E.G E.graph_le_original E.N E.rounds T.full
  refine {
    G := T.graph d
    h := E.h-d
    N := Q
    rounds := E.rounds+d
    graph_eq := (appendEpoch_suffix G₀ E.G E.graph_le_original E.N E.rounds
      T.full E.graph_eq d).symm
    perfect := appendEpoch_perfect G₀ E.G E.graph_le_original E.N E.rounds
      T.full d E.perfect hT.perfect
    present := appendEpoch_present G₀ E.G E.graph_le_original E.N E.rounds
      T.full d E.graph_eq E.present hT.present
    regular := hT.graph_degree E.regular
    no_overfull := hT.safe
    degree_le := (Nat.sub_le _ _).trans E.degree_le
    retained_degree := B.degree_reserve d le_rfl
    U := E.U
    H := T.currentCore d
    Z := E.Z
    assign := assign
    core_subset := E.core_subset
    core_order_loss := ?_
    exceptional_subset := E.exceptional_subset
    exceptional_card := ?_
    core_disjoint := E.core_disjoint
    core_exceptional_disjoint := E.core_exceptional_disjoint
    cover := E.cover
    core_embed := fun i => (hcores i).1
    core_degree := ?_
    core_robust := fun i => (hcores i).2.2
    foreign_bound := hT.final_incidence_bound E.Z E.marked E.c E.p assign
      k₀ j.val hI E.history E.core_exceptional_disjoint E.homogeneous E.regular
      hclasses E.degree_le E.retained_degree j.isLt
  }
  · intro i
    have hh := E.core_order_loss i
    omega
  · have hh := E.exceptional_card
    omega
  · intro i v
    have hh := ((hcores i).2.1 v).1
    have hjR : (j.val : ℝ) ≤ 3 := by exact_mod_cast hj
    linarith only [hh,hjR]

end Entry

end Overfull.ForeignProcess
