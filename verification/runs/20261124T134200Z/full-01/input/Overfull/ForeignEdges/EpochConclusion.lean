import Overfull.ForeignEdges.EpochState
import Overfull.ForeignEdges.RefinementHistory
import Overfull.ForeignEdges.GlobalParameters
import Overfull.ForeignEdges.Concatenation
import Overfull.ForeignEdges.FinalCount

/-!
# The actual conclusion of a completed foreign-edge epoch

The state supplies its actual processed matchings. Its final incidence bound
uses the freshly constructed classes, the stored refinement history, and the
degree reserve at the actual final prefix. A common positive robust parameter
is chosen over all four certified outputs before any graph is supplied.
-/

namespace Overfull.ForeignEpochParameters

open Finset Classical

noncomputable def RestartParameters.finalOutput {α τ ν₀ : ℝ}
    (P : RestartParameters α τ ν₀) : ℝ :=
  univ.inf' univ_nonempty P.output

theorem RestartParameters.finalOutput_pos {α τ ν₀ : ℝ}
    (P : RestartParameters α τ ν₀) : 0 < P.finalOutput := by
  exact (lt_inf'_iff _).mpr (fun j _ => P.output_pos j)

theorem RestartParameters.finalOutput_le {α τ ν₀ : ℝ}
    (P : RestartParameters α τ ν₀) (j : Fin 4) : P.finalOutput ≤ P.output j :=
  inf'_le P.output (mem_univ j)

theorem RestartParameters.finalOutput_le_range {α τ ν₀ : ℝ}
    (P : RestartParameters α τ ν₀) : P.finalOutput ≤ τ/2 :=
  (P.finalOutput_le 0).trans (P.output_le 0)

end Overfull.ForeignEpochParameters

namespace Overfull.ForeignEpoch

open Finset Classical SimpleGraph ForeignPhase ForeignAssignment
open ForeignRefinement ForeignEpochParameters ForeignConcatenation
open ForeignRuleCompletion ForeignTranscript
open scoped BigOperators

variable {V I : Type*} [Fintype V] [Fintype I]
variable {G : SimpleGraph V} {U : I → Finset V} {H₀ : ∀ i, SimpleGraph (U i)}
variable {rule : ∀ i, (s : ℕ) → (Fin s → Finset (U i) × (H₀ i).Subgraph) →
    Finset (U i) → (H₀ i).Subgraph}
variable {h₀ loss : ℕ} {ε : ℝ} {A : ℕ → Finset G.edgeSet}
variable {T : Transcript G U H₀}

set_option maxHeartbeats 800000 in
/-- A completed actual epoch, with its constructed cut history, has the
claimed total exceptional incidence in its actual final residual graph. -/
theorem Valid.final_incidence_bound
    (hT : Valid rule h₀ loss ε A (3*h₀/4) T)
    (Z Z₀ : Finset V) (c : V → Fin 4) (p : I → Fin 4) (assign : V → I)
    (k₀ r : ℕ) (hI : Fintype.card I ≤ 4)
    (history : RefinementHistory k₀ markingThreshold (∅ : Finset V) G Z₀ c p)
    (hUZ : ∀ i, Disjoint (U i) Z)
    (hcolor : ∀ i v, v ∈ U i → c v = p i)
    (hregular : ∀ v, G.degree v = h₀)
    (hclasses : (range (3*h₀/4)).biUnion A = foreignEdges G U (Z \ Z₀) c p assign)
    (hupper : h₀ ≤ k₀) (hreserve : k₀ ≤ 4^r*h₀) (hr : r < 4) :
    (∑ v ∈ Z, (((T.graph (3*h₀/4)).neighborFinset v).filter
      (fun w => ∃ i, w ∈ U i ∧ i ≠ assign v)).card) ≤
        256*(loss+6+markedLimit)*(h₀-3*h₀/4) := by
  classical
  let d := 3*h₀/4
  have hd : d ≤ h₀ := (phase_degree_reserve h₀ d le_rfl).1
  have hgraph : T.graph d ≤ G := fun _ _ huv => huv.1
  have hforeign : (foreignEdges (T.graph d) U (Z \ Z₀) c p assign).card ≤ loss*k₀ := by
    have hcount := complete_foreign_phase_card_le G U (Z \ Z₀) c p assign
      T.full d loss A hclasses hT.present hT.loss_bound
    exact hcount.trans (Nat.mul_le_mul_left loss (hd.trans hupper))
  have hcross := (history.mono_graph hgraph).crossing_card_le_six hI
  have hmarked : Z₀.card ≤ markedLimit := history.marked_card_le_nat hI
    markingThreshold_pos markedLimit (by rw [← markedLimit_eq])
  have hquarter := within_epoch_degree_reserve k₀ h₀ r d hreserve le_rfl
  have hpower : 4^(r+1) ≤ 256 := by interval_cases r <;> norm_num
  have hreserve' : k₀ ≤ 256*(h₀-d) :=
    hquarter.trans (Nat.mul_le_mul_right _ hpower)
  have hfinal := final_foreign_incidence_bound (T.graph d) U Z Z₀ c p assign hUZ hcolor
    (h₀-d) k₀ loss markedLimit (hT.graph_degree hregular) hforeign hcross hmarked
    ((Nat.sub_le _ _).trans hupper) hreserve'
  convert hfinal using 1
  apply Finset.sum_congr rfl
  intro v _
  apply congrArg Finset.card
  ext w
  simp only [Finset.mem_filter,SimpleGraph.mem_neighborFinset,d]

omit [Fintype I] in
/-- The actual unused cores of any valid prefix have one common positive
output parameter, independent of which of the four epochs finishes. -/
theorem Valid.common_core_guarantees {α τ ν₀ : ℝ}
    (P : RestartParameters α τ ν₀) (j : Fin 4) (s : ℕ)
    (hT : Valid rule h₀ loss (P.packingError j) A s T)
    (hH : ∀ i, H₀ i ≤ G.induce (U i : Set V))
    (hregular : ∀ v, G.degree v = h₀)
    (a : ℝ) (hdegree : ∀ i v, (h₀ : ℝ)-a ≤ (H₀ i).degree v)
    (ha : ∀ i, a ≤ P.packingError j*(U i).card)
    (q : I → ℕ)
    (hcertificate : ∀ i, RuleCertificate (H₀ i) (q i) (P.packingError j)
      (P.output j) (τ/2) (rule i))
    (hsq : ∀ i, s ≤ q i) (hsh : s ≤ h₀) :
    ∀ i, T.currentCore s i ≤ (T.graph s).induce (U i : Set V) ∧
      (∀ v, ((h₀-s : ℕ) : ℝ)-a ≤ (T.currentCore s i).degree v ∧
        ((T.currentCore s i).degree v : ℝ) ≤ (h₀-s : ℕ)) ∧
      IsRobustExpander (T.currentCore s i) P.finalOutput (τ/2) := by
  have hdegreeε : ∀ i v, (h₀ : ℝ)-P.packingError j*(U i).card ≤ (H₀ i).degree v := by
    intro i v
    have hd := hdegree i v
    have he := ha i
    linarith
  intro i
  refine ⟨hT.core_embed hH i,
    hT.core_degree hH hregular a hdegree ha q (P.output j) (τ/2) hcertificate hsq hsh i,?_⟩
  exact ((hT.core_packing hH hregular hdegreeε q (P.output j) (τ/2)
    hcertificate hsq i).2).mono_parameter _ (P.finalOutput_le j)

end Overfull.ForeignEpoch
