import Overfull.Absorption.Potential
import Overfull.ForceMatching.Adaptive
import Overfull.ForeignEdges.EpochState

/-!
# Finite exceptional-star forcing with fixed core rules

The phase begins with fixed core packing rules and scalar reserves. Each
round prepares an actual partial matching in the current graph, proves its
input admissible from the actual exterior incidences, and obtains its
completion from those same fixed rules. The actual outside-degree sum
strictly decreases, so the process terminates within its initial value.
-/

namespace Overfull.Absorption

open Finset Classical SimpleGraph ForceMatching SafePrescription
open ForeignEpoch ForeignTranscript ForeignPhase ForeignRuleCompletion

universe u v
variable {V : Type u} {I : Type v} [Fintype V] [Fintype I]

/-- Static graph data and proved fixed-rule certificates for a forcing
phase. No field asserts the existence of a future partial matching,
admissible input, or ambient completion. -/
structure ForcingSetup (G : SimpleGraph V) (U : I → Finset V)
    (H₀ : ∀ i, SimpleGraph (U i)) where
  Z : Finset V
  B : Finset V
  W : V → Finset V
  initialDegree : ℕ
  starBound : ℕ
  density : ℝ
  coreError : ℝ
  packingError : ℝ
  packingOutput : ℝ
  packingRange : ℝ
  horizon : I → ℕ
  rule : ∀ i, (s : ℕ) → (Fin s → Finset (U i) × (H₀ i).Subgraph) →
    Finset (U i) → (H₀ i).Subgraph
  certificate : ∀ i, RuleCertificate (H₀ i) (horizon i)
    packingError packingOutput packingRange (rule i)
  selected_subset : B ⊆ Z
  exceptional_bound : Z.card ≤ starBound
  core_count : Fintype.card I ≤ 4
  disjoint : Pairwise (fun i j => Disjoint (U i) (U j))
  core_exceptional_disjoint : ∀ i, Disjoint (U i) Z
  cover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i
  regular : ∀ v, G.degree v = initialDegree
  no_overfull : ∀ X : Finset V, ¬ IsOverfull G initialDegree X
  core_embed : ∀ i, H₀ i ≤ G.induce (U i : Set V)
  core_degree : ∀ i v, (initialDegree : ℝ)-coreError ≤ (H₀ i).degree v
  packing_budget : ∀ i, coreError ≤ packingError*(U i).card
  density_pos : 0 < density
  output_pos : 0 < packingOutput
  range_nonneg : 0 ≤ packingRange
  range_le_density : packingRange ≤ density/10
  degree_reserve : density*Fintype.card V ≤
    ((initialDegree-forcingPotential G B W-1 : ℕ) : ℝ)
  degree_upper : (initialDegree : ℝ) ≤ 2*Fintype.card V
  error_small : coreError ≤ density*Fintype.card V/10
  order_large : 3 < packingOutput^2*density^2*(Fintype.card V : ℝ)
  core_size : ∀ i, density*Fintype.card V ≤ ((U i).card : ℝ)
  footprint_bound : ∀ i, ((2*starBound+6 : ℕ) : ℝ) ≤ packingError*(U i).card
  horizon_bound : ∀ i, forcingPotential G B W ≤ horizon i

variable {G : SimpleGraph V} {U : I → Finset V} {H₀ : ∀ i, SimpleGraph (U i)}

namespace ForcingSetup

noncomputable def initialPotential (P : ForcingSetup G U H₀) : ℕ :=
  forcingPotential G P.B P.W

noncomputable def potential (P : ForcingSetup G U H₀)
    (T : Transcript G U H₀) (s : ℕ) : ℕ :=
  forcingPotential (T.graph s) P.B P.W

abbrev Valid (P : ForcingSetup G U H₀) (s : ℕ) (T : Transcript G U H₀) : Prop :=
  ForeignEpoch.Valid P.rule P.initialDegree 0 P.packingError (fun _ => ∅) s T

noncomputable def Terminal (P : ForcingSetup G U H₀)
    (T : Transcript G U H₀) (s : ℕ) : Prop :=
  ∀ z ∈ P.B, outsideDegree (T.graph s) (P.W z) z ≤ 11*2^(P.starBound+4)

theorem initial_packing_degrees (P : ForcingSetup G U H₀) :
    ∀ i v, (P.initialDegree : ℝ)-P.packingError*(U i).card ≤ (H₀ i).degree v := by
  intro i v
  have hd := P.core_degree i v
  have he := P.packing_budget i
  linarith

/-- The phase-entry reserve gives the required current residual density
throughout the entire potential budget. -/
theorem current_degree_bounds (P : ForcingSetup G U H₀)
    {s : ℕ} (hs : s ≤ P.initialPotential) :
    s < P.initialDegree ∧
      P.density*Fintype.card V ≤ ((P.initialDegree-s-1 : ℕ) : ℝ) ∧
      ((P.initialDegree-s-1 : ℕ) : ℝ) ≤ 2*Fintype.card V := by
  classical
  have hn : 0 < Fintype.card V := by
    by_contra hn
    have hnzero : Fintype.card V = 0 := Nat.eq_zero_of_not_pos hn
    have hl := P.order_large
    simp only [hnzero,Nat.cast_zero,mul_zero] at hl
    norm_num at hl
  have hmon : P.initialDegree-P.initialPotential-1 ≤ P.initialDegree-s-1 := by omega
  have hlo : P.density*Fintype.card V ≤ ((P.initialDegree-s-1 : ℕ) : ℝ) :=
    P.degree_reserve.trans (by exact_mod_cast hmon)
  have hpositive : 0 < P.initialDegree-s-1 := by
    exact_mod_cast (mul_pos P.density_pos (by exact_mod_cast hn)).trans_le hlo
  refine ⟨by omega,hlo,?_⟩
  have hu : P.initialDegree-s-1 ≤ P.initialDegree := by omega
  exact (by exact_mod_cast hu :
    ((P.initialDegree-s-1 : ℕ) : ℝ) ≤ P.initialDegree).trans P.degree_upper

theorem outsideDegree_le_potential (P : ForcingSetup G U H₀)
    (T : Transcript G U H₀) (s : ℕ) (z : V) (hz : z ∈ P.B) :
    outsideDegree (T.graph s) (P.W z) z ≤ P.potential T s := by
  classical
  unfold potential forcingPotential
  exact Finset.single_le_sum
    (f := fun w => outsideDegree (T.graph s) (P.W w) w)
    (fun _ _ => Nat.zero_le _) hz

set_option maxHeartbeats 1600000 in
/-- One violating exceptional vertex produces an actual safe matching
deletion with a strict decrease of the actual potential. -/
theorem extend (P : ForcingSetup G U H₀)
    (T : Transcript G U H₀) (s : ℕ)
    (hT : P.Valid s T) (hbudget : s+P.potential T s ≤ P.initialPotential)
    (z : V) (hz : z ∈ P.B)
    (hexcess : 11*2^(P.starBound+4) < outsideDegree (T.graph s) (P.W z) z) :
    ∃ T' : Transcript G U H₀,
      P.Valid (s+1) T' ∧ P.potential T' (s+1) < P.potential T s := by
  classical
  have hsingle := P.outsideDegree_le_potential T s z hz
  have hs : s < P.initialPotential := by omega
  have hreserve := P.current_degree_bounds hs.le
  let R := T.graph s
  let h := P.initialDegree-s
  let S := outsideStar R (P.W z) z
  have hRG : R ≤ G := sdiff_le
  have hsq (i : I) : s < P.horizon i := hs.trans_le (P.horizon_bound i)
  have hregular : ∀ v, R.degree v = h := hT.graph_degree P.regular
  have hH : ∀ i, T.currentCore s i ≤ R.induce (U i : Set V) :=
    hT.core_embed P.core_embed
  have hdegree : ∀ i v, (h : ℝ)-P.coreError ≤ (T.currentCore s i).degree v := by
    intro i v
    exact (hT.core_degree P.core_embed P.regular P.coreError P.core_degree
      P.packing_budget P.horizon P.packingOutput P.packingRange P.certificate
      (fun i => (hsq i).le) hreserve.1.le i v).1
  have hhpos : 0 < h := Nat.sub_pos_of_lt hreserve.1
  have hstarsize : 11*2^(P.starBound+4) < S.card := by
    simpa only [S,outsideStar_card] using hexcess
  obtain ⟨F,hF,hZF,_hFsize,heven,hfoot,hnoCore,hFstar,hcompletion⟩ :=
    prepare_forced_star_of_bounds R U P.Z h P.starBound P.coreError P.density
      P.packingOutput P.packingRange P.packingError S z
      P.core_count P.exceptional_bound P.disjoint P.core_exceptional_disjoint P.cover
      hregular hhpos hT.safe P.density_pos P.output_pos P.range_nonneg
      P.range_le_density hreserve.2.1 hreserve.2.2 P.error_small P.order_large
      P.core_size P.footprint_bound (P.selected_subset hz)
      (outsideStar_incident R (P.W z) z) hstarsize
  let F₀ := rehost R G F (fun _ _ he => hRG (F.adj_sub he))
  have hF₀ : F₀.IsMatching := rehost_isMatching R G F _ hF
  have hFpresent : F₀.spanningCoe ≤ T.graph s := fun _ _ he => F.adj_sub he
  have hFcovered (i : I) : coveredCore (U i) G F₀ = coveredCore (U i) R F := rfl
  have hFno : ∀ i u v, u ∈ U i → v ∈ U i → ¬ F₀.Adj u v := hnoCore
  have hFeven : ∀ i, Even (((U i : Set V) \ F₀.verts).ncard) := heven
  have hFfoot : ∀ i, ((coveredCore (U i) G F₀).card : ℝ) ≤ P.packingError*(U i).card := by
    intro i
    rw [hFcovered]
    exact hfoot i
  have hAllowed : ∀ i, OrdinaryPackingStrategy.Allowed (H₀ i) (Fintype.card (U i))
      P.packingError s (transcriptPrefix (T.core i) s) (coveredCore (U i) R F) := by
    intro i
    have ha := hT.allowed_next P.core_embed P.regular P.initial_packing_degrees
      F₀ hF₀ hFpresent hFno hFeven hFfoot i
    simpa only [hFcovered i] using ha
  have hsafe : ∀ (N : R.Subgraph) (Q : ∀ i, SimpleGraph (U i)),
      N.IsPerfectMatching → F ≤ N →
      (∀ u v, N.Adj u v → F.Adj u v ∨ ∃ i, u ∈ U i ∧ v ∈ U i) →
      (∀ i, Q i ≤ (R \ N.spanningCoe).induce (U i : Set V)) →
      (∀ i, IsRobustExpander (Q i) P.packingOutput P.packingRange) →
      (∀ i v, ((h-1 : ℕ) : ℝ)-P.coreError ≤ (Q i).degree v) →
      (((⊥ : R.Subgraph).edgeSet \ N.edgeSet).ncard ≤ 0) ∧
      (∀ X : Finset V, ¬ IsOverfull (R \ N.spanningCoe) (h-1) X) := by
    intro N Q hN hFN hloc hemb hrob hdeg
    obtain ⟨_hhit,hsafe⟩ := hcompletion N Q hN hFN hloc hemb hrob hdeg
    exact ⟨by simp,hsafe⟩
  obtain ⟨N,hN,hFN,_hloss,hsafeN,hlocal,_hRrobust,_hRembed⟩ :=
    safe_complete_from_certificates R U P.Z H₀ P.rule P.horizon P.packingError
      P.packingOutput P.packingRange P.packingOutput P.packingRange P.certificate T.core
      s h 0 P.coreError F ⊥ hH (fun i j hij => P.disjoint hij) P.cover hF hZF
      hnoCore hsq (fun i j hj => hT.consistent j hj i)
      (fun i j hj => hT.allowed P.core_embed P.regular P.initial_packing_degrees i j hj)
      hAllowed hhpos le_rfl le_rfl hdegree hsafe
  have hNstar : StarHit N S := starHit_mono F N hFN S hFstar
  let N₀ := rehost R G N (fun _ _ he => hRG (N.adj_sub he))
  have hN₀ : N₀.IsPerfectMatching := rehost_isPerfectMatching R G N _ hN
  have hNpresent : N₀.spanningCoe ≤ T.graph s := fun _ _ he => N.adj_sub he
  have hF₀N₀ : F₀.spanningCoe ≤ N₀.spanningCoe := hFN.2
  have hlocal₀ : ∀ i, N₀.spanningCoe.induce (U i : Set V) =
      (P.rule i s (transcriptPrefix (T.core i) s) (coveredCore (U i) G F₀)).spanningCoe := by
    intro i
    simpa only [hFcovered i] using hlocal i
  have hempty : (currentClass G (T.graph s) (∅ : Finset G.edgeSet)).edgeSet = ∅ := by
    ext e
    induction e using Sym2.ind with
    | _ u v =>
      simp [currentClass,survivingEdges,Compression.selectedMatching,rehost]
  have hloss₀ : ((currentClass G (T.graph s) (∅ : Finset G.edgeSet)).edgeSet \
      N₀.edgeSet).ncard ≤ 0 := by simp only [hempty,Set.empty_diff,Set.ncard_empty,le_refl]
  have hsafe₀ : ∀ X : Finset V,
      ¬ IsOverfull (T.graph s \ N₀.spanningCoe) (P.initialDegree-(s+1)) X := by
    intro X
    have hh : h-1 = P.initialDegree-(s+1) := by dsimp only [h]; omega
    simpa only [hh] using hsafeN X
  refine ⟨T.append P.rule s F₀ N₀,
    hT.append F₀ N₀ hN₀ hNpresent hF₀ hF₀N₀ hFno hFeven hFfoot hlocal₀ hloss₀ hsafe₀,?_⟩
  have hdecrease := forcingPotential_decreases R N P.B P.W z hz hNstar
  unfold potential
  rw [T.graph_append_succ P.rule s F₀ N₀]
  exact hdecrease

/-- Strong induction uses only the actual strictly decreasing potential.
The running time budget is retained together with the new potential. -/
theorem finish_from_valid (P : ForcingSetup G U H₀)
    (T : Transcript G U H₀) (s : ℕ)
    (hT : P.Valid s T) (hbudget : s+P.potential T s ≤ P.initialPotential) :
    ∃ r : ℕ, ∃ T' : Transcript G U H₀,
      s ≤ r ∧ r+P.potential T' r ≤ P.initialPotential ∧
      P.Valid r T' ∧ P.Terminal T' r := by
  classical
  have finish : ∀ p s : ℕ, ∀ T : Transcript G U H₀,
      P.potential T s = p → s+p ≤ P.initialPotential → P.Valid s T →
      ∃ r : ℕ, ∃ T' : Transcript G U H₀,
        s ≤ r ∧ r+P.potential T' r ≤ P.initialPotential ∧
        P.Valid r T' ∧ P.Terminal T' r := by
    intro p
    induction p using Nat.strong_induction_on with
    | h p ih =>
      intro s T hpotential hbudget hT
      by_cases hstop : P.Terminal T s
      · exact ⟨s,T,le_rfl,by simpa only [hpotential] using hbudget,hT,hstop⟩
      · have hex : ∃ z ∈ P.B,
            11*2^(P.starBound+4) < outsideDegree (T.graph s) (P.W z) z := by
          unfold Terminal at hstop
          push_neg at hstop
          exact hstop
        obtain ⟨z,hz,hzexcess⟩ := hex
        obtain ⟨T₁,hT₁,hdecrease⟩ := P.extend T s hT
          (by simpa only [hpotential] using hbudget) z hz hzexcess
        have hlt : P.potential T₁ (s+1) < p := by simpa only [hpotential] using hdecrease
        have hbudget₁ : s+1+P.potential T₁ (s+1) ≤ P.initialPotential := by omega
        obtain ⟨r,T',hsr,hr,hvalid,hterminal⟩ :=
          ih (P.potential T₁ (s+1)) hlt (s+1) T₁ rfl hbudget₁ hT₁
        exact ⟨r,T',by omega,hr,hvalid,hterminal⟩
  exact finish (P.potential T s) s T rfl hbudget hT

/-- The phase terminates within the initial actual incidence sum, keeps
the exact no-overfull condition, and retains the fixed certified robust
parameter, including when no forcing round is needed. -/
theorem exists_terminal_transcript (P : ForcingSetup G U H₀) :
    ∃ s : ℕ, ∃ T : Transcript G U H₀,
      s+P.potential T s ≤ P.initialPotential ∧
      P.Valid s T ∧ P.Terminal T s ∧
      (∀ v, (T.graph s).degree v = P.initialDegree-s) ∧
      (∀ X : Finset V, ¬ IsOverfull (T.graph s) (P.initialDegree-s) X) ∧
      (∀ i, T.currentCore s i ≤ (T.graph s).induce (U i : Set V)) ∧
      (∀ i, IsRobustExpander (T.currentCore s i) P.packingOutput P.packingRange) ∧
      (∀ i v, ((P.initialDegree-s : ℕ) : ℝ)-P.coreError ≤ (T.currentCore s i).degree v ∧
        ((T.currentCore s i).degree v : ℝ) ≤ (P.initialDegree-s : ℕ)) := by
  have hzero : P.Valid 0 (emptyTranscript : Transcript G U H₀) :=
    valid_zero P.rule P.initialDegree 0 P.packingError (fun _ => ∅) P.no_overfull
  have hbudget : 0+P.potential (emptyTranscript : Transcript G U H₀) 0 ≤ P.initialPotential := by
    simp only [potential,initialPotential,Transcript.graph,afterDeletions_zero,zero_add,le_refl]
  obtain ⟨s,T,_hzero,hs,hT,hterminal⟩ := P.finish_from_valid emptyTranscript 0 hzero hbudget
  have hs₀ : s ≤ P.initialPotential := by omega
  have hsq (i : I) : s ≤ P.horizon i := hs₀.trans (P.horizon_bound i)
  have hsh := (P.current_degree_bounds hs₀).1.le
  refine ⟨s,T,hs,hT,hterminal,hT.graph_degree P.regular,hT.safe,hT.core_embed P.core_embed,?_,?_⟩
  · intro i
    exact (hT.core_packing P.core_embed P.regular P.initial_packing_degrees
      P.horizon P.packingOutput P.packingRange P.certificate hsq i).2
  · intro i v
    exact hT.core_degree P.core_embed P.regular P.coreError P.core_degree P.packing_budget
      P.horizon P.packingOutput P.packingRange P.certificate hsq hsh i v

end ForcingSetup

end Overfull.Absorption
