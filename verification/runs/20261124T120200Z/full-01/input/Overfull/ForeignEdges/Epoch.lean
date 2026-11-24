import Overfull.ForeignEdges.EpochState
import Overfull.ForeignEdges.PreparationRule
import Overfull.ForeignEdges.RefinementHistory

/-!
# Constructing an interrupted or completed foreign-edge epoch

The setup contains fixed graph data, scalar budgets, the proved preparation
certificate, and prechosen packing rules. It does not contain a per-round
completion or admissibility oracle. Each new partial matching is prepared
in the actual current graph, its admissibility is derived from actual
exterior incidence, and its completion is produced by the fixed rules.
-/

namespace Overfull.ForeignEpoch

open Finset Classical SimpleGraph ForceMatching SafePrescription MatchingProbability
open ForeignTranscript ForeignPhase ForeignIncidence ForeignRuleCompletion
open ForeignEpochParameters ForeignRefinement
open BipartitePackingAccounting

universe u v
variable {V : Type u} {I : Type v} [Fintype V] [Fintype I]

/-- Static, independently checkable inputs for one epoch. -/
structure Setup (G : SimpleGraph V) (U : I → Finset V)
    (H₀ : ∀ i, SimpleGraph (U i)) where
  Z : Finset V
  marked : Finset V
  vertexLabel : V → Fin 4
  coreLabel : I → Fin 4
  initialDegree : ℕ
  originalDegree : ℕ
  markedBound : ℕ
  density : ℝ
  safeNu : ℝ
  safeRange : ℝ
  packingError : ℝ
  packingOutput : ℝ
  packingRange : ℝ
  safeError : ℝ
  safeOrder : ℕ
  coreError : ℝ
  horizon : I → ℕ
  rule : ∀ i, (s : ℕ) → (Fin s → Finset (U i) × (H₀ i).Subgraph) →
    Finset (U i) → (H₀ i).Subgraph
  classes : ℕ → Finset G.edgeSet
  preparation : PreparationRule.{u,v} density safeNu safeRange packingError
    markedBound safeError safeOrder
  certificate : ∀ i, RuleCertificate (H₀ i) (horizon i)
    packingError packingOutput packingRange (rule i)
  nu_pos : 0 < safeNu
  nu_le_output : safeNu ≤ packingOutput
  range_le : packingRange ≤ safeRange
  horizon_le : ∀ i, 3*initialDegree/4 ≤ horizon i
  order_le : safeOrder ≤ Fintype.card V
  core_count : Fintype.card I ≤ 4
  disjoint : Pairwise (fun i j => Disjoint (U i) (U j))
  core_exceptional_disjoint : ∀ i, Disjoint (U i) Z
  marked_subset : marked ⊆ Z
  marked_card : marked.card ≤ markedBound
  cover : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i
  labels : ∀ i v, v ∈ U i → vertexLabel v = coreLabel i
  regular : ∀ v, G.degree v = initialDegree
  degree_le_original : initialDegree ≤ originalDegree
  density_reserve : density*Fintype.card V ≤ (initialDegree-3*initialDegree/4 : ℕ)
  strict_reserve : (originalDegree : ℝ)/1024 < (initialDegree-3*initialDegree/4 : ℕ)
  no_overfull : ∀ X : Finset V, ¬ IsOverfull G initialDegree X
  error_nonneg : 0 ≤ coreError
  safe_budget : coreError+(Z.card : ℝ)+1 ≤ safeError*Fintype.card V
  core_size : ∀ i, density*Fintype.card V ≤ ((U i).card : ℝ)
  core_embed : ∀ i, H₀ i ≤ G.induce (U i : Set V)
  core_degree : ∀ i v, (initialDegree : ℝ)-coreError ≤ (H₀ i).degree v
  packing_budget : ∀ i, coreError ≤ packingError*(U i).card
  crossing : (clusterCrossingEdges G vertexLabel marked).card ≤ 6*originalDegree
  foreign_degree : ∀ v ∈ Z, v ∉ marked →
    (((G.neighborFinset v).filter
      (fun w => w ∉ marked ∧ vertexLabel w ≠ vertexLabel v)).card : ℝ) ≤
        (originalDegree : ℝ)/1024000
  class_properties : ∀ j < 3*initialDegree/4, ∀ R : SimpleGraph V,
    (currentClass G R (classes j)).IsMatching ∧
    (∀ u v, (currentClass G R (classes j)).Adj u v → u ∈ Z ∨ v ∈ Z) ∧
    (∀ u v, (currentClass G R (classes j)).Adj u v → vertexLabel u = vertexLabel v)

variable {G : SimpleGraph V} {U : I → Finset V} {H₀ : ∀ i, SimpleGraph (U i)}

def Setup.rounds (P : Setup G U H₀) : ℕ := 3*P.initialDegree/4

def Setup.loss (P : Setup G U H₀) : ℕ :=
  2*(4096*(P.markedBound+6))+4*135720

/-- The actual small cut that interrupts a phase. -/
noncomputable def Setup.Trigger (P : Setup G U H₀)
    (T : Transcript G U H₀) (s : ℕ) : Prop :=
  ∃ X : Finset V, X.card % 2 = 1 ∧
    (cutCount (univ : Finset (T.graph s).edgeSet) X : ℝ) ≤
      (P.initialDegree-s : ℕ)+
        ((2*(P.Z.card+P.markedBound+4096*(P.markedBound+6)+30) : ℕ) : ℝ) ∧
    ∃ i j, P.coreLabel i = P.coreLabel j ∧
      ¬ (coreMajority U X i ↔ coreMajority U X j)

theorem Setup.degree_reserve (P : Setup G U H₀) {s : ℕ} (hs : s ≤ P.rounds) :
    s < P.initialDegree ∧
    P.density*Fintype.card V ≤ (P.initialDegree-s : ℕ) ∧
    P.initialDegree-s ≤ P.originalDegree ∧
    (P.originalDegree : ℝ)/1024 < (P.initialDegree-s : ℕ) := by
  have hmon : P.initialDegree-P.rounds ≤ P.initialDegree-s := Nat.sub_le_sub_left hs _
  have hmonR : ((P.initialDegree-P.rounds : ℕ) : ℝ) ≤ (P.initialDegree-s : ℕ) := by
    exact_mod_cast hmon
  have hscale : (P.originalDegree : ℝ)/1024 < (P.initialDegree-s : ℕ) :=
    P.strict_reserve.trans_le hmonR
  have hpositive : 0 < P.initialDegree-s := by
    have hnonneg : (0 : ℝ) ≤ (P.originalDegree : ℝ)/1024 := by positivity
    exact_mod_cast hnonneg.trans_lt hscale
  exact ⟨Nat.sub_pos_iff_lt.mp hpositive,P.density_reserve.trans hmonR,
    (Nat.sub_le _ _).trans P.degree_le_original,hscale⟩

theorem Setup.initial_packing_degrees (P : Setup G U H₀) :
    ∀ i v, (P.initialDegree : ℝ)-P.packingError*(U i).card ≤ (H₀ i).degree v := by
  intro i v
  have hd := P.core_degree i v
  have he := P.packing_budget i
  linarith

set_option maxHeartbeats 1200000 in
/-- Without an actual triggering cut, one actual prepared partial matching
has an admissible input in every core and extends the matching transcript.
The admissibility proof precedes, and does not use, the new completion. -/
theorem Setup.extend_no_trigger (P : Setup G U H₀)
    (T : Transcript G U H₀) (s : ℕ)
    (hT : Valid P.rule P.initialDegree P.loss P.packingError P.classes s T)
    (hs : s < P.rounds) (hstop : ¬ P.Trigger T s) :
    ∃ T' : Transcript G U H₀,
      Valid P.rule P.initialDegree P.loss P.packingError P.classes (s+1) T' := by
  let R := T.graph s
  let H : ∀ i, SimpleGraph (U i) := T.currentCore s
  let h := P.initialDegree-s
  let M := currentClass G R (P.classes s)
  have hRG : R ≤ G := sdiff_le
  have hreserve := P.degree_reserve hs.le
  have hsq (i : I) : s < P.horizon i := hs.trans_le (P.horizon_le i)
  have hregular : ∀ v, R.degree v = h := hT.graph_degree P.regular
  have hH : ∀ i, H i ≤ R.induce (U i : Set V) := hT.core_embed P.core_embed
  have hdegree : ∀ i v, (h : ℝ)-P.coreError ≤ (H i).degree v := by
    intro i v
    exact (hT.core_degree P.core_embed P.regular P.coreError P.core_degree P.packing_budget
      P.horizon P.packingOutput P.packingRange P.certificate (fun i => (hsq i).le)
      hreserve.1.le i v).1
  have hrobust : ∀ i, IsRobustExpander (H i) P.safeNu P.safeRange := by
    intro i
    have hr := (hT.core_packing P.core_embed P.regular P.initial_packing_degrees
      P.horizon P.packingOutput P.packingRange P.certificate (fun i => (hsq i).le) i).2
    have hr' := (hr.mono_parameter _ P.nu_le_output).mono_range _ P.range_le
    convert hr' using 1
  have hcross : (clusterCrossingEdges R P.vertexLabel P.marked).card ≤ 6*P.originalDegree :=
    (clusterCrossingEdges_card_mono_graph R G P.vertexLabel P.marked hRG).trans P.crossing
  have hforeign : ∀ v ∈ P.Z, v ∉ P.marked →
      (((R.neighborFinset v).filter
        (fun w => w ∉ P.marked ∧ P.vertexLabel w ≠ P.vertexLabel v)).card : ℝ) ≤
          (P.originalDegree : ℝ)/1024000 := by
    intro v hv hvm
    have hm := filtered_neighbor_crossing_card_mono_graph R G P.vertexLabel P.marked hRG v
    have hm' : ((R.neighborFinset v).filter
        (fun w => w ∉ P.marked ∧ P.vertexLabel w ≠ P.vertexLabel v)).card ≤
      ((G.neighborFinset v).filter
        (fun w => w ∉ P.marked ∧ P.vertexLabel w ≠ P.vertexLabel v)).card := by
      convert hm using 1
      all_goals
        congr 1
        ext w
        simp only [mem_filter,SimpleGraph.mem_neighborFinset]
    exact (show (((R.neighborFinset v).filter
      (fun w => w ∉ P.marked ∧ P.vertexLabel w ≠ P.vertexLabel v)).card : ℝ) ≤
      ((G.neighborFinset v).filter
        (fun w => w ∉ P.marked ∧ P.vertexLabel w ≠ P.vertexLabel v)).card by
      exact_mod_cast hm').trans (P.foreign_degree v hv hvm)
  have hgroup : ∀ X : Finset V, X.card % 2 = 1 →
      (cutCount (univ : Finset R.edgeSet) X : ℝ) ≤
        h+((2*(P.Z.card+P.markedBound+4096*(P.markedBound+6)+30) : ℕ) : ℝ) →
      ∀ i j, P.coreLabel i = P.coreLabel j → (coreMajority U X i ↔ coreMajority U X j) := by
    intro X hodd hcut i j hij
    by_contra hbad
    exact hstop ⟨X,hodd,hcut,i,j,hij,hbad⟩
  obtain ⟨hM,hMZ,hMc⟩ := P.class_properties s hs R
  obtain ⟨K,B,F,_hK,_hfamily,_hB,_hBK,_hBsize,_hBcut,hF,_hBF,hZF,_hFsize,heven,
      _hFloc,_hFloss,_hFverts,hfoot,hnoCore,hcompletion⟩ :=
    P.preparation V I R U P.Z P.marked P.vertexLabel P.coreLabel H h P.originalDegree
      P.coreError M P.order_le P.core_count P.disjoint P.core_exceptional_disjoint
      P.marked_subset P.marked_card P.cover P.labels hregular hreserve.2.1
      hreserve.2.2.1 hreserve.2.2.2 hT.safe P.error_nonneg P.safe_budget P.core_size hH
      hdegree hrobust hcross hforeign hgroup hM hMZ hMc
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
  have hhpos : 0 < h := Nat.sub_pos_of_lt hreserve.1
  have hhalf : P.safeNu/2 ≤ P.packingOutput := by
    have hn := P.nu_pos
    have ho := P.nu_le_output
    linarith
  obtain ⟨N,hN,hFN,hloss,hsafe,hlocal,_hRrobust,_hRembed⟩ :=
    safe_complete_from_certificates R U P.Z H₀ P.rule P.horizon P.packingError
      P.packingOutput P.packingRange (P.safeNu/2) P.safeRange P.certificate T.core
      s h P.loss P.coreError F M hH (fun i j hij => P.disjoint hij) P.cover hF hZF
      hnoCore hsq (fun i j hj => hT.consistent j hj i)
      (fun i j hj => hT.allowed P.core_embed P.regular P.initial_packing_degrees i j hj)
      hAllowed hhpos hhalf P.range_le hdegree hcompletion
  let N₀ := rehost R G N (fun _ _ he => hRG (N.adj_sub he))
  have hN₀ : N₀.IsPerfectMatching := rehost_isPerfectMatching R G N _ hN
  have hNpresent : N₀.spanningCoe ≤ T.graph s := fun _ _ he => N.adj_sub he
  have hF₀N₀ : F₀.spanningCoe ≤ N₀.spanningCoe := hFN.2
  have hlocal₀ : ∀ i, N₀.spanningCoe.induce (U i : Set V) =
      (P.rule i s (transcriptPrefix (T.core i) s) (coveredCore (U i) G F₀)).spanningCoe := by
    intro i
    simpa only [hFcovered i] using hlocal i
  have hloss₀ : ((currentClass G (T.graph s) (P.classes s)).edgeSet \ N₀.edgeSet).ncard ≤ P.loss :=
    hloss
  have hsafe₀ : ∀ X : Finset V,
      ¬ IsOverfull (T.graph s \ N₀.spanningCoe) (P.initialDegree-(s+1)) X := by
    intro X
    have hh : h-1 = P.initialDegree-(s+1) := by dsimp only [h]; omega
    simpa only [hh] using hsafe X
  exact ⟨T.append P.rule s F₀ N₀,
    hT.append F₀ N₀ hN₀ hNpresent hF₀ hF₀N₀ hFno hFeven hFfoot hlocal₀ hloss₀ hsafe₀⟩

/-- Finite induction either processes every remaining class or stops at
an actual triggering cut. The only extension invoked is the proved
actual-graph construction above. -/
theorem Setup.finish_from_valid (P : Setup G U H₀)
    (T : Transcript G U H₀) (s : ℕ) (hs : s ≤ P.rounds)
    (hT : Valid P.rule P.initialDegree P.loss P.packingError P.classes s T) :
    ∃ t : ℕ, ∃ T' : Transcript G U H₀,
      s ≤ t ∧ t ≤ P.rounds ∧
      Valid P.rule P.initialDegree P.loss P.packingError P.classes t T' ∧
      (t = P.rounds ∨ P.Trigger T' t) := by
  have finish : ∀ r s : ℕ, s+r = P.rounds → ∀ T : Transcript G U H₀,
      Valid P.rule P.initialDegree P.loss P.packingError P.classes s T →
      ∃ t : ℕ, ∃ T' : Transcript G U H₀,
        s ≤ t ∧ t ≤ P.rounds ∧
        Valid P.rule P.initialDegree P.loss P.packingError P.classes t T' ∧
        (t = P.rounds ∨ P.Trigger T' t) := by
    intro r
    induction r with
    | zero =>
        intro s heq T hT
        have hs : s = P.rounds := by simpa using heq
        exact ⟨s,T,le_rfl,hs.le,hT,Or.inl hs⟩
    | succ r ih =>
        intro s heq T hT
        by_cases hstop : P.Trigger T s
        · exact ⟨s,T,le_rfl,by omega,hT,Or.inr hstop⟩
        · obtain ⟨T₁,hT₁⟩ := P.extend_no_trigger T s hT (by omega) hstop
          obtain ⟨t,T',hst,ht,hvalid,hend⟩ := ih (s+1) (by omega) T₁ hT₁
          exact ⟨t,T',by omega,ht,hvalid,hend⟩
  exact finish (P.rounds-s) s (by omega) T hT

/-- A foreign-edge epoch starts with empty matching transcripts and ends
after at most `floor(3h₀/4)` actual perfect-matching deletions, either having
processed every class or with an actual cut that requires refinement. -/
theorem Setup.exists_stopping_transcript (P : Setup G U H₀) :
    ∃ s : ℕ, ∃ T : Transcript G U H₀,
      s ≤ P.rounds ∧
      Valid P.rule P.initialDegree P.loss P.packingError P.classes s T ∧
      (s = P.rounds ∨ P.Trigger T s) := by
  have hzero := valid_zero P.rule P.initialDegree P.loss P.packingError P.classes P.no_overfull
  obtain ⟨s,T,_hzero,hs,hvalid,hend⟩ :=
    P.finish_from_valid emptyTranscript 0 (Nat.zero_le _) hzero
  exact ⟨s,T,hs,hvalid,hend⟩

end Overfull.ForeignEpoch
