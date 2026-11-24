import Overfull.Absorption.ForcingProcess
import Overfull.Absorption.PhaseParameters
import Overfull.Absorption.ThresholdsSchedule
import Overfull.Absorption.Result
import Overfull.ForeignEdges.PackingSchedule

/-!
# Bounded exceptional-set absorption

The threshold schedule is fixed before the graph and is evaluated against
the entry foreign incidences. The actual first enlargement is followed by
one fixed family of certified core rules. An actual decreasing potential
terminates the forcing phase; the second enlargement then absorbs the
selected band. The final requested error is evaluated at the actual final
exceptional cardinality, with no monotonicity assumption.
-/

namespace Overfull

open Finset Classical SimpleGraph Absorption AbsorptionThresholds
open AbsorptionParameters ForeignPackingSchedule ForeignRuleCompletion ForeignEpoch
open scoped BigOperators

universe u v

set_option maxHeartbeats 1600000 in
/-- Proposition 4.12. The robust output precedes the arbitrary positive
error function; every other parameter precedes the graph. The conclusion
records the actual original-host matching sequence and exact residual,
the enlarged robust cores, and the bounded remaining exceptional set. -/
theorem bounded_exceptional_absorption (α ν τ c : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτ : τ ≤ α/1000) (hc : 0 ≤ c) :
    ∃ νout : ℝ, 0 < νout ∧
      ∀ f : ℕ → ℝ, (∀ t, 0 < f t) →
        ∃ T : ℕ, ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ,
          ∀ (V : Type u) (I : Type v) [Fintype V] [Fintype I]
            (G : SimpleGraph V) (U : I → Finset V) (H : ∀ i, SimpleGraph (U i))
            (Z : Finset V) (assignment : V → I) (h : ℕ) (a : ℝ),
            n₀ ≤ Fintype.card V → Fintype.card I ≤ 4 →
            (∀ x, G.degree x = h) → α*Fintype.card V ≤ h →
            (∀ X : Finset V, ¬ IsOverfull G h X) →
            Pairwise (fun i j => Disjoint (U i) (U j)) →
            (∀ i, Disjoint (U i) Z) → (∀ x, x ∈ Z ∨ ∃ i, x ∈ U i) →
            (∀ i, α*Fintype.card V ≤ ((U i).card : ℝ)) →
            (∀ i, H i ≤ G.induce (U i : Set V)) →
            (∀ i x, (h : ℝ)-a ≤ ((H i).degree x : ℝ)) →
            (∀ i, IsRobustExpander (H i) ν τ) →
            0 ≤ a → a+(Z.card : ℝ)+1 ≤ ε*Fintype.card V →
            (∑ z ∈ Z, ((originalForeignNeighbors G U assignment z).card : ℝ)) ≤ c*h →
            Nonempty (AbsorptionResult G U Z h T f νout (2*τ)) := by
  classical
  have hτpos : 0 < τ := hν.trans_le hντ
  have hτquarter : τ ≤ 1/4 := by linarith only [hτ, hα1]
  obtain ⟨Pack⟩ := exists_epoch_parameters.{u} α (α/4) (2*τ) (ν/4)
    hα hα1 (by positivity) (by positivity)
    (by linarith only [hντ, hτpos]) (by linarith only [hτ, hα])
  have hθτ : Pack.output ≤ τ := by
    have hh := Pack.output_le
    linarith only [hh]
  refine ⟨Pack.output/4, div_pos Pack.output_pos (by norm_num), ?_⟩
  intro f hf
  let κ := firstThresholdBound α Pack.error
  have hκ : 0 < κ := firstThresholdBound_pos α Pack.error hα Pack.error_pos
  obtain ⟨L, ρ, t, T, hlength, hzero, hρpos, hρstrict, ht, hnext, hT⟩ :=
    exists_long_threshold_schedule c (lowerEnvelope f) (fun _ => 16*κ)
      (lowerEnvelope_pos f hf) (fun _ => by positivity)
  have hρanti : Antitone ρ := hρstrict.antitone
  have hρκ (i : ℕ) : ρ (i+1) ≤ κ := by
    have hh := (hnext i).2
    linarith only [hh]
  let D : ℕ := 11*2^(T+4)
  obtain ⟨εp, hεp, Np, hphase⟩ := exists_uniform_phase_parameters
    α Pack.error Pack.output ν hα Pack.error_pos Pack.output_pos hν T Pack.order
  obtain ⟨εf, hεf, Nf, _hNf, hfinalBound⟩ := uniform_final_error_actual_card
    L α f t (fun j => ρ (j+1)) (fun _ => (D : ℝ)) hα hf
      (fun j _ => (hnext j).1)
  let ε := min εp εf
  have hε : 0 < ε := lt_min hεp hεf
  let n₀ := max 1 (max Np Nf)
  refine ⟨T, ε, hε, n₀, ?_⟩
  intro V I _ _ G U H Z assignment h a hn hI hregular hdensity hsafe
    hdisjoint hUZ hcover hsize hembed hdegree hrobust ha hbudget hforeign
  let n := Fintype.card V
  have hnpos : 0 < n := by
    have hone : 1 ≤ n₀ := le_max_left _ _
    change n₀ ≤ n at hn
    omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hNp : Np ≤ n := (le_max_left Np Nf).trans ((le_max_right 1 _).trans hn)
  have hNf : Nf ≤ n := (le_max_right Np Nf).trans ((le_max_right 1 _).trans hn)
  have hbudgetp : a+(Z.card : ℝ)+1 ≤ εp*n :=
    hbudget.trans (mul_le_mul_of_nonneg_right (min_le_left εp εf) hnR.le)
  have hbudgetf : a+(Z.card : ℝ) ≤ εf*n := by
    have hh := hbudget.trans (mul_le_mul_of_nonneg_right (min_le_right εp εf) hnR.le)
    linarith only [hh]
  obtain ⟨v₀⟩ := Fintype.card_pos_iff.mp hnpos
  have hhn : h ≤ n := by
    have hh := G.degree_lt_card_verts v₀
    rw [hregular v₀] at hh
    exact hh.le
  have hhR : (0 : ℝ) < h := (mul_pos hα hnR).trans_le hdensity
  have hαn : α*n ≤ (n : ℝ) := mul_le_of_le_one_left hnR.le hα1
  let q : V → ℝ := fun z => ((originalForeignNeighbors G U assignment z).card : ℝ)
  have hq : ∀ z ∈ Z, 0 ≤ q z := fun z _ => Nat.cast_nonneg _
  obtain ⟨i, hi, hlight⟩ := exists_light_band Z q (h : ℝ) c ρ L
    hhR hc hρanti hq hforeign hlength
  let Low := low Z q (h : ℝ) (ρ (i+1))
  let B := band Z q (h : ℝ) ρ i
  let Z₁ := Z \ Low
  let U₁ := enlargedSets U Low assignment
  let H₁ := enlargedGraphs G U H Low assignment
  let W := fun z => U₁ (assignment z)
  let P := forcingPotential G B W
  let A : ℝ := a+ρ (i+1)*h+Z.card
  have hLowZ : Low ⊆ Z := by
    intro z hz
    exact ((mem_low Z q (h : ℝ) (ρ (i+1)) z).mp hz).1
  have hB₁ : B ⊆ Z₁ := by
    intro z hz
    obtain ⟨hzZ, hlo, _hhi⟩ := (mem_band Z q (h : ℝ) ρ i z).mp hz
    exact mem_sdiff.mpr ⟨hzZ, fun hzLow =>
      (not_lt_of_ge hlo) (((mem_low Z q (h : ℝ) (ρ (i+1)) z).mp hzLow).2)⟩
  have hZ₁card : Z₁.card ≤ t (i+1) := by
    rw [ht (i+1)]
    exact (absorption_card_bounds Z q (h : ℝ) c ρ i hhR hρpos hρanti hq hforeign).1
  have hZ₁T : Z₁.card ≤ T := hZ₁card.trans (hT (i+1) (Nat.succ_le_of_lt hi))
  have hBT : B.card ≤ T := (card_le_card hB₁).trans hZ₁T
  have hPbound : (P : ℝ) ≤ (h : ℝ)/8+(T : ℝ)*Z.card := by
    have hnat := forcingPotential_le_originalForeign_add G U Z B assignment W hcover
      (fun z => old_subset_enlarged U Low assignment (assignment z))
    have hreal : (P : ℝ) ≤ (∑ z ∈ B, q z)+(B.card : ℝ)*Z.card := by
      dsimp only [P, q]
      exact_mod_cast hnat
    have hBTreal : (B.card : ℝ) ≤ T := by exact_mod_cast hBT
    have hmul := mul_le_mul_of_nonneg_right hBTreal (Nat.cast_nonneg Z.card)
    linarith only [hreal, hlight, hmul]
  have scalar (m : ℕ) (hm : α*n ≤ (m : ℝ)) (hmn : m ≤ n) :
      PhaseScalarBounds α Pack.error Pack.output ν T Pack.order n h m Z.card P A :=
    hphase n h m Z.card P a (ρ (i+1)) hNp hdensity hhn hm hmn ha hbudgetp
      (hρpos (i+1)).le (hρκ i) hPbound
  have ambient := scalar n hαn le_rfl
  have hU₁size (j : I) : α*n ≤ ((U₁ j).card : ℝ) :=
    (hsize j).trans (by exact_mod_cast (enlargedSets_card_bounds U Low assignment j).1)
  have hU₁upper (j : I) : (U₁ j).card ≤ n := card_le_univ _
  have hUupper (j : I) : (U j).card ≤ n := card_le_univ _
  have coreScalar (j : I) := scalar (U₁ j).card (hU₁size j) (hU₁upper j)
  have originalScalar (j : I) := scalar (U j).card (hsize j) (hUupper j)
  have hU₁disjoint : Pairwise (fun j k => Disjoint (U₁ j) (U₁ k)) :=
    enlargedSets_pairwise_disjoint U Z Low assignment hdisjoint hUZ hLowZ
  have hU₁Z₁ : ∀ j, Disjoint (U₁ j) Z₁ :=
    enlargedSets_disjoint_remaining U Z Low assignment hUZ
  have hcover₁ : ∀ z, z ∈ Z₁ ∨ ∃ j, z ∈ U₁ j :=
    enlargedSets_cover U Z Low assignment hcover
  have hembed₁ : ∀ j, H₁ j ≤ G.induce (U₁ j : Set V) :=
    enlargedGraphs_le_ambient G U H Low assignment hembed
  have hdegree₁ : ∀ j v, (h : ℝ)-A ≤ ((H₁ j).degree v : ℝ) := by
    apply enlargedGraphs_degree_lower G U H Z Low assignment h a (ρ (i+1)*h)
      ha (mul_nonneg (hρpos (i+1)).le (Nat.cast_nonneg h)) hcover hregular hdegree
    intro z hz
    exact (((mem_low Z q (h : ℝ) (ρ (i+1)) z).mp hz).2).le
  have hupper₁ : ∀ j v, ((H₁ j).degree v : ℝ) ≤ h := by
    intro j v
    exact_mod_cast enlargedGraphs_degree_upper G U H Low assignment h hembed hregular j v
  have hrobust₁ : ∀ j, IsRobustExpander (H₁ j) (ν/4) (2*τ) :=
    enlargedGraphs_robust G U H Z Low assignment ν τ hν.le hντ hτquarter hLowZ
      (fun j => (originalScalar j).input_addition) hrobust
  have hpackingDensity (j : I) : α*(U₁ j).card ≤ (h : ℝ) :=
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hU₁upper j) hα.le).trans hdensity
  have hpackingDegree (j : I) (v : U₁ j) :
      |((H₁ j).degree v : ℝ)-(h : ℝ)| ≤ Pack.error*(U₁ j).card := by
    rw [abs_of_nonpos (sub_nonpos.mpr (hupper₁ j v))]
    have hl := hdegree₁ j v
    have he := (coreScalar j).packing_error
    linarith only [hl, he]
  obtain ⟨rule, hcertificate⟩ := exists_certified_core_rules U₁ H₁
    α (α/4) (ν/4) (2*τ) Pack.error Pack.output Pack.order Pack.rule (h : ℝ)
    (fun j => (coreScalar j).packing_order) hrobust₁ hpackingDensity hpackingDegree
  have hcertificate' : ∀ j, RuleCertificate (H₁ j)
      (Nat.floor ((h : ℝ)-(α/4)*(U₁ j).card)) Pack.error Pack.output τ (rule j) := by
    intro j
    convert hcertificate j using 1
    ring
  let Setup : ForcingSetup G U₁ H₁ := {
    Z := Z₁
    B := B
    W := W
    initialDegree := h
    starBound := T
    density := α/4
    coreError := A
    packingError := Pack.error
    packingOutput := Pack.output
    packingRange := τ
    horizon := fun j => Nat.floor ((h : ℝ)-(α/4)*(U₁ j).card)
    rule := rule
    certificate := hcertificate'
    selected_subset := hB₁
    exceptional_bound := hZ₁T
    core_count := hI
    disjoint := hU₁disjoint
    core_exceptional_disjoint := hU₁Z₁
    cover := hcover₁
    regular := hregular
    no_overfull := hsafe
    core_embed := hembed₁
    core_degree := hdegree₁
    packing_budget := fun j => (coreScalar j).packing_error
    density_pos := by positivity
    output_pos := Pack.output_pos
    range_nonneg := hτpos.le
    range_le_density := by linarith only [hτ, hα]
    degree_reserve := ambient.residual_density
    degree_upper := by
      have hh : (h : ℝ) ≤ n := by exact_mod_cast hhn
      change (h : ℝ) ≤ 2*(n : ℝ)
      linarith only [hh, hnR]
    error_small := ambient.safe_error
    order_large := ambient.robust_cut
    core_size := fun j => by
      have hh := hU₁size j
      have hnonneg := mul_nonneg hα.le hnR.le
      change (α/4)*n ≤ ((U₁ j).card : ℝ)
      nlinarith only [hh, hnonneg]
    footprint_bound := fun j => (coreScalar j).footprint
    horizon_bound := fun j => (coreScalar j).horizon
  }
  obtain ⟨s, Tr, hpotential, hvalid, hterminal, hregularR, hsafeR,
      hembedR, hrobustR, hdegreeR⟩ := Setup.exists_terminal_transcript
  have hsP : s ≤ P := (Nat.le_add_right s _).trans hpotential
  obtain ⟨hfinalpos, hretained⟩ := retained_degree_three_quarters h P s
    ambient.phase_short hsP
  let R := Tr.graph s
  let HR := Tr.currentCore s
  let hfinal := h-s
  let Z₂ := Z₁ \ B
  let U₂ := enlargedSets U₁ B assignment
  let H₂ := enlargedGraphs R U₁ HR B assignment
  have hZ₂card : Z₂.card ≤ t i := by
    rw [ht i]
    exact (absorption_card_bounds Z q (h : ℝ) c ρ i hhR hρpos hρanti hq hforeign).2
  have hZ₂T : Z₂.card ≤ T := hZ₂card.trans (hT i hi.le)
  have hterminal' : ∀ z ∈ B, outsideDegree R (U₁ (assignment z)) z ≤ D := hterminal
  have hdegree₂ : ∀ j v, (hfinal : ℝ)-(A+D) ≤ ((H₂ j).degree v : ℝ) :=
    enlargedGraphs_degree_lower_of_outside R U₁ HR B assignment hfinal D A
      ambient.error_nonneg hregularR (fun j v => (hdegreeR j v).1) hterminal'
  have hsmall₂ (j : I) : (Z₁.card : ℝ) ≤ Pack.output*(U₁ j).card/4 :=
    (show (Z₁.card : ℝ) ≤ Z.card by exact_mod_cast card_le_card (sdiff_subset : Z₁ ⊆ Z)).trans
      (coreScalar j).output_addition
  have hrobust₂ : ∀ j, IsRobustExpander (H₂ j) (Pack.output/4) (2*τ) :=
    enlargedGraphs_robust R U₁ HR Z₁ B assignment Pack.output τ Pack.output_pos.le
      hθτ hτquarter hB₁ hsmall₂ hrobustR
  have herror₂ : A+(D : ℝ) ≤ f Z₂.card*hfinal :=
    hfinalBound i n Z₂.card (h : ℝ) (hfinal : ℝ) a Z.card hi.le hNf hZ₂card
      hdensity hretained hbudgetf
  refine ⟨{
    G := R
    h := hfinal
    N := Tr.full
    rounds := s
    graph_eq := rfl
    degree_eq := rfl
    perfect := hvalid.perfect
    present := hvalid.present
    regular := hregularR
    no_overfull := hsafeR
    degree_positive := hfinalpos
    retained_degree := hretained
    U := U₂
    H := H₂
    Z := Z₂
    error := A+D
    error_nonneg := add_nonneg ambient.error_nonneg (Nat.cast_nonneg D)
    error_bound := herror₂
    exceptional_subset := sdiff_subset.trans sdiff_subset
    exceptional_card := hZ₂T
    core_enlargement := fun j => (old_subset_enlarged U Low assignment j).trans
      (old_subset_enlarged U₁ B assignment j)
    core_disjoint := enlargedSets_pairwise_disjoint U₁ Z₁ B assignment hU₁disjoint hU₁Z₁ hB₁
    core_exceptional_disjoint := enlargedSets_disjoint_remaining U₁ Z₁ B assignment hU₁Z₁
    cover := enlargedSets_cover U₁ Z₁ B assignment hcover₁
    core_embed := enlargedGraphs_le_ambient R U₁ HR B assignment hembedR
    core_degree := hdegree₂
    core_robust := hrobust₂
  }⟩

end Overfull
