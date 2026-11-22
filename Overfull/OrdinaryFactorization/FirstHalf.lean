import Overfull.OrdinaryFactorization.FirstHalfData
import Overfull.OrdinaryFactorization.CutReserveBounds
import Overfull.OrdinaryFactorization.UniformColorRepair

/-!
# Uniform construction of the first completed colors

The crossing robustness constant is fixed before the reserve probability.
The reserve range and repair tolerance follow that probability; only then
are the coloring tolerances and the order threshold chosen. All graphs,
the embedded core, and the initial exterior coloring are supplied last.

The conclusion contains actual pairwise disjoint perfect matchings on the
original host copies. It does not supply a coloring of the remaining graph.
-/

noncomputable section

namespace Overfull.OrdinaryFactorization

open Finset Classical SmallCuts ColoringExtension

/-- Changing only the decision procedure preserves actual robust expansion. -/
private theorem robust_expander_change_instance
    {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W)
    {d₁ d₂ : DecidableRel H.Adj} {ρ θ : ℝ}
    (h : @IsRobustExpander W _ _ H d₁ ρ θ) :
    @IsRobustExpander W _ _ H d₂ ρ θ := by
  have hd : d₁ = d₂ := Subsingleton.elim _ _
  cases hd
  exact h

/-- Uniformly construct the first group of completed colors in an ordinary
robust core. The actual initial exterior coloring is the only coloring
input; the internal coloring and all repaired matchings are constructed. -/
theorem exists_uniform_first_half (α ν τ : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτα : τ ≤ α / 8) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∀ p : ℝ, 0 < p → p ≤ 1 / 2 →
      ∃ σ μ₀ : ℝ, 0 < σ ∧ σ ≤ τ ∧ 0 < μ₀ ∧
        ∀ μ : ℝ, 0 < μ → μ ≤ μ₀ →
          ∃ κ δ ε : ℝ, 0 < κ ∧ κ ≤ α / 512 ∧
            0 < δ ∧ δ ≤ p * α / 32 ∧ 0 < ε ∧ ε ≤ p ∧
            ∃ m₀ : ℕ, ∀ (V E : Type*) [Fintype V] [Fintype E]
              (G : Multigraph V E) (U : Finset V) (C : Core G U)
              (k : ℕ) (a : ℝ),
              m₀ ≤ U.card → Even U.card → Even (Fintype.card V) →
              (∀ v, G.degree v = k) → α * U.card ≤ (k : ℝ) →
              IsRobustExpander C.graph ν τ → 0 ≤ a → a ≤ ε * U.card →
              (∀ v, (k : ℝ) - a ≤ (C.graph.degree v : ℝ)) →
              (_c₀ : (G.restrictEdges (OneCore.coreEdges C)ᶜ).EdgeColoring k) →
              Nonempty (FirstHalfData G U C k α ν τ ξ p σ κ δ μ) := by
  have hτ : 0 < τ := hν.trans_le hντ
  obtain ⟨ξ, hξ, hgeometry⟩ := exists_cut_reserve (α / 2) ν τ
    (by positivity) (by linarith) hν hντ (by linarith) (by linarith)
  refine ⟨ξ, hξ, ?_⟩
  intro p hp hpHalf
  have hp1 : p ≤ 1 := by linarith
  let σ : ℝ := min τ (min (1 / 16) (p * α / 1000))
  have hσ : 0 < σ := lt_min hτ (lt_min (by norm_num) (by positivity))
  have hστ : σ ≤ τ := min_le_left _ _
  have hσ16 : σ ≤ 1 / 16 := (min_le_right _ _).trans (min_le_left _ _)
  have hσp : σ ≤ p * α / 1000 := (min_le_right _ _).trans (min_le_right _ _)
  let νR : ℝ := min ν (α * σ / 4)
  have hνR : 0 < νR := lt_min hν (by positivity)
  have hνRσ : νR ≤ σ := by
    have h := min_le_right ν (α * σ / 4)
    have hασ := mul_le_mul_of_nonneg_right hα1 hσ.le
    dsimp only [νR]
    linarith
  have hreserveRange : p * νR / 4 ≤ 4 * σ := by
    have hpνR := mul_le_mul_of_nonneg_right hp1 hνR.le
    nlinarith only [hpνR, hνRσ, hσ]
  obtain ⟨μ₀, hμ₀, hrepair⟩ := exists_uniform_repaired_color_family
    (p * α / 2) (p * νR / 4) σ (α / 8)
    (by positivity) (by positivity) hreserveRange hσ16
    (by nlinarith only [hσp, mul_pos hp hα])
    (by positivity) (by linarith)
  refine ⟨σ, μ₀, hσ, hστ, hμ₀, ?_⟩
  intro μ hμ hμμ₀
  obtain ⟨κ, εColor, hκ, _hκQuarter, hκβ, hεColor, nRepair, hRepair⟩ :=
    hrepair μ hμ hμμ₀
  have hκsmall : κ ≤ α / 512 := by linarith only [hκβ]
  let δ : ℝ := min (κ / 24) (min (p * α / 32) (α / 1000))
  have hδ : 0 < δ := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hδκ : δ ≤ κ / 24 := min_le_left _ _
  have hδp : δ ≤ p * α / 32 := (min_le_right _ _).trans (min_le_left _ _)
  have hδα : δ ≤ α / 1000 := (min_le_right _ _).trans (min_le_right _ _)
  let ε : ℝ := min (α / 4) (min κ (min εColor (min (α * εColor / 4) p)))
  have hε : 0 < ε := lt_min (by positivity)
    (lt_min hκ (lt_min hεColor (lt_min (by positivity) hp)))
  have hεα : ε ≤ α / 4 := min_le_left _ _
  have hεκ : ε ≤ κ := (min_le_right _ _).trans (min_le_left _ _)
  have hεc : ε ≤ εColor :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hεαc : ε ≤ α * εColor / 4 :=
    (((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)).trans
      (min_le_left _ _)
  have hεp : ε ≤ p :=
    (((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)).trans
      (min_le_right _ _)
  obtain ⟨nGeometry, hGeometry⟩ := hgeometry p hp hp1 σ hσ hστ δ hδ
  obtain ⟨nRound, hnRound⟩ := exists_nat_gt (max (100 / α) (8 / εColor))
  refine ⟨κ, δ, ε, hκ, hκsmall, hδ, hδp, hε, hεp,
    max nGeometry (max nRepair nRound), ?_⟩
  intro V E _ _ G U C k a hn hEven hHostEven hregular hk hrob ha hεa hdegree c₀
  have hnGeometry : nGeometry ≤ U.card := (le_max_left _ _).trans hn
  have hnRepair : nRepair ≤ U.card :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnRoundNat : nRound ≤ U.card :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hnRoundReal : (nRound : ℝ) ≤ U.card := by exact_mod_cast hnRoundNat
  have hnα : 100 / α ≤ (U.card : ℝ) :=
    ((le_max_left _ _).trans hnRound.le).trans hnRoundReal
  have hnc : 8 / εColor ≤ (U.card : ℝ) :=
    ((le_max_right _ _).trans hnRound.le).trans hnRoundReal
  have hn0 : (0 : ℝ) < U.card := (by positivity : (0 : ℝ) < 100 / α).trans_le hnα
  have hn0Nat : 0 < U.card := by exact_mod_cast hn0
  have hk0 : (0 : ℝ) < k := (mul_pos hα hn0).trans_le hk
  have hnnonneg : (0 : ℝ) ≤ U.card := hn0.le
  have haα : a ≤ α * U.card / 4 := by
    have h := mul_le_mul_of_nonneg_right hεα hnnonneg
    nlinarith only [hεa, h]
  have haκ : a ≤ κ * U.card :=
    hεa.trans (mul_le_mul_of_nonneg_right hεκ hnnonneg)
  have haColor : a ≤ εColor * U.card :=
    hεa.trans (mul_le_mul_of_nonneg_right hεc hnnonneg)
  have haαColor : a ≤ α * εColor * U.card / 4 := by
    have h := mul_le_mul_of_nonneg_right hεαc hnnonneg
    nlinarith only [hεa, h]
  have hcoreUpper (v : U) : (C.graph.degree v : ℝ) ≤ k := by
    exact_mod_cast (OneCore.core_degree_le C v).trans_eq (hregular v.val)
  have hcoreMin (v : U) : (α / 2) * U.card ≤ (C.graph.degree v : ℝ) := by
    nlinarith only [hk, haα, hdegree v, mul_nonneg hα.le hnnonneg]
  have hpairCard : Fintype.card (Fin (U.card / 2) × Bool) = Fintype.card U := by
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, Fintype.card_coe]
    have he := hEven.two_dvd
    omega
  let pairing : Fin (U.card / 2) × Bool ≃ U := Fintype.equivOfCardEq hpairCard
  obtain ⟨D⟩ := hGeometry U (Fin (U.card / 2)) C.graph pairing
    (by simpa only [Fintype.card_coe] using hnGeometry)
    (by simpa only [Fintype.card_coe] using hcoreMin) hrob
  have hνReq : min ν ((α / 2) * σ / 2) = min ν (α * σ / 4) := by congr 1; ring
  rw [hνReq] at D
  have hRmin (v : U) : (p * α / 2) * U.card ≤ (D.reserve.degree v : ℝ) := by
    simpa only [Fintype.card_coe] using D.reserve_degree_linear_lower k a α hp.le
      (by simpa only [Fintype.card_coe] using hk)
      (by simpa only [Fintype.card_coe] using haα)
      (by nlinarith only [hδp, mul_pos hp hα]) hdegree v
  have hJmin (v : U) : (α / 8) * U.card ≤ (D.internal.degree v : ℝ) := by
    simpa only [Fintype.card_coe] using D.internal_degree_linear_lower k a α hpHalf
      (by simpa only [Fintype.card_coe] using hk)
      (by simpa only [Fintype.card_coe] using haα)
      (by linarith only [hδα, hα]) hdegree v
  have hJspread (v : U) :
      (D.internal.maxDegree : ℝ) - D.internal.degree v ≤ κ * U.card := by
    have h := D.internal_degree_spread k a ha hp.le hp1
      (fun w => ⟨hdegree w, hcoreUpper w⟩) v
    simp only [Fintype.card_coe] at h
    have hδn := mul_le_mul_of_nonneg_right hδκ hnnonneg
    nlinarith only [h, hδn, haκ, mul_pos hκ hn0]
  let h : ℕ := D.internal.maxDegree + 1 + Nat.ceil (κ * U.card)
  obtain ⟨hhpos, hhupper, hhle, _hhremaining⟩ := D.paletteSize_bounds k α κ hα
    hκ.le hκsmall hδ.le hδα hp.le hp1
    (by simpa only [Fintype.card_coe] using hk)
    (by simpa only [Fintype.card_coe] using hnα) hcoreUpper
  simp only [CutReserveData.paletteSize, Fintype.card_coe] at hhpos hhupper hhle
  change 0 < h at hhpos
  change (h : ℝ) ≤ 3 * k / 5 at hhupper
  change h ≤ k at hhle
  let labels : Fin h ↪ Fin k := Fin.castLEEmb hhle
  have hOutsideEven : Even Uᶜ.card := by
    rw [Finset.card_compl]
    have hle := U.card_le_univ
    simp only [Nat.even_iff] at hHostEven hEven ⊢
    omega
  obtain ⟨c, _hequitable, hFparity, hFscaled, hFload⟩ :=
    exists_equitable_selected_exterior C c₀ labels a hregular hdegree hOutsideEven
  have hsmall2 : (2 : ℝ) ≤ εColor * U.card / 4 := by
    have h := (div_le_iff₀ hεColor).mp hnc
    nlinarith only [h]
  have hFsize (i : Fin h) :
      ((selectedFootprint C c labels i).card : ℝ) ≤ εColor * U.card := by
    have hscaled := hFscaled i
    have hmul1 := mul_le_mul_of_nonneg_right haαColor hnnonneg
    have hmul2 := mul_le_mul_of_nonneg_right hk
      (show 0 ≤ εColor * (U.card : ℝ) / 4 by positivity)
    have hmul3 := mul_le_mul_of_nonneg_left hsmall2 hk0.le
    have hpositive : 0 ≤ (k : ℝ) * εColor * U.card := by positivity
    apply (mul_le_mul_iff_right₀ hk0).mp
    nlinarith only [hscaled, hmul1, hmul2, hmul3, hpositive]
  have hFloadColor (v : U) :
      ((forbiddenColors (selectedFootprint C c labels) v).card : ℝ) ≤ εColor * U.card := by
    convert (hFload v).trans haColor using 2
    congr 1
    ext i
    simp only [mem_forbiddenColors, mem_filter, mem_univ, true_and]
  have hRepairGraph :=
    hRepair U C.graph D.reserve D.internal D.reserve_le D.internal_le D.internal_disjoint
      U.card (Fintype.card_coe U) hnRepair hEven
  have hRepairReserveDegree := hRepairGraph
      (by
        intro v
        simpa only [← SimpleGraph.card_neighborSet_eq_degree, Fintype.card_eq_nat_card]
          using hRmin v)
  have hRepairReserve := hRepairReserveDegree
    (robust_expander_change_instance D.reserve D.reserve_robust)
  have hRepairInternal := hRepairReserve hJmin hJspread
  obtain ⟨_hcount, cInternal, havoid, N, hN, hverts, hsupport, hdisjoint, hused, hreleased⟩ :=
    hRepairInternal (selectedFootprint C c labels) hFparity hFsize hFloadColor
  have hcountLower : (α / 8) * U.card ≤ (h : ℝ) := by
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hn0Nat
    have hdegreeMax : D.internal.degree ⟨v, hv⟩ ≤ D.internal.maxDegree :=
      D.internal.degree_le_maxDegree ⟨v, hv⟩
    have hmaxCount : D.internal.maxDegree ≤ h := by dsimp only [h]; omega
    exact (hJmin ⟨v, hv⟩).trans (by exact_mod_cast hdegreeMax.trans hmaxCount)
  exact ⟨{
    pairing := pairing
    geometry := D
    count := h
    count_eq := rfl
    count_pos := hhpos
    count_le := hhle
    count_upper := hhupper
    count_lower := hcountLower
    exteriorColor := c
    labels := labels
    internalColor := cInternal
    avoids := havoid
    matchings := N
    matching := hN
    verts := hverts
    support := hsupport
    disjoint := hdisjoint
    reserve_used := hused
    internal_released := hreleased
  }⟩

end Overfull.OrdinaryFactorization
