import Overfull.OneCore.NeighborPairing
import Overfull.OneCore.ApexChoices
import Overfull.OrdinaryFactorization.Reduction

/-!
# A one-apex graph reduced to a bipartite core with a supplied apex

The old core vertex moved outside retains a linear number of actual
incidences on both shores. The pairing is chosen from its original simple
neighbors, and the first completed labels are chosen evenly from its two
rows. All constants precede the host graph and all edge-copy choices.
-/

noncomputable section

namespace Overfull.OneCore

open Finset Classical SmallCuts OrdinaryFactorization

set_option maxHeartbeats 800000 in
/-- Uniformly reduce the one-apex problem while preserving the supply
needed by the two-apex bipartite cleanup. -/
theorem exists_uniform_two_apex_reduction (α ν τ : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτα : τ ≤ α / 8) :
    ∃ ν₁ τ₁ ξ : ℝ,
      0 < ν₁ ∧ ν₁ ≤ τ₁ ∧ 0 < τ₁ ∧ τ₁ ≤ α / 512 ∧ 0 < ξ ∧
      ∀ η : ℝ, 0 < η →
        ∃ p σ κ δ μ ε : ℝ,
          0 < p ∧ 0 < σ ∧ 0 < κ ∧ 0 < δ ∧ 0 < μ ∧ 0 < ε ∧
          ∀ mExt : ℕ, ∃ m₀ : ℕ,
            ∀ (V E : Type*) [Fintype V] [Fintype E]
              (G : Multigraph V E) (U : Finset V) (C : Core G U)
              (z : V) (k : ℕ) (a : ℝ),
              m₀ ≤ U.card → U.card % 2 = 1 → Uᶜ = {z} →
              (∀ v, G.degree v = k) → α * U.card ≤ (k : ℝ) →
              IsRobustExpander C.graph ν τ → 0 ≤ a → a ≤ ε * U.card →
              (∀ v, (k : ℝ) - a ≤ (C.graph.degree v : ℝ)) →
              ∃ (y : U) (D : FirstHalfData G (U \ {y.val})
                  (restrictCore C {y.val}) k (α / 2) ν₁ τ₁ ξ p σ κ δ μ),
                mExt ≤ D.geometry.left.card ∧ Nonempty (BipartiteResidualData D η) ∧
                (U \ {y.val})ᶜ = {z, y.val} ∧ z ≠ y.val ∧
                (α / 100) * D.geometry.left.card ≤
                  ((D.remaining.edgesTo y.val (D.geometry.left.map
                    (Function.Embedding.subtype (fun v => v ∈ U \ {y.val})))).card : ℝ) ∧
                (α / 100) * D.geometry.left.card ≤
                  ((D.remaining.edgesTo y.val (D.geometry.right.map
                    (Function.Embedding.subtype (fun v => v ∈ U \ {y.val})))).card : ℝ) := by
  have hτ : 0 < τ := hν.trans_le hντ
  let τ₀ := min τ (α / 1024)
  have hτ₀ : 0 < τ₀ := lt_min hτ (by positivity)
  have hτ₀τ : τ₀ ≤ τ := min_le_left _ _
  have hτ₀α : τ₀ ≤ α / 1024 := min_le_right _ _
  let ν₀ := min ν (α * τ₀ / 4)
  have hν₀ : 0 < ν₀ := lt_min hν (by positivity)
  have hν₀τ : ν₀ ≤ τ₀ := by
    have h := min_le_right ν (α * τ₀ / 4)
    have hmul := mul_le_mul_of_nonneg_right hα1 hτ₀.le
    dsimp only [ν₀]
    linarith
  have hν₀one : ν₀ ≤ 1 := by linarith
  have hν₁τ₁ : ν₀ / 2 ≤ 2 * τ₀ := by linarith
  have hτ₁α : 2 * τ₀ ≤ α / 512 := by linarith
  obtain ⟨ξ, hξ, hreduce⟩ := exists_uniform_bipartite_reduction_with_choices
    (α / 2) (ν₀ / 2) (2 * τ₀) (by positivity) (by linarith)
    (by positivity) hν₁τ₁ (by linarith)
  refine ⟨ν₀ / 2, 2 * τ₀, ξ, by positivity, hν₁τ₁, by positivity, hτ₁α, hξ, ?_⟩
  intro η hη
  obtain ⟨p, σ, κ, δ, μ, ε₁, hp, hσ, hκ, hδ, hμ, hε₁, hthreshold⟩ := hreduce η hη
  let ε := min (ε₁ / 4) (α / 100)
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  have hε₁bound : ε ≤ ε₁ / 4 := min_le_left _ _
  have hεα : ε ≤ α / 100 := min_le_right _ _
  refine ⟨p, σ, κ, δ, μ, ε, hp, hσ, hκ, hδ, hμ, hε, ?_⟩
  intro mExt
  obtain ⟨nFirst, hFirst⟩ := hthreshold mExt
  obtain ⟨nRound, hnRound⟩ := exists_nat_gt
    (max (100 / α) (max (4 / ε₁) (2 / ν₀)))
  refine ⟨max (nFirst + 1) nRound, ?_⟩
  intro V E _ _ G U C z k a hn hodd hout hregular hk hrob ha haε hdegree
  have hnFirst : nFirst + 1 ≤ U.card := (le_max_left _ _).trans hn
  have hnRoundNat : nRound ≤ U.card := (le_max_right _ _).trans hn
  have hnRoundReal : (nRound : ℝ) ≤ U.card := by exact_mod_cast hnRoundNat
  have hnα : 100 / α ≤ (U.card : ℝ) :=
    ((le_max_left _ _).trans hnRound.le).trans hnRoundReal
  have hnε : 4 / ε₁ ≤ (U.card : ℝ) :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans hnRound.le).trans hnRoundReal
  have hnν : 2 / ν₀ ≤ (U.card : ℝ) :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans hnRound.le).trans hnRoundReal
  have hαn : 100 ≤ α * (U.card : ℝ) := by
    have h := (div_le_iff₀ hα).mp hnα
    nlinarith only [h]
  have hn2 : 2 ≤ U.card := by
    have hmul := mul_le_mul_of_nonneg_right hα1 (Nat.cast_nonneg U.card : (0 : ℝ) ≤ U.card)
    have : (2 : ℝ) ≤ U.card := by linarith
    exact_mod_cast this
  have haα : a ≤ α * U.card / 100 := by
    have h := haε.trans (mul_le_mul_of_nonneg_right hεα (Nat.cast_nonneg _))
    linarith
  have haFirst : a ≤ ε₁ * U.card / 4 := by
    have h := haε.trans (mul_le_mul_of_nonneg_right hε₁bound (Nat.cast_nonneg _))
    linarith
  have hcoreMin (v : U) : (α / 2) * Fintype.card U ≤ (C.graph.degree v : ℝ) := by
    simp only [Fintype.card_coe]
    nlinarith only [hk, haα, hdegree v, hαn]
  have hparam : min ν ((α / 2) * τ₀ / 2) = ν₀ := by
    dsimp only [ν₀]
    congr 1
    ring
  have hsmallRange : IsRobustExpander C.graph ν₀ τ₀ := by
    rw [← hparam]
    exact robust_range_reduction C.graph (α / 2) ν τ τ₀ (by positivity)
      (by linarith) hν (by linarith) hτ₀ hτ₀τ hcoreMin hrob
  have hlarge : 2 ≤ ν₀ * U.card := by
    have h := (div_le_iff₀ hν₀).mp hnν
    nlinarith only [h]
  have hka : 3 * (a + 1) < (k : ℝ) := by nlinarith only [haα, hαn, hk]
  obtain ⟨yv, hyv⟩ := Finset.card_pos.mp (show 0 < U.card by omega)
  let y : U := ⟨yv, hyv⟩
  let W := U \ {y.val}
  let Cnew := restrictCore C {y.val}
  obtain ⟨heven, houtside, _houtsideCard, ⟨c₀⟩, hnewDegree, hnewRobust⟩ :=
    even_core_complement C z y.val k a ν₀ τ₀ hregular hout hodd y.property
      hdegree hka hsmallRange hν₀.le hν₀one hτ₀.le (by linarith) hlarge
  have hWcard : W.card + 1 = U.card := by
    simpa only [W, Finset.sdiff_singleton_eq_erase] using Finset.card_erase_add_one y.property
  have hWcardReal : (W.card : ℝ) + 1 = U.card := by exact_mod_cast hWcard
  have hWle : (W.card : ℝ) ≤ U.card := by linarith
  have hWnonneg : (0 : ℝ) ≤ W.card := Nat.cast_nonneg _
  have hnW : nFirst ≤ W.card := by omega
  have hWeven : Even W.card := Nat.even_iff.mpr heven
  have hhostCard : Fintype.card V = U.card + 1 := by
    have hcompl := Finset.card_compl U
    rw [hout, card_singleton] at hcompl
    have hle := U.card_le_univ
    omega
  have hHostEven : Even (Fintype.card V) := by
    rw [Nat.even_iff, hhostCard]
    omega
  have haNew : a + 1 ≤ ε₁ * W.card := by
    have hfour := (div_le_iff₀ hε₁).mp hnε
    have hn2Real : (2 : ℝ) ≤ U.card := by exact_mod_cast hn2
    have hhalf : (U.card : ℝ) / 2 ≤ W.card := by linarith
    have hmul := mul_le_mul_of_nonneg_left hhalf hε₁.le
    nlinarith only [haFirst, hfour, hmul]
  have hkW : (α / 2) * W.card ≤ (k : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hWle hα.le
    nlinarith only [hmul, hk, mul_nonneg hα.le hWnonneg]
  have hz : z ∉ U := mem_compl.mp (by rw [hout]; simp)
  have hzy : z ≠ y.val := by intro h; exact hz (h ▸ y.property)
  have hpairExists := NeighborPairing.exists_balancing_pairing
    (W := W) (by simpa only [Fintype.card_coe] using hWeven) (movedNeighbors C y)
  have hWtype : Fintype.card ↥W = W.card := Fintype.card_coe W
  rw [hWtype] at hpairExists
  obtain ⟨pairing, hpairing⟩ := hpairExists
  let t : ℝ := (α / 100) * W.card / 2
  have ht : 0 ≤ t := by dsimp only [t]; positivity
  have htbudget : t + a / 2 + 1 ≤ (k : ℝ) / 5 := by
    have hmul := mul_le_mul_of_nonneg_left hWle hα.le
    dsimp only [t]
    nlinarith only [hmul, haα, hαn, hk]
  obtain ⟨D, hmSide, hD, _hpair, hSupply⟩ := hFirst V E G W Cnew k (a + 1)
    hnW hWeven hHostEven hregular hkW hnewRobust (by linarith) haNew hnewDegree c₀
    pairing (apexSupply Cnew y.val t) (by
      intro geometry h _hhpos _hhle hhupper c
      obtain ⟨_hleftHalf, _hrightHalf, hleft, hright⟩ :=
        hpairing geometry.left geometry.right (fun i => by
          rcases geometry.split_pairs i with hi | hi
          · exact Or.inl hi
          · exact Or.inr ⟨hi.2, hi.1⟩)
      exact exists_apexSupply C y geometry.left geometry.right k h a t
        geometry.disjoint
        (by
          convert hleft using 1
          congr 3
          ext v
          simp only [mem_inter])
        (by
          convert hright using 1
          congr 3
          ext v
          simp only [mem_inter])
        (hdegree y) hhupper ht htbudget c)
  have hsupply := D.remaining_apex_supply y.val (by simp [W]) t
    D.geometry.left D.geometry.right hSupply
  have hhalf : (W.card : ℝ) = 2 * D.geometry.left.card := by
    have h := core_card_eq_twice_left_card Cnew D
    simp only [Fintype.card_coe] at h
    exact_mod_cast h
  have htSide : t = (α / 100) * D.geometry.left.card := by
    dsimp only [t]
    rw [hhalf]
    ring
  rw [htSide] at hsupply
  exact ⟨y, D, hmSide, hD, houtside, hzy, hsupply.1, hsupply.2⟩

end Overfull.OneCore
