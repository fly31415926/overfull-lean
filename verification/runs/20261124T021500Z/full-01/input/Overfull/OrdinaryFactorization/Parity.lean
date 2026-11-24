import Overfull.OrdinaryFactorization.Full

/-!
# Ordinary-core factorization with either core parity

The parity adjustment is carried out on the original embedded core.  At
most one vertex is moved outside, its old core copies remain in the host,
and the proved bounded-core-move theorem colors the new complement.
Uniform tolerances and thresholds precede all graph data.
-/

noncomputable section

namespace Overfull.OrdinaryFactorization

open Finset Classical SmallCuts OneCore

/-- Every nonempty finite core has an even subset obtained by moving at
most one of its own vertices outside. -/
theorem exists_even_core_move {V : Type*} (U : Finset V) (hU : U.Nonempty) :
    ∃ W : Finset V, W ⊆ U ∧ W.card ≤ 1 ∧ Even (U \ W).card := by
  classical
  by_cases heven : Even U.card
  · exact ⟨∅, empty_subset _, by simp, by simpa using heven⟩
  · obtain ⟨x, hx⟩ := hU
    refine ⟨{x}, singleton_subset_iff.mpr hx, by simp, ?_⟩
    have hcard := card_erase_add_one hx
    rw [sdiff_singleton_eq_erase, Nat.even_iff]
    rw [Nat.even_iff] at heven
    omega

/-- The full bounded-exterior ordinary-core coloring conclusion, allowing
an odd or even original core.  The complement coloring is an explicit
input here; later applications construct it from their graph hypotheses. -/
theorem exists_uniform_factorization_any_core_parity (α ν τ : ℝ) (s : ℕ)
    (hα : 0 < α) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτ : τ ≤ min α 1 / 16) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ m₀ : ℕ,
      ∀ (V E : Type*) [Fintype V] [Fintype E]
        (G : Multigraph V E) (U : Finset V) (C : Core G U) (k : ℕ) (a : ℝ),
        m₀ ≤ U.card → Even (Fintype.card V) → Uᶜ.card ≤ s →
        (∀ v, G.degree v = k) → α * U.card ≤ (k : ℝ) →
        IsRobustExpander C.graph ν τ → a ≤ ε * U.card →
        (∀ v, (k : ℝ) - a ≤ (C.graph.degree v : ℝ)) →
        Nonempty ((G.restrictEdges (coreEdges C)ᶜ).EdgeColoring k) →
        Nonempty (G.EdgeColoring k) := by
  classical
  let β : ℝ := min α 1
  have hβ : 0 < β := lt_min hα zero_lt_one
  have hβα : β ≤ α := min_le_left _ _
  have hβ1 : β ≤ 1 := min_le_right _ _
  have hτpos : 0 < τ := hν.trans_le hντ
  have hν1 : ν ≤ 1 := by linarith
  have hτquarter : τ < 1 / 4 := by linarith
  obtain ⟨η, hη, m₁, hfactor⟩ := ordinary_core_factorization β (ν / 2) (2 * τ) (s + 1)
    hβ (by positivity) (by linarith)
    (by rw [min_eq_left hβ1]; linarith)
  let ε : ℝ := min (η / 4) (β / 100)
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  obtain ⟨nRound, hnRound⟩ := exists_nat_gt
    (max (100 / β) (max (4 / η) (2 / ν)))
  refine ⟨ε, hε, max (m₁ + 1) nRound, ?_⟩
  intro V E _ _ G U C k a hn hHostEven hZcard hregular hk hrob hae hdegree hc
  have hnFirst : m₁ + 1 ≤ U.card := (le_max_left _ _).trans hn
  have hnRoundNat : nRound ≤ U.card := (le_max_right _ _).trans hn
  have hnRoundReal : (nRound : ℝ) ≤ U.card := by exact_mod_cast hnRoundNat
  have hnβ : 100 / β ≤ (U.card : ℝ) :=
    ((le_max_left _ _).trans hnRound.le).trans hnRoundReal
  have hnη : 4 / η ≤ (U.card : ℝ) :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans hnRound.le).trans hnRoundReal
  have hnν : 2 / ν ≤ (U.card : ℝ) :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans hnRound.le).trans hnRoundReal
  have hβn : 100 ≤ β * (U.card : ℝ) := by
    have h := (div_le_iff₀ hβ).mp hnβ
    nlinarith only [h]
  have hn2 : 2 ≤ U.card := by
    have hmul := mul_le_mul_of_nonneg_right hβ1 (Nat.cast_nonneg U.card : (0 : ℝ) ≤ U.card)
    have : (2 : ℝ) ≤ U.card := by linarith
    exact_mod_cast this
  have hkβ : β * U.card ≤ (k : ℝ) :=
    (mul_le_mul_of_nonneg_right hβα (Nat.cast_nonneg _)).trans hk
  have haβ : a ≤ β * U.card / 100 := by
    have h := hae.trans (mul_le_mul_of_nonneg_right
      (min_le_right (η / 4) (β / 100)) (Nat.cast_nonneg U.card))
    linarith
  have haη : a ≤ η * U.card / 4 := by
    have h := hae.trans (mul_le_mul_of_nonneg_right
      (min_le_left (η / 4) (β / 100)) (Nat.cast_nonneg U.card))
    linarith
  have hlarge : 2 ≤ ν * U.card := by
    have h := (div_le_iff₀ hν).mp hnν
    nlinarith only [h]
  have hka : 3 * (a + 1) < (k : ℝ) := by nlinarith only [haβ, hβn, hkβ]
  obtain ⟨W, hWU, hWcard, heven⟩ := exists_even_core_move U
    (card_pos.mp (show 0 < U.card by omega))
  let U' := U \ W
  let C' := restrictCore C W
  have hcard : U'.card + W.card = U.card := card_sdiff_add_card_eq_card hWU
  have hcardReal : (U'.card : ℝ) + W.card = U.card := by exact_mod_cast hcard
  have hWcardReal : (W.card : ℝ) ≤ 1 := by exact_mod_cast hWcard
  have hU'le : (U'.card : ℝ) ≤ U.card := by
    exact_mod_cast card_le_card (sdiff_subset : U \ W ⊆ U)
  have hcore : ∀ v ∈ U, ((G.restrictEdges (coreEdges C)ᶜ).degree v : ℝ) ≤ a := by
    intro v hv
    exact complement_degree_le_error C k a hregular hdegree ⟨v, hv⟩
  obtain ⟨hc', _⟩ := G.bounded_core_move_full k a U W (coreEdges C)
    hregular (coreEdges_subset_internal C) (coreEdges_simple C) hcore hc (by linarith)
  have hcNew : Nonempty ((G.restrictEdges (coreEdges C')ᶜ).EdgeColoring k) := by
    change Nonempty ((G.restrictEdges (coreEdges (restrictCore C W))ᶜ).EdgeColoring k)
    rw [restrictCore_edges]
    exact hc'
  have hdegreeNew : ∀ v, (k : ℝ) - (a + 1) ≤ (C'.graph.degree v : ℝ) := by
    intro v
    have hh := (ForeignRefinement.survivingCore_degree_bounds U W C.graph v).2
    have hh' : (C.graph.degree (ForeignRefinement.survivingInclusion U W v) : ℝ) ≤
        C'.graph.degree v + W.card := by exact_mod_cast hh
    linarith only [hh', hdegree (ForeignRefinement.survivingInclusion U W v), hWcardReal]
  have hrobNew : IsRobustExpander C'.graph (ν / 2) (2 * τ) :=
    ForeignRefinement.survivingCore_robust_one U W C.graph ν τ
      hrob hν.le hν1 hτpos.le hτquarter hWcard hlarge
  have hZNew : U'ᶜ.card ≤ s + 1 := by
    have heq : U'ᶜ = Uᶜ ∪ W := by
      ext v
      simp only [U', mem_compl, mem_sdiff, mem_union]
      tauto
    rw [heq]
    exact (card_union_le _ _).trans (Nat.add_le_add hZcard hWcard)
  have haNew : a + 1 ≤ η * U'.card := by
    have hfour := (div_le_iff₀ hη).mp hnη
    have hn2Real : (2 : ℝ) ≤ U.card := by exact_mod_cast hn2
    have hhalf : (U.card : ℝ) / 2 ≤ U'.card := by linarith
    have hmul := mul_le_mul_of_nonneg_left hhalf hη.le
    nlinarith only [haη, hfour, hmul]
  have hkNew : β * U'.card ≤ (k : ℝ) :=
    (mul_le_mul_of_nonneg_left hU'le hβ.le).trans hkβ
  exact hfactor V E G U' C' k (a + 1) (by omega) heven hHostEven hZNew
    hregular hkNew hrobNew haNew hdegreeNew hcNew

end Overfull.OrdinaryFactorization
