import Overfull.OrdinaryFactorization.ReductionBounded
import Overfull.BoundedExterior.ReserveChoice
import Overfull.BoundedExterior.ResidualReserve
import Overfull.BoundedExterior.ReservedColors
import Overfull.BoundedExterior.ColorFactorization

/-!
# Full ordinary-core factorization with bounded exterior

An equitable coloring of the original core complement determines bounded
even exterior footprints. A quantitative paired cut balances a positive
fraction of them. Finite pigeonholing gives a linear palette compatible
with one balanced exterior split, and the first completed colors avoid
that palette. Its actual exterior copies survive with their original
labels in the residual complementary coloring. The bounded-exterior
cleanup colors the whole residual, and exact reconstruction colors every
original copy. All parameters precede the input graph and coloring.
-/

noncomputable section

namespace Overfull.OrdinaryFactorization

open Finset Classical SmallCuts BoundedExterior OneCore

private theorem bipartite_robust_change_bounded_instances
    {A B : Type*} [Fintype A] [Fintype B] (H : SimpleGraph (A ⊕ B))
    {d₁ d₂ : DecidableEq A} {r₁ r₂ : DecidableRel H.Adj} {ν τ : ℝ}
    (h : @IsBipartiteRobustExpander A B _ _ d₁ H r₁ ν τ) :
    @IsBipartiteRobustExpander A B _ _ d₂ H r₂ ν τ := by
  have hd : d₁ = d₂ := Subsingleton.elim _ _
  have hr : r₁ = r₂ := Subsingleton.elim _ _
  cases hd
  cases hr
  exact h

set_option maxHeartbeats 1600000 in
/-- Complete uniform factorization from an ordinary robust core, a bounded
even exterior, and the supplied coloring of the actual core complement. -/
theorem exists_uniform_ordinary_core_factorization (α ν τ : ℝ) (s : ℕ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτα : τ ≤ α / 8) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ m₀ : ℕ,
      ∀ (V E : Type*) [Fintype V] [Fintype E]
        (G : Multigraph V E) (U : Finset V) (C : Core G U) (k : ℕ) (a : ℝ),
        m₀ ≤ U.card → Even U.card → Even (Fintype.card V) → Uᶜ.card ≤ s →
        (∀ v, G.degree v = k) → α * U.card ≤ (k : ℝ) →
        IsRobustExpander C.graph ν τ → 0 ≤ a → a ≤ ε * U.card →
        (∀ v, (k : ℝ) - a ≤ (C.graph.degree v : ℝ)) →
        (G.restrictEdges (coreEdges C)ᶜ).EdgeColoring k →
        Nonempty (G.EdgeColoring k) := by
  have hτ : 0 < τ := hν.trans_le hντ
  let τ₀ : ℝ := min τ (α / 1024)
  have hτ₀ : 0 < τ₀ := lt_min hτ (by positivity)
  have hτ₀τ : τ₀ ≤ τ := min_le_left _ _
  have hτ₀α : τ₀ ≤ α / 1024 := min_le_right _ _
  let ν₀ : ℝ := min ν (α * τ₀ / 4)
  have hν₀ : 0 < ν₀ := lt_min hν (by positivity)
  have hν₀τ : ν₀ ≤ τ₀ := by
    have h := min_le_right ν (α * τ₀ / 4)
    have hmul := mul_le_mul_of_nonneg_right hα1 hτ₀.le
    dsimp only [ν₀]
    linarith
  obtain ⟨ξ, hξ, hreduce⟩ :=
    exists_uniform_bipartite_reduction_with_bounded_footprints α ν₀ τ₀ s
      hα hα1 hν₀ hν₀τ (by linarith)
  let νB : ℝ := min (ξ / 2) (4 * τ₀)
  have hνB : 0 < νB := lt_min (by positivity) (by positivity)
  have hνBτ : νB ≤ 4 * τ₀ := min_le_right _ _
  have hτB : 4 * τ₀ < (α / 4) / 16 := by linarith
  have hdenom : (0 : ℝ) < reserveDenominator s := by
    exact_mod_cast reserveDenominator_pos s
  have hdenom8 : (8 : ℝ) ≤ reserveDenominator s := by
    exact_mod_cast reserveDenominator_ge_eight s
  let γ : ℝ := α / (reserveDenominator s : ℝ)
  have hγ : 0 < γ := div_pos hα hdenom
  have hγ1 : γ < 1 := (div_lt_one hdenom).mpr (by linarith)
  obtain ⟨η, hη, mB, hfactor⟩ :=
    exists_uniform_factorization_of_reserved_colors (α / 4) (α / 4) γ νB (4 * τ₀)
      (by positivity) (by linarith) (by positivity) hγ hγ1 hνB hνBτ hτB
  obtain ⟨p, σ, κ, δ, μ, ε₁, _hp, _hσ, _hκ, _hδ, _hμ, hε₁, hthreshold⟩ :=
    hreduce η hη
  obtain ⟨nFirst, hFirst⟩ := hthreshold mB
  let ε : ℝ := min ε₁ (α / 2)
  have hε : 0 < ε := lt_min hε₁ (by positivity)
  obtain ⟨nLarge, hnLarge⟩ := exists_nat_gt (2 * (reserveDenominator s : ℝ) / α)
  refine ⟨ε, hε, max nFirst (max nLarge 1), ?_⟩
  intro V E _ _ G U C k a hn heven hHostEven hZcard hregular hk hrob ha hae hdegree c₀
  have hnFirst : nFirst ≤ U.card := (le_max_left _ _).trans hn
  have hnLargeNat : nLarge ≤ U.card :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hn
  have hnLargeReal : (nLarge : ℝ) ≤ U.card := by exact_mod_cast hnLargeNat
  have hlarge : 2 * reserveDenominator s ≤ k := by
    have h := (div_le_iff₀ hα).mp (hnLarge.le.trans hnLargeReal)
    have hreal : (2 : ℝ) * reserveDenominator s ≤ k := by nlinarith only [h, hk]
    exact_mod_cast hreal
  have haFirst : a ≤ ε₁ * U.card := hae.trans
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _))
  have haα : a ≤ (α / 2) * U.card := hae.trans
    (mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg _))
  have hcoreMin (v : U) : (α / 2) * Fintype.card U ≤ (C.graph.degree v : ℝ) := by
    simp only [Fintype.card_coe]
    nlinarith only [hk, haα, hdegree v]
  have hsmallRange : IsRobustExpander C.graph ν₀ τ₀ := by
    have hparam : min ν ((α / 2) * τ₀ / 2) = ν₀ := by
      dsimp only [ν₀]
      congr 1
      ring
    rw [← hparam]
    exact robust_range_reduction C.graph (α / 2) ν τ τ₀ (by positivity)
      (by linarith) hν (by linarith) hτ₀ hτ₀τ hcoreMin hrob
  have hZeven : Even Uᶜ.card := by
    rw [Nat.even_iff] at heven hHostEven ⊢
    rw [card_compl]
    have hle := U.card_le_univ
    omega
  have hpairCard : Fintype.card (Fin (U.card / 2) × Bool) = Fintype.card U := by
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, Fintype.card_coe]
    have hmod := Nat.even_iff.mp heven
    omega
  let pairing : Fin (U.card / 2) × Bool ≃ U := Fintype.equivOfCardEq hpairCard
  let X := fun (c : (G.restrictEdges (coreEdges C)ᶜ).EdgeColoring k) (i : Fin k) =>
    coreFootprintSubtype G U (exteriorClass U c i)
  have hXeven : ∀ c i, Even (X c i).card := fun c i =>
    (coreComplement_exteriorClass_footprint_bounds C c hregular hZeven i).1
  have hXsize : ∀ c i, (X c i).card ≤ s := fun c i =>
    (coreComplement_exteriorClass_footprint_bounds C c hregular hZeven i).2.trans hZcard
  let P := fun (A _B : Finset U) (h : ℕ)
    (c : (G.restrictEdges (coreEdges C)ᶜ).EdgeColoring k) (labels : Fin h ↪ Fin k) =>
    Nonempty (OriginalReserve C c A labels s)
  obtain ⟨D, hmB, ⟨R⟩, _hpair, ⟨S⟩⟩ :=
    hFirst V E G U C k a hnFirst heven hHostEven hregular hk hsmallRange ha haFirst hdegree
      c₀ pairing X hXeven hXsize P (by
        intro geometry h _hpos _hle hupper c hmany
        exact exists_originalReserve C c geometry.left geometry.right s h hregular
          hZcard hlarge geometry.disjoint geometry.cover hmany hupper)
  let J : Finset (Fin (k - D.count)) := residualReservedLabels D.labels S.J
  have hJcard : J.card = reserveCount k s :=
    (residualReservedLabels_card D.labels S.J S.avoid).trans S.reserved_card
  let e := residualShoreEquiv C D
  have hrobB : IsBipartiteRobustExpander
      ((residualCrossingCore C D).graph.comap e) νB (4 * τ₀) := by
    apply residualShore_robust C D
    exact IsBipartiteRobustExpander.mono_parameter _ R.robust (min_le_left _ _)
  have hhalf : (U.card : ℝ) = 2 * Fintype.card D.geometry.left := by
    have h := core_card_eq_twice_left_card C D
    simp only [Fintype.card_coe] at h ⊢
    exact_mod_cast h
  have hsideNonneg : (0 : ℝ) ≤ Fintype.card D.geometry.left := Nat.cast_nonneg _
  have hdensity : (α / 4) * Fintype.card D.geometry.left ≤
      ((k - D.count : ℕ) : ℝ) := by
    have h := R.density
    simp only [Fintype.card_coe] at h ⊢
    nlinarith only [h, mul_nonneg hα.le (Nat.cast_nonneg D.geometry.left.card)]
  have hJle : J.card ≤ k - D.count := by
    simpa only [Fintype.card_fin] using J.card_le_univ
  have hJupper : (J.card : ℝ) * 8 ≤ k := by
    have h := (Nat.le_div_iff_mul_le (by decide : 0 < 8)).mp
      (reserveCount_le_eighth k s)
    rw [hJcard]
    exact_mod_cast h
  have hselected : (α / 4) * Fintype.card D.geometry.left ≤
      ((k - D.count - J.card : ℕ) : ℝ) := by
    rw [Nat.cast_sub hJle]
    have hremaining := D.remaining_degree_lower
    rw [hhalf] at hk
    nlinarith only [hk, hremaining, hJupper, mul_nonneg hα.le hsideNonneg]
  have hreserve : γ * Fintype.card D.geometry.left ≤ (J.card : ℝ) := by
    rw [hJcard]
    calc
      γ * Fintype.card D.geometry.left =
          (α * (2 * Fintype.card D.geometry.left)) /
            (2 * (reserveDenominator s : ℝ)) := by dsimp only [γ]; ring
      _ ≤ (k : ℝ) / (2 * (reserveDenominator s : ℝ)) :=
        div_le_div_of_nonneg_right (by simpa only [← hhalf] using hk) (by positivity)
      _ ≤ (reserveCount k s : ℝ) := reserveCount_lower_of_large k s hlarge
  letI : DecidableEq ↥((deleted C D.exteriorColor D.labels D.matchings)ᶜ) := Classical.decEq _
  let cRest : (D.remaining.restrictEdges (coreEdges (residualCrossingCore C D))ᶜ).EdgeColoring
      (k - D.count) := {
    color := fun f => R.complementColor.color
      ⟨f.val, by simpa only [mem_compl] using f.property⟩
    proper := by
      intro f g v hcolor hv hw
      have h := R.complementColor.proper hcolor hv hw
      have hval := congrArg Subtype.val h
      exact Subtype.ext hval
  }
  have hcrossRest : ∀ f : ↥((coreEdges (residualCrossingCore C D))ᶜ),
      f.val ∉ D.remaining.internalEdges U → cRest.color f ∈ J →
        f.val ∈ D.remaining.cutEdges (TwoApexFactorization.leftShore e ∪ S.ZA) := by
    intro f hf hj
    exact residualReservedLabels_crossing C D R S.J S.ZA S.crossing
      ⟨f.val, by simpa only [mem_compl] using f.property⟩ hf hj
  obtain ⟨rest⟩ := hfactor V _ D.geometry.left D.geometry.right D.remaining U
    (residualCrossingCore C D) e (k - D.count) R.error
    cRest J S.ZA S.ZB
    (residualShore_balance C D) (by simpa only [Fintype.card_coe] using hmB)
    (residualShore_bipartite C D) (bipartite_robust_change_bounded_instances _ hrobB)
    hdensity hselected hreserve R.regular R.error_nonneg
    (by simpa only [Fintype.card_coe] using R.error_small) R.core_degree
    S.disjoint S.cover S.balance hcrossRest
  exact ⟨R.reassemble rest⟩

end Overfull.OrdinaryFactorization

namespace Overfull

open Finset Classical SmallCuts OneCore

/-- Full Lemma 4.2. Every sufficiently large even ordinary robust core
with bounded exterior and a colorable complement admits factorization.
The density parameter may be any positive real number, and nonnegativity
of the core deficit is derived from actual embedded core degrees. -/
theorem ordinary_core_factorization (α ν τ : ℝ) (s : ℕ)
    (hα : 0 < α) (hν : 0 < ν) (hντ : ν ≤ τ) (hτ : τ ≤ min α 1 / 8) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ m₀ : ℕ,
      ∀ (V E : Type*) [Fintype V] [Fintype E]
        (G : Multigraph V E) (U : Finset V) (C : Core G U) (k : ℕ) (a : ℝ),
        m₀ ≤ U.card → Even U.card → Even (Fintype.card V) → Uᶜ.card ≤ s →
        (∀ v, G.degree v = k) → α * U.card ≤ (k : ℝ) →
        IsRobustExpander C.graph ν τ → a ≤ ε * U.card →
        (∀ v, (k : ℝ) - a ≤ (C.graph.degree v : ℝ)) →
        Nonempty ((G.restrictEdges (coreEdges C)ᶜ).EdgeColoring k) →
        Nonempty (G.EdgeColoring k) := by
  obtain ⟨ε, hε, n₀, hfactor⟩ :=
    OrdinaryFactorization.exists_uniform_ordinary_core_factorization (min α 1) ν τ s
      (lt_min hα zero_lt_one) (min_le_right _ _) hν hντ hτ
  refine ⟨ε, hε, max n₀ 1, ?_⟩
  intro V E _ _ G U C k a hn heven hHostEven hZcard hregular hk hrob hae hdegree ⟨c⟩
  have hn0 : 0 < U.card := lt_of_lt_of_le Nat.zero_lt_one ((le_max_right _ _).trans hn)
  obtain ⟨v, hv⟩ := card_pos.mp hn0
  have hcoreUpper : (C.graph.degree ⟨v, hv⟩ : ℝ) ≤ k := by
    exact_mod_cast (core_degree_le C ⟨v, hv⟩).trans_eq (hregular v)
  have ha : 0 ≤ a := by linarith only [hdegree ⟨v, hv⟩, hcoreUpper]
  exact hfactor V E G U C k a ((le_max_left _ _).trans hn) heven hHostEven hZcard
    hregular ((mul_le_mul_of_nonneg_right (min_le_left α 1) (Nat.cast_nonneg _)).trans hk)
    hrob ha hae hdegree c

/-- The full source conclusion as an exact partition of all original edge
copies into `k` actual perfect matchings. -/
theorem ordinary_core_one_factorization (α ν τ : ℝ) (s : ℕ)
    (hα : 0 < α) (hν : 0 < ν) (hντ : ν ≤ τ) (hτ : τ ≤ min α 1 / 8) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ m₀ : ℕ,
      ∀ (V E : Type*) [Fintype V] [Fintype E]
        (G : Multigraph V E) (U : Finset V) (C : Core G U) (k : ℕ) (a : ℝ),
        m₀ ≤ U.card → Even U.card → Even (Fintype.card V) → Uᶜ.card ≤ s →
        (∀ v, G.degree v = k) → α * U.card ≤ (k : ℝ) →
        IsRobustExpander C.graph ν τ → a ≤ ε * U.card →
        (∀ v, (k : ℝ) - a ≤ (C.graph.degree v : ℝ)) →
        Nonempty ((G.restrictEdges (coreEdges C)ᶜ).EdgeColoring k) →
        ∃ M : Fin k → Finset E,
          (∀ i, G.IsPerfectMatching (M i)) ∧
          Pairwise (fun i j => Disjoint (M i) (M j)) ∧
          univ.biUnion M = univ := by
  obtain ⟨ε, hε, m₀, hfactor⟩ := ordinary_core_factorization α ν τ s hα hν hντ hτ
  refine ⟨ε, hε, m₀, ?_⟩
  intro V E _ _ G U C k a hm heven hHostEven hZcard hregular hk hrob hae hdegree hc
  obtain ⟨c⟩ := hfactor V E G U C k a hm heven hHostEven hZcard hregular hk hrob hae hdegree hc
  exact BoundedExterior.exists_oneFactorization_of_coloring G k hregular c

end Overfull
