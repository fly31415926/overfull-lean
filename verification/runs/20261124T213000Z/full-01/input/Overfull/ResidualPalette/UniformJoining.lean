import Overfull.ResidualPalette.UniformCompletion
import Overfull.ResidualPalette.JoiningBounds

/-!
# Uniform native residual with a bounded joining graph

The surviving robustness is chosen before the requested small error. The
original-host hypotheses then construct the reserve and the actual residual,
with both a real joining bound and an explicit natural palette bound.
-/

noncomputable section
namespace Overfull.NativeReserve
open Finset Classical AssignedParts

/-- Uniform parameters construct the actual residual with small joining
degrees and the strict six-times-degree palette margin. These parameters
are chosen before the host, its representative, and its reserve. This
does not yet construct palette classes or factor the residual. -/
theorem exists_uniform_native_reserve_completion_with_small_joining (α c ν τ σ : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hc : 0 < c)
    (hν : 0 < ν) (hντ : ν ≤ τ) (hτ : τ ≤ α/8)
    (hσ : 0 < σ) (hσhalf : σ < 1/2) (hσsmall : σ ≤ α/300) :
    ∃ θ : ℝ, 0 < θ ∧ θ ≤ σ ∧ ∀ δ : ℝ, 0 < δ →
      ∃ ξ : ℝ, 0 < ξ ∧ ∃ n₀ : ℕ, 1 ≤ n₀ ∧
      ∀ (V E : Type*) [Fintype V] [Fintype E] (G : Multigraph V E) (k : ℕ)
        (U₀ U₁ Z : Finset V) (C₀ : SmallCuts.Core G U₀) (C₁ : SmallCuts.Core G U₁) (a : ℝ),
        n₀ ≤ Fintype.card V → α*Fintype.card V ≤ k →
        c*Fintype.card V ≤ U₀.card → c*Fintype.card V ≤ U₁.card →
        Disjoint U₀ U₁ → Disjoint U₀ Z → Disjoint U₁ Z →
        (∀ v, v ∈ U₀ ∨ v ∈ U₁ ∨ v ∈ Z) → Z.card ≤ 2 →
        (∀ v, G.degree v = k) → (∀ X : Finset V, ¬ G.IsOverfull k X) →
        IsRobustExpander C₀.graph ν τ → IsRobustExpander C₁.graph ν τ →
        0 < a → a ≤ ξ*Fintype.card V →
        (∀ v, (k : ℝ)-a ≤ (C₀.graph.degree v : ℝ)) →
        (∀ v, (k : ℝ)-a ≤ (C₁.graph.degree v : ℝ)) →
        ∃ (r h q : ℕ) (M : Finset E) (Q : BoundaryPacking G U₀ U₁ Z M r)
          (N : Fin q → Finset E)
          (C₀' : SmallCuts.Core (residualGraph G N univ) U₀)
          (C₁' : SmallCuts.Core (residualGraph G N univ) U₁),
          G.IsPerfectMatching M ∧ (k : ℝ)/30 ≤ r ∧ h+q=k ∧ r≤h ∧
          (h : ℝ)-r ≤ δ*Fintype.card V ∧
          (∀ j, G.IsPerfectMatching (N j)) ∧
          Pairwise (fun i j => Disjoint (N i) (N j)) ∧
          (∀ j, Disjoint (N j) (removedCopies Q.boundary univ)) ∧
          (∀ v, (residualGraph G N univ).degree v = h) ∧
          (∀ X : Finset V, ¬ (residualGraph G N univ).IsOverfull h X) ∧
          IsRobustExpander C₀'.graph θ σ ∧ IsRobustExpander C₁'.graph θ σ ∧
          (∀ v, (h : ℝ)-a ≤ (C₀'.graph.degree v : ℝ)) ∧
          (∀ v, (h : ℝ)-a ≤ (C₁'.graph.degree v : ℝ)) ∧
          (∀ v, ((FourOdd.joiningGraph (residualGraph G N univ)
            (assignedLabel G M U₀ U₁ Z)).degree v : ℝ) ≤ max a ((h : ℝ)-r)) ∧
          max a ((h : ℝ)-r) ≤ δ*Fintype.card V ∧
          6*max a ((h : ℝ)-r) < h ∧
          (∀ v, (FourOdd.joiningGraph (residualGraph G N univ)
            (assignedLabel G M U₀ U₁ Z)).degree v ≤ ⌊max a ((h : ℝ)-r)⌋₊) ∧
          6*⌊max a ((h : ℝ)-r)⌋₊ < h := by
  obtain ⟨θ, hθ, hθσ, huniform⟩ :=
    exists_uniform_native_reserve_completion_parameters α c ν τ σ
      hα hα1 hc hν hντ hτ hσ hσhalf hσsmall
  refine ⟨θ, hθ, hθσ, ?_⟩
  intro δ hδ
  let δ' := min δ (α/360)
  have hδ' : 0 < δ' := lt_min hδ (by positivity)
  obtain ⟨ξ, hξ, n₀, hn₀, hconstruct⟩ := huniform δ' hδ'
  refine ⟨min ξ δ', lt_min hξ hδ', n₀, hn₀, ?_⟩
  intro V E _ _ G k U₀ U₁ Z C₀ C₁ a hn hdensity hsize₀ hsize₁
    h01 h0Z h1Z hcover hZ hregular hno hrobust₀ hrobust₁ ha haSmall hdegree₀ hdegree₁
  have haξ : a ≤ ξ*Fintype.card V := haSmall.trans
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _))
  have haδ' : a ≤ δ'*Fintype.card V := haSmall.trans
    (mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg _))
  obtain ⟨r, h, q, M, Q, N, C₀', C₁', hM, hr, hcount, hrh, hmargin,
    hNperfect, hNdisj, hNavoid, hRregular, hRno, hRrobust₀, hRrobust₁,
    hRdegree₀, hRdegree₁⟩ :=
    hconstruct V E G k U₀ U₁ Z C₀ C₁ a hn hdensity hsize₀ hsize₁
      h01 h0Z h1Z hcover hZ hregular hno hrobust₀ hrobust₁ ha haξ hdegree₀ hdegree₁
  have hbound := native_residual_joining_degree_bounds G U₀ U₁ Z hM
    h01 h0Z h1Z hcover hZ r Q N univ (fun j _ => hNavoid j) h a hrh
    hRregular C₀' C₁' hRdegree₀ hRdegree₁
  have hmax : max a ((h : ℝ)-r) ≤ δ'*Fintype.card V := max_le haδ' hmargin
  have hδle : δ'*Fintype.card V ≤ δ*Fintype.card V :=
    mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _)
  have hmarginδ := hmargin.trans hδle
  have hmaxδ := hmax.trans hδle
  have hsmall : δ'*Fintype.card V ≤ (α/360)*Fintype.card V :=
    mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg _)
  have hnpos : (0 : ℝ) < Fintype.card V := by
    exact_mod_cast (show 0 < Fintype.card V from by omega)
  have hrhR : (r : ℝ) ≤ h := by exact_mod_cast hrh
  have hpalette : 6*max a ((h : ℝ)-r) < h := by
    have hpositive := mul_pos hα hnpos
    nlinarith only [hmax, hsmall, hdensity, hr, hrhR, hpositive]
  have hnat := natural_joining_degree_bound (residualGraph G N univ)
    (assignedLabel G M U₀ U₁ Z) (max a ((h : ℝ)-r))
    (ha.le.trans (le_max_left _ _)) h hbound.2.2.2 hpalette
  exact ⟨r, h, q, M, Q, N, C₀', C₁', hM, hr, hcount, hrh, hmarginδ,
    hNperfect, hNdisj, hNavoid, hRregular, hRno, hRrobust₀, hRrobust₁,
    hRdegree₀, hRdegree₁, hbound.2.2.2, hmaxδ, hpalette, hnat.1, hnat.2.2⟩


end Overfull.NativeReserve
