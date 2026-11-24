import Overfull.BoundaryExtension.Result
import Overfull.BoundaryExtension.Residual
import Overfull.BoundaryExtension.SurvivingLabels
import Overfull.BoundaryExtension.Colors

/-!
# Reducing boundary extension to an actual one-apex factorization

The selected triple classes, their internal completions, the residual
multigraph, and its robust embedded core are constructed from the original
data. An actual coloring of the resulting contraction then gives the exact
prescribed extension. `OneCore.Factorization` supplies that coloring, and
`BoundaryExtension.Full` assembles the complete Lemma 4.14.
-/

namespace Overfull.BoundaryExtension

open Finset Classical

variable {V E : Type*} [Fintype E]
variable {G : Multigraph V E} {U : Finset V} {d : ℕ} {θ σ : ℝ}

/-- Given the actual packed triple completions, a coloring of their exact
apex residual restores every original prescribed boundary label. -/
theorem extend_from_completed_triples (c : BoundaryColoring G U d)
    (C : SmallCuts.Core G U)
    (P : CorePacking C.graph c.tripleColors.card
      (fun j => c.footprint (c.tripleLabel j)) θ σ)
    (hclasses : ∀ i, (c.classEdges i).card = 1 ∨ (c.classEdges i).card = 3)
    (color : (contract (remainingAmbient c C c.tripleLabel P) U).EdgeColoring
      (d - c.tripleColors.card)) :
    ∃ full : (retainedGraph G U).EdgeColoring d,
      ∀ e : G.cutEdges U, full.color (boundaryLift G U e) = c.color e := by
  let D := completedUnion c C c.tripleLabel P
  let R := remainingAmbient c C c.tripleLabel P
  have hdeleted : ∀ e : G.cutEdges U, e.val ∈ D ↔ c.color e ∈ c.tripleColors :=
    completedTriples_boundary c C P
  have hboundary : R.cutSize U = d - c.tripleColors.card :=
    c.residual_cutSize_eq_sub D hclasses hdeleted
  obtain ⟨rest, hagree, hrange⟩ := exists_singleton_boundary_extension R U
    (d - c.tripleColors.card) color hboundary (c.residualLabel D)
    (c.residualLabel_injective D hclasses hdeleted)
  have hpalette : ∀ e, rest.color e ∉ Set.range c.tripleLabel := by
    intro e hlabel
    obtain ⟨b, hb⟩ := hrange e
    obtain ⟨j, hj⟩ := hlabel
    have htriple : c.residualLabel D b ∈ c.tripleColors := by
      rw [← hb, ← hj]
      exact c.tripleLabel_mem j
    exact c.residualLabel_not_mem_triples D hdeleted b htriple
  have hrest : ∀ e : RetainedEdge (G.restrictEdges Dᶜ) U,
      ∀ he : e.val.val ∈ G.cutEdges U,
      rest.color e = c.color ⟨e.val.val, he⟩ := by
    intro e he
    let b : R.cutEdges U := ⟨e.val,
      (restrictedBoundary_mem_iff G U Dᶜ e.val).mpr he⟩
    have h := hagree b
    have hlift : boundaryLift R U b = e := Subtype.ext rfl
    rw [hlift] at h
    exact h
  obtain ⟨full, hfull, _hselected, _hremaining⟩ := reassemble_deleted_colors G U c
    c.tripleColors.card c.tripleLabel (completedColor c C c.tripleLabel P)
    (completedColor_isMatching c C c.tripleLabel P)
    (completedColor_disjoint c C c.tripleLabel P)
    (fun j e he => completedColor_retained c C c.tripleLabel P j he)
    (fun e j => completedColor_boundary c C c.tripleLabel P j e)
    rest hpalette hrest
  exact ⟨full, hfull⟩

end Overfull.BoundaryExtension

namespace Overfull

open Finset Classical BoundaryExtension

/-- Uniformly construct the entire boundary-extension reduction from the
original graph and prescribed coloring. The only remaining task is to color
the explicit regular one-apex graph returned by the result. This theorem
does not assert that factorization, and is not the full Lemma 4.14. -/
theorem boundary_extension_reduction (α γ ν τ : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hγ : 0 < γ)
    (hν : 0 < ν) (hντ : ν ≤ τ) (hτ : τ ≤ α / 8) :
    ∃ ε θ σ : ℝ, 0 < ε ∧ 0 < θ ∧ θ ≤ σ ∧ 0 < σ ∧
      σ ≤ τ ∧ σ ≤ min γ 1 / 20 ∧ ∃ m₀ : ℕ,
      ∀ (V E : Type*) [Fintype E] (G : Multigraph V E)
        (U : Finset V) (C : SmallCuts.Core G U) (d : ℕ) (a : ℝ)
        (c : BoundaryColoring G U d),
        m₀ ≤ U.card → U.card % 2 = 1 →
        (∀ v : U, G.degree v.val = d) → α * U.card ≤ d →
        IsRobustExpander C.graph ν τ → 0 ≤ a → a ≤ ε * U.card →
        (∀ v, (d : ℝ) - a ≤ C.graph.degree v) →
        (∀ i, (c.classEdges i).card = 1 ∨ (c.classEdges i).card = 3) →
        γ * U.card ≤ c.singletonColors.card →
        Nonempty (BoundaryReduction G U d a γ θ σ c) := by
  let β := min γ 1
  have hβ : 0 < β := lt_min hγ zero_lt_one
  have hβ1 : β ≤ 1 := min_le_right _ _
  have hβγ : β ≤ γ := min_le_left _ _
  let σ := min τ (β / 100)
  have hσ : 0 < σ := lt_min (hν.trans_le hντ) (by positivity)
  have hστ : σ ≤ τ := min_le_left _ _
  have hσβ : σ ≤ β / 100 := min_le_right _ _
  have hσhalf : σ < 1/2 := by linarith
  have hσcut : σ ≤ β / 20 := by linarith
  obtain ⟨ε₀, θ₀, hε₀, hθ₀, mPack, hpack⟩ := exists_triple_core_packing
    α γ ν τ σ hα hα1 hγ hν hντ hτ hσ hσhalf
  let θ := min θ₀ σ
  have hθ : 0 < θ := lt_min hθ₀ hσ
  have hθσ : θ ≤ σ := min_le_right _ _
  obtain ⟨mCut, hcut⟩ := exists_contraction_cut_threshold β θ σ
    hβ hβ1 hθ hθσ hσcut
  let ε := min ε₀ (β/20)
  have hε : 0 < ε := lt_min hε₀ (by positivity)
  have hεpack : ε ≤ ε₀ := min_le_left _ _
  have hεcut : ε ≤ β/20 := min_le_right _ _
  refine ⟨ε, θ, σ, hε, hθ, hθσ, hσ, hστ, hσcut, max mPack mCut, ?_⟩
  intro V E _ G U C d a c hm hodd hregular hd hrob ha haSmall hdegree hclasses hsingle
  have hmPack : mPack ≤ U.card := (le_max_left _ _).trans hm
  have hmCut : mCut ≤ U.card := (le_max_right _ _).trans hm
  have haPack : a ≤ ε₀ * U.card := haSmall.trans
    (mul_le_mul_of_nonneg_right hεpack (Nat.cast_nonneg _))
  have haCut : a ≤ β * U.card / 20 := by
    have h := haSmall.trans (mul_le_mul_of_nonneg_right hεcut (Nat.cast_nonneg U.card))
    linarith
  obtain ⟨P₀⟩ := hpack V E G U C d a c hmPack hodd hregular hd
    hrob ha haPack hdegree hclasses hsingle
  let P := P₀.weakenParameter θ (min_le_left θ₀ σ)
  let D := completedUnion c C c.tripleLabel P
  let R := remainingAmbient c C c.tripleLabel P
  let C' := remainingEmbeddedCore c C c.tripleLabel P
  have hdeleted : ∀ e : G.cutEdges U, e.val ∈ D ↔ c.color e ∈ c.tripleColors :=
    completedTriples_boundary c C P
  have hboundary : R.cutSize U = d - c.tripleColors.card :=
    c.residual_cutSize_eq_sub D hclasses hdeleted
  have hreg : ∀ v : U, R.degree v.val = d - c.tripleColors.card :=
    remainingAmbient_regular c C c.tripleLabel P hregular
  have hretained : γ * U.card ≤ (d - c.tripleColors.card : ℕ) := by
    have hcount := c.singletons_add_triples hclasses
    have heq : d - c.tripleColors.card = c.singletonColors.card := by omega
    simpa only [heq] using hsingle
  have hdensity : β * U.card ≤ (d - c.tripleColors.card : ℕ) :=
    (mul_le_mul_of_nonneg_right hβγ (Nat.cast_nonneg _)).trans hretained
  have hcore : ∀ v, ((d - c.tripleColors.card : ℕ) : ℝ) - a ≤ C'.graph.degree v :=
    remainingEmbeddedCore_degree_lower c C c.tripleLabel P a hdegree
  have hrobust : IsRobustExpander C'.graph θ σ :=
    remainingEmbeddedCore_robust c C c.tripleLabel P
  have hOdd : Odd U.card := Nat.odd_iff.mpr hodd
  have hsafe := hcut V _ R U C' (d - c.tripleColors.card) a hmCut hOdd hreg
    hboundary hdensity ha haCut hrobust hcore
  refine ⟨{
    completed := completedColor c C c.tripleLabel P
    deleted := D
    deleted_eq := rfl
    completed_matching := completedColor_isMatching c C c.tripleLabel P
    completed_disjoint := completedColor_disjoint c C c.tripleLabel P
    completed_covers := completedColor_covers_uniquely c C c.tripleLabel P
    completed_retained := fun j _ he => completedColor_retained c C c.tripleLabel P j he
    completed_boundary := fun e j => completedColor_boundary c C c.tripleLabel P j e
    residual_degree := hreg
    residual_boundary := hboundary
    retained_density := hretained
    core := C'
    core_degree := hcore
    core_robust := hrobust
    contracted_regular := contract_regular R U (d - c.tripleColors.card) hreg hboundary
    contracted_even := even_contracted_order U hOdd
    contracted_no_overfull := hsafe.2
    extend := fun color => extend_from_completed_triples c C P hclasses color
  }⟩

end Overfull

