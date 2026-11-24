import Overfull.TerminalFourOdd.MultiGeometry
import Overfull.TerminalFourOdd.MultiGluing
import Overfull.NativeTerminal.ShoreFactorization

/-!
# Factorization of a robust center with odd robust leaves

The central host is constructed by contracting the leaves separately.
Their cut degrees give its regularity; the absence of edges between distinct
leaves gives independent apices. Central and leaf colorings are constructed
uniformly and aligned on every original boundary copy.
-/

noncomputable section

namespace Overfull.TerminalFourOdd

open Finset Classical Multigraph SmallCuts BoundaryExtension NativeTerminal Multi

theorem exists_uniform_dominant_coloring (α ν τ : ℝ) (s : ℕ)
    (hα : 0 < α) (hν : 0 < ν) (hντ : ν ≤ τ) (hτ : τ ≤ min α 1/16) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ m₀ : ℕ,
      ∀ (V E I : Type*) [Fintype E] [Fintype I]
        (G : Multigraph V E) (U : Finset V) (X : I → Finset V)
        (label : V → I) (C : Core G U) (D : ∀ i, Core G (X i)) (k : ℕ) (a : ℝ),
        (∀ i, Disjoint U (X i)) → Pairwise (fun i j => Disjoint (X i) (X j)) →
        (∀ v, v ∈ U ∨ ∃ i, v ∈ X i) →
        (∀ i v, centralMap U label v = Sum.inr i ↔ v ∈ X i) →
        Even (U.card+Fintype.card I) → Fintype.card I ≤ s →
        (∀ i, Odd (X i).card) → m₀ ≤ U.card → (∀ i, m₀ ≤ (X i).card) →
        (∀ v, G.degree v = k) → (∀ i, G.cutSize (X i) = k) →
        α*U.card ≤ (k : ℝ) → (∀ i, α*(X i).card ≤ (k : ℝ)) →
        (∀ e, G.firstEnd e ∉ U → G.secondEnd e ∉ U →
          label (G.firstEnd e) = label (G.secondEnd e)) →
        IsRobustExpander C.graph ν τ → (∀ i, IsRobustExpander (D i).graph ν τ) →
        a ≤ ε*U.card → (∀ i, a ≤ ε*(X i).card) →
        (∀ v, (k : ℝ)-a ≤ (C.graph.degree v : ℝ)) →
        (∀ i v, (k : ℝ)-a ≤ ((D i).graph.degree v : ℝ)) →
        Nonempty (G.EdgeColoring k) := by
  obtain ⟨εC,hεC,mC,hcentral⟩ := exists_uniform_central_star_coloring α ν τ s
    hα hν hντ hτ
  obtain ⟨εL,hεL,mL,hleaf⟩ := exists_uniform_shore_coloring α ν τ 0 hα hν hντ hτ
  refine ⟨min εC εL,lt_min hεC hεL,max mC mL,?_⟩
  intro V E I _ _ G U X label C D k a hUX hXX hcover hfiber heven hI hodd
    hmU hmX hregular hcut hkU hkX hout hrobU hrobX haU haX hdegreeU hdegreeX
  obtain ⟨c⟩ := hcentral V E I G U C label X k a
    ((le_max_left mC mL).trans hmU) heven hI hfiber (fun u _ => hregular u) hcut hkU
    hout hrobU (haU.trans (mul_le_mul_of_nonneg_right (min_le_left εC εL)
      (Nat.cast_nonneg U.card))) hdegreeU
  have hleaves : ∀ i, Nonempty ((contract G (X i)).EdgeColoring k) := by
    intro i
    obtain ⟨_,hfactor⟩ := hleaf V E G (X i) (X i) (D i) k a subset_rfl
      ((le_max_right mC mL).trans (hmX i)) (by simp) (fun v _ => hregular v)
      (hkX i) (hrobX i) ((haX i).trans (mul_le_mul_of_nonneg_right
        (min_le_right εC εL) (Nat.cast_nonneg (X i).card))) (hdegreeX i)
      (by ext e; simp)
    exact hfactor (hcut i) (hodd i) (by intro e he v hv hvi; exact hvi)
  let cX := fun i => Classical.choice (hleaves i)
  exact glue_central_and_leaves G U label X k hUX hXX hcover hfiber hcut c cX

end Overfull.TerminalFourOdd
