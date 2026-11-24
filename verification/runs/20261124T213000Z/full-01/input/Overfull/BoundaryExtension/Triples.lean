import Overfull.BoundaryExtension.BoundaryData
import Overfull.BoundaryExtension.Packing
import Overfull.OneCore.Complement

/-!
# Completing the prescribed boundary classes of size three

The actual boundary classes determine the forbidden sets. Their distinct
core endpoints and total incidence budgets follow from properness and the
embedded simple core. The packing constants precede all graph and coloring
data, and the positive singleton reserve supplies the exact horizon.
-/

namespace Overfull.BoundaryExtension

open Finset Classical

variable {V E : Type*} [Fintype E]
variable {G : Multigraph V E} {U : Finset V} {d : ℕ}

/-- The boundary degree is charged to the actual complement of the embedded
core. Only core vertices are required to have the common ambient degree. -/
theorem boundary_degree_le_error (C : SmallCuts.Core G U) (a : ℝ)
    (hregular : ∀ v : U, G.degree v.val = d)
    (hdegree : ∀ v, (d : ℝ) - a ≤ C.graph.degree v) (v : U) :
    ((boundaryGraph G U).degree v.val : ℝ) ≤ a := by
  have hboundary := OneCore.boundary_incidence_le_complement C v.val
  rw [← Multigraph.restrictEdges_degree] at hboundary
  have hsplit := OneCore.complement_degree_add_core C v
  rw [hregular v] at hsplit
  have hsplitR :
      ((G.restrictEdges (OneCore.coreEdges C)ᶜ).degree v.val : ℝ) + C.graph.degree v = d := by
    exact_mod_cast hsplit
  have hboundaryR : ((boundaryGraph G U).degree v.val : ℝ) ≤
      (G.restrictEdges (OneCore.coreEdges C)ᶜ).degree v.val := by exact_mod_cast hboundary
  linarith [hdegree v]

/-- The uniform packing result for all prescribed triple classes. It
constructs internal matchings and their actual robust residual core. -/
theorem exists_triple_core_packing (α γ ν τ σ : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hγ : 0 < γ)
    (hν : 0 < ν) (hντ : ν ≤ τ) (hτ : τ ≤ α / 8)
    (hσ : 0 < σ) (hσhalf : σ < 1/2) :
    ∃ ε θ : ℝ, 0 < ε ∧ 0 < θ ∧ ∃ m₀ : ℕ,
      ∀ (V E : Type*) [Fintype E] (G : Multigraph V E)
        (U : Finset V) (C : SmallCuts.Core G U) (d : ℕ) (a : ℝ)
        (c : BoundaryColoring G U d),
        m₀ ≤ U.card → U.card % 2 = 1 →
        (∀ v : U, G.degree v.val = d) → α * U.card ≤ d →
        IsRobustExpander C.graph ν τ → 0 ≤ a → a ≤ ε * U.card →
        (∀ v, (d : ℝ) - a ≤ C.graph.degree v) →
        (∀ i, (c.classEdges i).card = 1 ∨ (c.classEdges i).card = 3) →
        γ * U.card ≤ c.singletonColors.card →
        Nonempty (CorePacking C.graph c.tripleColors.card
          (fun j => c.footprint (c.tripleLabel j)) θ σ) := by
  obtain ⟨ε, θ, hε, hθ, m₀, hpack⟩ := pack_fixed_forbidden_sets α γ ν τ σ
    hα hα1 hγ hν hντ hτ hσ hσhalf
  obtain ⟨mSize, hmSize⟩ := exists_nat_ge (3 / ε)
  refine ⟨ε, θ, hε, hθ, max m₀ mSize, ?_⟩
  intro V E _ G U C d a c hm hodd hregular hd hrob _ha haSmall hdegree hclasses hsingle
  have hm₀ : m₀ ≤ U.card := (le_max_left _ _).trans hm
  have hmSize' : (mSize : ℝ) ≤ U.card := by
    exact_mod_cast (le_max_right m₀ mSize).trans hm
  have hthree : (3 : ℝ) ≤ ε * U.card := by
    have h := (div_le_iff₀ hε).mp (hmSize.trans hmSize')
    simpa only [mul_comm] using h
  apply hpack U C.graph d (by simpa only [Fintype.card_coe] using hm₀)
    (by convert hrob using 1) (by simpa only [Fintype.card_coe] using hd)
  · intro v
    have hupper := (OneCore.core_degree_le C v).trans_eq (hregular v)
    have hupperR : (C.graph.degree v : ℝ) ≤ d := by exact_mod_cast hupper
    simp only [Fintype.card_coe]
    apply abs_le.mpr
    constructor <;> linarith [hdegree v]
  · simpa only [Fintype.card_coe] using c.triple_horizon γ hclasses hsingle
  · intro j
    simp only [c.triple_footprint_card j, Fintype.card_coe, hodd]
  · intro j
    simpa only [c.triple_footprint_card j, Fintype.card_coe] using hthree
  · intro v
    have hcount := c.selected_footprint_incidence_le c.tripleLabel v
    have hcountR :
        ((univ.filter (fun j : Fin c.tripleColors.card =>
          v ∈ c.footprint (c.tripleLabel j))).card : ℝ) ≤
          (boundaryGraph G U).degree v.val := by exact_mod_cast hcount
    convert (hcountR.trans (boundary_degree_le_error C a hregular hdegree v)).trans haSmall using 1
    · congr 2
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    · simp only [Fintype.card_coe]

end Overfull.BoundaryExtension

