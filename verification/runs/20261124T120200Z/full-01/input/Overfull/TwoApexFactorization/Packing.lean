import Overfull.TwoApexFactorization.Completion

/-!
# Uniform packing of selected exterior colors

The actual selected exterior classes have balanced small core footprints.
Variance-free deterministic bounds on their sizes and vertex loads allow
the proved robust bipartite packing theorem to complete all selected
colors. The genuinely bipartite unselected remainder is then colored by
König, producing a coloring of the whole original host.
-/

noncomputable section

namespace Overfull.TwoApexFactorization

open Finset Classical SmallCuts SimpleGraph

/-- Complete every selected exterior color and color the original host.
All constants precede the graph, selected copy set, and its coloring. -/
theorem exists_uniform_selected_coloring (α β γ ν τ : ℝ)
    (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hγ : 0 < γ) (hγ1 : γ < 1)
    (hν : 0 < ν) (hντ : ν ≤ τ) (hτ : τ < α / 16) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ m₀ : ℕ,
      ∀ (V E A B : Type*) [Fintype V] [Fintype E] [Fintype A] [Fintype B]
        (G : Multigraph V E) (U : Finset V) (C : Core G U)
        (e : A ⊕ B ≃ U) (k q : ℕ) (a : ℝ) (F : Finset E)
        (c : (G.restrictEdges F).EdgeColoring q),
        Fintype.card A = Fintype.card B → m₀ ≤ Fintype.card A →
        (C.graph.comap e).IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr) →
        IsBipartiteRobustExpander (C.graph.comap e) ν τ →
        α * Fintype.card A ≤ k → β * Fintype.card A ≤ q →
        (q : ℝ) ≤ k - γ * Fintype.card A →
        (∀ v, G.degree v = k) →
        (∀ v, v ∉ U → (G.restrictEdges F).degree v = q) →
        F ⊆ (OneCore.coreEdges C)ᶜ → 0 ≤ a → a ≤ ε * Fintype.card A →
        (∀ v : U, (k : ℝ) - a ≤ C.graph.degree v) →
        (G.restrictEdges Fᶜ).IsBipartite →
        (∀ i, (univ.filter (fun x : A => c.Covers i (e (.inl x)).val)).card =
          (univ.filter (fun y : B => c.Covers i (e (.inr y)).val)).card) →
        (∀ i, ((U ∩ c.coveredVertices i).card : ℝ) ≤
          2 * Fintype.card A * a / q + 4) →
        Nonempty (G.EdgeColoring k) := by
  obtain ⟨ε₀, θ, σ, hε₀, _hθ, _hσ, _hστ, m₁, hpack⟩ :=
    BipartiteFactorization.pack_fixed_bipartite_forbidden_sets α γ ν τ
      hα hα1 hγ hγ1 hν hντ hτ
  let ε := min ε₀ (ε₀ * β / 8)
  have hε : 0 < ε := lt_min hε₀ (by positivity)
  have hεle : ε ≤ ε₀ := min_le_left _ _
  have hεsmall : ε ≤ ε₀ * β / 8 := min_le_right _ _
  obtain ⟨m₂, hm₂⟩ := exists_nat_gt (8 / ε₀)
  refine ⟨ε, hε, max m₁ (max m₂ 1), ?_⟩
  intro V E A B _ _ _ _ G U C e k q a F c hcard hm hbip hrob hk hq hreserve
    hregular houtside hF ha hae hdegree hremaining hbalance hsize
  have hm₁ : m₁ ≤ Fintype.card A := (le_max_left _ _).trans hm
  have hm₂' : m₂ ≤ Fintype.card A :=
    (le_trans (le_max_left _ _) (le_max_right _ _)).trans hm
  have hm1 : 1 ≤ Fintype.card A :=
    (le_trans (le_max_right _ _) (le_max_right _ _)).trans hm
  have hmpos : (0 : ℝ) < Fintype.card A := by exact_mod_cast hm1
  have hqpos : (0 : ℝ) < q := (mul_pos hβ hmpos).trans_le hq
  have hconstant : 8 ≤ ε₀ * Fintype.card A := by
    have hm₂R : (m₂ : ℝ) ≤ Fintype.card A := by exact_mod_cast hm₂'
    have hlarge : 8 / ε₀ < (Fintype.card A : ℝ) := hm₂.trans_le hm₂R
    have h := (div_lt_iff₀ hε₀).mp hlarge
    linarith
  have haε : a ≤ ε₀ * Fintype.card A :=
    hae.trans (mul_le_mul_of_nonneg_right hεle hmpos.le)
  have hselected (v : U) : ((G.restrictEdges F).degree v.val : ℝ) ≤ a := by
    have hs := OneCore.complement_degree_add_core C v
    rw [hregular v.val] at hs
    have hsR : ((G.restrictEdges (OneCore.coreEdges C)ᶜ).degree v.val : ℝ) +
        C.graph.degree v = k := by exact_mod_cast hs
    have hsub : ((G.restrictEdges F).degree v.val : ℝ) ≤
        (G.restrictEdges (OneCore.coreEdges C)ᶜ).degree v.val := by
      exact_mod_cast G.restrictEdges_degree_mono hF v.val
    linarith [hdegree v]
  have hcoreError (v : A ⊕ B) :
      |((C.graph.comap e).degree v : ℝ) - k| ≤ ε₀ * Fintype.card A := by
    have heq : (C.graph.comap e).degree v = C.graph.degree (e v) :=
      Overfull.iso_degree_eq (SimpleGraph.Iso.comap e C.graph) v
    rw [heq]
    have hupper : C.graph.degree (e v) ≤ k :=
      (OneCore.core_degree_le C (e v)).trans_eq (hregular (e v).val)
    have hupperR : (C.graph.degree (e v) : ℝ) ≤ k := by exact_mod_cast hupper
    apply abs_le.mpr
    constructor <;> linarith [hdegree (e v)]
  have hfootprint (i : Fin q) :
      ((sideFootprint c e i).card : ℝ) ≤ ε₀ * Fintype.card A := by
    rw [sideFootprint_card]
    have hnumer : 2 * Fintype.card A * a ≤ (2 * a / β) * q := by
      have hx := mul_le_mul_of_nonneg_left hq
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) ha)
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hβ).mpr
      nlinarith [hx]
    have hfraction : 2 * Fintype.card A * a / q ≤ 2 * a / β :=
      (div_le_iff₀ hqpos).mpr hnumer
    have hasmall : 2 * a / β ≤ ε₀ * Fintype.card A / 4 := by
      apply (div_le_iff₀ hβ).mpr
      have hb := mul_le_mul_of_nonneg_right hεsmall hmpos.le
      nlinarith
    exact (hsize i).trans (by linarith)
  have hload (v : A ⊕ B) :
      ((univ.filter (fun i : Fin q => v ∈ sideFootprint c e i)).card : ℝ) ≤
        ε₀ * Fintype.card A := by
    rw [sideFootprint_load]
    exact (hselected (e v)).trans haε
  have hqfloor : q ≤ Nat.floor ((k : ℝ) - γ * Fintype.card A) :=
    Nat.le_floor hreserve
  obtain ⟨P⟩ := hpack A B (C.graph.comap e) k hbip hcard hm₁ hrob hk hcoreError
    q (sideFootprint c e) hqfloor
    (by intro i; simpa only [mem_sideFootprint] using hbalance i) hfootprint hload
  have hqk : q ≤ k := by
    have hnonneg := mul_nonneg hγ.le hmpos.le
    have hR : (q : ℝ) ≤ k := by linarith
    exact_mod_cast hR
  exact (completionOfPacking C c e P).edgeColorable k hqk hF houtside hregular hremaining

end Overfull.TwoApexFactorization
