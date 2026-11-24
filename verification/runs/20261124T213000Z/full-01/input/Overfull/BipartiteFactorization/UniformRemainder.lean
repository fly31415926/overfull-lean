import Overfull.BipartiteFactorization.CompletionTransport
import Overfull.BipartiteFactorization.ResidualOrientation

/-!
# Uniform completion of the remaining colors to an exact regular core

This is the packing stage after the reserved edges have been removed.  The
remaining ambient graph has degree `q + 2*r` on its core and degree `q`
outside.  Its actual exterior coloring supplies balanced small footprints.
Uniform robust packing completes every one of its `q` classes, leaving an
actual simple bipartite `2*r`-regular graph, with an `r`-regular orientation.

The reservation and its absorber are not supplied by this theorem.  Every
input refers to the prepared graph and its actual original edge copies.
-/

noncomputable section

namespace Overfull.BipartiteFactorization

open Finset Classical SmallCuts SimpleGraph

/-- Uniform constants for the last packing stage. The `q` completed classes
preserve every color of the actual exterior. All surviving copies belong to
the actual simple core; its balanced orientation is constructed by König. -/
theorem exists_uniform_oriented_remainder (α γ ν τ : ℝ)
    (hα : 0 < α) (hα1 : α < 1) (hγ : 0 < γ) (hγ1 : γ < 1)
    (hν : 0 < ν) (hντ : ν ≤ τ) (hτ : τ < α / 16) :
    ∃ ε θ σ : ℝ, 0 < ε ∧ 0 < θ ∧ 0 < σ ∧ σ ≤ τ ∧ ∃ m₀ : ℕ,
      ∀ (V E A B : Type*) [Fintype V] [Fintype E] [Fintype A] [Fintype B]
        (G : Multigraph V E) (U : Finset V) (C : Core G U)
        (e : A ⊕ B ≃ U) (q r : ℕ) (a : ℝ)
        (c : (G.restrictEdges (OneCore.coreEdges C)ᶜ).EdgeColoring q),
        Fintype.card A = Fintype.card B → m₀ ≤ Fintype.card A →
        (C.graph.comap e).IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr) →
        IsBipartiteRobustExpander (C.graph.comap e) ν τ →
        α * Fintype.card A ≤ q → γ * Fintype.card A ≤ 2 * r →
        (∀ v, v ∉ U → G.degree v = q) →
        (∀ v : U, G.degree v.val = q + 2 * r) →
        0 ≤ a → a ≤ ε * Fintype.card A →
        (∀ v : U, (q + 2 * r : ℕ) - a ≤ (C.graph.degree v : ℝ)) →
        (∀ i, (univ.filter (fun x : A => c.Covers i (e (.inl x)).val)).card =
          (univ.filter (fun y : B => c.Covers i (e (.inr y)).val)).card) →
        (∀ i, ((c.exteriorFootprint U i).card : ℝ) ≤
          2 * Fintype.card A * a / q + 4) →
        ∃ D : ComplementCompletion C c,
          IsBipartiteRobustExpander (D.remainingGraph.comap e) θ σ ∧
          Nonempty (ResidualOrientation (D.remainingGraph.comap e) r) := by
  obtain ⟨ε₀, θ, σ, hε₀, hθ, hσ, hστ, m₁, hpack⟩ :=
    pack_fixed_bipartite_forbidden_sets α γ ν τ hα hα1 hγ hγ1 hν hντ hτ
  let ε := min ε₀ (ε₀ * α / 8)
  have hε : 0 < ε := lt_min hε₀ (by positivity)
  have hεle : ε ≤ ε₀ := min_le_left _ _
  have hεsmall : ε ≤ ε₀ * α / 8 := min_le_right _ _
  obtain ⟨m₂, hm₂⟩ := exists_nat_gt (8 / ε₀)
  refine ⟨ε, θ, σ, hε, hθ, hσ, hστ, max m₁ (max m₂ 1), ?_⟩
  intro V E A B _ _ _ _ G U C e q r a c hcard hm hbip hrob hq hr
    houtside hcore ha hae hdegree hbalance hsize
  have hm₁ : m₁ ≤ Fintype.card A := (le_max_left _ _).trans hm
  have hm₂' : m₂ ≤ Fintype.card A := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hm
  have hm1 : 1 ≤ Fintype.card A := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hm
  have hmpos : (0 : ℝ) < Fintype.card A := by exact_mod_cast hm1
  have hqpos : (0 : ℝ) < q := (mul_pos hα hmpos).trans_le hq
  have hconstant : 8 ≤ ε₀ * Fintype.card A := by
    have hm₂R : (m₂ : ℝ) ≤ Fintype.card A := by exact_mod_cast hm₂'
    have hlarge : 8 / ε₀ < (Fintype.card A : ℝ) := hm₂.trans_le hm₂R
    have h := (div_lt_iff₀ hε₀).mp hlarge
    linarith
  have haε : a ≤ ε₀ * Fintype.card A :=
    hae.trans (mul_le_mul_of_nonneg_right hεle hmpos.le)
  have hcomplement (v : U) :
      ((G.restrictEdges (OneCore.coreEdges C)ᶜ).degree v.val : ℝ) ≤ a := by
    have hs := OneCore.complement_degree_add_core C v
    rw [hcore v] at hs
    have hsR : ((G.restrictEdges (OneCore.coreEdges C)ᶜ).degree v.val : ℝ) +
        C.graph.degree v = (q + 2 * r : ℕ) := by exact_mod_cast hs
    linarith [hdegree v]
  have hcoreError (v : A ⊕ B) :
      |((C.graph.comap e).degree v : ℝ) - (q + 2 * r : ℕ)| ≤
        ε₀ * Fintype.card A := by
    have heq : (C.graph.comap e).degree v = C.graph.degree (e v) :=
      Overfull.iso_degree_eq (SimpleGraph.Iso.comap e C.graph) v
    rw [heq]
    have hupper : C.graph.degree (e v) ≤ q + 2 * r :=
      (OneCore.core_degree_le C (e v)).trans_eq (hcore (e v))
    have hupperR : (C.graph.degree (e v) : ℝ) ≤ (q + 2 * r : ℕ) := by
      exact_mod_cast hupper
    apply abs_le.mpr
    constructor <;> linarith [hdegree (e v)]
  have hfootprint (i : Fin q) :
      ((sideFootprint C c e i).card : ℝ) ≤ ε₀ * Fintype.card A := by
    rw [sideFootprint_card]
    have hnumer : 2 * Fintype.card A * a ≤ (2 * a / α) * q := by
      have hx := mul_le_mul_of_nonneg_left hq (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) ha)
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hα).mpr
      nlinarith [hx]
    have hfraction : 2 * Fintype.card A * a / q ≤ 2 * a / α :=
      (div_le_iff₀ hqpos).mpr hnumer
    have hasmall : 2 * a / α ≤ ε₀ * Fintype.card A / 4 := by
      apply (div_le_iff₀ hα).mpr
      have hb := mul_le_mul_of_nonneg_right hεsmall hmpos.le
      nlinarith
    exact (hsize i).trans (by linarith)
  have hload (v : A ⊕ B) :
      ((univ.filter (fun i : Fin q => v ∈ sideFootprint C c e i)).card : ℝ) ≤
        ε₀ * Fintype.card A := by
    rw [sideFootprint_load]
    exact (hcomplement (e v)).trans haε
  have hqfloor : q ≤ Nat.floor ((q + 2 * r : ℕ) - γ * Fintype.card A : ℝ) := by
    apply Nat.le_floor
    push_cast
    linarith
  have hdensity : α * Fintype.card A ≤ (q + 2 * r : ℕ) := by
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) r]
  obtain ⟨P⟩ := hpack A B (C.graph.comap e) (q + 2 * r : ℕ) hbip hcard hm₁
    hrob hdensity hcoreError q (sideFootprint C c e) hqfloor
    (by intro i; simpa only [mem_sideFootprint] using hbalance i) hfootprint hload
  let D := P.toComplementCompletion C c e
  have hremainBip : (D.remainingGraph.comap e).IsBipartiteWith
      (Set.range Sum.inl) (Set.range Sum.inr) := by
    rw [P.remaining_comap C c e]
    exact ⟨hbip.disjoint, fun _ _ h => hbip.mem_of_adj h.1⟩
  have hregular (v : A ⊕ B) : (D.remainingGraph.comap e).degree v = 2 * r := by
    exact (Overfull.iso_degree_eq (SimpleGraph.Iso.comap e D.remainingGraph) v).trans
      (D.remainingGraph_regular r houtside hcore (e v))
  exact ⟨D, P.completion_robust C c e,
    exists_regular_bipartite_orientation _ r hremainBip hregular⟩

end Overfull.BipartiteFactorization
