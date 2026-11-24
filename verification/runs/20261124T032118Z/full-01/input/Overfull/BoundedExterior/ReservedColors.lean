import Overfull.BoundedExterior.SelectedColoring
import Overfull.BoundedExterior.Factorization

/-!
# Factorization from a linear reserve of crossing exterior colors

Keep all nonreserved exterior colors and every internal complementary copy.
Sparse recoloring and balancing produce selected classes whose small core
footprints can be completed in the robust bipartite core.  Every remaining
copy crosses the same augmented bipartition, so König's theorem colors the
regular residue.  All parameter choices precede the host graph.

Reconstructed from the recovered full ordinary-factorization interface;
the source and verification evidence are newly generated.
-/

noncomputable section

namespace Overfull.BoundedExterior

open Finset Classical SmallCuts SimpleGraph OneCore TwoApexFactorization

theorem exists_uniform_factorization_of_reserved_colors (α β γ ν τ : ℝ)
    (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hγ : 0 < γ) (hγ1 : γ < 1)
    (hν : 0 < ν) (hντ : ν ≤ τ) (hτ : τ < α / 16) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ m₀ : ℕ,
      ∀ (V E A B : Type*) [Fintype V] [Fintype E] [Fintype A] [Fintype B]
        (G : Multigraph V E) (U : Finset V) (C : Core G U)
        (e : A ⊕ B ≃ U) (k : ℕ) (a : ℝ)
        (c : (G.restrictEdges (coreEdges C)ᶜ).EdgeColoring k)
        (J : Finset (Fin k)) (ZA ZB : Finset V),
        Fintype.card A = Fintype.card B → m₀ ≤ Fintype.card A →
        (C.graph.comap e).IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr) →
        IsBipartiteRobustExpander (C.graph.comap e) ν τ →
        α * Fintype.card A ≤ k →
        β * Fintype.card A ≤ (k - J.card : ℕ) →
        γ * Fintype.card A ≤ J.card →
        (∀ v, G.degree v = k) → 0 ≤ a → a ≤ ε * Fintype.card A →
        (∀ v : U, (k : ℝ) - a ≤ C.graph.degree v) →
        Disjoint ZA ZB → ZA ∪ ZB = Uᶜ → ZA.card = ZB.card →
        (∀ f : ↥((coreEdges C)ᶜ), f.val ∉ G.internalEdges U → c.color f ∈ J →
          f.val ∈ G.cutEdges (leftShore e ∪ ZA)) →
        Nonempty (G.EdgeColoring k) := by
  obtain ⟨ε₀, hε₀, m₁, hpack⟩ := exists_uniform_selected_coloring α β γ ν τ
    hα hα1 hβ hγ hγ1 hν hντ hτ
  let ε : ℝ := min ε₀ (β / 4)
  have hε : 0 < ε := lt_min hε₀ (by positivity)
  refine ⟨ε, hε, max m₁ 1, ?_⟩
  intro V E A B _ _ _ _ G U C e k a c J ZA ZB hcard hm hbip hrob hk hq
    hreserve hregular ha hae hdegree hZ hcover hbalance hreserved
  have hm₁ : m₁ ≤ Fintype.card A := (le_max_left _ _).trans hm
  have hm1 : 1 ≤ Fintype.card A := (le_max_right _ _).trans hm
  have hmpos : (0 : ℝ) < Fintype.card A := by exact_mod_cast hm1
  have haPack : a ≤ ε₀ * Fintype.card A :=
    hae.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hmpos.le)
  have haSmall : a ≤ (β / 4) * Fintype.card A :=
    hae.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hmpos.le)
  have hqposR : (0 : ℝ) < (k - J.card : ℕ) := (mul_pos hβ hmpos).trans_le hq
  have hqpos : 0 < k - J.card := by exact_mod_cast hqposR
  have hslack : 2 * a < (k - J.card : ℕ) := by nlinarith [mul_pos hβ hmpos]
  have hlow (v : U) :
      ((G.restrictEdges (coreEdges C)ᶜ).degree v.val : ℝ) ≤ a :=
    complement_degree_le_error C k a hregular hdegree v
  obtain ⟨F, d, hF, houtside, hleftover⟩ :=
    exists_selected_coloring G U C k a c J hregular hlow hslack
  have hZA : ZA ⊆ Uᶜ := by
    intro v hv
    exact hcover ▸ mem_union_left ZB hv
  have hcoreCross := core_copies_cross_augmented C e ZA hZA hbip
  have hcross (f : E) (hf : f ∉ F) : f ∈ G.cutEdges (leftShore e ∪ ZA) := by
    rcases hleftover f hf with hc | ⟨hc, hout, hj⟩
    · exact hcoreCross f hc
    · exact hreserved ⟨f, hc⟩ hout hj
  have hremaining : (G.restrictEdges Fᶜ).IsBipartite := by
    refine ⟨fun v => decide (v ∈ leftShore e ∪ ZA), ?_⟩
    intro f
    have hc := (G.mem_cutEdges (leftShore e ∪ ZA) f.val).mp
      (hcross f.val (mem_compl.mp f.property))
    change decide (G.firstEnd f.val ∈ leftShore e ∪ ZA) ≠
      decide (G.secondEnd f.val ∈ leftShore e ∪ ZA)
    simpa only [ne_eq, decide_eq_decide, eq_iff_iff] using hc
  have hlowF (v : V) (hv : v ∈ U) : ((G.restrictEdges F).degree v : ℝ) ≤ a := by
    exact (Nat.cast_le.mpr (G.restrictEdges_degree_mono hF v)).trans (hlow ⟨v, hv⟩)
  have hsidecard : (leftShore e).card = (rightShore e).card := by
    simp only [leftShore_card, rightShore_card, hcard]
  obtain ⟨d', hbalanced, hsize⟩ := exists_balanced_selected_coloring G U
    (leftShore e) (rightShore e) ZA ZB F k (k - J.card) a hqpos
    (shores_disjoint e) (shores_union e) hsidecard hZ hcover hbalance
    hregular houtside hlowF hcross ⟨d⟩
  have hJk : J.card ≤ k := by simpa only [Fintype.card_fin] using J.card_le_univ
  have hgap : ((k - J.card : ℕ) : ℝ) ≤ k - γ * Fintype.card A := by
    rw [Nat.cast_sub hJk]
    linarith only [hreserve]
  apply hpack V E A B G U C e k (k - J.card) a F d'
    hcard hm₁ hbip hrob hk hq hgap hregular houtside hF ha haPack hdegree hremaining
  · intro i
    rw [left_covered_card, right_covered_card]
    exact hbalanced i
  · intro i
    simpa only [leftShore_card] using hsize i

end Overfull.BoundedExterior
