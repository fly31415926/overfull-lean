import Overfull.TwoApexFactorization.Balance
import Overfull.TwoApexFactorization.Packing

/-!
# Factorization through a robust bipartite core with two apices

One apex has a linear number of incidences into both core shores.  A
linear residual palette can therefore be left genuinely bipartite after
all selected exceptional copies are completed.  The selected coloring,
the core completions, and the final coloring are all constructed.
-/

noncomputable section

namespace Overfull.TwoApexFactorization

open Finset Classical SmallCuts SimpleGraph

/-- A regular multigraph with a nearly spanning robust bipartite core and
exactly two exterior vertices has a one-factorization when one exterior
vertex has linearly many incidences into each core shore.

The core error and order threshold are uniform. No coloring of the
complement, no absorber, and no residual coloring is an assumption. -/
theorem exists_uniform_two_apex_factorization (α lam ν τ : ℝ)
    (hα : 0 < α) (hα1 : α < 1) (hlam : 0 < lam) (hlamα : lam ≤ α / 4)
    (hν : 0 < ν) (hντ : ν ≤ τ) (hτ : τ < α / 16) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ m₀ : ℕ,
      ∀ (V E A B : Type*) [Fintype V] [Fintype E] [Fintype A] [Fintype B]
        (G : Multigraph V E) (U : Finset V) (C : Core G U)
        (e : A ⊕ B ≃ U) (x y : V) (k : ℕ) (a : ℝ),
        Fintype.card A = Fintype.card B → m₀ ≤ Fintype.card A →
        x ≠ y → Uᶜ = {x, y} → (∀ v, G.degree v = k) →
        α * Fintype.card A ≤ k →
        (C.graph.comap e).IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr) →
        IsBipartiteRobustExpander (C.graph.comap e) ν τ →
        0 ≤ a → a ≤ ε * Fintype.card A →
        (∀ v : U, (k : ℝ) - a ≤ C.graph.degree v) →
        lam * Fintype.card A ≤ (G.edgesTo y (leftShore e)).card →
        lam * Fintype.card A ≤ (G.edgesTo y (rightShore e)).card →
        Nonempty (G.EdgeColoring k) := by
  have hhalf : 0 < α / 2 := by positivity
  have hquarter : 0 < lam / 4 := by positivity
  have hquarter1 : lam / 4 < 1 := by linarith only [hlamα, hα1]
  obtain ⟨ε₁, hε₁, m₁, hpack⟩ := exists_uniform_selected_coloring α (α / 2) (lam / 4) ν τ
    hα hα1 hhalf hquarter hquarter1 hν hντ hτ
  let ε : ℝ := min ε₁ (lam / 8)
  have hε : 0 < ε := lt_min hε₁ (by positivity)
  obtain ⟨m₂, hm₂⟩ := exists_nat_gt (4 / lam)
  refine ⟨ε, hε, max m₁ (max m₂ 1), ?_⟩
  intro V E A B _ _ _ _ G U C e x y k a hcard hm hxy houtside hregular hk hbip hrob
    ha hae hdegree hyA hyB
  have hm₁ : m₁ ≤ Fintype.card A := (le_max_left _ _).trans hm
  have hm₂' : m₂ ≤ Fintype.card A :=
    (le_trans (le_max_left _ _) (le_max_right _ _)).trans hm
  have hm1 : 1 ≤ Fintype.card A :=
    (le_trans (le_max_right _ _) (le_max_right _ _)).trans hm
  have hmpos : (0 : ℝ) < Fintype.card A := by exact_mod_cast hm1
  have hlamm : 0 < lam * Fintype.card A := mul_pos hlam hmpos
  have hlarge : 4 < lam * Fintype.card A := by
    have hmR : (m₂ : ℝ) ≤ Fintype.card A := by exact_mod_cast hm₂'
    have hh := (div_lt_iff₀ hlam).mp (hm₂.trans_le hmR)
    nlinarith only [hh]
  have haPack : a ≤ ε₁ * Fintype.card A :=
    hae.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hmpos.le)
  have haSmall : a ≤ lam * Fintype.card A / 8 := by
    have hh := hae.trans (mul_le_mul_of_nonneg_right (min_le_right ε₁ (lam / 8)) hmpos.le)
    nlinarith only [hh]
  let d : ℕ := Nat.ceil ((lam / 4) * Fintype.card A)
  have hdlo : (lam / 4) * Fintype.card A ≤ d := Nat.le_ceil _
  have hdhi : (d : ℝ) ≤ lam * Fintype.card A / 2 := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ (lam / 4) * (Fintype.card A : ℝ) by positivity)
    change (d : ℝ) < (lam / 4) * Fintype.card A + 1 at hh
    nlinarith only [hh, hlarge]
  have hlambound : lam * Fintype.card A ≤ α * Fintype.card A / 4 := by
    have hh := mul_le_mul_of_nonneg_right hlamα hmpos.le
    nlinarith only [hh]
  have hdk : d ≤ k := by
    have hh : (d : ℝ) ≤ k := by linarith only [hdhi, hlambound, hk]
    exact_mod_cast hh
  let q : ℕ := k - d
  have hqk : q ≤ k := Nat.sub_le _ _
  have hqR : (q : ℝ) = k - d := by dsimp only [q]; exact Nat.cast_sub hdk
  have hqDensity : (α / 2) * Fintype.card A ≤ (q : ℝ) := by
    rw [hqR]
    nlinarith only [hdhi, hlambound, hk]
  have hqreserve : (q : ℝ) ≤ k - (lam / 4) * Fintype.card A := by rw [hqR]; linarith only [hdlo]
  have hqhalf : k ≤ 2 * q := by
    have hh : (k : ℝ) ≤ 2 * q := by rw [hqR]; linarith only [hdhi, hlambound, hk]
    exact_mod_cast hh
  have hqa : 2 * a < (q : ℝ) := by
    nlinarith only [hqDensity, hlambound, haSmall, hlamm]
  have hcomplement (v : U) :
      ((G.restrictEdges (OneCore.coreEdges C)ᶜ).degree v.val : ℝ) ≤ a :=
    OneCore.complement_degree_le_error C k a hregular hdegree v
  have hsidecard : (leftShore e).card = (rightShore e).card := by simp only [leftShore_card,
    rightShore_card, hcard]
  have hcorecount := apex_core_counts_eq G U x y k houtside hregular
  have hysum := side_edges_sum G e y
  have hxsum := side_edges_sum G e x
  have hytotal : (G.edgesTo y U).card ≤ k := by
    have hh := G.edgesTo_compl_card_add y U
    rw [hregular y] at hh
    omega
  have hxtotal : (G.edgesTo x U).card ≤ k := by rw [hcorecount]; exact hytotal
  have hb : 2 * lam * Fintype.card A ≤ ((G.edgesTo x U).card : ℝ) := by
    have hsR : ((G.edgesTo y (leftShore e)).card : ℝ) +
        (G.edgesTo y (rightShore e)).card = (G.edgesTo y U).card := by exact_mod_cast hysum
    rw [hcorecount]
    nlinarith only [hyA, hyB, hsR]
  have hactive : 2 * a < (min q (G.edgesTo x U).card : ℕ) := by
    rw [Nat.cast_min]
    exact lt_min hqa (by nlinarith only [haSmall, hb, hlamm])
  have hyAq : (G.edgesTo y (leftShore e)).card ≤ q := by
    have hsR : ((G.edgesTo y (leftShore e)).card : ℝ) +
        (G.edgesTo y (rightShore e)).card ≤ k := by exact_mod_cast (hysum.le.trans hytotal)
    have hh : ((G.edgesTo y (leftShore e)).card : ℝ) ≤ q := by
      rw [hqR]
      linarith only [hsR, hyB, hdhi, hlamm]
    exact_mod_cast hh
  have hyBq : (G.edgesTo y (rightShore e)).card ≤ q := by
    have hsR : ((G.edgesTo y (leftShore e)).card : ℝ) +
        (G.edgesTo y (rightShore e)).card ≤ k := by exact_mod_cast (hysum.le.trans hytotal)
    have hh : ((G.edgesTo y (rightShore e)).card : ℝ) ≤ q := by
      rw [hqR]
      linarith only [hsR, hyA, hdhi, hlamm]
    exact_mod_cast hh
  have finish (z w : V) (hzw : z ≠ w) (hout : Uᶜ = {z, w})
      (hact : 2 * a < (min q (G.edgesTo z U).card : ℕ))
      (S : Selection G U (leftShore e) (rightShore e) C z w q) :
      Nonempty (G.EdgeColoring k) := by
    have hz : z ∉ U := by
      apply mem_compl.mp
      rw [hout]
      simp
    have hcross := core_copies_cross C e z hz hbip
    obtain ⟨c, hbalance, hsize⟩ := exists_balanced_selection_coloring G U
      (leftShore e) (rightShore e) C z w k q S a hzw hout (shores_disjoint e)
      (shores_union e) hsidecard hregular hcross ha hqa hact hcomplement
    apply hpack V E A B G U C e k q a S.edges c hcard hm₁ hbip hrob hk hqDensity
      hqreserve hregular
    · intro v hv
      have hv' : v = z ∨ v = w := by
        have hh : v ∈ Uᶜ := mem_compl.mpr hv
        simpa only [hout, mem_insert, mem_singleton] using hh
      rcases hv' with rfl | rfl
      · exact S.apex_degree_left
      · exact S.apex_degree_right
    · exact S.subset_complement
    · exact ha
    · exact haPack
    · exact hdegree
    · exact S.remaining_bipartite hcross
    · intro i
      rw [left_covered_card, right_covered_card]
      exact hbalance i
    · intro i
      simpa only [leftShore_card] using hsize i
  by_cases hxAq : (G.edgesTo x (leftShore e)).card ≤ q
  · obtain ⟨S⟩ := exists_selection G U (leftShore e) (rightShore e) C x y k q
      hxy houtside (shores_disjoint e) (shores_union e) hregular hqk hxAq hyBq
    exact finish x y hxy houtside hactive S
  · have hxBq : (G.edgesTo x (rightShore e)).card ≤ q := by omega
    have hout' : Uᶜ = {y, x} := houtside.trans (Finset.pair_comm _ _)
    obtain ⟨S⟩ := exists_selection G U (leftShore e) (rightShore e) C y x k q
      hxy.symm hout' (shores_disjoint e) (shores_union e) hregular hqk hyAq hxBq
    exact finish y x hxy.symm hout' (by simpa only [hcorecount] using hactive) S

end Overfull.TwoApexFactorization
