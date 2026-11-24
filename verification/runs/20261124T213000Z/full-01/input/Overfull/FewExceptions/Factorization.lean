import Overfull.FewExceptions.Complement
import Overfull.OrdinaryFactorization.Parity

/-!
# One robust core with at most three exceptional vertices

The complement coloring is constructed from no-overfullness and the
actual core degree bound.  The core may have either parity.  The public
host-normalized statements retain the original regular multigraph, all
parallel copies, the linear degree and core-order bounds, and the source
error convention. They prove the one-core branch of Corollary 4.6; the
separate two-core branch is not asserted here.
-/

noncomputable section

namespace Overfull.FewExceptions

open Finset Classical SmallCuts OneCore OrdinaryFactorization

/-- Construct the entire host coloring from the original one-core
hypotheses, with no supplied coloring or parity premise on the core. -/
theorem exists_uniform_one_core_factorization (α ν τ : ℝ)
    (hα : 0 < α) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτ : τ ≤ min α 1 / 16) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ m₀ : ℕ,
      ∀ (V E : Type*) [Fintype V] [Fintype E]
        (G : Multigraph V E) (U : Finset V) (C : Core G U) (k : ℕ) (a : ℝ),
        m₀ ≤ U.card → Even (Fintype.card V) → Uᶜ.card ≤ 3 →
        (∀ v, G.degree v = k) → α * U.card ≤ (k : ℝ) →
        (∀ X : Finset V, ¬ G.IsOverfull k X) →
        IsRobustExpander C.graph ν τ → a ≤ ε * U.card →
        (∀ v, (k : ℝ) - a ≤ (C.graph.degree v : ℝ)) →
        Nonempty (G.EdgeColoring k) := by
  classical
  obtain ⟨η, hη, m₁, hfactor⟩ :=
    exists_uniform_factorization_any_core_parity α ν τ 3 hα hν hντ hτ
  let ε : ℝ := min η (α / 100)
  have hε : 0 < ε := lt_min hη (by positivity)
  refine ⟨ε, hε, max m₁ 1, ?_⟩
  intro V E _ _ G U C k a hn hEven hZ hregular hk hsafe hrob hae hdegree
  have hn1 : 1 ≤ U.card := (le_max_right _ _).trans hn
  have hnpos : (0 : ℝ) < U.card := by exact_mod_cast (show 0 < U.card by omega)
  obtain ⟨v, hv⟩ := card_pos.mp (show 0 < U.card by omega)
  have hupper : (C.graph.degree ⟨v, hv⟩ : ℝ) ≤ k := by
    exact_mod_cast (core_degree_le C ⟨v, hv⟩).trans_eq (hregular v)
  have ha : 0 ≤ a := by linarith only [hdegree ⟨v, hv⟩, hupper]
  have hαn : 0 < α * U.card := mul_pos hα hnpos
  have haα : a ≤ α * U.card / 100 := by
    have h := hae.trans (mul_le_mul_of_nonneg_right (min_le_right η (α / 100))
      (Nat.cast_nonneg U.card))
    linarith
  have hka : 24 * a < (k : ℝ) := by linarith
  have hc := core_complement_colorable G U C k a hregular hsafe hZ ha hdegree hka
  have haη : a ≤ η * U.card :=
    hae.trans (mul_le_mul_of_nonneg_right (min_le_left η (α / 100))
      (Nat.cast_nonneg U.card))
  exact hfactor V E G U C k a ((le_max_left _ _).trans hn) hEven hZ
    hregular hk hrob haη hdegree hc

end Overfull.FewExceptions

namespace Overfull

open Finset Classical SmallCuts

/-- The complete one-core branch of the bounded-input Corollary 4.6,
with degree, core order, and error normalized by the original host order.
The distinct two-core branch remains a separate statement. -/
theorem one_core_three_exception_factorization (α ν τ : ℝ)
    (hα : 0 < α) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτ : τ ≤ min α 1 / 16) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ,
      ∀ (V E : Type*) [Fintype V] [Fintype E]
        (G : Multigraph V E) (U : Finset V) (C : Core G U) (k : ℕ) (a : ℝ),
        n₀ ≤ Fintype.card V → Even (Fintype.card V) → Uᶜ.card ≤ 3 →
        (∀ v, G.degree v = k) → α * Fintype.card V ≤ (k : ℝ) →
        α * Fintype.card V ≤ (U.card : ℝ) →
        (∀ X : Finset V, ¬ G.IsOverfull k X) →
        IsRobustExpander C.graph ν τ → a + 1 ≤ ε * Fintype.card V →
        (∀ v, (k : ℝ) - a ≤ (C.graph.degree v : ℝ)) →
        Nonempty (G.EdgeColoring k) := by
  obtain ⟨η, hη, m₀, hfactor⟩ :=
    FewExceptions.exists_uniform_one_core_factorization α ν τ hα hν hντ hτ
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt ((m₀ : ℝ) / α)
  refine ⟨η * α, mul_pos hη hα, n₀, ?_⟩
  intro V E _ _ G U C k a hn hEven hZ hregular hk hU hsafe hrob hae hdegree
  have hnReal : (n₀ : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  have hlarge : (m₀ : ℝ) ≤ U.card := by
    have h := (div_lt_iff₀ hα).mp hn₀
    have hmul := mul_le_mul_of_nonneg_left hnReal hα.le
    nlinarith only [h, hmul, hU]
  have hsub : (U.card : ℝ) ≤ Fintype.card V := by exact_mod_cast U.card_le_univ
  have hkCore : α * U.card ≤ (k : ℝ) :=
    (mul_le_mul_of_nonneg_left hsub hα.le).trans hk
  have haCore : a ≤ η * U.card := by
    have h := mul_le_mul_of_nonneg_left hU hη.le
    nlinarith only [hae, h]
  exact hfactor V E G U C k a (by exact_mod_cast hlarge) hEven hZ
    hregular hkCore hsafe hrob haCore hdegree

/-- The same original-hypothesis conclusion as exactly `k` pairwise
disjoint perfect matchings whose union is every original edge copy. -/
theorem one_core_three_exception_one_factorization (α ν τ : ℝ)
    (hα : 0 < α) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτ : τ ≤ min α 1 / 16) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ,
      ∀ (V E : Type*) [Fintype V] [Fintype E]
        (G : Multigraph V E) (U : Finset V) (C : Core G U) (k : ℕ) (a : ℝ),
        n₀ ≤ Fintype.card V → Even (Fintype.card V) → Uᶜ.card ≤ 3 →
        (∀ v, G.degree v = k) → α * Fintype.card V ≤ (k : ℝ) →
        α * Fintype.card V ≤ (U.card : ℝ) →
        (∀ X : Finset V, ¬ G.IsOverfull k X) →
        IsRobustExpander C.graph ν τ → a + 1 ≤ ε * Fintype.card V →
        (∀ v, (k : ℝ) - a ≤ (C.graph.degree v : ℝ)) →
        ∃ M : Fin k → Finset E,
          (∀ i, G.IsPerfectMatching (M i)) ∧
          Pairwise (fun i j => Disjoint (M i) (M j)) ∧
          univ.biUnion M = univ := by
  obtain ⟨ε, hε, n₀, hfactor⟩ :=
    one_core_three_exception_factorization α ν τ hα hν hντ hτ
  refine ⟨ε, hε, n₀, ?_⟩
  intro V E _ _ G U C k a hn hEven hZ hregular hk hU hsafe hrob hae hdegree
  obtain ⟨c⟩ := hfactor V E G U C k a hn hEven hZ hregular hk hU hsafe hrob hae hdegree
  exact BoundedExterior.exists_oneFactorization_of_coloring G k hregular c

end Overfull
