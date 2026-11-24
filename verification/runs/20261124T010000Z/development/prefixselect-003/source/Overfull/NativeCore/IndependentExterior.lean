import Overfull.FewExceptions.Complement
import Overfull.OrdinaryFactorization.Parity

/-!
# A robust core with independent exterior vertices

When no edge joins two exterior vertices, the first-fan theorem removes
every exterior incidence from a hypothetical minimal obstruction to coloring
the core complement. This constructs the complementary coloring without a
no-overfull hypothesis. The existing ordinary-core theorem then gives a
uniform factorization for either parity of the original core.

This module is a one-core ingredient. It does not construct the shore
restrictions, contractions, or palette alignment needed to factor a terminal
two-core residual graph.
-/

noncomputable section

namespace Overfull.NativeCore

open Finset Classical SmallCuts OneCore OrdinaryFactorization

variable {V E : Type*} [Fintype V] [Fintype E] (G : Multigraph V E)

/-- Independence of the exterior means that every incidence at an
exterior vertex goes to the core. -/
theorem edgesTo_exterior_eq_empty (U : Finset V)
    (hindependent : G.internalEdges Uᶜ = ∅) (x : V) (hx : x ∉ U) :
    G.edgesTo x Uᶜ = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨hxe, ho⟩ := (G.mem_edgesTo x Uᶜ e).mp he
  have hi := (G.internalEdges_iff_of_edge e x (G.otherEnd x e)
    (G.edge_eq_otherEnd x e hxe) Uᶜ).mpr ⟨mem_compl.mpr hx, ho⟩
  rw [hindependent] at hi
  exact notMem_empty e hi

/-- The actual complementary copies admit `k` colors when the exterior
is independent and the complementary core degree is less than `k / 2`.
There is no bound on the number of exterior vertices in this lemma. -/
theorem complement_colorable_of_independent_exterior
    (U : Finset V) (H : Finset E) (k a : ℕ)
    (hregular : ∀ v, G.degree v = k)
    (hindependent : G.internalEdges Uᶜ = ∅)
    (hcore : ∀ v ∈ U, (G.restrictEdges Hᶜ).degree v ≤ a)
    (hka : 2 * a < k) :
    Nonempty ((G.restrictEdges Hᶜ).EdgeColoring k) := by
  by_contra hn
  obtain ⟨F, hFsub, hF⟩ := G.exists_kMinimal_subset k
    (fun v => (hregular v).le) Hᶜ hn
  have hlow : ∀ v ∈ U, (G.restrictEdges F).degree v ≤ a := by
    intro v hv
    exact (G.restrictEdges_degree_mono hFsub v).trans (hcore v hv)
  obtain ⟨hinside, hfan⟩ := G.first_fan_of_core_degree k a U F
    hregular hF hlow hka
  have hout : ∀ x, x ∉ U → (G.restrictEdges F).edgesTo x U = ∅ := by
    intro x hx
    have hsum := G.edgesTo_compl_card_add x U
    rw [edgesTo_exterior_eq_empty G U hindependent x hx, card_empty,
      Nat.zero_add, hregular] at hsum
    exact (hfan x (by omega)).1
  have hall := FewExceptions.internal_compl_eq_univ (G.restrictEdges F)
    U hinside hout
  have hcard : Fintype.card F ≤ k := by
    have hb := FewExceptions.restriction_internal_card_le G F Uᶜ
    rw [hall, card_univ, hindependent, card_empty] at hb
    exact hb.trans (Nat.zero_le k)
  obtain ⟨f⟩ : Nonempty (F ↪ Fin k) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hcard)
  apply hF.2.1
  refine ⟨⟨f, ?_⟩⟩
  intro e e' v he _ _
  exact f.injective he

/-- Real-error version of the exact-copy independent-exterior lemma. -/
theorem complement_colorable_of_independent_exterior_real
    (U : Finset V) (H : Finset E) (k : ℕ) (a : ℝ) (ha : 0 ≤ a)
    (hregular : ∀ v, G.degree v = k)
    (hindependent : G.internalEdges Uᶜ = ∅)
    (hcore : ∀ v ∈ U, ((G.restrictEdges Hᶜ).degree v : ℝ) ≤ a)
    (hka : 2 * a < k) :
    Nonempty ((G.restrictEdges Hᶜ).EdgeColoring k) := by
  apply complement_colorable_of_independent_exterior G U H k ⌊a⌋₊
    hregular hindependent (fun v hv => Nat.le_floor (hcore v hv))
  have hfloor := Nat.floor_le ha
  have hh : (2 : ℝ) * ⌊a⌋₊ < k := by linarith
  exact_mod_cast hh

/-- For an embedded simple core the complementary degree follows from
the actual host regularity and the core minimum degree. -/
theorem core_complement_colorable_of_independent_exterior
    (U : Finset V) (C : Core G U) (k : ℕ) (a : ℝ) (ha : 0 ≤ a)
    (hregular : ∀ v, G.degree v = k)
    (hindependent : G.internalEdges Uᶜ = ∅)
    (hdegree : ∀ v, (k : ℝ) - a ≤ (C.graph.degree v : ℝ))
    (hka : 2 * a < k) :
    Nonempty ((G.restrictEdges (coreEdges C)ᶜ).EdgeColoring k) := by
  exact complement_colorable_of_independent_exterior_real G U (coreEdges C)
    k a ha hregular hindependent
    (fun v hv => complement_degree_le_error C k a hregular hdegree ⟨v, hv⟩) hka

/-- Uniform factorization with any fixed number of independent exterior
vertices. The original core may have either parity, and neither a supplied
complementary coloring nor a no-overfull hypothesis is required. -/
theorem exists_uniform_independent_exterior_factorization (α ν τ : ℝ) (s : ℕ)
    (hα : 0 < α) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτ : τ ≤ min α 1 / 16) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ m₀ : ℕ,
      ∀ (V E : Type*) [Fintype V] [Fintype E]
        (G : Multigraph V E) (U : Finset V) (C : Core G U) (k : ℕ) (a : ℝ),
        m₀ ≤ U.card → Even (Fintype.card V) → Uᶜ.card ≤ s →
        (∀ v, G.degree v = k) → α * U.card ≤ (k : ℝ) →
        G.internalEdges Uᶜ = ∅ →
        IsRobustExpander C.graph ν τ → a ≤ ε * U.card →
        (∀ v, (k : ℝ) - a ≤ (C.graph.degree v : ℝ)) →
        Nonempty (G.EdgeColoring k) := by
  obtain ⟨η, hη, m₁, hfactor⟩ :=
    exists_uniform_factorization_any_core_parity α ν τ s hα hν hντ hτ
  let ε : ℝ := min η (α / 4)
  have hε : 0 < ε := lt_min hη (by positivity)
  refine ⟨ε, hε, max m₁ 1, ?_⟩
  intro V E _ _ G U C k a hn hEven hZ hregular hk hindependent hrob hae hdegree
  have hn1 : 1 ≤ U.card := (le_max_right _ _).trans hn
  have hnpos : (0 : ℝ) < U.card := by exact_mod_cast (show 0 < U.card by omega)
  obtain ⟨v, hv⟩ := card_pos.mp (show 0 < U.card by omega)
  have hupper : (C.graph.degree ⟨v, hv⟩ : ℝ) ≤ k := by
    exact_mod_cast (core_degree_le C ⟨v, hv⟩).trans_eq (hregular v)
  have ha : 0 ≤ a := by linarith only [hdegree ⟨v, hv⟩, hupper]
  have hαn : 0 < α * U.card := mul_pos hα hnpos
  have haα : a ≤ α * U.card / 4 := by
    have h := hae.trans (mul_le_mul_of_nonneg_right (min_le_right η (α / 4))
      (Nat.cast_nonneg U.card))
    linarith
  have hka : 2 * a < (k : ℝ) := by linarith
  have hc := core_complement_colorable_of_independent_exterior G U C k a ha
    hregular hindependent hdegree hka
  have haη : a ≤ η * U.card :=
    hae.trans (mul_le_mul_of_nonneg_right (min_le_left η (α / 4))
      (Nat.cast_nonneg U.card))
  exact hfactor V E G U C k a ((le_max_left _ _).trans hn) hEven hZ
    hregular hk hrob haη hdegree hc

/-- The uniform coloring conclusion partitions every original edge copy
into exactly `k` pairwise disjoint perfect matchings. -/
theorem exists_uniform_independent_exterior_one_factorization (α ν τ : ℝ) (s : ℕ)
    (hα : 0 < α) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτ : τ ≤ min α 1 / 16) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ m₀ : ℕ,
      ∀ (V E : Type*) [Fintype V] [Fintype E]
        (G : Multigraph V E) (U : Finset V) (C : Core G U) (k : ℕ) (a : ℝ),
        m₀ ≤ U.card → Even (Fintype.card V) → Uᶜ.card ≤ s →
        (∀ v, G.degree v = k) → α * U.card ≤ (k : ℝ) →
        G.internalEdges Uᶜ = ∅ →
        IsRobustExpander C.graph ν τ → a ≤ ε * U.card →
        (∀ v, (k : ℝ) - a ≤ (C.graph.degree v : ℝ)) →
        ∃ M : Fin k → Finset E,
          (∀ i, G.IsPerfectMatching (M i)) ∧
          Pairwise (fun i j => Disjoint (M i) (M j)) ∧
          univ.biUnion M = univ := by
  obtain ⟨ε, hε, m₀, hfactor⟩ :=
    exists_uniform_independent_exterior_factorization α ν τ s hα hν hντ hτ
  refine ⟨ε, hε, m₀, ?_⟩
  intro V E _ _ G U C k a hm heven hZ hregular hk hindependent hrob hae hdegree
  obtain ⟨c⟩ := hfactor V E G U C k a hm heven hZ hregular hk
    hindependent hrob hae hdegree
  exact BoundedExterior.exists_oneFactorization_of_coloring G k hregular c

end Overfull.NativeCore
