import Overfull.Terminal.CentralCuts
import Overfull.NativeTerminal.BoundedInput

/-!
# Uniform factorization of the central host

The actual exterior matching cover supplies no-overfullness.  The completed
bounded-input theorem then constructs the coloring of the one-core host with
two other vertices.  The error and order threshold are chosen uniformly.
-/

noncomputable section

namespace Overfull.Terminal

open Finset Classical Multigraph SmallCuts OneCore

theorem exists_uniform_central_coloring (α ν τ : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτ : τ ≤ α / 64) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ m₀ : ℕ,
      ∀ (V E : Type*) [Fintype V] [Fintype E]
        (G : Multigraph V E) (U : Finset V) (C : Core G U) (k : ℕ) (a : ℝ),
        m₀ ≤ U.card → Even (Fintype.card V) → Uᶜ.card ≤ 2 →
        (∀ v, G.degree v = k) → α * U.card ≤ (k : ℝ) →
        IsRobustExpander C.graph ν τ → a ≤ ε * U.card →
        (∀ v, (k : ℝ) - a ≤ (C.graph.degree v : ℝ)) →
        (M : Fin k → Finset E) → (∀ i, G.IsMatching (M i)) →
        (∀ e, e ∉ G.internalEdges U → ∃ i, e ∈ M i) →
        Nonempty (G.EdgeColoring k) := by
  have hτcut : τ ≤ α / 20 := by linarith
  obtain ⟨mcut,hcut⟩ := robust_two_exterior_no_overfull α ν τ hα hα1 hν hντ hτcut
  have hτfactor : τ ≤ min (α/2) (min (1/2 : ℝ) 1) / 16 := by
    rw [min_eq_left (by norm_num : (1/2 : ℝ) ≤ 1),min_eq_left (by linarith : α/2 ≤ (1/2 : ℝ))]
    linarith
  obtain ⟨η,hη,n₀,_hn₀,hfactor⟩ := bounded_input_factorization (α/2) (1/2) ν τ
    (by positivity) (by norm_num) hν hντ hτfactor
  let ε := min (α/20) (η/2)
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  refine ⟨ε,hε,max (max mcut n₀) (max 2 ⌈2/η⌉₊),?_⟩
  intro V E _ _ G U C k a hm heven hout hregular hk hrob ha hdegree M hM hcover
  have hmcut : mcut ≤ U.card :=
    (le_max_left _ _).trans ((le_max_left _ _).trans hm)
  have hmn : n₀ ≤ U.card :=
    (le_max_right _ _).trans ((le_max_left _ _).trans hm)
  have hmtwo : 2 ≤ U.card :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hm)
  have hmceil : ⌈2/η⌉₊ ≤ U.card :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hm)
  have hUn : U.card ≤ Fintype.card V := card_le_univ U
  have hUnR : (U.card : ℝ) ≤ Fintype.card V := by exact_mod_cast hUn
  have hparts := card_add_card_compl U
  have hnm : Fintype.card V ≤ 2 * U.card := by omega
  have hnmR : (Fintype.card V : ℝ) ≤ 2 * U.card := by exact_mod_cast hnm
  have hsize : (1/2 : ℝ) * Fintype.card V ≤ U.card := by linarith
  have hkhost : α/2 * Fintype.card V ≤ (k : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hnmR hα.le]
  obtain ⟨u,hu⟩ := card_pos.mp (show 0 < U.card by omega)
  have hupper : (C.graph.degree ⟨u,hu⟩ : ℝ) ≤ k := by
    exact_mod_cast (core_degree_le C ⟨u,hu⟩).trans_eq (hregular u)
  have ha0 : 0 ≤ a := by linarith only [hdegree ⟨u,hu⟩,hupper]
  have hasmall : a ≤ α * U.card / 20 := by
    have hb := ha.trans (mul_le_mul_of_nonneg_right (min_le_left (α/20) (η/2))
      (Nat.cast_nonneg U.card))
    linarith
  have hno := hcut V E G U C k a hmcut (Nat.even_iff.mp heven) hout hregular hk
    ha0 hasmall hrob hdegree M hM hcover
  have hone : 1 ≤ η/2 * U.card := by
    have hceil : (2/η : ℝ) ≤ U.card := (Nat.le_ceil (2/η)).trans (by exact_mod_cast hmceil)
    have hh := (div_le_iff₀ hη).mp hceil
    nlinarith
  have haη : a ≤ η/2 * U.card := ha.trans
    (mul_le_mul_of_nonneg_right (min_le_right (α/20) (η/2)) (Nat.cast_nonneg U.card))
  have haHost : a+1 ≤ η * Fintype.card V := by
    nlinarith [mul_le_mul_of_nonneg_left hUnR hη.le]
  exact hfactor V E G k a (hmn.trans hUn) heven hregular hkhost hno haHost
    (Or.inl ⟨U,C,by omega,hsize,hrob,hdegree⟩)

end Overfull.Terminal
