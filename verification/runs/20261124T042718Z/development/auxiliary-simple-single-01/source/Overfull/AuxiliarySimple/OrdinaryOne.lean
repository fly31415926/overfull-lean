import Overfull.AuxiliarySimple.Completion
import Overfull.AuxiliarySimple.Deficiency
import Overfull.AuxiliaryCompletion
import Overfull.AuxiliarySimple.OrdinaryTwo

/-!
# One ordinary robust core via a second auxiliary completion

The two-core nonregular theorem colors the actual auxiliary completion of a
one-core input.  Original edge copies are then restored by restriction.  The
outer theorem gives the source one-core coloring lemma at maximum degree.
-/

noncomputable section

namespace Overfull

open Finset Classical SimpleGraph AuxiliarySimple AuxiliaryCompletion

universe u

set_option maxHeartbeats 1200000 in
/-- An original one-core input with a small linear exceptional set is colored
by constructing an auxiliary core and using the proved two-core theorem. -/
theorem one_core_nonregular_factorization (α ν τ : ℝ)
    (hα : 0 < α) (hα1 : α < 1) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτ : τ ≤ α / 1024000) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, 0 < n₀ ∧
      ∀ (V : Type u) [Fintype V] (G : SimpleGraph V)
        (U : Fin 1 → Finset V) (H : ∀ i, SimpleGraph (U i))
        (Z : Finset V) (k : ℕ) (a : ℝ),
        n₀ ≤ Fintype.card V → k < Fintype.card V →
        (∀ v, G.degree v ≤ k) → α * Fintype.card V ≤ (k : ℝ) →
        (∀ X : Finset V, ¬ IsOverfull G k X) →
        Pairwise (fun i j => Disjoint (U i) (U j)) →
        (∀ i, Disjoint (U i) Z) → (∀ v, v ∈ Z ∨ ∃ i, v ∈ U i) →
        (∀ i, α * Fintype.card V ≤ ((U i).card : ℝ)) →
        (∀ i, H i ≤ G.induce (U i : Set V)) →
        (∀ i, IsRobustExpander (H i) ν τ) →
        (∀ i v, (k : ℝ) - a ≤ ((H i).degree v : ℝ)) →
        0 ≤ a → a + (Z.card : ℝ) + 1 ≤ ε * Fintype.card V →
        Nonempty ((Multigraph.ofSimpleGraph G).EdgeColoring k) := by
  have hτpos : 0 < τ := hν.trans_le hντ
  obtain ⟨νC, εC, hνC, hεC, nC, hcomplete⟩ :=
    robust_auxiliary_completion α τ hα hα1 hτpos (by linarith only [hτ, hα])
  let μ := min ν νC
  have hμ : 0 < μ := lt_min hν hνC
  have hμτ : μ ≤ τ := (min_le_left _ _).trans hντ
  obtain ⟨εR, hεR, nR, _hnR, hfactor⟩ :=
    two_core_nonregular_factorization.{u} (α / 2) μ τ (by positivity) (by linarith)
      hμ hμτ (by linarith only [hτ])
  let ε := min εC εR
  have hε : 0 < ε := lt_min hεC hεR
  let n₀ := max 1 (max nC nR)
  have hn₀ : 0 < n₀ := lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) (le_max_left _ _)
  refine ⟨ε, hε, n₀, hn₀, ?_⟩
  intro V _ G U H Z k a hn hk hdegree hdensity hno _hdisjoint hUZ hcover
    hsize hembed hrobust hcore ha herror
  have hnpos : 0 < Fintype.card V := hn₀.trans_le hn
  have hnC : nC ≤ Fintype.card V :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnR : nR ≤ Fintype.card V :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have herrorC : a + (Z.card : ℝ) + 1 ≤ εC * Fintype.card V :=
    herror.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _))
  have herrorR : a + (Z.card : ℝ) + 1 ≤ εR * Fintype.card V :=
    herror.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg _))
  have hdeficiency : (∑ v, ((k - G.degree v : ℕ) : ℝ)) ≤
      εC * (Fintype.card V : ℝ)^2 := by
    have htotal := total_deficiency_le G U H Z k a hdegree hk.le hcover hembed hcore ha
    have hb : a + (Z.card : ℝ) ≤ εC * Fintype.card V := by linarith only [herrorC]
    have hh := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (Fintype.card V))
    nlinarith only [htotal, hh]
  have hdegreeM : ∀ v, (Multigraph.ofSimpleGraph G).degree v ≤ k := by
    simpa only [Multigraph.ofSimpleGraph_degree] using hdegree
  have hnoM : ∀ X : Finset V, ¬ (Multigraph.ofSimpleGraph G).IsOverfull k X := by
    simpa only [Multigraph.IsOverfull, Multigraph.ofSimpleGraph_internalEdges, IsOverfull] using hno
  have hdeficiencyM : (∑ v, ((k - (Multigraph.ofSimpleGraph G).degree v : ℕ) : ℝ)) ≤
      εC * (Fintype.card V : ℝ)^2 := by
    simpa only [Multigraph.ofSimpleGraph_degree] using hdeficiency
  let m := auxiliaryOrder (Fintype.card V) k
  have hm : m = Fintype.card V := auxiliaryOrder_eq_of_lt _ _ hk
  obtain ⟨N, L, hregular, _heven, _hOriginal, _hAux, _hAdded, hLrobust, hLdegree, hnoPlus⟩ :=
    hcomplete V G.edgeSet (Multigraph.ofSimpleGraph G) k hnC hdegreeM hdensity
      (by omega) hdeficiencyM hnoM
  let R := completion G N L
  let P : Fin 2 → Finset (V ⊕ Fin m) :=
    Fin.cases ((U 0).map Function.Embedding.inl) (fun _ => auxiliaryVertices V (Fin m))
  let K : ∀ i, SimpleGraph (P i) :=
    Fin.cases (mappedCore Function.Embedding.inl (U 0) (H 0))
      (fun _ => auxiliaryCore (V := V) L)
  let Z' : Finset (V ⊕ Fin m) := Z.map Function.Embedding.inl
  let a' := a + (Z.card : ℝ) + 1
  have horder : Fintype.card (V ⊕ Fin m) = 2 * Fintype.card V := by
    simp only [Fintype.card_sum, Fintype.card_fin, hm]
    omega
  have horderR : (Fintype.card (V ⊕ Fin m) : ℝ) = 2 * Fintype.card V := by
    exact_mod_cast horder
  have hRregular : ∀ v, R.degree v = k := by
    intro v
    exact (completion_degree G N L v).trans (hregular v)
  have hRno : ∀ X : Finset (V ⊕ Fin m), ¬ IsOverfull R k X := by
    intro X hX
    exact hnoPlus X ((completion_overfull_iff G N L k X).mp hX)
  have hPdisjoint : Pairwise (fun i j => Disjoint (P i) (P j)) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> dsimp [P, auxiliaryVertices]
    all_goals first
      | exact (hij rfl).elim
      | exact Finset.disjoint_map_inl_map_inr _ _
      | exact (Finset.disjoint_map_inl_map_inr _ _).symm
  have hPZ : ∀ i, Disjoint (P i) Z' := by
    intro i
    fin_cases i <;> dsimp [P, Z', auxiliaryVertices]
    · exact (Finset.disjoint_map _).mpr (hUZ 0)
    · exact (Finset.disjoint_map_inl_map_inr _ _).symm
  have hPcover : ∀ v, v ∈ Z' ∨ ∃ i, v ∈ P i := by
    intro v
    rcases v with v | v
    · rcases hcover v with hv | ⟨i, hi⟩
      · exact Or.inl (mem_map.mpr ⟨v, hv, rfl⟩)
      · right
        fin_cases i
        · exact ⟨0, mem_map.mpr ⟨v, hi, rfl⟩⟩
    · exact Or.inr ⟨1, mem_map.mpr ⟨v, mem_univ v, rfl⟩⟩
  have hPsize : ∀ i, (α / 2) * Fintype.card (V ⊕ Fin m) ≤ ((P i).card : ℝ) := by
    intro i
    rw [horderR]
    fin_cases i
    · change α / 2 * (2 * Fintype.card V) ≤ (((U 0).map Function.Embedding.inl).card : ℝ)
      rw [Finset.card_map]
      nlinarith only [hsize 0]
    · have hmR : (m : ℝ) = Fintype.card V := by exact_mod_cast hm
      have hN := mul_le_mul_of_nonneg_right hα1.le (Nat.cast_nonneg (Fintype.card V))
      change α / 2 * (2 * Fintype.card V) ≤ ((auxiliaryVertices V (Fin m)).card : ℝ)
      rw [auxiliaryVertices_card, Fintype.card_fin]
      nlinarith only [hN, hmR]
  have hKembed : ∀ i, K i ≤ R.induce (P i : Set (V ⊕ Fin m)) := by
    intro i
    fin_cases i
    · exact completion_original_core G N L (U 0) (H 0) (hembed 0)
    · exact completion_auxiliary_core G N L
  have hKrobust : ∀ i, IsRobustExpander (K i) μ τ := by
    intro i
    fin_cases i
    · exact mappedCore_robust Function.Embedding.inl (U 0) (H 0) μ τ
        (IsRobustExpander.mono_parameter (H 0) (hrobust 0) (min_le_left _ _))
    · exact auxiliaryCore_robust L μ τ
        (IsRobustExpander.mono_parameter L hLrobust (min_le_right _ _))
  have hb := ceil_average_deficiency_le G U H Z k a hnpos hdegree hk.le hcover hembed hcore ha
  have hKdegree : ∀ i v, (k : ℝ) - a' ≤ ((K i).degree v : ℝ) := by
    intro i v
    fin_cases i
    · change (k : ℝ) - a' ≤ ((mappedCore Function.Embedding.inl (U 0) (H 0)).degree v : ℝ)
      rw [mappedCore_degree]
      have hh := hcore 0 ((partEquiv Function.Embedding.inl (U 0)).symm v)
      dsimp [a']
      linarith only [hh, Nat.cast_nonneg Z.card]
    · change (k : ℝ) - a' ≤ ((auxiliaryCore (V := V) L).degree v : ℝ)
      rw [auxiliaryCore_degree]
      have hh := hLdegree ((auxiliaryEquiv (V := V)).symm v)
      simp only [Multigraph.ofSimpleGraph_degree, auxiliaryOrder_eq_of_lt _ _ hk] at hh
      dsimp [a']
      linarith only [hh, hb]
  have hbudget : a' + (Z'.card : ℝ) + 1 ≤ εR * Fintype.card (V ⊕ Fin m) := by
    rw [horderR]
    dsimp [a', Z']
    rw [Finset.card_map]
    linarith only [herrorR]
  obtain ⟨c⟩ := hfactor (V ⊕ Fin m) R P K Z' k a'
    (by rw [horder]; omega) (by rw [horder]; omega)
    (fun v => (hRregular v).le)
    (by rw [horderR]; nlinarith only [hdensity]) hRno hPdisjoint hPZ hPcover
    hPsize hKembed hKrobust hKdegree (by dsimp [a']; positivity) hbudget
  exact ⟨restrictCompletionColoring G N L c⟩

end Overfull
