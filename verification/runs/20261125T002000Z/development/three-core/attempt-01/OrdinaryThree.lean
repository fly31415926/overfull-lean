import Overfull.AuxiliarySimple.Completion
import Overfull.AuxiliarySimple.Deficiency
import Overfull.AuxiliaryCompletion
import Overfull.FourCoreReduction.Regular

/-!
# Three ordinary robust cores in a graph of bounded maximum degree

An actual auxiliary completion adds the fourth core.  Its simple realization
has the original copies, the original three robust cores, and the constructed
auxiliary core.  Applying the four-core regular theorem and restricting the
resulting coloring proves the nonregular three-core case.
-/

noncomputable section

namespace Overfull

open Finset Classical SimpleGraph AuxiliarySimple AuxiliaryCompletion

universe u

set_option maxHeartbeats 1200000 in
/-- The three-core ordinary coloring theorem in the nontrivial palette range
`k < n`. The original graph need not be regular and may have a small linear
exceptional set. No completion graph or coloring is supplied as a hypothesis. -/
theorem three_core_nonregular_factorization (α ν τ : ℝ)
    (hα : 0 < α) (hα1 : α < 1) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτ : τ ≤ α / 512000) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, 0 < n₀ ∧
      ∀ (V : Type u) [Fintype V] (G : SimpleGraph V)
        (U : Fin 3 → Finset V) (H : ∀ i, SimpleGraph (U i))
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
    core_regular_normalized_factorization.{u,0} (α / 2) μ τ (by positivity) (by linarith)
      hμ hμτ (by linarith only [hτ])
  let ε := min εC εR
  have hε : 0 < ε := lt_min hεC hεR
  let n₀ := max 1 (max nC nR)
  have hn₀ : 0 < n₀ := lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) (le_max_left _ _)
  refine ⟨ε, hε, n₀, hn₀, ?_⟩
  intro V _ G U H Z k a hn hk hdegree hdensity hno hdisjoint hUZ hcover
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
  letI : DecidableEq (V ⊕ Fin m) := fun v w => propDecidable (v = w)
  obtain ⟨N, L, hregular, heven, _hOriginal, _hAux, _hAdded, hLrobust, hLdegree, hnoPlus⟩ :=
    hcomplete V G.edgeSet (Multigraph.ofSimpleGraph G) k hnC hdegreeM hdensity
      (by omega) hdeficiencyM hnoM
  let R := completion G N L
  let P : Fin 4 → Finset (V ⊕ Fin m) :=
    Fin.cases ((U 0).map Function.Embedding.inl)
      (Fin.cases ((U 1).map Function.Embedding.inl)
        (Fin.cases ((U 2).map Function.Embedding.inl) (fun _ => auxiliaryVertices V (Fin m))))
  let K : ∀ i, SimpleGraph (P i) :=
    Fin.cases (mappedCore Function.Embedding.inl (U 0) (H 0))
      (Fin.cases (mappedCore Function.Embedding.inl (U 1) (H 1))
        (Fin.cases (mappedCore Function.Embedding.inl (U 2) (H 2))
          (fun _ => auxiliaryCore (V := V) L)))
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
      | exact (Finset.disjoint_map _).mpr (hdisjoint (by decide))
      | exact Finset.disjoint_map_inl_map_inr _ _
      | exact (Finset.disjoint_map_inl_map_inr _ _).symm
  have hPZ : ∀ i, Disjoint (P i) Z' := by
    intro i
    fin_cases i <;> dsimp [P, Z', auxiliaryVertices]
    · exact (Finset.disjoint_map _).mpr (hUZ 0)
    · exact (Finset.disjoint_map _).mpr (hUZ 1)
    · exact (Finset.disjoint_map _).mpr (hUZ 2)
    · exact (Finset.disjoint_map_inl_map_inr _ _).symm
  have hPcover : ∀ v, v ∈ Z' ∨ ∃ i, v ∈ P i := by
    intro v
    rcases v with v | v
    · rcases hcover v with hv | ⟨i, hi⟩
      · exact Or.inl (mem_map.mpr ⟨v, hv, rfl⟩)
      · right
        fin_cases i
        · exact ⟨0, mem_map.mpr ⟨v, hi, rfl⟩⟩
        · exact ⟨1, mem_map.mpr ⟨v, hi, rfl⟩⟩
        · exact ⟨2, mem_map.mpr ⟨v, hi, rfl⟩⟩
    · exact Or.inr ⟨3, mem_map.mpr ⟨v, mem_univ v, rfl⟩⟩
  have hPsize : ∀ i, (α / 2) * Fintype.card (V ⊕ Fin m) ≤ ((P i).card : ℝ) := by
    intro i
    rw [horderR]
    fin_cases i
    · change α / 2 * (2 * Fintype.card V) ≤ (((U 0).map Function.Embedding.inl).card : ℝ)
      rw [Finset.card_map]
      nlinarith only [hsize 0]
    · change α / 2 * (2 * Fintype.card V) ≤ (((U 1).map Function.Embedding.inl).card : ℝ)
      rw [Finset.card_map]
      nlinarith only [hsize 1]
    · change α / 2 * (2 * Fintype.card V) ≤ (((U 2).map Function.Embedding.inl).card : ℝ)
      rw [Finset.card_map]
      nlinarith only [hsize 2]
    · have hmR : (m : ℝ) = Fintype.card V := by exact_mod_cast hm
      have hN := mul_le_mul_of_nonneg_right hα1.le (Nat.cast_nonneg (Fintype.card V))
      change α / 2 * (2 * Fintype.card V) ≤ ((auxiliaryVertices V (Fin m)).card : ℝ)
      rw [auxiliaryVertices_card, Fintype.card_fin]
      nlinarith only [hN, hmR]
  have hKembed : ∀ i, K i ≤ R.induce (P i : Set (V ⊕ Fin m)) := by
    intro i
    fin_cases i
    · exact completion_original_core G N L (U 0) (H 0) (hembed 0)
    · exact completion_original_core G N L (U 1) (H 1) (hembed 1)
    · exact completion_original_core G N L (U 2) (H 2) (hembed 2)
    · exact completion_auxiliary_core G N L
  have hKrobust : ∀ i, IsRobustExpander (K i) μ τ := by
    intro i
    fin_cases i
    · exact robust_instance_transfer _
        (mappedCore_robust (Function.Embedding.inl : V ↪ V ⊕ Fin m) (U 0) (H 0) μ τ
          (robust_instance_transfer _
            (IsRobustExpander.mono_parameter (H 0) (hrobust 0) (min_le_left _ _))))
    · exact robust_instance_transfer _
        (mappedCore_robust (Function.Embedding.inl : V ↪ V ⊕ Fin m) (U 1) (H 1) μ τ
          (robust_instance_transfer _
            (IsRobustExpander.mono_parameter (H 1) (hrobust 1) (min_le_left _ _))))
    · exact robust_instance_transfer _
        (mappedCore_robust (Function.Embedding.inl : V ↪ V ⊕ Fin m) (U 2) (H 2) μ τ
          (robust_instance_transfer _
            (IsRobustExpander.mono_parameter (H 2) (hrobust 2) (min_le_left _ _))))
    · exact robust_instance_transfer _ (auxiliaryCore_robust (V := V) L μ τ
        (robust_instance_transfer _
          (IsRobustExpander.mono_parameter L hLrobust (min_le_right _ _))))
  have hb := ceil_average_deficiency_le G U H Z k a hnpos hdegree hk.le hcover hembed hcore ha
  have hKdegree : ∀ i v, (k : ℝ) - a' ≤ ((K i).degree v : ℝ) := by
    intro i v
    fin_cases i
    · change (k : ℝ) - a' ≤ ((mappedCore Function.Embedding.inl (U 0) (H 0)).degree v : ℝ)
      rw [mappedCore_degree]
      have hh := hcore 0 ((partEquiv Function.Embedding.inl (U 0)).symm v)
      dsimp [a']
      linarith only [hh, (Nat.cast_nonneg Z.card : (0 : ℝ) ≤ Z.card)]
    · change (k : ℝ) - a' ≤ ((mappedCore Function.Embedding.inl (U 1) (H 1)).degree v : ℝ)
      rw [mappedCore_degree]
      have hh := hcore 1 ((partEquiv Function.Embedding.inl (U 1)).symm v)
      dsimp [a']
      linarith only [hh, (Nat.cast_nonneg Z.card : (0 : ℝ) ≤ Z.card)]
    · change (k : ℝ) - a' ≤ ((mappedCore Function.Embedding.inl (U 2) (H 2)).degree v : ℝ)
      rw [mappedCore_degree]
      have hh := hcore 2 ((partEquiv Function.Embedding.inl (U 2)).symm v)
      dsimp [a']
      linarith only [hh, (Nat.cast_nonneg Z.card : (0 : ℝ) ≤ Z.card)]
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
    linarith only [herrorR, ha]
  obtain ⟨c⟩ := hfactor (V ⊕ Fin m) (Fin 4) R P K Z' k a'
    (by rw [horder]; omega) (by norm_num) (Nat.even_iff.mpr heven) hRregular
    (by rw [horderR]; nlinarith only [hdensity]) hRno hPdisjoint hPZ hPcover
    hPsize hKembed hKrobust hKdegree (by dsimp [a']; positivity) hbudget
  exact ⟨restrictCompletionColoring G N L c⟩

/-- A simple graph with three large disjoint ordinary robust cores and a small
combined core-error and exceptional budget has a maximum-degree edge coloring.
The graph need not have even order or be regular. The exceptional set may
overlap the cores, and nonnegative core error is derived from the embedding.
Every tolerance and order threshold is chosen before the graph. -/
theorem three_core_coloring (α ν τ : ℝ)
    (hα : 0 < α) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτ : τ ≤ min α 1 / 1024000) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, 0 < n₀ ∧
      ∀ (V : Type u) [Fintype V] (G : SimpleGraph V)
        (U : Fin 3 → Finset V) (H : ∀ i, SimpleGraph (U i))
        (Z : Finset V) (a : ℝ),
        n₀ ≤ Fintype.card V → α * Fintype.card V ≤ G.maxDegree →
        (∀ X : Finset V, ¬ IsOverfull G G.maxDegree X) →
        Pairwise (fun i j => Disjoint (U i) (U j)) →
        (∀ v, v ∈ Z ∨ ∃ i, v ∈ U i) →
        (∀ i, α * Fintype.card V ≤ ((U i).card : ℝ)) →
        (∀ i, H i ≤ G.induce (U i : Set V)) →
        (∀ i, IsRobustExpander (H i) ν τ) →
        (∀ i v, (G.maxDegree : ℝ) - a ≤ ((H i).degree v : ℝ)) →
        a + (Z.card : ℝ) + 1 ≤ ε * Fintype.card V →
        Nonempty (Overfull.EdgeColoring G G.maxDegree) := by
  let β := min α (1 / 2)
  have hβ : 0 < β := lt_min hα (by norm_num)
  have hβ1 : β < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hβα : β ≤ α := min_le_left _ _
  have hhalf : min α 1 / 2 ≤ β := by
    apply le_min
    · linarith only [min_le_left α 1, hα]
    · linarith only [min_le_right α 1]
  have hτβ : τ ≤ β / 512000 := by linarith only [hτ, hhalf]
  obtain ⟨ε, hε, n₀, hn₀, hfactor⟩ :=
    three_core_nonregular_factorization.{u} β ν τ hβ hβ1 hν hντ hτβ
  refine ⟨ε, hε, n₀, hn₀, ?_⟩
  intro V _ G U H Z a hn hdensity hno hdisjoint hcover hsize hembed hrobust hcore hbudget
  have hnpos : 0 < Fintype.card V := hn₀.trans_le hn
  letI : Nonempty V := Fintype.card_pos_iff.mp hnpos
  have hUpos : 0 < (U 0).card := by
    have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hnpos
    have hUR : (0 : ℝ) < (U 0).card := (mul_pos hα hnR).trans_le (hsize 0)
    exact_mod_cast hUR
  obtain ⟨v, hv⟩ := card_pos.mp hUpos
  let C := ForceMatching.embeddedCore G (U 0) (H 0) (hembed 0)
  have hupper : (H 0).degree ⟨v, hv⟩ ≤ G.maxDegree := by
    have hh := OneCore.core_degree_le C (⟨v, hv⟩ : U 0)
    have hHG : (H 0).degree ⟨v, hv⟩ ≤ G.degree v := by
      simpa only [C, ForceMatching.embeddedCore, Multigraph.ofSimpleGraph_degree] using hh
    exact hHG.trans (G.degree_le_maxDegree v)
  have hupperR : ((H 0).degree ⟨v, hv⟩ : ℝ) ≤ G.maxDegree := by exact_mod_cast hupper
  have ha : 0 ≤ a := by linarith only [hcore 0 ⟨v, hv⟩, hupperR]
  let Z₀ := Z \ univ.biUnion U
  have hUZ (i : Fin 3) : Disjoint (U i) Z₀ := by
    apply disjoint_left.mpr
    intro w hw hZ
    exact (mem_sdiff.mp hZ).2 (mem_biUnion.mpr ⟨i, mem_univ i, hw⟩)
  have hcover₀ (w : V) : w ∈ Z₀ ∨ ∃ i, w ∈ U i := by
    by_cases hw : ∃ i, w ∈ U i
    · exact Or.inr hw
    · left
      refine mem_sdiff.mpr ⟨(hcover w).resolve_right hw, ?_⟩
      intro hmem
      obtain ⟨i, _, hi⟩ := mem_biUnion.mp hmem
      exact hw ⟨i, hi⟩
  have hZcard : (Z₀.card : ℝ) ≤ Z.card := by
    exact_mod_cast card_le_card (sdiff_subset : Z \ univ.biUnion U ⊆ Z)
  have hbudget₀ : a + (Z₀.card : ℝ) + 1 ≤ ε * Fintype.card V := by
    linarith only [hZcard, hbudget]
  have hdensityβ : β * Fintype.card V ≤ G.maxDegree :=
    (mul_le_mul_of_nonneg_right hβα (Nat.cast_nonneg _)).trans hdensity
  have hsizeβ (i : Fin 3) : β * Fintype.card V ≤ ((U i).card : ℝ) :=
    (mul_le_mul_of_nonneg_right hβα (Nat.cast_nonneg _)).trans (hsize i)
  obtain ⟨c⟩ := hfactor V G U H Z₀ G.maxDegree a hn
    G.maxDegree_lt_card_verts G.degree_le_maxDegree hdensityβ hno
    hdisjoint hUZ hcover₀ hsizeβ hembed hrobust hcore ha hbudget₀
  refine ⟨{ color := c.color, proper := ?_ }⟩
  intro e f w he hf h
  exact c.proper h he hf

end Overfull
