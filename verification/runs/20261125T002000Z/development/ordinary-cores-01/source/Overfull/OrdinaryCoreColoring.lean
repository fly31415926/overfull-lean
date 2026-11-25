import Overfull.AuxiliarySimple.OrdinaryOne
import Overfull.AuxiliarySimple.OrdinaryThree
import Overfull.Vizing.Theorem

/-!
# Coloring with one, two, or three ordinary robust cores

The same positive error tolerance and order threshold work for all three
possible core counts.  The auxiliary construction supplies the nontrivial
palette range.  Larger palettes are obtained from the proved Vizing bound.
The public theorem derives nonnegative error from an actual embedded core and
removes overlap with the exceptional set without increasing its size.
-/

noncomputable section

namespace Overfull

open Finset Classical SimpleGraph

universe u v

/-- Uniform nonregular coloring for one, two, or three labelled cores.  This
construction interface keeps the palette below the original graph order. -/
theorem ordinary_cores_normalized_factorization (α ν τ : ℝ)
    (hα : 0 < α) (hα1 : α < 1) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτ : τ ≤ α / 1024000) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, 0 < n₀ ∧
      ∀ (V : Type u) [Fintype V] (q : ℕ) (G : SimpleGraph V)
        (U : Fin q → Finset V) (H : ∀ i, SimpleGraph (U i))
        (Z : Finset V) (k : ℕ) (a : ℝ),
        n₀ ≤ Fintype.card V → (q = 1 ∨ q = 2 ∨ q = 3) →
        k < Fintype.card V →
        (∀ v, G.degree v ≤ k) → α * Fintype.card V ≤ (k : ℝ) →
        (∀ X : Finset V, ¬ IsOverfull G k X) →
        Pairwise (fun i j => Disjoint (U i) (U j)) →
        (∀ i, Disjoint (U i) Z) → (∀ w, w ∈ Z ∨ ∃ i, w ∈ U i) →
        (∀ i, α * Fintype.card V ≤ ((U i).card : ℝ)) →
        (∀ i, H i ≤ G.induce (U i : Set V)) →
        (∀ i, IsRobustExpander (H i) ν τ) →
        (∀ i w, (k : ℝ) - a ≤ ((H i).degree w : ℝ)) →
        0 ≤ a → a + (Z.card : ℝ) + 1 ≤ ε * Fintype.card V →
        Nonempty ((Multigraph.ofSimpleGraph G).EdgeColoring k) := by
  obtain ⟨ε₁, hε₁, n₁, hn₁, h₁⟩ :=
    one_core_nonregular_factorization.{u} α ν τ hα hα1 hν hντ hτ
  obtain ⟨ε₂, hε₂, n₂, _hn₂, h₂⟩ :=
    two_core_nonregular_factorization.{u} α ν τ hα hα1 hν hντ
      (by linarith only [hτ, hα])
  obtain ⟨ε₃, hε₃, n₃, _hn₃, h₃⟩ :=
    three_core_nonregular_factorization.{u} α ν τ hα hα1 hν hντ
      (by linarith only [hτ, hα])
  let ε := min ε₁ (min ε₂ ε₃)
  let n₀ := max n₁ (max n₂ n₃)
  have hε : 0 < ε := lt_min hε₁ (lt_min hε₂ hε₃)
  have hn₀ : 0 < n₀ := hn₁.trans_le (le_max_left _ _)
  refine ⟨ε, hε, n₀, hn₀, ?_⟩
  intro V _ q G U H Z k a hn hq hk hdegree hdensity hno hdisj hUZ hcover
    hsize hembed hrobust hcore ha hbudget
  have hn₁' : n₁ ≤ Fintype.card V := (le_max_left _ _).trans hn
  have hn₂' : n₂ ≤ Fintype.card V :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hn₃' : n₃ ≤ Fintype.card V :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hb₁ : a + (Z.card : ℝ) + 1 ≤ ε₁ * Fintype.card V :=
    hbudget.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _))
  have hb₂ : a + (Z.card : ℝ) + 1 ≤ ε₂ * Fintype.card V :=
    hbudget.trans (mul_le_mul_of_nonneg_right
      ((min_le_right _ _).trans (min_le_left _ _)) (Nat.cast_nonneg _))
  have hb₃ : a + (Z.card : ℝ) + 1 ≤ ε₃ * Fintype.card V :=
    hbudget.trans (mul_le_mul_of_nonneg_right
      ((min_le_right _ _).trans (min_le_right _ _)) (Nat.cast_nonneg _))
  rcases hq with rfl | rfl | rfl
  · exact h₁ V G U H Z k a hn₁' hk hdegree hdensity hno hdisj hUZ hcover
      hsize hembed hrobust hcore ha hb₁
  · exact h₂ V G U H Z k a hn₂' hk hdegree hdensity hno hdisj hUZ hcover
      hsize hembed hrobust hcore ha hb₂
  · exact h₃ V G U H Z k a hn₃' hk hdegree hdensity hno hdisj hUZ hcover
      hsize hembed hrobust hcore ha hb₃

/-- Coloring from at most three ordinary robust cores, with an arbitrary
positive density, arbitrary finite core labels, and arbitrary palette bound.
The constants precede the graph, core count, palette, and error. -/
theorem ordinary_cores_coloring (α ν τ : ℝ)
    (hα : 0 < α) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτ : τ ≤ min α 1 / 2048000) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, 0 < n₀ ∧
      ∀ (V : Type u) [Fintype V] (I : Type v) [Fintype I]
        (G : SimpleGraph V) (U : I → Finset V) (H : ∀ i, SimpleGraph (U i))
        (Z : Finset V) (k : ℕ) (a : ℝ),
        n₀ ≤ Fintype.card V → 1 ≤ Fintype.card I → Fintype.card I ≤ 3 →
        (∀ w, G.degree w ≤ k) → α * Fintype.card V ≤ (k : ℝ) →
        (∀ X : Finset V, ¬ IsOverfull G k X) →
        Pairwise (fun i j => Disjoint (U i) (U j)) →
        (∀ w, w ∈ Z ∨ ∃ i, w ∈ U i) →
        (∀ i, α * Fintype.card V ≤ ((U i).card : ℝ)) →
        (∀ i, H i ≤ G.induce (U i : Set V)) →
        (∀ i, IsRobustExpander (H i) ν τ) →
        (∀ i w, (k : ℝ) - a ≤ ((H i).degree w : ℝ)) →
        a + (Z.card : ℝ) + 1 ≤ ε * Fintype.card V →
        Nonempty (Overfull.EdgeColoring G k) := by
  let β := min α (1 / 2)
  have hβ : 0 < β := lt_min hα (by norm_num)
  have hβ1 : β < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hβα : β ≤ α := min_le_left _ _
  have hτβ : τ ≤ β / 1024000 := by
    have hminα := min_le_left α (1 : ℝ)
    have hmin1 := min_le_right α (1 : ℝ)
    have hτa : τ ≤ α / 1024000 := by linarith only [hτ, hminα, hα]
    have hτhalf : τ ≤ (1 / 2 : ℝ) / 1024000 := by linarith only [hτ, hmin1]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 1024000)).mpr
    exact le_min (by linarith only [hτa]) (by linarith only [hτhalf])
  obtain ⟨ε, hε, n₀, hn₀, hfactor⟩ :=
    ordinary_cores_normalized_factorization.{u} β ν τ hβ hβ1 hν hντ hτβ
  refine ⟨ε, hε, n₀, hn₀, ?_⟩
  intro V _ I _ G U H Z k a hn hIpos hIle hdegree hdensity hno hdisj hcover
    hsize hembed hrobust hcore hbudget
  have hnpos : 0 < Fintype.card V := hn₀.trans_le hn
  letI : Nonempty V := Fintype.card_pos_iff.mp hnpos
  by_cases hk : k < Fintype.card V
  · have hI : Fintype.card I = 1 ∨ Fintype.card I = 2 ∨ Fintype.card I = 3 := by omega
    obtain ⟨i₀⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card I)
    have hUpos : 0 < (U i₀).card := by
      have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hnpos
      have hUR := (mul_pos hα hnR).trans_le (hsize i₀)
      exact_mod_cast hUR
    obtain ⟨w, hw⟩ := Finset.card_pos.mp hUpos
    have hupper := (Replacement.lift (U i₀) (H i₀)).degree_le_of_le (v := w)
      (Replacement.lift_le (U i₀) (H i₀) G (hembed i₀))
    rw [Replacement.lift_degree (U i₀) (H i₀) ⟨w, hw⟩] at hupper
    have hupperR : ((H i₀).degree ⟨w, hw⟩ : ℝ) ≤ k := by
      exact_mod_cast hupper.trans (hdegree w)
    have ha : 0 ≤ a := by linarith only [hcore i₀ ⟨w, hw⟩, hupperR]
    let Z₀ := Z \ univ.biUnion U
    have hUZ : ∀ i, Disjoint (U i) Z₀ := by
      intro i
      apply disjoint_left.mpr
      intro x hx hZ
      exact (mem_sdiff.mp hZ).2 (mem_biUnion.mpr ⟨i, mem_univ _, hx⟩)
    have hcover₀ (x : V) : x ∈ Z₀ ∨ ∃ i, x ∈ U i := by
      by_cases hx : ∃ i, x ∈ U i
      · exact Or.inr hx
      · left
        refine mem_sdiff.mpr ⟨(hcover x).resolve_right hx, ?_⟩
        intro hh
        obtain ⟨i, _, hi⟩ := mem_biUnion.mp hh
        exact hx ⟨i, hi⟩
    have hZcard : (Z₀.card : ℝ) ≤ Z.card := by
      exact_mod_cast card_le_card (sdiff_subset : Z \ univ.biUnion U ⊆ Z)
    have hbudget₀ : a + (Z₀.card : ℝ) + 1 ≤ ε * Fintype.card V := by
      linarith only [hbudget, hZcard]
    let e := (Fintype.equivFin I).symm
    let U' : Fin (Fintype.card I) → Finset V := fun i => U (e i)
    let H' : ∀ i, SimpleGraph (U' i) := fun i => H (e i)
    have hdisj' : Pairwise (fun i j => Disjoint (U' i) (U' j)) := by
      intro i j hij
      exact hdisj (fun hh => hij (e.injective hh))
    have hcover' (x : V) : x ∈ Z₀ ∨ ∃ i, x ∈ U' i := by
      rcases hcover₀ x with hx | ⟨i, hi⟩
      · exact Or.inl hx
      · exact Or.inr ⟨e.symm i, by simpa only [U', Equiv.apply_symm_apply] using hi⟩
    obtain ⟨c⟩ := hfactor V (Fintype.card I) G U' H' Z₀ k a hn hI hk hdegree
      ((mul_le_mul_of_nonneg_right hβα (Nat.cast_nonneg _)).trans hdensity)
      hno hdisj' (fun i => hUZ (e i)) hcover'
      (fun i => (mul_le_mul_of_nonneg_right hβα (Nat.cast_nonneg _)).trans (hsize (e i)))
      (fun i => hembed (e i)) (fun i => hrobust (e i)) (fun i => hcore (e i)) ha hbudget₀
    refine ⟨{ color := c.color, proper := ?_ }⟩
    intro e f x he hf hh
    exact c.proper hh he hf
  · obtain ⟨c⟩ := vizing_finite G
    exact ⟨VizingAdapter.enlargeColors c (by have hh := G.maxDegree_lt_card_verts; omega)⟩

end Overfull
