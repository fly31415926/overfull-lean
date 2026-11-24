import Overfull.FourCoreReduction.Bounded
import Overfull.ForeignEdges.ReductionError
import Overfull.Absorption.Bounded

/-!
# Regular factorization with three or four cores and a small exceptional set

The absorption tolerance is a positive function of the eventual exceptional
cardinality.  We choose that entire function before absorption chooses its
finite bound, and take a finite maximum of the resulting order thresholds.
The foreign, absorption, and frequent-pattern prefixes are restored on the
original edge copies.  No residual factorization is a public hypothesis.
-/

noncomputable section

namespace Overfull

open Finset Classical SimpleGraph Terminal ForeignPhase ForeignEpochParameters
open Absorption

universe u v

/-- The three-or-four-core case of the regular factorization theorem, allowing an
exceptional set whose size is controlled by the original linear error budget.
The input tolerance and order threshold precede the graph and its error. -/
theorem core_regular_normalized_factorization (α ν τ : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτ : τ ≤ α / 256000) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, 0 < n₀ ∧
      ∀ (V : Type u) [Fintype V] (I : Type v) [Fintype I] (G : SimpleGraph V)
        (U : I → Finset V) (H : ∀ i, SimpleGraph (U i))
        (Z : Finset V) (k : ℕ) (a : ℝ),
        n₀ ≤ Fintype.card V → (Fintype.card I = 3 ∨ Fintype.card I = 4) →
        Even (Fintype.card V) →
        (∀ v, G.degree v = k) → α * Fintype.card V ≤ (k : ℝ) →
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
  obtain ⟨νF, hνF, hνFτ, hforeign⟩ :=
    foreign_edge_reduction_with_small_error.{u,v} α τ ν hα hα1 hν hντ
      (by linarith only [hτ])
  let c : ℝ := (256 * (classLoss + 6 + markedLimit) : ℕ)
  obtain ⟨νA, hνA, habsorb⟩ := bounded_exceptional_absorption.{u,v}
    (α / 256) νF (τ / 2) c (by positivity) (by linarith) hνF hνFτ
      (by linarith only [hτ, hτpos]) (by dsimp [c]; positivity)
  let β := α / 1024
  have hβ : 0 < β := by dsimp [β]; positivity
  have hβ1 : β ≤ 1 := by dsimp [β]; linarith
  have hτβ : τ ≤ β / 8 := by dsimp [β]; linarith only [hτ, hα]
  have hper (t : ℕ) :=
    core_bounded_exception_factorization.{u,v} t β νA τ hβ hβ1 hνA hτpos hτβ
  choose εB hεB nB hnB hbounded using hper
  let f : ℕ → ℝ := fun t => min (1 / 4) (εB t / 2)
  have hf (t : ℕ) : 0 < f t :=
    lt_min (by norm_num) (div_pos (hεB t) (by norm_num))
  obtain ⟨T, εA, hεA, nA, hconstructA⟩ := habsorb f hf
  obtain ⟨ε, hε, nF, hconstructF⟩ := hforeign (εA / 2) (by positivity)
  let n₀ := max 1 (max nF (max nA ((range (T + 1)).sup nB)))
  have hn₀ : 0 < n₀ := lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) (le_max_left _ _)
  refine ⟨ε, hε, n₀, hn₀, ?_⟩
  intro V _ I _ G U H Z k a hn hI heven hregular hdensity hno hdisjoint hUZ hcover
    hsize hembed hrobust hdegree ha herror
  have hIle : Fintype.card I ≤ 4 := by rcases hI with hI | hI <;> omega
  have hIpos : 0 < Fintype.card I := by rcases hI with hI | hI <;> omega
  letI : Nonempty I := Fintype.card_pos_iff.mp hIpos
  have hnF : nF ≤ Fintype.card V :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnA : nA ≤ Fintype.card V :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  have hnSup : (range (T + 1)).sup nB ≤ Fintype.card V :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  have hnpos : 0 < Fintype.card V := hn₀.trans_le hn
  obtain ⟨v₀⟩ := Fintype.card_pos_iff.mp hnpos
  obtain ⟨F, hFbudget, hFsize⟩ := hconstructF V I G U H Z k a hnF
    hIle hregular hdensity hno hdisjoint hUZ hcover hsize
    hembed hdegree hrobust ha herror
  have hFdensity : (α / 256) * Fintype.card V ≤ (F.h : ℝ) := by
    have hr : (k : ℝ) ≤ 256 * F.h := by exact_mod_cast F.retained_degree
    linarith only [hdensity, hr]
  have hFsizeA (i : I) : (α / 256) * Fintype.card V ≤ ((F.U i).card : ℝ) := by
    have hm := hFsize i
    have hp : 0 ≤ α * Fintype.card V := mul_nonneg hα.le (Nat.cast_nonneg _)
    linarith only [hm, hp]
  have hFn : (F.h : ℝ) ≤ Fintype.card V := by
    have hh := F.G.degree_lt_card_verts v₀
    rw [F.regular v₀] at hh
    exact_mod_cast hh.le
  have hFbudgetA : (a + 3) + (F.Z.card : ℝ) + 1 ≤ εA * Fintype.card V := by
    have hh := mul_le_mul_of_nonneg_left hFn (by positivity : 0 ≤ εA / 2)
    have hp : 0 ≤ εA * Fintype.card V := mul_nonneg hεA.le (Nat.cast_nonneg _)
    linarith only [hFbudget, hh, hp]
  have hFforeign :
      (∑ z ∈ F.Z, ((originalForeignNeighbors F.G F.U F.assign z).card : ℝ)) ≤ c * F.h := by
    have hh := (Nat.cast_le (α := ℝ)).mpr F.foreign_bound
    convert hh using 1 <;>
      simp only [originalForeignNeighbors, c, Nat.cast_sum, Nat.cast_mul,
        Nat.cast_add, Nat.cast_ofNat]
    congr 3
    funext x
    congr 2
    ext w
    simp
  obtain ⟨A⟩ := hconstructA V I F.G F.U F.H F.Z F.assign F.h (a + 3)
    hnA hIle F.regular hFdensity F.no_overfull F.core_disjoint
    F.core_exceptional_disjoint F.cover hFsizeA F.core_embed F.core_degree
    F.core_robust (by linarith only [ha]) hFbudgetA hFforeign
  have hAn : (A.h : ℝ) ≤ Fintype.card V := by
    have hh := A.G.degree_lt_card_verts v₀
    rw [A.regular v₀] at hh
    exact_mod_cast hh.le
  have hAdensity : β * Fintype.card V ≤ (A.h : ℝ) := by
    have hh := A.retained_degree
    dsimp [β]
    linarith only [hFdensity, hh, mul_nonneg hα.le (Nat.cast_nonneg (Fintype.card V))]
  have hAsize (i : I) : β * Fintype.card V ≤ ((A.U i).card : ℝ) := by
    have hc : ((F.U i).card : ℝ) ≤ (A.U i).card := by
      exact_mod_cast card_le_card (A.core_enlargement i)
    have hm := hFsize i
    have hp : 0 ≤ α * Fintype.card V := mul_nonneg hα.le (Nat.cast_nonneg _)
    dsimp [β]
    linarith only [hc, hm, hp]
  have hArobust (i : I) : IsRobustExpander (A.H i) νA τ := by
    convert A.core_robust i using 1
    ring
  have hAnB : nB A.Z.card ≤ Fintype.card V := by
    apply le_trans _ hnSup
    exact Finset.le_sup (f := nB) (mem_range.mpr (Nat.lt_succ_of_le A.exceptional_card))
  have hAerror : A.error ≤ εB A.Z.card * Fintype.card V := by
    have hfbound : f A.Z.card ≤ εB A.Z.card := by
      have hh := min_le_right (1 / 4 : ℝ) (εB A.Z.card / 2)
      have hp := hεB A.Z.card
      dsimp [f]
      linarith only [hh, hp]
    exact A.error_bound.trans ((mul_le_mul_of_nonneg_left hAn (hf _).le).trans
      (mul_le_mul_of_nonneg_right hfbound (Nat.cast_nonneg _)))
  obtain ⟨cA⟩ := hbounded A.Z.card V I A.G A.U A.H A.Z A.h A.error hAnB hI heven
    A.regular hAdensity A.no_overfull A.core_disjoint A.core_exceptional_disjoint
    A.cover le_rfl hAsize A.core_embed hArobust A.core_degree A.error_nonneg hAerror
  have cA' : (Multigraph.ofSimpleGraph (afterDeletions F.G A.N A.rounds)).EdgeColoring A.h := by
    rw [← A.graph_eq]
    exact cA
  have hAsum : A.rounds + A.h = F.h := by
    have hh := ForeignIncidence.perfect_deletion_degree_identity F.G A.N A.rounds
      A.perfect A.present v₀
    have hr := F.regular v₀
    have hs := A.regular v₀
    rw [A.graph_eq] at hs
    simp only [afterDeletions, ← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] at hh hr hs
    omega
  have cF : (Multigraph.ofSimpleGraph F.G).EdgeColoring F.h := by
    have cc := restoredColoring F.G A.N A.rounds (fun j hj => (A.perfect j hj).1) cA'
    simpa only [hAsum] using cc
  have cF' : (Multigraph.ofSimpleGraph (afterDeletions G F.N F.rounds)).EdgeColoring F.h := by
    rw [← F.graph_eq]
    exact cF
  have hFsum : F.rounds + F.h = k := by
    have hh := ForeignIncidence.perfect_deletion_degree_identity G F.N F.rounds
      F.perfect F.present v₀
    have hr := hregular v₀
    have hs := F.regular v₀
    rw [F.graph_eq] at hs
    simp only [afterDeletions, ← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] at hh hr hs
    omega
  have cc := restoredColoring G F.N F.rounds (fun j hj => (F.perfect j hj).1) cF'
  exact ⟨by simpa only [hFsum] using cc⟩

/-- Exact partition of all original copies into the degree number of perfect
matchings in the three-or-four-core regular case with a small exceptional set. -/
theorem core_regular_normalized_one_factorization (α ν τ : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτ : τ ≤ α / 256000) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, 0 < n₀ ∧
      ∀ (V : Type u) [Fintype V] (I : Type v) [Fintype I] (G : SimpleGraph V)
        (U : I → Finset V) (H : ∀ i, SimpleGraph (U i))
        (Z : Finset V) (k : ℕ) (a : ℝ),
        n₀ ≤ Fintype.card V → (Fintype.card I = 3 ∨ Fintype.card I = 4) →
        Even (Fintype.card V) →
        (∀ v, G.degree v = k) → α * Fintype.card V ≤ (k : ℝ) →
        (∀ X : Finset V, ¬ IsOverfull G k X) →
        Pairwise (fun i j => Disjoint (U i) (U j)) →
        (∀ i, Disjoint (U i) Z) → (∀ v, v ∈ Z ∨ ∃ i, v ∈ U i) →
        (∀ i, α * Fintype.card V ≤ ((U i).card : ℝ)) →
        (∀ i, H i ≤ G.induce (U i : Set V)) →
        (∀ i, IsRobustExpander (H i) ν τ) →
        (∀ i v, (k : ℝ) - a ≤ ((H i).degree v : ℝ)) →
        0 ≤ a → a + (Z.card : ℝ) + 1 ≤ ε * Fintype.card V →
        ∃ M : Fin k → Finset G.edgeSet,
          (∀ i, (Multigraph.ofSimpleGraph G).IsPerfectMatching (M i)) ∧
          Pairwise (fun i j => Disjoint (M i) (M j)) ∧
          univ.biUnion M = univ := by
  obtain ⟨ε, hε, n₀, hn₀, hfactor⟩ :=
    core_regular_normalized_factorization α ν τ hα hα1 hν hντ hτ
  refine ⟨ε, hε, n₀, hn₀, ?_⟩
  intro V _ I _ G U H Z k a hn hI heven hregular hdensity hno hdisjoint hUZ hcover
    hsize hembed hrobust hdegree ha herror
  obtain ⟨c⟩ := hfactor V I G U H Z k a hn hI heven hregular hdensity hno hdisjoint
    hUZ hcover hsize hembed hrobust hdegree ha herror
  have hregularM : ∀ v, (Multigraph.ofSimpleGraph G).degree v = k := by
    simpa only [Multigraph.ofSimpleGraph_degree] using hregular
  have hinst : (fun e f : G.edgeSet => propDecidable (e = f)) =
      (inferInstance : DecidableEq G.edgeSet) := Subsingleton.elim _ _
  simpa only [hinst] using
    BoundedExterior.exists_oneFactorization_of_coloring (Multigraph.ofSimpleGraph G) k hregularM c

/-- Theorem 4.17 for any positive density and any finite core index type
of cardinality three or four. The original linear exceptional/error budget
is unchanged. Nonnegative core error follows from the actual embedding. -/
theorem regular_core_one_factorization (α ν τ : ℝ)
    (hα : 0 < α) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτ : τ ≤ min α 1 / 256000) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, 0 < n₀ ∧
      ∀ (V : Type u) [Fintype V] (I : Type v) [Fintype I] (G : SimpleGraph V)
        (U : I → Finset V) (H : ∀ i, SimpleGraph (U i))
        (Z : Finset V) (k : ℕ) (a : ℝ),
        n₀ ≤ Fintype.card V → (Fintype.card I = 3 ∨ Fintype.card I = 4) →
        Even (Fintype.card V) →
        (∀ v, G.degree v = k) → α * Fintype.card V ≤ (k : ℝ) →
        (∀ X : Finset V, ¬ IsOverfull G k X) →
        Pairwise (fun i j => Disjoint (U i) (U j)) →
        (∀ i, Disjoint (U i) Z) → (∀ v, v ∈ Z ∨ ∃ i, v ∈ U i) →
        (∀ i, α * Fintype.card V ≤ ((U i).card : ℝ)) →
        (∀ i, H i ≤ G.induce (U i : Set V)) →
        (∀ i, IsRobustExpander (H i) ν τ) →
        (∀ i v, (k : ℝ) - a ≤ ((H i).degree v : ℝ)) →
        a + (Z.card : ℝ) + 1 ≤ ε * Fintype.card V →
        ∃ M : Fin k → Finset G.edgeSet,
          (∀ i, (Multigraph.ofSimpleGraph G).IsPerfectMatching (M i)) ∧
          Pairwise (fun i j => Disjoint (M i) (M j)) ∧ univ.biUnion M = univ := by
  let β := min α 1
  have hβ : 0 < β := lt_min hα zero_lt_one
  have hβ1 : β ≤ 1 := min_le_right _ _
  have hβα : β ≤ α := min_le_left _ _
  obtain ⟨ε,hε,n₀,hn₀,hfactor⟩ := core_regular_normalized_one_factorization.{u,v}
    β ν τ hβ hβ1 hν hντ hτ
  refine ⟨ε,hε,n₀,hn₀,?_⟩
  intro V _ I _ G U H Z k a hn hI heven hregular hdensity hno hdisj hUZ hcover
    hsize hembed hrobust hdegree herror
  have hIpos : 0 < Fintype.card I := by rcases hI with hI | hI <;> omega
  obtain ⟨i⟩ := Fintype.card_pos_iff.mp hIpos
  have hnpos : 0 < (Fintype.card V : ℝ) := by exact_mod_cast hn₀.trans_le hn
  have hUpos : 0 < (U i).card := by
    have hh := (mul_pos hα hnpos).trans_le (hsize i)
    exact_mod_cast hh
  obtain ⟨v,hv⟩ := Finset.card_pos.mp hUpos
  have hupper := (Replacement.lift (U i) (H i)).degree_le_of_le (v := v)
    (Replacement.lift_le (U i) (H i) G (hembed i))
  have hupper' : ((H i).degree ⟨v,hv⟩ : ℝ) ≤ k := by
    rw [Replacement.lift_degree (U i) (H i) ⟨v,hv⟩, hregular] at hupper
    exact_mod_cast hupper
  have ha : 0 ≤ a := by linarith only [hdegree i ⟨v,hv⟩, hupper']
  have hdensity' : β * Fintype.card V ≤ (k : ℝ) :=
    (mul_le_mul_of_nonneg_right hβα (Nat.cast_nonneg _)).trans hdensity
  have hsize' (i : I) : β * Fintype.card V ≤ ((U i).card : ℝ) :=
    (mul_le_mul_of_nonneg_right hβα (Nat.cast_nonneg _)).trans (hsize i)
  exact hfactor V I G U H Z k a hn hI heven hregular hdensity' hno hdisj hUZ hcover
    hsize' hembed hrobust hdegree ha herror

end Overfull
