import Overfull.AuxiliarySimple.OrdinaryOne

/-!
# The one-core coloring lemma

The public theorem follows the manuscript hypotheses: maximum degree at least
one quarter of the order, no overfull set, a spanning ordinary robust core on
at least one quarter of the vertices, and a small combined degree/exceptional
budget.  Core-error nonnegativity is derived, and any overlap in the displayed
cover is removed from the exceptional set without increasing that budget.
-/

noncomputable section

namespace Overfull

open Finset Classical SimpleGraph AuxiliarySimple

universe u

/-- Lemma 3.1: a simple graph with one large ordinary robust core and a small
exceptional budget has a coloring with its maximum-degree palette.  There is
no regularity, even-order, disjoint-cover, or nonnegative-error hypothesis. -/
theorem single_core_coloring (ν τ : ℝ)
    (hν : 0 < ν) (hντ : ν ≤ τ) (hτ : τ ≤ (1 : ℝ) / 4096000) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, 0 < n₀ ∧
      ∀ (V : Type u) [Fintype V] (G : SimpleGraph V)
        (U Z : Finset V) (H : SimpleGraph U) (a : ℝ),
        n₀ ≤ Fintype.card V → (Fintype.card V : ℝ) / 4 ≤ G.maxDegree →
        (∀ X : Finset V, ¬ IsOverfull G G.maxDegree X) →
        (∀ v, v ∈ U ∨ v ∈ Z) → (Fintype.card V : ℝ) / 4 ≤ U.card →
        H ≤ G.induce (U : Set V) → IsRobustExpander H ν τ →
        (∀ v, (G.maxDegree : ℝ) - a ≤ (H.degree v : ℝ)) →
        a + (Z.card : ℝ) + 1 ≤ ε * Fintype.card V →
        Nonempty (Overfull.EdgeColoring G G.maxDegree) := by
  obtain ⟨ε, hε, n₀, hn₀, hfactor⟩ :=
    one_core_nonregular_factorization.{u} (1 / 4) ν τ (by norm_num) (by norm_num)
      hν hντ (by norm_num; exact hτ)
  refine ⟨ε, hε, n₀, hn₀, ?_⟩
  intro V _ G U Z H a hn hdensity hno hcover hsize hembed hrobust hcore hbudget
  have hnpos : 0 < Fintype.card V := hn₀.trans_le hn
  letI : Nonempty V := Fintype.card_pos_iff.mp hnpos
  have hUpos : 0 < U.card := by
    have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hnpos
    have hUR : (0 : ℝ) < U.card := (by positivity : (0 : ℝ) < Fintype.card V / 4).trans_le hsize
    exact_mod_cast hUR
  obtain ⟨v, hv⟩ := card_pos.mp hUpos
  let C := ForceMatching.embeddedCore G U H hembed
  have hupper : H.degree ⟨v, hv⟩ ≤ G.maxDegree := by
    have hh := OneCore.core_degree_le C (⟨v, hv⟩ : U)
    have hHG : H.degree ⟨v, hv⟩ ≤ G.degree v := by
      simpa only [C, ForceMatching.embeddedCore, Multigraph.ofSimpleGraph_degree] using hh
    exact hHG.trans (G.degree_le_maxDegree v)
  have hupperR : (H.degree ⟨v, hv⟩ : ℝ) ≤ G.maxDegree := by exact_mod_cast hupper
  have ha : 0 ≤ a := by linarith only [hcore ⟨v, hv⟩, hupperR]
  let Z₀ := Z \ U
  have hUZ : Disjoint U Z₀ := by
    apply disjoint_left.mpr
    intro w hw hZ
    exact (mem_sdiff.mp hZ).2 hw
  have hcover₀ (w : V) : w ∈ Z₀ ∨ ∃ _i : Fin 1, w ∈ U := by
    by_cases hw : w ∈ U
    · exact Or.inr ⟨0, hw⟩
    · exact Or.inl (mem_sdiff.mpr ⟨(hcover w).resolve_left hw, hw⟩)
  have hZcard : (Z₀.card : ℝ) ≤ Z.card := by
    exact_mod_cast card_le_card (sdiff_subset : Z \ U ⊆ Z)
  have hbudget₀ : a + (Z₀.card : ℝ) + 1 ≤ ε * Fintype.card V := by
    linarith only [hZcard, hbudget]
  obtain ⟨c⟩ := hfactor V G (fun _ : Fin 1 => U) (fun _ => H) Z₀ G.maxDegree a
    hn G.maxDegree_lt_card_verts G.degree_le_maxDegree
    (by nlinarith only [hdensity]) hno
    (fun i j hij => (hij (Subsingleton.elim i j)).elim) (fun _ => hUZ) hcover₀
    (fun _ => by nlinarith only [hsize]) (fun _ => hembed) (fun _ => hrobust)
    (fun _ => hcore) ha hbudget₀
  refine ⟨{ color := c.color, proper := ?_ }⟩
  intro e f w he hf h
  exact c.proper h he hf

end Overfull
