import Overfull.ColorCoverage

/-!
# Actual perfect-matching factors from a regular multigraph coloring

Each color occurs exactly once at every vertex of full palette degree.
The color classes therefore give perfect matchings, pairwise disjoint on
the original edge-copy identities and covering every original copy.
-/

noncomputable section

namespace Overfull.BoundedExterior

open Finset Classical

variable {V E : Type*} [Fintype E]
variable {G : Multigraph V E} {k : ℕ}

/-- In a regular graph of full palette degree, each actual color class
is a perfect matching in the original multigraph. -/
theorem colorClass_isPerfectMatching (c : G.EdgeColoring k)
    (hregular : ∀ v, G.degree v = k) (i : Fin k) :
    G.IsPerfectMatching (c.colorClass i) := by
  apply G.isPerfectMatching_iff.mpr
  refine ⟨c.colorClass_isMatching i, ?_⟩
  intro v
  obtain ⟨f, hfi, hfv⟩ := c.covers_of_degree_eq v (hregular v) i
  exact ⟨f, mem_filter.mpr ⟨mem_univ _, hfi⟩, hfv⟩

/-- Distinct labels give disjoint sets of original copies. -/
theorem colorClasses_pairwise_disjoint (c : G.EdgeColoring k) :
    Pairwise (fun i j => Disjoint (c.colorClass i) (c.colorClass j)) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro f hfi hfj
  exact hij ((mem_filter.mp hfi).2.symm.trans (mem_filter.mp hfj).2)

/-- The actual color classes cover every original edge copy. -/
theorem colorClasses_union (c : G.EdgeColoring k) :
    univ.biUnion c.colorClass = univ := by
  ext f
  simp only [mem_biUnion, mem_univ, true_and, Multigraph.EdgeColoring.colorClass,
    mem_filter, iff_true]
  exact ⟨c.color f, rfl⟩

/-- An explicit one-factorization of a regular multigraph, expressed as
an exact partition of its original copies into perfect matchings. -/
theorem exists_oneFactorization_of_coloring (G : Multigraph V E) (k : ℕ)
    (hregular : ∀ v, G.degree v = k) (c : G.EdgeColoring k) :
    ∃ M : Fin k → Finset E,
      (∀ i, G.IsPerfectMatching (M i)) ∧
      Pairwise (fun i j => Disjoint (M i) (M j)) ∧
      univ.biUnion M = univ :=
  ⟨c.colorClass, colorClass_isPerfectMatching c hregular,
    colorClasses_pairwise_disjoint c, colorClasses_union c⟩

end Overfull.BoundedExterior
