import Overfull.Replacement.Graph
import Overfull.RobustStability

/-!
# Deleting the forbidden edges of a replacement core

The degree lost at a core vertex is at most the original degree error.
Consequently the actual replacement inherits robust expansion and the
required minimum degree.
-/

namespace Overfull.Replacement

open Classical SimpleGraph

variable {V : Type*} [Fintype V]

theorem induced_degree_le (G : SimpleGraph V) (U : Finset V) (v : U) :
    (G.induce (U : Set V)).degree v ≤ G.degree v.val := by
  rw [← lift_degree U (G.induce (U : Set V)) v]
  exact SimpleGraph.degree_le_of_le (lift_le U (G.induce (U : Set V)) G le_rfl)

theorem forbidden_degree_le (G : SimpleGraph V) (U : Finset V) (H : SimpleGraph U)
    (k : ℕ) (a : ℝ) (hH : H ≤ G.induce (U : Set V))
    (hdegree : ∀ v, G.degree v ≤ k)
    (hHdegree : ∀ v, (k : ℝ)-a ≤ H.degree v) (v : U) :
    ((G.induce (U : Set V) \ H).degree v : ℝ) ≤ a := by
  have hid := BipartitePackingAccounting.degree_sdiff_add_of_le
    (G.induce (U : Set V)) H hH v
  have hu := (induced_degree_le G U v).trans (hdegree v.val)
  have hl := hHdegree v
  have hidR : ((G.induce (U : Set V) \ H).degree v : ℝ) + H.degree v =
      (G.induce (U : Set V)).degree v := by exact_mod_cast hid
  have huR : ((G.induce (U : Set V)).degree v : ℝ) ≤ k := by exact_mod_cast hu
  linarith

theorem core_degree_loss (G : SimpleGraph V) (U : Finset V) (H R : SimpleGraph U)
    (k : ℕ) (a : ℝ) (hH : H ≤ G.induce (U : Set V))
    (hdegree : ∀ v, G.degree v ≤ k)
    (hHdegree : ∀ v, (k : ℝ)-a ≤ H.degree v) (v : U) :
    (R.degree v : ℝ) ≤ (core G U H R).degree v + a := by
  have hid := BipartitePackingAccounting.degree_sdiff_add_degree_inf
    R (G.induce (U : Set V) \ H) v
  have hsub : R ⊓ (G.induce (U : Set V) \ H) ≤ G.induce (U : Set V) \ H := inf_le_right
  have hle := SimpleGraph.degree_le_of_le hsub (v := v)
  have hf := forbidden_degree_le G U H k a hH hdegree hHdegree v
  have hidR : ((core G U H R).degree v : ℝ) +
      (R ⊓ (G.induce (U : Set V) \ H)).degree v = R.degree v := by
    simp only [core, ← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] at hid ⊢
    exact_mod_cast hid
  have hleR : ((R ⊓ (G.induce (U : Set V) \ H)).degree v : ℝ) ≤
      (G.induce (U : Set V) \ H).degree v := by exact_mod_cast hle
  linarith

theorem core_degree_lower (G : SimpleGraph V) (U : Finset V) (H R : SimpleGraph U)
    (k r : ℕ) (a : ℝ) (hH : H ≤ G.induce (U : Set V))
    (hdegree : ∀ v, G.degree v ≤ k)
    (hHdegree : ∀ v, (k : ℝ)-a ≤ H.degree v)
    (hR : ∀ v, R.degree v = r) (hr : (k : ℝ)-a-1 ≤ r) (v : U) :
    (k : ℝ)-2*a-1 ≤ (core G U H R).degree v := by
  have hh := core_degree_loss G U H R k a hH hdegree hHdegree v
  rw [hR v] at hh
  linarith

theorem core_robust [DecidableEq V] (G : SimpleGraph V) (U : Finset V) (H R : SimpleGraph U)
    (k : ℕ) (a ν μ τ : ℝ) (hH : H ≤ G.induce (U : Set V))
    (hdegree : ∀ v, G.degree v ≤ k)
    (hHdegree : ∀ v, (k : ℝ)-a ≤ H.degree v)
    (hR : IsRobustExpander R ν τ) (hμ : 0 ≤ μ) (ha : a ≤ μ*U.card) :
    IsRobustExpander (core G U H R) (ν-μ) τ := by
  apply IsRobustExpander.after_edge_deletion R (core G U H R) hR
    (core_le G U H R) hμ
  intro v
  have hh := core_degree_loss G U H R k a hH hdegree hHdegree v
  simpa only [Fintype.card_coe] using hh.trans (add_le_add_left ha _)

end Overfull.Replacement
