import Overfull.OneCore.MovedNeighbors
import Overfull.OrdinaryFactorization.ApexPalette

/-!
# Preserving the moved apex's supply on both shores

Balanced original simple neighbors provide enough actual complementary
incidences on each shore. Choosing the first group of color labels evenly
between the two rows leaves the stated supply on both shores, for every
proper coloring of the actual core complement.
-/

noncomputable section

namespace Overfull.OneCore

open Finset Classical SmallCuts OrdinaryFactorization

variable {V E : Type*} [Fintype E] {G : Multigraph V E} {U : Finset V}
variable {k : ℕ}

/-- The two actual complementary rows at an exterior vertex each retain
at least `t` original copies whose original colors avoid the chosen labels. -/
def apexSupply (C : Core G U) (y : V) (t : ℝ) (A B : Finset U) (h : ℕ)
    (c : (G.restrictEdges (coreEdges C)ᶜ).EdgeColoring k)
    (labels : Fin h ↪ Fin k) : Prop :=
  t ≤ ((((G.restrictEdges (coreEdges C)ᶜ).edgesTo y
    (A.map (Function.Embedding.subtype (fun v => v ∈ U)))).filter
      (fun e => c.color e ∉ Set.range labels)).card : ℝ) ∧
  t ≤ ((((G.restrictEdges (coreEdges C)ᶜ).edgesTo y
    (B.map (Function.Embedding.subtype (fun v => v ∈ U)))).filter
      (fun e => c.color e ∉ Set.range labels)).card : ℝ)

private theorem row_budget (k h n d : ℕ) (a t : ℝ)
    (hneighbors : (k : ℝ) - a ≤ 2 * n + 1)
    (hlabels : (h : ℝ) ≤ 3 * k / 5)
    (hbudget : t + a / 2 + 1 ≤ (k : ℝ) / 5)
    (hd : 2 * d ≤ h + 1) : t + d ≤ (n : ℝ) := by
  have hd' : 2 * (d : ℝ) ≤ h + 1 := by exact_mod_cast hd
  linarith

/-- For any original coloring of the new core complement, select the first
group of labels while retaining the required supply on both shores. -/
theorem exists_apexSupply (C : Core G U) (y : U)
    (A B : Finset ↥(U \ {y.val})) (k h : ℕ) (a t : ℝ)
    (hAB : Disjoint A B)
    (hbalanceA : (movedNeighbors C y).card ≤ 2 * (movedNeighbors C y ∩ A).card + 1)
    (hbalanceB : (movedNeighbors C y).card ≤ 2 * (movedNeighbors C y ∩ B).card + 1)
    (hdegree : (k : ℝ) - a ≤ (C.graph.degree y : ℝ))
    (hlabels : (h : ℝ) ≤ 3 * k / 5) (ht : 0 ≤ t)
    (hbudget : t + a / 2 + 1 ≤ (k : ℝ) / 5)
    (c : (G.restrictEdges (coreEdges (restrictCore C {y.val}))ᶜ).EdgeColoring k) :
    ∃ labels : Fin h ↪ Fin k,
      apexSupply (restrictCore C {y.val}) y.val t A B h c labels := by
  let inc : ↥(U \ {y.val}) ↪ V :=
    Function.Embedding.subtype (fun v => v ∈ U \ {y.val})
  let AA := A.map inc
  let BB := B.map inc
  let R := G.restrictEdges (coreEdges (restrictCore C {y.val}))ᶜ
  have hy : y.val ∉ U \ {y.val} := by simp
  have hdisj : Disjoint AA BB := (Finset.disjoint_map inc).mpr hAB
  have hrowA : (movedNeighbors C y ∩ A).card ≤ (R.edgesTo y.val AA).card := by
    rw [complement_apex_row_card (restrictCore C {y.val}) y.val hy]
    exact movedNeighbors_shore_le C y A
  have hrowB : (movedNeighbors C y ∩ B).card ≤ (R.edgesTo y.val BB).card := by
    rw [complement_apex_row_card (restrictCore C {y.val}) y.val hy]
    exact movedNeighbors_shore_le C y B
  have hneighborA : (k : ℝ) - a ≤ 2 * (movedNeighbors C y ∩ A).card + 1 := by
    have hb : ((movedNeighbors C y).card : ℝ) ≤
        2 * (movedNeighbors C y ∩ A).card + 1 := by exact_mod_cast hbalanceA
    rw [movedNeighbors_card] at hb
    exact hdegree.trans hb
  have hneighborB : (k : ℝ) - a ≤ 2 * (movedNeighbors C y ∩ B).card + 1 := by
    have hb : ((movedNeighbors C y).card : ℝ) ≤
        2 * (movedNeighbors C y ∩ B).card + 1 := by exact_mod_cast hbalanceB
    rw [movedNeighbors_card] at hb
    exact hdegree.trans hb
  have hbudgetA : t + (h / 2 : ℕ) ≤ ((R.edgesTo y.val AA).card : ℝ) :=
    (row_budget k h _ (h / 2) a t hneighborA hlabels hbudget (by omega)).trans
      (by exact_mod_cast hrowA)
  have hbudgetB : t + (h - h / 2 : ℕ) ≤ ((R.edgesTo y.val BB).card : ℝ) :=
    (row_budget k h _ (h - h / 2) a t hneighborB hlabels hbudget (by omega)).trans
      (by exact_mod_cast hrowB)
  have hA : h / 2 ≤ (R.edgesTo y.val AA).card := by
    exact_mod_cast (show ((h / 2 : ℕ) : ℝ) ≤ ((R.edgesTo y.val AA).card : ℝ) by linarith)
  have hB : h - h / 2 ≤ (R.edgesTo y.val BB).card := by
    exact_mod_cast (show ((h - h / 2 : ℕ) : ℝ) ≤ ((R.edgesTo y.val BB).card : ℝ) by linarith)
  obtain ⟨labels, hleft, hright⟩ :=
    exists_labels_preserving_rows c y.val AA BB hdisj hA hB
  refine ⟨labels, ?_, ?_⟩
  · change t ≤ (((R.edgesTo y.val AA).filter
      (fun e => c.color e ∉ Set.range labels)).card : ℝ)
    rw [hleft, Nat.cast_sub hA]
    linarith
  · change t ≤ (((R.edgesTo y.val BB).filter
      (fun e => c.color e ∉ Set.range labels)).card : ℝ)
    rw [hright, Nat.cast_sub hB]
    linarith

/-- Completing the selected core matchings preserves the two exterior row
counts specified by `apexSupply` exactly. -/
theorem apexSupply_residual_rows (C : Core G U) (y : V) (hy : y ∉ U)
    (t : ℝ) (A B : Finset U) (h : ℕ)
    (c : (G.restrictEdges (coreEdges C)ᶜ).EdgeColoring k)
    (labels : Fin h ↪ Fin k) (N : Fin h → C.graph.Subgraph)
    (hsupply : apexSupply C y t A B h c labels) :
    t ≤ (((residualGraph C c labels N).edgesTo y
      (A.map (Function.Embedding.subtype (fun v => v ∈ U)))).card : ℝ) ∧
    t ≤ (((residualGraph C c labels N).edgesTo y
      (B.map (Function.Embedding.subtype (fun v => v ∈ U)))).card : ℝ) := by
  rw [residualGraph_apex_row_card C c labels N y hy,
    residualGraph_apex_row_card C c labels N y hy]
  exact hsupply

end Overfull.OneCore

namespace Overfull.OrdinaryFactorization.FirstHalfData

open Finset Classical SmallCuts

variable {V E : Type*} [Fintype V] [Fintype E]
variable {G : Multigraph V E} {U : Finset V} {C : Core G U} {k : ℕ}
variable {α ν τ ξ p σ κ δ μ : ℝ}

/-- A first-half construction carrying the chosen-label supply retains that
supply in its actual original-copy remainder. -/
theorem remaining_apex_supply
    (D : FirstHalfData G U C k α ν τ ξ p σ κ δ μ)
    (y : V) (hy : y ∉ U) (t : ℝ) (A B : Finset U)
    (hsupply : OneCore.apexSupply C y t A B D.count D.exteriorColor D.labels) :
    t ≤ ((D.remaining.edgesTo y
      (A.map (Function.Embedding.subtype (fun v => v ∈ U)))).card : ℝ) ∧
    t ≤ ((D.remaining.edgesTo y
      (B.map (Function.Embedding.subtype (fun v => v ∈ U)))).card : ℝ) :=
  OneCore.apexSupply_residual_rows C y hy t A B D.count
    D.exteriorColor D.labels D.matchings hsupply

end Overfull.OrdinaryFactorization.FirstHalfData
